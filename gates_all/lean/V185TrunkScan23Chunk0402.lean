import V185TrunkScan23Chunk0401

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2377603 : List Nat := [1, 1, 1, 3, 4, 2, 2, 4, 1, 4]
def baseStart_2377603 : Nat := 118140960795 + 2377603 * 2 ^ 59
def prefixEnd_2377603 : Nat := 4983230072969 + 3 ^ 40 * 2377603 * 2
def baseEnd_2377603 : Nat := 406951048190655450342703

theorem tailTrace_2377603 : CollatzResearch.WordTrace tailWord_2377603 prefixEnd_2377603 406951048190655450342703 := by
  unfold tailWord_2377603
  simp only [CollatzResearch.WordTrace]
  refine ⟨86718305605357868109241463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57812203736905245406160975 86718305605357868109241463)
  ·
    refine ⟨130077458408036802163862195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86718305605357868109241463 130077458408036802163862195)
    ·
      refine ⟨195116187612055203245793293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130077458408036802163862195 195116187612055203245793293)
      ·
        refine ⟨73168570354520701217172485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 195116187612055203245793293 73168570354520701217172485)
        ·
          refine ⟨13719106941472631478219841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73168570354520701217172485 13719106941472631478219841)
          ·
            refine ⟨10289330206104473608664881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13719106941472631478219841 10289330206104473608664881)
            ·
              refine ⟨7716997654578355206498661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10289330206104473608664881 7716997654578355206498661)
              ·
                refine ⟨1446937060233441601218499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7716997654578355206498661 1446937060233441601218499)
                ·
                  refine ⟨2170405590350162401827749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1446937060233441601218499 2170405590350162401827749)
                  ·
                    refine ⟨406951048190655450342703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2170405590350162401827749 406951048190655450342703)
                    ·
                      rfl

theorem cell23_2377603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 4, 1, 4].length) (baseStart_2377603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2377603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2377603 prefixEnd_2377603 := by exact prefixLift 2377603
  have htrace : WordTrace (prefixWord ++ tailWord_2377603) baseStart_2377603 baseEnd_2377603 := by
    simpa [prefixWord, tailWord_2377603, baseEnd_2377603] using wordTrace_append hprefix tailTrace_2377603
  have hstable : (prefixWord ++ tailWord_2377603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377603).length < 2 ^ (prefixWord ++ tailWord_2377603).sum := by decide
  have hdescent : baseEnd_2377603 < baseStart_2377603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377653 : List Nat := [1, 3, 3, 2, 1, 2, 1, 1, 4, 3, 2]
def baseStart_2377653 : Nat := 118140960795 + 2377653 * 2 ^ 59
def prefixEnd_2377653 : Nat := 4983230072969 + 3 ^ 40 * 2377653 * 2
def baseEnd_2377653 : Nat := 1220878818604691155402879

theorem tailTrace_2377653 : CollatzResearch.WordTrace tailWord_2377653 prefixEnd_2377653 1220878818604691155402879 := by
  unfold tailWord_2377653
  simp only [CollatzResearch.WordTrace]
  refine ⟨86720129255176726648561613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57813419503451151099041075 86720129255176726648561613)
  ·
    refine ⟨32520048470691272493210605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86720129255176726648561613 32520048470691272493210605)
    ·
      refine ⟨12195018176509227184953977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32520048470691272493210605 12195018176509227184953977)
      ·
        refine ⟨9146263632381920388715483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12195018176509227184953977 9146263632381920388715483)
        ·
          refine ⟨13719395448572880583073225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9146263632381920388715483 13719395448572880583073225)
          ·
            refine ⟨10289546586429660437304919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13719395448572880583073225 10289546586429660437304919)
            ·
              refine ⟨15434319879644490655957379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10289546586429660437304919 15434319879644490655957379)
              ·
                refine ⟨23151479819466735983936069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15434319879644490655957379 23151479819466735983936069)
                ·
                  refine ⟨4340902466150012996988013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23151479819466735983936069 4340902466150012996988013)
                  ·
                    refine ⟨1627838424806254873870505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4340902466150012996988013 1627838424806254873870505)
                    ·
                      refine ⟨1220878818604691155402879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1627838424806254873870505 1220878818604691155402879)
                      ·
                        rfl

theorem cell23_2377653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_2377653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2377653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2377653 prefixEnd_2377653 := by exact prefixLift 2377653
  have htrace : WordTrace (prefixWord ++ tailWord_2377653) baseStart_2377653 baseEnd_2377653 := by
    simpa [prefixWord, tailWord_2377653, baseEnd_2377653] using wordTrace_append hprefix tailTrace_2377653
  have hstable : (prefixWord ++ tailWord_2377653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377653).length < 2 ^ (prefixWord ++ tailWord_2377653).sum := by decide
  have hdescent : baseEnd_2377653 < baseStart_2377653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377669 : List Nat := [1, 3, 1, 1, 1, 1, 1, 5, 3, 1, 5]
def baseStart_2377669 : Nat := 118140960795 + 2377669 * 2 ^ 59
def prefixEnd_2377669 : Nat := 4983230072969 + 3 ^ 40 * 2377669 * 2
def baseEnd_2377669 : Nat := 1220887034295163092802805

theorem tailTrace_2377669 : CollatzResearch.WordTrace tailWord_2377669 prefixEnd_2377669 1220887034295163092802805 := by
  unfold tailWord_2377669
  simp only [CollatzResearch.WordTrace]
  refine ⟨86720712823118761381144061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57813808548745840920762707 86720712823118761381144061)
  ·
    refine ⟨32520267308669535517929023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86720712823118761381144061 32520267308669535517929023)
    ·
      refine ⟨48780400963004303276893535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32520267308669535517929023 48780400963004303276893535)
      ·
        refine ⟨73170601444506454915340303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48780400963004303276893535 73170601444506454915340303)
        ·
          refine ⟨109755902166759682373010455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73170601444506454915340303 109755902166759682373010455)
          ·
            refine ⟨164633853250139523559515683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109755902166759682373010455 164633853250139523559515683)
            ·
              refine ⟨246950779875209285339273525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164633853250139523559515683 246950779875209285339273525)
              ·
                refine ⟨23151635613300870500556893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 246950779875209285339273525 23151635613300870500556893)
                ·
                  refine ⟨8681863354987826437708835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23151635613300870500556893 8681863354987826437708835)
                  ·
                    refine ⟨13022795032481739656563253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8681863354987826437708835 13022795032481739656563253)
                    ·
                      refine ⟨1220887034295163092802805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13022795032481739656563253 1220887034295163092802805)
                      ·
                        rfl

theorem cell23_2377669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 1, 5].length) (baseStart_2377669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2377669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2377669 prefixEnd_2377669 := by exact prefixLift 2377669
  have htrace : WordTrace (prefixWord ++ tailWord_2377669) baseStart_2377669 baseEnd_2377669 := by
    simpa [prefixWord, tailWord_2377669, baseEnd_2377669] using wordTrace_append hprefix tailTrace_2377669
  have hstable : (prefixWord ++ tailWord_2377669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377669).length < 2 ^ (prefixWord ++ tailWord_2377669).sum := by decide
  have hdescent : baseEnd_2377669 < baseStart_2377669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377679 : List Nat := [1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 6]
def baseStart_2377679 : Nat := 118140960795 + 2377679 * 2 ^ 59
def prefixEnd_2377679 : Nat := 4983230072969 + 3 ^ 40 * 2377679 * 2
def baseEnd_2377679 : Nat := 1220892169101708053677759

theorem tailTrace_2377679 : CollatzResearch.WordTrace tailWord_2377679 prefixEnd_2377679 1220892169101708053677759 := by
  unfold tailWord_2377679
  simp only [CollatzResearch.WordTrace]
  refine ⟨86721077553082533089008091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57814051702055022059338727 86721077553082533089008091)
  ·
    refine ⟨130081616329623799633512137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86721077553082533089008091 130081616329623799633512137)
    ·
      refine ⟨97561212247217849725134103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130081616329623799633512137 97561212247217849725134103)
      ·
        refine ⟨146341818370826774587701155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97561212247217849725134103 146341818370826774587701155)
        ·
          refine ⟨219512727556240161881551733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146341818370826774587701155 219512727556240161881551733)
          ·
            refine ⟨20579318208397515176395475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 219512727556240161881551733 20579318208397515176395475)
            ·
              refine ⟨30868977312596272764593213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20579318208397515176395475 30868977312596272764593213)
              ·
                refine ⟨11575866492223602286722455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30868977312596272764593213 11575866492223602286722455)
                ·
                  refine ⟨17363799738335403430083683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11575866492223602286722455 17363799738335403430083683)
                  ·
                    refine ⟨26045699607503105145125525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17363799738335403430083683 26045699607503105145125525)
                    ·
                      refine ⟨1220892169101708053677759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26045699607503105145125525 1220892169101708053677759)
                      ·
                        rfl

theorem cell23_2377679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 6].length) (baseStart_2377679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2377679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2377679 prefixEnd_2377679 := by exact prefixLift 2377679
  have htrace : WordTrace (prefixWord ++ tailWord_2377679) baseStart_2377679 baseEnd_2377679 := by
    simpa [prefixWord, tailWord_2377679, baseEnd_2377679] using wordTrace_append hprefix tailTrace_2377679
  have hstable : (prefixWord ++ tailWord_2377679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377679).length < 2 ^ (prefixWord ++ tailWord_2377679).sum := by decide
  have hdescent : baseEnd_2377679 < baseStart_2377679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377693 : List Nat := [1, 4, 3, 1, 3, 1, 1, 2, 1, 6]
def baseStart_2377693 : Nat := 118140960795 + 2377693 * 2 ^ 59
def prefixEnd_2377693 : Nat := 4983230072969 + 3 ^ 40 * 2377693 * 2
def baseEnd_2377693 : Nat := 406966452610290332967565

theorem tailTrace_2377693 : CollatzResearch.WordTrace tailWord_2377693 prefixEnd_2377693 406966452610290332967565 := by
  unfold tailWord_2377693
  simp only [CollatzResearch.WordTrace]
  refine ⟨86721588175031813480017733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57814392116687875653345155 86721588175031813480017733)
  ·
    refine ⟨16260297782818465027503325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86721588175031813480017733 16260297782818465027503325)
    ·
      refine ⟨6097611668556924385313747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16260297782818465027503325 6097611668556924385313747)
      ·
        refine ⟨9146417502835386577970621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6097611668556924385313747 9146417502835386577970621)
        ·
          refine ⟨3429906563563269966738983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9146417502835386577970621 3429906563563269966738983)
          ·
            refine ⟨5144859845344904950108475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3429906563563269966738983 5144859845344904950108475)
            ·
              refine ⟨7717289768017357425162713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5144859845344904950108475 7717289768017357425162713)
              ·
                refine ⟨5787967326013018068872035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7717289768017357425162713 5787967326013018068872035)
                ·
                  refine ⟨8681950989019527103308053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5787967326013018068872035 8681950989019527103308053)
                  ·
                    refine ⟨406966452610290332967565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8681950989019527103308053 406966452610290332967565)
                    ·
                      rfl

theorem cell23_2377693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_2377693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2377693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2377693 prefixEnd_2377693 := by exact prefixLift 2377693
  have htrace : WordTrace (prefixWord ++ tailWord_2377693) baseStart_2377693 baseEnd_2377693 := by
    simpa [prefixWord, tailWord_2377693, baseEnd_2377693] using wordTrace_append hprefix tailTrace_2377693
  have hstable : (prefixWord ++ tailWord_2377693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377693).length < 2 ^ (prefixWord ++ tailWord_2377693).sum := by decide
  have hdescent : baseEnd_2377693 < baseStart_2377693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377710 : List Nat := [4, 1, 2, 1, 3, 2, 2, 2, 2, 4]
def baseStart_2377710 : Nat := 118140960795 + 2377710 * 2 ^ 59
def prefixEnd_2377710 : Nat := 4983230072969 + 3 ^ 40 * 2377710 * 2
def baseEnd_2377710 : Nat := 406969362333999144130039

theorem tailTrace_2377710 : CollatzResearch.WordTrace tailWord_2377710 prefixEnd_2377710 406969362333999144130039 := by
  unfold tailWord_2377710
  simp only [CollatzResearch.WordTrace]
  refine ⟨10840276026996278172923323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57814805477313483588924389 10840276026996278172923323)
  ·
    refine ⟨16260414040494417259384985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10840276026996278172923323 16260414040494417259384985)
    ·
      refine ⟨12195310530370812944538739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16260414040494417259384985 12195310530370812944538739)
      ·
        refine ⟨18292965795556219416808109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12195310530370812944538739 18292965795556219416808109)
        ·
          refine ⟨6859862173333582281303041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18292965795556219416808109 6859862173333582281303041)
          ·
            refine ⟨5144896630000186710977281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6859862173333582281303041 5144896630000186710977281)
            ·
              refine ⟨3858672472500140033232961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5144896630000186710977281 3858672472500140033232961)
              ·
                refine ⟨2894004354375105024924721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3858672472500140033232961 2894004354375105024924721)
                ·
                  refine ⟨2170503265781328768693541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2894004354375105024924721 2170503265781328768693541)
                  ·
                    refine ⟨406969362333999144130039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2170503265781328768693541 406969362333999144130039)
                    ·
                      rfl

theorem cell23_2377710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_2377710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2377710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2377710 prefixEnd_2377710 := by exact prefixLift 2377710
  have htrace : WordTrace (prefixWord ++ tailWord_2377710) baseStart_2377710 baseEnd_2377710 := by
    simpa [prefixWord, tailWord_2377710, baseEnd_2377710] using wordTrace_append hprefix tailTrace_2377710
  have hstable : (prefixWord ++ tailWord_2377710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377710).length < 2 ^ (prefixWord ++ tailWord_2377710).sum := by decide
  have hdescent : baseEnd_2377710 < baseStart_2377710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377733 : List Nat := [1, 3, 1, 1, 2, 5, 2, 1, 1, 3, 3]
def baseStart_2377733 : Nat := 118140960795 + 2377733 * 2 ^ 59
def prefixEnd_2377733 : Nat := 4983230072969 + 3 ^ 40 * 2377733 * 2
def baseEnd_2377733 : Nat := 1220919897057050842402511

theorem tailTrace_2377733 : CollatzResearch.WordTrace tailWord_2377733 prefixEnd_2377733 1220919897057050842402511 := by
  unfold tailWord_2377733
  simp only [CollatzResearch.WordTrace]
  refine ⟨86723047094886900311473853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57815364729924600207649235 86723047094886900311473853)
  ·
    refine ⟨32521142660582587616802695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86723047094886900311473853 32521142660582587616802695)
    ·
      refine ⟨48781713990873881425204043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32521142660582587616802695 48781713990873881425204043)
      ·
        refine ⟨73172570986310822137806065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48781713990873881425204043 73172570986310822137806065)
        ·
          refine ⟨54879428239733116603354549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73172570986310822137806065 54879428239733116603354549)
          ·
            refine ⟨5144946397474979681564489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54879428239733116603354549 5144946397474979681564489)
            ·
              refine ⟨3858709798106234761173367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5144946397474979681564489 3858709798106234761173367)
              ·
                refine ⟨5788064697159352141760051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3858709798106234761173367 5788064697159352141760051)
                ·
                  refine ⟨8682097045739028212640077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5788064697159352141760051 8682097045739028212640077)
                  ·
                    refine ⟨3255786392152135579740029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8682097045739028212640077 3255786392152135579740029)
                    ·
                      refine ⟨1220919897057050842402511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3255786392152135579740029 1220919897057050842402511)
                      ·
                        rfl

theorem cell23_2377733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 3, 3].length) (baseStart_2377733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2377733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2377733 prefixEnd_2377733 := by exact prefixLift 2377733
  have htrace : WordTrace (prefixWord ++ tailWord_2377733) baseStart_2377733 baseEnd_2377733 := by
    simpa [prefixWord, tailWord_2377733, baseEnd_2377733] using wordTrace_append hprefix tailTrace_2377733
  have hstable : (prefixWord ++ tailWord_2377733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377733).length < 2 ^ (prefixWord ++ tailWord_2377733).sum := by decide
  have hdescent : baseEnd_2377733 < baseStart_2377733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377767 : List Nat := [1, 1, 7, 1, 2, 1, 1, 1, 4, 1, 3]
def baseStart_2377767 : Nat := 118140960795 + 2377767 * 2 ^ 59
def prefixEnd_2377767 : Nat := 4983230072969 + 3 ^ 40 * 2377767 * 2
def baseEnd_2377767 : Nat := 1220937355399303709377355

theorem tailTrace_2377767 : CollatzResearch.WordTrace tailWord_2377767 prefixEnd_2377767 1220937355399303709377355 := by
  unfold tailWord_2377767
  simp only [CollatzResearch.WordTrace]
  refine ⟨86724287176763724118211555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57816191451175816078807703 86724287176763724118211555)
  ·
    refine ⟨130086430765145586177317333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86724287176763724118211555 130086430765145586177317333)
    ·
      refine ⟨3048900721058099676030875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 130086430765145586177317333 3048900721058099676030875)
      ·
        refine ⟨4573351081587149514046313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3048900721058099676030875 4573351081587149514046313)
        ·
          refine ⟨3430013311190362135534735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4573351081587149514046313 3430013311190362135534735)
          ·
            refine ⟨5145019966785543203302103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3430013311190362135534735 5145019966785543203302103)
            ·
              refine ⟨7717529950178314804953155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5145019966785543203302103 7717529950178314804953155)
              ·
                refine ⟨11576294925267472207429733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7717529950178314804953155 11576294925267472207429733)
                ·
                  refine ⟨2170555298487651038893075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11576294925267472207429733 2170555298487651038893075)
                  ·
                    refine ⟨3255832947731476558339613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2170555298487651038893075 3255832947731476558339613)
                    ·
                      refine ⟨1220937355399303709377355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3255832947731476558339613 1220937355399303709377355)
                      ·
                        rfl

theorem cell23_2377767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_2377767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2377767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2377767 prefixEnd_2377767 := by exact prefixLift 2377767
  have htrace : WordTrace (prefixWord ++ tailWord_2377767) baseStart_2377767 baseEnd_2377767 := by
    simpa [prefixWord, tailWord_2377767, baseEnd_2377767] using wordTrace_append hprefix tailTrace_2377767
  have hstable : (prefixWord ++ tailWord_2377767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377767).length < 2 ^ (prefixWord ++ tailWord_2377767).sum := by decide
  have hdescent : baseEnd_2377767 < baseStart_2377767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377833 : List Nat := [1, 2, 1, 1, 1, 5, 2, 1, 2, 5, 2]
def baseStart_2377833 : Nat := 118140960795 + 2377833 * 2 ^ 59
def prefixEnd_2377833 : Nat := 4983230072969 + 3 ^ 40 * 2377833 * 2
def baseEnd_2377833 : Nat := 1220971245122500451152051

theorem tailTrace_2377833 : CollatzResearch.WordTrace tailWord_2377833 prefixEnd_2377833 1220971245122500451152051 := by
  unfold tailWord_2377833
  simp only [CollatzResearch.WordTrace]
  refine ⟨86726694394524617390114153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57817796263016411593409435 86726694394524617390114153)
  ·
    refine ⟨65045020795893463042585615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86726694394524617390114153 65045020795893463042585615)
    ·
      refine ⟨97567531193840194563878423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65045020795893463042585615 97567531193840194563878423)
      ·
        refine ⟨146351296790760291845817635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97567531193840194563878423 146351296790760291845817635)
        ·
          refine ⟨219526945186140437768726453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146351296790760291845817635 219526945186140437768726453)
          ·
            refine ⟨20580651111200666040818105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 219526945186140437768726453 20580651111200666040818105)
            ·
              refine ⟨15435488333400499530613579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20580651111200666040818105 15435488333400499530613579)
              ·
                refine ⟨23153232500100749295920369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15435488333400499530613579 23153232500100749295920369)
                ·
                  refine ⟨17364924375075561971940277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23153232500100749295920369 17364924375075561971940277)
                  ·
                    refine ⟨1627961660163333934869401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17364924375075561971940277 1627961660163333934869401)
                    ·
                      refine ⟨1220971245122500451152051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1627961660163333934869401 1220971245122500451152051)
                      ·
                        rfl

theorem cell23_2377833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 5, 2].length) (baseStart_2377833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2377833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2377833 prefixEnd_2377833 := by exact prefixLift 2377833
  have htrace : WordTrace (prefixWord ++ tailWord_2377833) baseStart_2377833 baseEnd_2377833 := by
    simpa [prefixWord, tailWord_2377833, baseEnd_2377833] using wordTrace_append hprefix tailTrace_2377833
  have hstable : (prefixWord ++ tailWord_2377833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377833).length < 2 ^ (prefixWord ++ tailWord_2377833).sum := by decide
  have hdescent : baseEnd_2377833 < baseStart_2377833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377836 : List Nat := [2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 7]
def baseStart_2377836 : Nat := 118140960795 + 2377836 * 2 ^ 59
def prefixEnd_2377836 : Nat := 4983230072969 + 3 ^ 40 * 2377836 * 2
def baseEnd_2377836 : Nat := 1220972785564463939414537

theorem tailTrace_2377836 : CollatzResearch.WordTrace tailWord_2377836 prefixEnd_2377836 1220972785564463939414537 := by
  unfold tailWord_2377836
  simp only [CollatzResearch.WordTrace]
  refine ⟨43363401906756874451236681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57817869209009165934982241 43363401906756874451236681)
  ·
    refine ⟨32522551430067655838427511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43363401906756874451236681 32522551430067655838427511)
    ·
      refine ⟨48783827145101483757641267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32522551430067655838427511 48783827145101483757641267)
      ·
        refine ⟨73175740717652225636461901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48783827145101483757641267 73175740717652225636461901)
        ·
          refine ⟨27440902769119584613673213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73175740717652225636461901 27440902769119584613673213)
          ·
            refine ⟨10290338538419844230127455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27440902769119584613673213 10290338538419844230127455)
            ·
              refine ⟨15435507807629766345191183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10290338538419844230127455 15435507807629766345191183)
              ·
                refine ⟨23153261711444649517786775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15435507807629766345191183 23153261711444649517786775)
                ·
                  refine ⟨34729892567166974276680163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23153261711444649517786775 34729892567166974276680163)
                  ·
                    refine ⟨52094838850750461415020245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34729892567166974276680163 52094838850750461415020245)
                    ·
                      refine ⟨1220972785564463939414537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 52094838850750461415020245 1220972785564463939414537)
                      ·
                        rfl

theorem cell23_2377836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 7].length) (baseStart_2377836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2377836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2377836 prefixEnd_2377836 := by exact prefixLift 2377836
  have htrace : WordTrace (prefixWord ++ tailWord_2377836) baseStart_2377836 baseEnd_2377836 := by
    simpa [prefixWord, tailWord_2377836, baseEnd_2377836] using wordTrace_append hprefix tailTrace_2377836
  have hstable : (prefixWord ++ tailWord_2377836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377836).length < 2 ^ (prefixWord ++ tailWord_2377836).sum := by decide
  have hdescent : baseEnd_2377836 < baseStart_2377836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377863 : List Nat := [1, 1, 4, 2, 1, 1, 3, 3, 2, 1, 4]
def baseStart_2377863 : Nat := 118140960795 + 2377863 * 2 ^ 59
def prefixEnd_2377863 : Nat := 4983230072969 + 3 ^ 40 * 2377863 * 2
def baseEnd_2377863 : Nat := 1220986649542135333776913

theorem tailTrace_2377863 : CollatzResearch.WordTrace tailWord_2377863 prefixEnd_2377863 1220986649542135333776913 := by
  unfold tailWord_2377863
  simp only [CollatzResearch.WordTrace]
  refine ⟨86727788584415932513706243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57818525722943955009137495 86727788584415932513706243)
  ·
    refine ⟨130091682876623898770559365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86727788584415932513706243 130091682876623898770559365)
    ·
      refine ⟨24392190539366981019479881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130091682876623898770559365 24392190539366981019479881)
      ·
        refine ⟨18294142904525235764609911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24392190539366981019479881 18294142904525235764609911)
        ·
          refine ⟨27441214356787853646914867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18294142904525235764609911 27441214356787853646914867)
          ·
            refine ⟨41161821535181780470372301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27441214356787853646914867 41161821535181780470372301)
            ·
              refine ⟨15435683075693167676389613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41161821535181780470372301 15435683075693167676389613)
              ·
                refine ⟨5788381153384937878646105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15435683075693167676389613 5788381153384937878646105)
                ·
                  refine ⟨4341285865038703408984579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5788381153384937878646105 4341285865038703408984579)
                  ·
                    refine ⟨6511928797558055113476869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4341285865038703408984579 6511928797558055113476869)
                    ·
                      refine ⟨1220986649542135333776913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6511928797558055113476869 1220986649542135333776913)
                      ·
                        rfl

theorem cell23_2377863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_2377863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2377863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2377863 prefixEnd_2377863 := by exact prefixLift 2377863
  have htrace : WordTrace (prefixWord ++ tailWord_2377863) baseStart_2377863 baseEnd_2377863 := by
    simpa [prefixWord, tailWord_2377863, baseEnd_2377863] using wordTrace_append hprefix tailTrace_2377863
  have hstable : (prefixWord ++ tailWord_2377863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377863).length < 2 ^ (prefixWord ++ tailWord_2377863).sum := by decide
  have hdescent : baseEnd_2377863 < baseStart_2377863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377883 : List Nat := [1, 1, 1, 1, 1, 1, 2, 8, 2, 2, 3]
def baseStart_2377883 : Nat := 118140960795 + 2377883 * 2 ^ 59
def prefixEnd_2377883 : Nat := 4983230072969 + 3 ^ 40 * 2377883 * 2
def baseEnd_2377883 : Nat := 1220996919155225255526821

theorem tailTrace_2377883 : CollatzResearch.WordTrace tailWord_2377883 prefixEnd_2377883 1220996919155225255526821 := by
  unfold tailWord_2377883
  simp only [CollatzResearch.WordTrace]
  refine ⟨86728518044343475929434303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57819012029562317286289535 86728518044343475929434303)
  ·
    refine ⟨130092777066515213894151455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86728518044343475929434303 130092777066515213894151455)
    ·
      refine ⟨195139165599772820841227183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130092777066515213894151455 195139165599772820841227183)
      ·
        refine ⟨292708748399659231261840775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195139165599772820841227183 292708748399659231261840775)
        ·
          refine ⟨439063122599488846892761163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 292708748399659231261840775 439063122599488846892761163)
          ·
            refine ⟨658594683899233270339141745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 439063122599488846892761163 658594683899233270339141745)
            ·
              refine ⟨493946012924424952754356309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 658594683899233270339141745 493946012924424952754356309)
              ·
                refine ⟨5788429838958104915090113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 493946012924424952754356309 5788429838958104915090113)
                ·
                  refine ⟨4341322379218578686317585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5788429838958104915090113 4341322379218578686317585)
                  ·
                    refine ⟨3255991784413934014738189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4341322379218578686317585 3255991784413934014738189)
                    ·
                      refine ⟨1220996919155225255526821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3255991784413934014738189 1220996919155225255526821)
                      ·
                        rfl

theorem cell23_2377883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 2, 2, 3].length) (baseStart_2377883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2377883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2377883 prefixEnd_2377883 := by exact prefixLift 2377883
  have htrace : WordTrace (prefixWord ++ tailWord_2377883) baseStart_2377883 baseEnd_2377883 := by
    simpa [prefixWord, tailWord_2377883, baseEnd_2377883] using wordTrace_append hprefix tailTrace_2377883
  have hstable : (prefixWord ++ tailWord_2377883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377883).length < 2 ^ (prefixWord ++ tailWord_2377883).sum := by decide
  have hdescent : baseEnd_2377883 < baseStart_2377883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377924 : List Nat := [2, 3, 3, 1, 2, 2, 2, 3, 1, 4]
def baseStart_2377924 : Nat := 118140960795 + 2377924 * 2 ^ 59
def prefixEnd_2377924 : Nat := 4983230072969 + 3 ^ 40 * 2377924 * 2
def baseEnd_2377924 : Nat := 407005990620686531704711

theorem tailTrace_2377924 : CollatzResearch.WordTrace tailWord_2377924 prefixEnd_2377924 407005990620686531704711 := by
  unfold tailWord_2377924
  simp only [CollatzResearch.WordTrace]
  refine ⟨43365006718597469965838413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57820008958129959954451217 43365006718597469965838413)
  ·
    refine ⟨16261877519474051237189405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43365006718597469965838413 16261877519474051237189405)
    ·
      refine ⟨6098204069802769213946027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16261877519474051237189405 6098204069802769213946027)
      ·
        refine ⟨9147306104704153820919041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6098204069802769213946027 9147306104704153820919041)
        ·
          refine ⟨6860479578528115365689281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9147306104704153820919041 6860479578528115365689281)
          ·
            refine ⟨5145359683896086524266961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6860479578528115365689281 5145359683896086524266961)
            ·
              refine ⟨3859019762922064893200221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5145359683896086524266961 3859019762922064893200221)
              ·
                refine ⟨1447132411095774334950083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3859019762922064893200221 1447132411095774334950083)
                ·
                  refine ⟨2170698616643661502425125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1447132411095774334950083 2170698616643661502425125)
                  ·
                    refine ⟨407005990620686531704711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2170698616643661502425125 407005990620686531704711)
                    ·
                      rfl

theorem cell23_2377924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_2377924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2377924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2377924 prefixEnd_2377924 := by exact prefixLift 2377924
  have htrace : WordTrace (prefixWord ++ tailWord_2377924) baseStart_2377924 baseEnd_2377924 := by
    simpa [prefixWord, tailWord_2377924, baseEnd_2377924] using wordTrace_append hprefix tailTrace_2377924
  have hstable : (prefixWord ++ tailWord_2377924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377924).length < 2 ^ (prefixWord ++ tailWord_2377924).sum := by decide
  have hdescent : baseEnd_2377924 < baseStart_2377924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377930 : List Nat := [3, 1, 2, 1, 3, 1, 1, 2, 5, 1, 3]
def baseStart_2377930 : Nat := 118140960795 + 2377930 * 2 ^ 59
def prefixEnd_2377930 : Nat := 4983230072969 + 3 ^ 40 * 2377930 * 2
def baseEnd_2377930 : Nat := 1221021052745986571639105

theorem tailTrace_2377930 : CollatzResearch.WordTrace tailWord_2377930 prefixEnd_2377930 1221021052745986571639105 := by
  unfold tailWord_2377930
  simp only [CollatzResearch.WordTrace]
  refine ⟨21682558068793300739098811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57820154850115468637596829 21682558068793300739098811)
  ·
    refine ⟨32523837103189951108648217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21682558068793300739098811 32523837103189951108648217)
    ·
      refine ⟨24392877827392463331486163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32523837103189951108648217 24392877827392463331486163)
      ·
        refine ⟨36589316741088694997229245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24392877827392463331486163 36589316741088694997229245)
        ·
          refine ⟨13720993777908260623960967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36589316741088694997229245 13720993777908260623960967)
          ·
            refine ⟨20581490666862390935941451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13720993777908260623960967 20581490666862390935941451)
            ·
              refine ⟨30872236000293586403912177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20581490666862390935941451 30872236000293586403912177)
              ·
                refine ⟨23154177000220189802934133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30872236000293586403912177 23154177000220189802934133)
                ·
                  refine ⟨2170704093770642794025075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23154177000220189802934133 2170704093770642794025075)
                  ·
                    refine ⟨3256056140655964191037613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2170704093770642794025075 3256056140655964191037613)
                    ·
                      refine ⟨1221021052745986571639105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3256056140655964191037613 1221021052745986571639105)
                      ·
                        rfl

theorem cell23_2377930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 5, 1, 3].length) (baseStart_2377930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2377930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2377930 prefixEnd_2377930 := by exact prefixLift 2377930
  have htrace : WordTrace (prefixWord ++ tailWord_2377930) baseStart_2377930 baseEnd_2377930 := by
    simpa [prefixWord, tailWord_2377930, baseEnd_2377930] using wordTrace_append hprefix tailTrace_2377930
  have hstable : (prefixWord ++ tailWord_2377930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377930).length < 2 ^ (prefixWord ++ tailWord_2377930).sum := by decide
  have hdescent : baseEnd_2377930 < baseStart_2377930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377980 : List Nat := [2, 2, 2, 1, 4, 1, 1, 2, 4, 4]
def baseStart_2377980 : Nat := 118140960795 + 2377980 * 2 ^ 59
def prefixEnd_2377980 : Nat := 4983230072969 + 3 ^ 40 * 2377980 * 2
def baseEnd_2377980 : Nat := 407015575592903792004625

theorem tailTrace_2377980 : CollatzResearch.WordTrace tailWord_2377980 prefixEnd_2377980 407015575592903792004625 := by
  unfold tailWord_2377980
  simp only [CollatzResearch.WordTrace]
  refine ⟨43366027962496030747857697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57821370616661374330476929 43366027962496030747857697)
  ·
    refine ⟨32524520971872023060893273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43366027962496030747857697 32524520971872023060893273)
    ·
      refine ⟨24393390728904017295669955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32524520971872023060893273 24393390728904017295669955)
      ·
        refine ⟨36590086093356025943504933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24393390728904017295669955 36590086093356025943504933)
        ·
          refine ⟨6860641142504254864407175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36590086093356025943504933 6860641142504254864407175)
          ·
            refine ⟨10290961713756382296610763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6860641142504254864407175 10290961713756382296610763)
            ·
              refine ⟨15436442570634573444916145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10290961713756382296610763 15436442570634573444916145)
              ·
                refine ⟨11577331927975930083687109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15436442570634573444916145 11577331927975930083687109)
                ·
                  refine ⟨2170749736495486890691333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11577331927975930083687109 2170749736495486890691333)
                  ·
                    refine ⟨407015575592903792004625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2170749736495486890691333 407015575592903792004625)
                    ·
                      rfl

theorem cell23_2377980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 4, 4].length) (baseStart_2377980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2377980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2377980 prefixEnd_2377980 := by exact prefixLift 2377980
  have htrace : WordTrace (prefixWord ++ tailWord_2377980) baseStart_2377980 baseEnd_2377980 := by
    simpa [prefixWord, tailWord_2377980, baseEnd_2377980] using wordTrace_append hprefix tailTrace_2377980
  have hstable : (prefixWord ++ tailWord_2377980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377980).length < 2 ^ (prefixWord ++ tailWord_2377980).sum := by decide
  have hdescent : baseEnd_2377980 < baseStart_2377980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377983 : List Nat := [1, 1, 2, 2, 1, 4, 2, 1, 3, 2, 4]
def baseStart_2377983 : Nat := 118140960795 + 2377983 * 2 ^ 59
def prefixEnd_2377983 : Nat := 4983230072969 + 3 ^ 40 * 2377983 * 2
def baseEnd_2377983 : Nat := 1221048267220674864276361

theorem tailTrace_2377983 : CollatzResearch.WordTrace tailWord_2377983 prefixEnd_2377983 1221048267220674864276361 := by
  unfold tailWord_2377983
  simp only [CollatzResearch.WordTrace]
  refine ⟨86732165343981193008074603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57821443562654128672049735 86732165343981193008074603)
  ·
    refine ⟨130098248015971789512111905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86732165343981193008074603 130098248015971789512111905)
    ·
      refine ⟨97573686011978842134083929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130098248015971789512111905 97573686011978842134083929)
      ·
        refine ⟨73180264508984131600562947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97573686011978842134083929 73180264508984131600562947)
        ·
          refine ⟨109770396763476197400844421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73180264508984131600562947 109770396763476197400844421)
          ·
            refine ⟨20581949393151787012658329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109770396763476197400844421 20581949393151787012658329)
            ·
              refine ⟨15436462044863840259493747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20581949393151787012658329 15436462044863840259493747)
              ·
                refine ⟨23154693067295760389240621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15436462044863840259493747 23154693067295760389240621)
                ·
                  refine ⟨8683009900235910145965233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23154693067295760389240621 8683009900235910145965233)
                  ·
                    refine ⟨6512257425176932609473925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8683009900235910145965233 6512257425176932609473925)
                    ·
                      refine ⟨1221048267220674864276361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6512257425176932609473925 1221048267220674864276361)
                      ·
                        rfl

theorem cell23_2377983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 2, 4].length) (baseStart_2377983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2377983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2377983 prefixEnd_2377983 := by exact prefixLift 2377983
  have htrace : WordTrace (prefixWord ++ tailWord_2377983) baseStart_2377983 baseEnd_2377983 := by
    simpa [prefixWord, tailWord_2377983, baseEnd_2377983] using wordTrace_append hprefix tailTrace_2377983
  have hstable : (prefixWord ++ tailWord_2377983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377983).length < 2 ^ (prefixWord ++ tailWord_2377983).sum := by decide
  have hdescent : baseEnd_2377983 < baseStart_2377983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377993 : List Nat := [1, 2, 1, 1, 3, 6, 9]
def baseStart_2377993 : Nat := 118140960795 + 2377993 * 2 ^ 59
def prefixEnd_2377993 : Nat := 4983230072969 + 3 ^ 40 * 2377993 * 2
def baseEnd_2377993 : Nat := 15074733358360738582115

theorem tailTrace_2377993 : CollatzResearch.WordTrace tailWord_2377993 prefixEnd_2377993 15074733358360738582115 := by
  unfold tailWord_2377993
  simp only [CollatzResearch.WordTrace]
  refine ⟨86732530073944964715938633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57821686715963309810625755 86732530073944964715938633)
  ·
    refine ⟨65049397555458723536953975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86732530073944964715938633 65049397555458723536953975)
    ·
      refine ⟨97574096333188085305430963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65049397555458723536953975 97574096333188085305430963)
      ·
        refine ⟨146361144499782127958146445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97574096333188085305430963 146361144499782127958146445)
        ·
          refine ⟨54885429187418297984304917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146361144499782127958146445 54885429187418297984304917)
          ·
            refine ⟨2572754493160232718014293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 54885429187418297984304917 2572754493160232718014293)
            ·
              refine ⟨15074733358360738582115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2572754493160232718014293 15074733358360738582115)
              ·
                rfl

theorem cell23_2377993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 9].length) (baseStart_2377993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2377993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2377993 prefixEnd_2377993 := by exact prefixLift 2377993
  have htrace : WordTrace (prefixWord ++ tailWord_2377993) baseStart_2377993 baseEnd_2377993 := by
    simpa [prefixWord, tailWord_2377993, baseEnd_2377993] using wordTrace_append hprefix tailTrace_2377993
  have hstable : (prefixWord ++ tailWord_2377993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377993).length < 2 ^ (prefixWord ++ tailWord_2377993).sum := by decide
  have hdescent : baseEnd_2377993 < baseStart_2377993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378010 : List Nat := [3, 1, 1, 3, 4, 1, 2, 8]
def baseStart_2378010 : Nat := 118140960795 + 2378010 * 2 ^ 59
def prefixEnd_2378010 : Nat := 4983230072969 + 3 ^ 40 * 2378010 * 2
def baseEnd_2378010 : Nat := 45224523377716528097731

theorem tailTrace_2378010 : CollatzResearch.WordTrace tailWord_2378010 prefixEnd_2378010 45224523377716528097731 := by
  unfold tailWord_2378010
  simp only [CollatzResearch.WordTrace]
  refine ⟨21683287528720844154826871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57822100076588917746204989 21683287528720844154826871)
  ·
    refine ⟨32524931293081266232240307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21683287528720844154826871 32524931293081266232240307)
    ·
      refine ⟨48787396939621899348360461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32524931293081266232240307 48787396939621899348360461)
      ·
        refine ⟨18295273852358212255635173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48787396939621899348360461 18295273852358212255635173)
        ·
          refine ⟨3430363847317164797931595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18295273852358212255635173 3430363847317164797931595)
          ·
            refine ⟨5145545770975747196897393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3430363847317164797931595 5145545770975747196897393)
            ·
              refine ⟨3859159328231810397673045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5145545770975747196897393 3859159328231810397673045)
              ·
                refine ⟨45224523377716528097731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3859159328231810397673045 45224523377716528097731)
                ·
                  rfl

theorem cell23_2378010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 8].length) (baseStart_2378010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2378010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2378010 prefixEnd_2378010 := by exact prefixLift 2378010
  have htrace : WordTrace (prefixWord ++ tailWord_2378010) baseStart_2378010 baseEnd_2378010 := by
    simpa [prefixWord, tailWord_2378010, baseEnd_2378010] using wordTrace_append hprefix tailTrace_2378010
  have hstable : (prefixWord ++ tailWord_2378010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378010).length < 2 ^ (prefixWord ++ tailWord_2378010).sum := by decide
  have hdescent : baseEnd_2378010 < baseStart_2378010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378063 : List Nat := [1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 5]
def baseStart_2378063 : Nat := 118140960795 + 2378063 * 2 ^ 59
def prefixEnd_2378063 : Nat := 4983230072969 + 3 ^ 40 * 2378063 * 2
def baseEnd_2378063 : Nat := 1221089345673034551275993

theorem tailTrace_2378063 : CollatzResearch.WordTrace tailWord_2378063 prefixEnd_2378063 1221089345673034551275993 := by
  unfold tailWord_2378063
  simp only [CollatzResearch.WordTrace]
  refine ⟨86735083183691366670986843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57823388789127577780657895 86735083183691366670986843)
  ·
    refine ⟨130102624775537050006480265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86735083183691366670986843 130102624775537050006480265)
    ·
      refine ⟨97576968581652787504860199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130102624775537050006480265 97576968581652787504860199)
      ·
        refine ⟨146365452872479181257290299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97576968581652787504860199 146365452872479181257290299)
        ·
          refine ⟨219548179308718771885935449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146365452872479181257290299 219548179308718771885935449)
          ·
            refine ⟨164661134481539078914451587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 219548179308718771885935449 164661134481539078914451587)
            ·
              refine ⟨246991701722308618371677381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164661134481539078914451587 246991701722308618371677381)
              ·
                refine ⟨46310944072932865944689509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 246991701722308618371677381 46310944072932865944689509)
                ·
                  refine ⟨8683302013674912364629283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46310944072932865944689509 8683302013674912364629283)
                  ·
                    refine ⟨13024953020512368546943925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8683302013674912364629283 13024953020512368546943925)
                    ·
                      refine ⟨1221089345673034551275993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13024953020512368546943925 1221089345673034551275993)
                      ·
                        rfl

theorem cell23_2378063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 5].length) (baseStart_2378063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2378063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2378063 prefixEnd_2378063 := by exact prefixLift 2378063
  have htrace : WordTrace (prefixWord ++ tailWord_2378063) baseStart_2378063 baseEnd_2378063 := by
    simpa [prefixWord, tailWord_2378063, baseEnd_2378063] using wordTrace_append hprefix tailTrace_2378063
  have hstable : (prefixWord ++ tailWord_2378063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378063).length < 2 ^ (prefixWord ++ tailWord_2378063).sum := by decide
  have hdescent : baseEnd_2378063 < baseStart_2378063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378078 : List Nat := [4, 4, 2, 1, 1, 1, 3, 7]
def baseStart_2378078 : Nat := 118140960795 + 2378078 * 2 ^ 59
def prefixEnd_2378078 : Nat := 4983230072969 + 3 ^ 40 * 2378078 * 2
def baseEnd_2378078 : Nat := 45225816588253777503275

theorem tailTrace_2378078 : CollatzResearch.WordTrace tailWord_2378078 prefixEnd_2378078 45225816588253777503275 := by
  unfold tailWord_2378078
  simp only [CollatzResearch.WordTrace]
  refine ⟨10841953784829628029097861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57823753519091349488521925 10841953784829628029097861)
  ·
    refine ⟨2032866334655555255455849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10841953784829628029097861 2032866334655555255455849)
    ·
      refine ⟨1524649750991666441591887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2032866334655555255455849 1524649750991666441591887)
      ·
        refine ⟨2286974626487499662387831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1524649750991666441591887 2286974626487499662387831)
        ·
          refine ⟨3430461939731249493581747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2286974626487499662387831 3430461939731249493581747)
          ·
            refine ⟨5145692909596874240372621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3430461939731249493581747 5145692909596874240372621)
            ·
              refine ⟨1929634841098827840139733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5145692909596874240372621 1929634841098827840139733)
              ·
                refine ⟨45225816588253777503275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1929634841098827840139733 45225816588253777503275)
                ·
                  rfl

theorem cell23_2378078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 7].length) (baseStart_2378078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2378078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2378078 prefixEnd_2378078 := by exact prefixLift 2378078
  have htrace : WordTrace (prefixWord ++ tailWord_2378078) baseStart_2378078 baseEnd_2378078 := by
    simpa [prefixWord, tailWord_2378078, baseEnd_2378078] using wordTrace_append hprefix tailTrace_2378078
  have hstable : (prefixWord ++ tailWord_2378078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378078).length < 2 ^ (prefixWord ++ tailWord_2378078).sum := by decide
  have hdescent : baseEnd_2378078 < baseStart_2378078 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378167 : List Nat := [1, 1, 3, 1, 3, 4, 1, 2, 2, 1, 4]
def baseStart_2378167 : Nat := 118140960795 + 2378167 * 2 ^ 59
def prefixEnd_2378167 : Nat := 4983230072969 + 3 ^ 40 * 2378167 * 2
def baseEnd_2378167 : Nat := 1221142747661102144375515

theorem tailTrace_2378167 : CollatzResearch.WordTrace tailWord_2378167 prefixEnd_2378167 1221142747661102144375515 := by
  unfold tailWord_2378167
  simp only [CollatzResearch.WordTrace]
  refine ⟨86738876375314592432772755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57825917583543061621848503 86738876375314592432772755)
  ·
    refine ⟨130108314562971888649159133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86738876375314592432772755 130108314562971888649159133)
    ·
      refine ⟨48790617961114458243434675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130108314562971888649159133 48790617961114458243434675)
      ·
        refine ⟨73185926941671687365152013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48790617961114458243434675 73185926941671687365152013)
        ·
          refine ⟨27444722603126882761932005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73185926941671687365152013 27444722603126882761932005)
          ·
            refine ⟨5145885488086290517862251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27444722603126882761932005 5145885488086290517862251)
            ·
              refine ⟨7718828232129435776793377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5145885488086290517862251 7718828232129435776793377)
              ·
                refine ⟨5789121174097076832595033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7718828232129435776793377 5789121174097076832595033)
                ·
                  refine ⟨4341840880572807624446275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5789121174097076832595033 4341840880572807624446275)
                  ·
                    refine ⟨6512761320859211436669413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4341840880572807624446275 6512761320859211436669413)
                    ·
                      refine ⟨1221142747661102144375515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6512761320859211436669413 1221142747661102144375515)
                      ·
                        rfl

theorem cell23_2378167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 2, 1, 4].length) (baseStart_2378167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2378167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2378167 prefixEnd_2378167 := by exact prefixLift 2378167
  have htrace : WordTrace (prefixWord ++ tailWord_2378167) baseStart_2378167 baseEnd_2378167 := by
    simpa [prefixWord, tailWord_2378167, baseEnd_2378167] using wordTrace_append hprefix tailTrace_2378167
  have hstable : (prefixWord ++ tailWord_2378167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378167).length < 2 ^ (prefixWord ++ tailWord_2378167).sum := by decide
  have hdescent : baseEnd_2378167 < baseStart_2378167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378217 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 7, 1, 3]
def baseStart_2378217 : Nat := 118140960795 + 2378217 * 2 ^ 59
def prefixEnd_2378217 : Nat := 4983230072969 + 3 ^ 40 * 2378217 * 2
def baseEnd_2378217 : Nat := 1221168421693826948750285

theorem tailTrace_2378217 : CollatzResearch.WordTrace tailWord_2378217 prefixEnd_2378217 1221168421693826948750285 := by
  unfold tailWord_2378217
  simp only [CollatzResearch.WordTrace]
  refine ⟨86740700025133450972092905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57827133350088967314728603 86740700025133450972092905)
  ·
    refine ⟨65055525018850088229069679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86740700025133450972092905 65055525018850088229069679)
    ·
      refine ⟨97583287528275132343604519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65055525018850088229069679 97583287528275132343604519)
      ·
        refine ⟨146374931292412698515406779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97583287528275132343604519 146374931292412698515406779)
        ·
          refine ⟨219562396938619047773110169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146374931292412698515406779 219562396938619047773110169)
          ·
            refine ⟨164671797703964285829832627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 219562396938619047773110169 164671797703964285829832627)
            ·
              refine ⟨247007696555946428744748941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164671797703964285829832627 247007696555946428744748941)
              ·
                refine ⟨92627886208479910779280853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 247007696555946428744748941 92627886208479910779280853)
                ·
                  refine ⟨2170966083011247908889395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 92627886208479910779280853 2170966083011247908889395)
                  ·
                    refine ⟨3256449124516871863334093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2170966083011247908889395 3256449124516871863334093)
                    ·
                      refine ⟨1221168421693826948750285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3256449124516871863334093 1221168421693826948750285)
                      ·
                        rfl

theorem cell23_2378217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 7, 1, 3].length) (baseStart_2378217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2378217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2378217 prefixEnd_2378217 := by exact prefixLift 2378217
  have htrace : WordTrace (prefixWord ++ tailWord_2378217) baseStart_2378217 baseEnd_2378217 := by
    simpa [prefixWord, tailWord_2378217, baseEnd_2378217] using wordTrace_append hprefix tailTrace_2378217
  have hstable : (prefixWord ++ tailWord_2378217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378217).length < 2 ^ (prefixWord ++ tailWord_2378217).sum := by decide
  have hdescent : baseEnd_2378217 < baseStart_2378217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378257 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 1, 8, 2]
def baseStart_2378257 : Nat := 118140960795 + 2378257 * 2 ^ 59
def prefixEnd_2378257 : Nat := 4983230072969 + 3 ^ 40 * 2378257 * 2
def baseEnd_2378257 : Nat := 1221188960920006792250101

theorem tailTrace_2378257 : CollatzResearch.WordTrace tailWord_2378257 prefixEnd_2378257 1221188960920006792250101 := by
  unfold tailWord_2378257
  simp only [CollatzResearch.WordTrace]
  refine ⟨86742158944988537803549025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57828105963325691869032683 86742158944988537803549025)
  ·
    refine ⟨65056619208741403352661769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86742158944988537803549025 65056619208741403352661769)
    ·
      refine ⟨48792464406556052514496327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65056619208741403352661769 48792464406556052514496327)
      ·
        refine ⟨73188696609834078771744491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48792464406556052514496327 73188696609834078771744491)
        ·
          refine ⟨109783044914751118157616737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73188696609834078771744491 109783044914751118157616737)
          ·
            refine ⟨82337283686063338618212553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109783044914751118157616737 82337283686063338618212553)
            ·
              refine ⟨61752962764547503963659415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82337283686063338618212553 61752962764547503963659415)
              ·
                refine ⟨92629444146821255945489123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61752962764547503963659415 92629444146821255945489123)
                ·
                  refine ⟨138944166220231883918233685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92629444146821255945489123 138944166220231883918233685)
                  ·
                    refine ⟨1628251947893342389666801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 138944166220231883918233685 1628251947893342389666801)
                    ·
                      refine ⟨1221188960920006792250101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1628251947893342389666801 1221188960920006792250101)
                      ·
                        rfl

theorem cell23_2378257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 8, 2].length) (baseStart_2378257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2378257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2378257 prefixEnd_2378257 := by exact prefixLift 2378257
  have htrace : WordTrace (prefixWord ++ tailWord_2378257) baseStart_2378257 baseEnd_2378257 := by
    simpa [prefixWord, tailWord_2378257, baseEnd_2378257] using wordTrace_append hprefix tailTrace_2378257
  have hstable : (prefixWord ++ tailWord_2378257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378257).length < 2 ^ (prefixWord ++ tailWord_2378257).sum := by decide
  have hdescent : baseEnd_2378257 < baseStart_2378257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378268 : List Nat := [2, 2, 3, 1, 2, 3, 2, 3, 1, 1, 3]
def baseStart_2378268 : Nat := 118140960795 + 2378268 * 2 ^ 59
def prefixEnd_2378268 : Nat := 4983230072969 + 3 ^ 40 * 2378268 * 2
def baseEnd_2378268 : Nat := 1221194609207206249212551

theorem tailTrace_2378268 : CollatzResearch.WordTrace tailWord_2378268 prefixEnd_2378268 1221194609207206249212551 := by
  unfold tailWord_2378268
  simp only [CollatzResearch.WordTrace]
  refine ⟨43371280073974343341099729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57828373431965791121466305 43371280073974343341099729)
  ·
    refine ⟨32528460055480757505824797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43371280073974343341099729 32528460055480757505824797)
    ·
      refine ⟨12198172520805284064684299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32528460055480757505824797 12198172520805284064684299)
      ·
        refine ⟨18297258781207926097026449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12198172520805284064684299 18297258781207926097026449)
        ·
          refine ⟨13722944085905944572769837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18297258781207926097026449 13722944085905944572769837)
          ·
            refine ⟨5146104032214729214788689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13722944085905944572769837 5146104032214729214788689)
            ·
              refine ⟨3859578024161046911091517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5146104032214729214788689 3859578024161046911091517)
              ·
                refine ⟨1447341759060392591659319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3859578024161046911091517 1447341759060392591659319)
                ·
                  refine ⟨2171012638590588887488979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1447341759060392591659319 2171012638590588887488979)
                  ·
                    refine ⟨3256518957885883331233469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2171012638590588887488979 3256518957885883331233469)
                    ·
                      refine ⟨1221194609207206249212551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3256518957885883331233469 1221194609207206249212551)
                      ·
                        rfl

theorem cell23_2378268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 3, 1, 1, 3].length) (baseStart_2378268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2378268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2378268 prefixEnd_2378268 := by exact prefixLift 2378268
  have htrace : WordTrace (prefixWord ++ tailWord_2378268) baseStart_2378268 baseEnd_2378268 := by
    simpa [prefixWord, tailWord_2378268, baseEnd_2378268] using wordTrace_append hprefix tailTrace_2378268
  have hstable : (prefixWord ++ tailWord_2378268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378268).length < 2 ^ (prefixWord ++ tailWord_2378268).sum := by decide
  have hdescent : baseEnd_2378268 < baseStart_2378268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378291 : List Nat := [1, 1, 1, 2, 4, 2, 4, 1, 3, 2, 2]
def baseStart_2378291 : Nat := 118140960795 + 2378291 * 2 ^ 59
def prefixEnd_2378291 : Nat := 4983230072969 + 3 ^ 40 * 2378291 * 2
def baseEnd_2378291 : Nat := 1221206419262259659224945

theorem tailTrace_2378291 : CollatzResearch.WordTrace tailWord_2378291 prefixEnd_2378291 1221206419262259659224945 := by
  unfold tailWord_2378291
  simp only [CollatzResearch.WordTrace]
  refine ⟨86743399026865361610286727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57828932684576907740191151 86743399026865361610286727)
  ·
    refine ⟨130115098540298042415430091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86743399026865361610286727 130115098540298042415430091)
    ·
      refine ⟨195172647810447063623145137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130115098540298042415430091 195172647810447063623145137)
      ·
        refine ⟨146379485857835297717358853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195172647810447063623145137 146379485857835297717358853)
        ·
          refine ⟨27446153598344118322004785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 146379485857835297717358853 27446153598344118322004785)
          ·
            refine ⟨20584615198758088741503589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27446153598344118322004785 20584615198758088741503589)
            ·
              refine ⟨3859615349767141639031923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20584615198758088741503589 3859615349767141639031923)
              ·
                refine ⟨5789423024650712458547885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3859615349767141639031923 5789423024650712458547885)
                ·
                  refine ⟨2171033634244017171955457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5789423024650712458547885 2171033634244017171955457)
                  ·
                    refine ⟨1628275225683012878966593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2171033634244017171955457 1628275225683012878966593)
                    ·
                      refine ⟨1221206419262259659224945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1628275225683012878966593 1221206419262259659224945)
                      ·
                        rfl

theorem cell23_2378291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 3, 2, 2].length) (baseStart_2378291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2378291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2378291 prefixEnd_2378291 := by exact prefixLift 2378291
  have htrace : WordTrace (prefixWord ++ tailWord_2378291) baseStart_2378291 baseEnd_2378291 := by
    simpa [prefixWord, tailWord_2378291, baseEnd_2378291] using wordTrace_append hprefix tailTrace_2378291
  have hstable : (prefixWord ++ tailWord_2378291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378291).length < 2 ^ (prefixWord ++ tailWord_2378291).sum := by decide
  have hdescent : baseEnd_2378291 < baseStart_2378291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378294 : List Nat := [5, 1, 2, 1, 2, 1, 1, 1, 3, 1, 5]
def baseStart_2378294 : Nat := 118140960795 + 2378294 * 2 ^ 59
def prefixEnd_2378294 : Nat := 4983230072969 + 3 ^ 40 * 2378294 * 2
def baseEnd_2378294 : Nat := 1221207959704223147487431

theorem tailTrace_2378294 : CollatzResearch.WordTrace tailWord_2378294 prefixEnd_2378294 1221207959704223147487431 := by
  unfold tailWord_2378294
  simp only [CollatzResearch.WordTrace]
  refine ⟨5421469277865905820165371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57829005630569662081763957 5421469277865905820165371)
  ·
    refine ⟨8132203916798858730248057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5421469277865905820165371 8132203916798858730248057)
    ·
      refine ⟨6099152937599144047686043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8132203916798858730248057 6099152937599144047686043)
      ·
        refine ⟨9148729406398716071529065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6099152937599144047686043 9148729406398716071529065)
        ·
          refine ⟨6861547054799037053646799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9148729406398716071529065 6861547054799037053646799)
          ·
            refine ⟨10292320582198555580470199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6861547054799037053646799 10292320582198555580470199)
            ·
              refine ⟨15438480873297833370705299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10292320582198555580470199 15438480873297833370705299)
              ·
                refine ⟨23157721309946750056057949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15438480873297833370705299 23157721309946750056057949)
                ·
                  refine ⟨8684145491230031271021731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23157721309946750056057949 8684145491230031271021731)
                  ·
                    refine ⟨13026218236845046906532597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8684145491230031271021731 13026218236845046906532597)
                    ·
                      refine ⟨1221207959704223147487431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13026218236845046906532597 1221207959704223147487431)
                      ·
                        rfl

theorem cell23_2378294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_2378294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2378294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2378294 prefixEnd_2378294 := by exact prefixLift 2378294
  have htrace : WordTrace (prefixWord ++ tailWord_2378294) baseStart_2378294 baseEnd_2378294 := by
    simpa [prefixWord, tailWord_2378294, baseEnd_2378294] using wordTrace_append hprefix tailTrace_2378294
  have hstable : (prefixWord ++ tailWord_2378294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378294).length < 2 ^ (prefixWord ++ tailWord_2378294).sum := by decide
  have hdescent : baseEnd_2378294 < baseStart_2378294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378311 : List Nat := [1, 1, 4, 1, 4, 2, 2, 2, 1, 2, 3]
def baseStart_2378311 : Nat := 118140960795 + 2378311 * 2 ^ 59
def prefixEnd_2378311 : Nat := 4983230072969 + 3 ^ 40 * 2378311 * 2
def baseEnd_2378311 : Nat := 1221216688875349580974853

theorem tailTrace_2378311 : CollatzResearch.WordTrace tailWord_2378311 prefixEnd_2378311 1221216688875349580974853 := by
  unfold tailWord_2378311
  simp only [CollatzResearch.WordTrace]
  refine ⟨86744128486792905026014787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57829418991195270017343191 86744128486792905026014787)
  ·
    refine ⟨130116192730189357539022181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86744128486792905026014787 130116192730189357539022181)
    ·
      refine ⟨24396786136910504538566659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130116192730189357539022181 24396786136910504538566659)
      ·
        refine ⟨36595179205365756807849989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24396786136910504538566659 36595179205365756807849989)
        ·
          refine ⟨6861596101006079401471873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36595179205365756807849989 6861596101006079401471873)
          ·
            refine ⟨5146197075754559551103905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6861596101006079401471873 5146197075754559551103905)
            ·
              refine ⟨3859647806815919663327929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5146197075754559551103905 3859647806815919663327929)
              ·
                refine ⟨2894735855111939747495947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3859647806815919663327929 2894735855111939747495947)
                ·
                  refine ⟨4342103782667909621243921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2894735855111939747495947 4342103782667909621243921)
                  ·
                    refine ⟨3256577837000932215932941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4342103782667909621243921 3256577837000932215932941)
                    ·
                      refine ⟨1221216688875349580974853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3256577837000932215932941 1221216688875349580974853)
                      ·
                        rfl

theorem cell23_2378311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 2, 1, 2, 3].length) (baseStart_2378311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2378311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2378311 prefixEnd_2378311 := by exact prefixLift 2378311
  have htrace : WordTrace (prefixWord ++ tailWord_2378311) baseStart_2378311 baseEnd_2378311 := by
    simpa [prefixWord, tailWord_2378311, baseEnd_2378311] using wordTrace_append hprefix tailTrace_2378311
  have hstable : (prefixWord ++ tailWord_2378311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378311).length < 2 ^ (prefixWord ++ tailWord_2378311).sum := by decide
  have hdescent : baseEnd_2378311 < baseStart_2378311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378314 : List Nat := [3, 1, 2, 1, 1, 6, 2, 7]
def baseStart_2378314 : Nat := 118140960795 + 2378314 * 2 ^ 59
def prefixEnd_2378314 : Nat := 4983230072969 + 3 ^ 40 * 2378314 * 2
def baseEnd_2378314 : Nat := 45230304789530113675457

theorem tailTrace_2378314 : CollatzResearch.WordTrace tailWord_2378314 prefixEnd_2378314 45230304789530113675457 := by
  unfold tailWord_2378314
  simp only [CollatzResearch.WordTrace]
  refine ⟨21686059476445509134593499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57829491937188024358915997 21686059476445509134593499)
  ·
    refine ⟨32529089214668263701890249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21686059476445509134593499 32529089214668263701890249)
    ·
      refine ⟨24396816911001197776417687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32529089214668263701890249 24396816911001197776417687)
      ·
        refine ⟨36595225366501796664626531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24396816911001197776417687 36595225366501796664626531)
        ·
          refine ⟨54892838049752694996939797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36595225366501796664626531 54892838049752694996939797)
          ·
            refine ⟨2573101783582157577981553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 54892838049752694996939797 2573101783582157577981553)
            ·
              refine ⟨1929826337686618183486165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2573101783582157577981553 1929826337686618183486165)
              ·
                refine ⟨45230304789530113675457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1929826337686618183486165 45230304789530113675457)
                ·
                  rfl

theorem cell23_2378314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 7].length) (baseStart_2378314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2378314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2378314 prefixEnd_2378314 := by exact prefixLift 2378314
  have htrace : WordTrace (prefixWord ++ tailWord_2378314) baseStart_2378314 baseEnd_2378314 := by
    simpa [prefixWord, tailWord_2378314, baseEnd_2378314] using wordTrace_append hprefix tailTrace_2378314
  have hstable : (prefixWord ++ tailWord_2378314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378314).length < 2 ^ (prefixWord ++ tailWord_2378314).sum := by decide
  have hdescent : baseEnd_2378314 < baseStart_2378314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378367 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 4, 4, 3]
def baseStart_2378367 : Nat := 118140960795 + 2378367 * 2 ^ 59
def prefixEnd_2378367 : Nat := 4983230072969 + 3 ^ 40 * 2378367 * 2
def baseEnd_2378367 : Nat := 1221245443792001361874595

theorem tailTrace_2378367 : CollatzResearch.WordTrace tailWord_2378367 prefixEnd_2378367 1221245443792001361874595 := by
  unfold tailWord_2378367
  simp only [CollatzResearch.WordTrace]
  refine ⟨86746170974590026590053355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57830780649726684393368903 86746170974590026590053355)
  ·
    refine ⟨130119256461885039885080033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86746170974590026590053355 130119256461885039885080033)
    ·
      refine ⟨97589442346413779913810025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130119256461885039885080033 97589442346413779913810025)
      ·
        refine ⟨73192081759810334935357519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97589442346413779913810025 73192081759810334935357519)
        ·
          refine ⟨109788122639715502403036279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73192081759810334935357519 109788122639715502403036279)
          ·
            refine ⟨164682183959573253604554419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109788122639715502403036279 164682183959573253604554419)
            ·
              refine ⟨247023275939359880406831629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164682183959573253604554419 247023275939359880406831629)
              ·
                refine ⟨92633728477259955152561861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 247023275939359880406831629 92633728477259955152561861)
                ·
                  refine ⟨17368824089486241591105349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 92633728477259955152561861 17368824089486241591105349)
                  ·
                    refine ⟨3256654516778670298332253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17368824089486241591105349 3256654516778670298332253)
                    ·
                      refine ⟨1221245443792001361874595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3256654516778670298332253 1221245443792001361874595)
                      ·
                        rfl

theorem cell23_2378367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 4, 3].length) (baseStart_2378367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2378367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2378367 prefixEnd_2378367 := by exact prefixLift 2378367
  have htrace : WordTrace (prefixWord ++ tailWord_2378367) baseStart_2378367 baseEnd_2378367 := by
    simpa [prefixWord, tailWord_2378367, baseEnd_2378367] using wordTrace_append hprefix tailTrace_2378367
  have hstable : (prefixWord ++ tailWord_2378367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378367).length < 2 ^ (prefixWord ++ tailWord_2378367).sum := by decide
  have hdescent : baseEnd_2378367 < baseStart_2378367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378368 : List Nat := [2, 1, 1, 2, 1, 7, 1, 2, 1, 3, 2]
def baseStart_2378368 : Nat := 118140960795 + 2378368 * 2 ^ 59
def prefixEnd_2378368 : Nat := 4983230072969 + 3 ^ 40 * 2378368 * 2
def baseEnd_2378368 : Nat := 1221245957272655857962091

theorem tailTrace_2378368 : CollatzResearch.WordTrace tailWord_2378368 prefixEnd_2378368 1221245957272655857962091 := by
  unfold tailWord_2378368
  simp only [CollatzResearch.WordTrace]
  refine ⟨43373103723793201880419879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57830804965057602507226505 43373103723793201880419879)
  ·
    refine ⟨65059655585689802820629819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43373103723793201880419879 65059655585689802820629819)
    ·
      refine ⟨97589483378534704230944729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65059655585689802820629819 97589483378534704230944729)
      ·
        refine ⟨73192112533901028173208547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97589483378534704230944729 73192112533901028173208547)
        ·
          refine ⟨109788168800851542259812821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73192112533901028173208547 109788168800851542259812821)
          ·
            refine ⟨2573160206269958021714363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 109788168800851542259812821 2573160206269958021714363)
            ·
              refine ⟨3859740309404937032571545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2573160206269958021714363 3859740309404937032571545)
              ·
                refine ⟨2894805232053702774428659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3859740309404937032571545 2894805232053702774428659)
                ·
                  refine ⟨4342207848080554161642989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2894805232053702774428659 4342207848080554161642989)
                  ·
                    refine ⟨1628327943030207810616121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4342207848080554161642989 1628327943030207810616121)
                    ·
                      refine ⟨1221245957272655857962091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1628327943030207810616121 1221245957272655857962091)
                      ·
                        rfl

theorem cell23_2378368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 2, 1, 3, 2].length) (baseStart_2378368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2378368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2378368 prefixEnd_2378368 := by exact prefixLift 2378368
  have htrace : WordTrace (prefixWord ++ tailWord_2378368) baseStart_2378368 baseEnd_2378368 := by
    simpa [prefixWord, tailWord_2378368, baseEnd_2378368] using wordTrace_append hprefix tailTrace_2378368
  have hstable : (prefixWord ++ tailWord_2378368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378368).length < 2 ^ (prefixWord ++ tailWord_2378368).sum := by decide
  have hdescent : baseEnd_2378368 < baseStart_2378368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378377 : List Nat := [1, 2, 1, 1, 4, 1, 1, 2, 4, 2, 4]
def baseStart_2378377 : Nat := 118140960795 + 2378377 * 2 ^ 59
def prefixEnd_2378377 : Nat := 4983230072969 + 3 ^ 40 * 2378377 * 2
def baseEnd_2378377 : Nat := 1221250578598546322749549

theorem tailTrace_2378377 : CollatzResearch.WordTrace tailWord_2378377 prefixEnd_2378377 1221250578598546322749549 := by
  unfold tailWord_2378377
  simp only [CollatzResearch.WordTrace]
  refine ⟨86746535704553798297917385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57831023803035865531944923 86746535704553798297917385)
  ·
    refine ⟨65059901778415348723438039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86746535704553798297917385 65059901778415348723438039)
    ·
      refine ⟨97589852667623023085157059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65059901778415348723438039 97589852667623023085157059)
      ·
        refine ⟨146384779001434534627735589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97589852667623023085157059 146384779001434534627735589)
        ·
          refine ⟨27447146062768975242700423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 146384779001434534627735589 27447146062768975242700423)
          ·
            refine ⟨41170719094153462864050635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27447146062768975242700423 41170719094153462864050635)
            ·
              refine ⟨61756078641230194296075953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41170719094153462864050635 61756078641230194296075953)
              ·
                refine ⟨46317058980922645722056965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61756078641230194296075953 46317058980922645722056965)
                ·
                  refine ⟨8684448558922996072885681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46317058980922645722056965 8684448558922996072885681)
                  ·
                    refine ⟨6513336419192247054664261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8684448558922996072885681 6513336419192247054664261)
                    ·
                      refine ⟨1221250578598546322749549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6513336419192247054664261 1221250578598546322749549)
                      ·
                        rfl

theorem cell23_2378377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 2, 4].length) (baseStart_2378377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2378377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2378377 prefixEnd_2378377 := by exact prefixLift 2378377
  have htrace : WordTrace (prefixWord ++ tailWord_2378377) baseStart_2378377 baseEnd_2378377 := by
    simpa [prefixWord, tailWord_2378377, baseEnd_2378377] using wordTrace_append hprefix tailTrace_2378377
  have hstable : (prefixWord ++ tailWord_2378377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378377).length < 2 ^ (prefixWord ++ tailWord_2378377).sum := by decide
  have hdescent : baseEnd_2378377 < baseStart_2378377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378397 : List Nat := [1, 4, 2, 1, 1, 1, 2, 1, 1, 2, 7]
def baseStart_2378397 : Nat := 118140960795 + 2378397 * 2 ^ 59
def prefixEnd_2378397 : Nat := 4983230072969 + 3 ^ 40 * 2378397 * 2
def baseEnd_2378397 : Nat := 1221260848211636244499457

theorem tailTrace_2378397 : CollatzResearch.WordTrace tailWord_2378397 prefixEnd_2378397 1221260848211636244499457 := by
  unfold tailWord_2378397
  simp only [CollatzResearch.WordTrace]
  refine ⟨86747265164481341713645445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57831510109654227809096963 86747265164481341713645445)
  ·
    refine ⟨16265112218340251571308521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86747265164481341713645445 16265112218340251571308521)
    ·
      refine ⟨12198834163755188678481391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16265112218340251571308521 12198834163755188678481391)
      ·
        refine ⟨18298251245632783017722087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12198834163755188678481391 18298251245632783017722087)
        ·
          refine ⟨27447376868449174526583131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18298251245632783017722087 27447376868449174526583131)
          ·
            refine ⟨41171065302673761789874697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27447376868449174526583131 41171065302673761789874697)
            ·
              refine ⟨30878298977005321342406023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41171065302673761789874697 30878298977005321342406023)
              ·
                refine ⟨46317448465507982013609035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30878298977005321342406023 46317448465507982013609035)
                ·
                  refine ⟨69476172698261973020413553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46317448465507982013609035 69476172698261973020413553)
                  ·
                    refine ⟨52107129523696479765310165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 69476172698261973020413553 52107129523696479765310165)
                    ·
                      refine ⟨1221260848211636244499457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 52107129523696479765310165 1221260848211636244499457)
                      ·
                        rfl

theorem cell23_2378397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_2378397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2378397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2378397 prefixEnd_2378397 := by exact prefixLift 2378397
  have htrace : WordTrace (prefixWord ++ tailWord_2378397) baseStart_2378397 baseEnd_2378397 := by
    simpa [prefixWord, tailWord_2378397, baseEnd_2378397] using wordTrace_append hprefix tailTrace_2378397
  have hstable : (prefixWord ++ tailWord_2378397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378397).length < 2 ^ (prefixWord ++ tailWord_2378397).sum := by decide
  have hdescent : baseEnd_2378397 < baseStart_2378397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378521 : List Nat := [1, 2, 1, 2, 1, 1, 1, 7, 3, 1, 3]
def baseStart_2378521 : Nat := 118140960795 + 2378521 * 2 ^ 59
def prefixEnd_2378521 : Nat := 4983230072969 + 3 ^ 40 * 2378521 * 2
def baseEnd_2378521 : Nat := 1221324519812793759348887

theorem tailTrace_2378521 : CollatzResearch.WordTrace tailWord_2378521 prefixEnd_2378521 1221324519812793759348887 := by
  unfold tailWord_2378521
  simp only [CollatzResearch.WordTrace]
  refine ⟨86751787816032110891159417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57834525210688073927439611 86751787816032110891159417)
  ·
    refine ⟨65063840862024083168369563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86751787816032110891159417 65063840862024083168369563)
    ·
      refine ⟨97595761293036124752554345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65063840862024083168369563 97595761293036124752554345)
      ·
        refine ⟨73196820969777093564415759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97595761293036124752554345 73196820969777093564415759)
        ·
          refine ⟨109795231454665640346623639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73196820969777093564415759 109795231454665640346623639)
          ·
            refine ⟨164692847181998460519935459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109795231454665640346623639 164692847181998460519935459)
            ·
              refine ⟨247039270772997690779903189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164692847181998460519935459 247039270772997690779903189)
              ·
                refine ⟨5789982908742133377653981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 247039270772997690779903189 5789982908742133377653981)
                ·
                  refine ⟨2171243590778300016620243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5789982908742133377653981 2171243590778300016620243)
                  ·
                    refine ⟨3256865386167450024930365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2171243590778300016620243 3256865386167450024930365)
                    ·
                      refine ⟨1221324519812793759348887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3256865386167450024930365 1221324519812793759348887)
                      ·
                        rfl

theorem cell23_2378521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 3, 1, 3].length) (baseStart_2378521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2378521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2378521 prefixEnd_2378521 := by exact prefixLift 2378521
  have htrace : WordTrace (prefixWord ++ tailWord_2378521) baseStart_2378521 baseEnd_2378521 := by
    simpa [prefixWord, tailWord_2378521, baseEnd_2378521] using wordTrace_append hprefix tailTrace_2378521
  have hstable : (prefixWord ++ tailWord_2378521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378521).length < 2 ^ (prefixWord ++ tailWord_2378521).sum := by decide
  have hdescent : baseEnd_2378521 < baseStart_2378521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378528 : List Nat := [2, 1, 1, 5, 1, 4, 2, 1, 6]
def baseStart_2378528 : Nat := 118140960795 + 2378528 * 2 ^ 59
def prefixEnd_2378528 : Nat := 4983230072969 + 3 ^ 40 * 2378528 * 2
def baseEnd_2378528 : Nat := 135703123797486136884595

theorem tailTrace_2378528 : CollatzResearch.WordTrace tailWord_2378528 prefixEnd_2378528 135703123797486136884595 := by
  unfold tailWord_2378528
  simp only [CollatzResearch.WordTrace]
  refine ⟨43376021563503375543332119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57834695418004500724442825 43376021563503375543332119)
  ·
    refine ⟨65064032345255063314998179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43376021563503375543332119 65064032345255063314998179)
    ·
      refine ⟨97596048517882594972497269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65064032345255063314998179 97596048517882594972497269)
      ·
        refine ⟨9149629548551493278671619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 97596048517882594972497269 9149629548551493278671619)
        ·
          refine ⟨13724444322827239918007429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9149629548551493278671619 13724444322827239918007429)
          ·
            refine ⟨2573333310530107484626393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13724444322827239918007429 2573333310530107484626393)
            ·
              refine ⟨1929999982897580613469795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2573333310530107484626393 1929999982897580613469795)
              ·
                refine ⟨2894999974346370920204693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1929999982897580613469795 2894999974346370920204693)
                ·
                  refine ⟨135703123797486136884595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2894999974346370920204693 135703123797486136884595)
                  ·
                    rfl

theorem cell23_2378528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 1, 6].length) (baseStart_2378528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2378528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2378528 prefixEnd_2378528 := by exact prefixLift 2378528
  have htrace : WordTrace (prefixWord ++ tailWord_2378528) baseStart_2378528 baseEnd_2378528 := by
    simpa [prefixWord, tailWord_2378528, baseEnd_2378528] using wordTrace_append hprefix tailTrace_2378528
  have hstable : (prefixWord ++ tailWord_2378528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378528).length < 2 ^ (prefixWord ++ tailWord_2378528).sum := by decide
  have hdescent : baseEnd_2378528 < baseStart_2378528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378531 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 6, 3, 2]
def baseStart_2378531 : Nat := 118140960795 + 2378531 * 2 ^ 59
def prefixEnd_2378531 : Nat := 4983230072969 + 3 ^ 40 * 2378531 * 2
def baseEnd_2378531 : Nat := 1221329654619338720223841

theorem tailTrace_2378531 : CollatzResearch.WordTrace tailWord_2378531 prefixEnd_2378531 1221329654619338720223841 := by
  unfold tailWord_2378531
  simp only [CollatzResearch.WordTrace]
  refine ⟨86752152545995882599023447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57834768363997255066015631 86752152545995882599023447)
  ·
    refine ⟨130128228818993823898535171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86752152545995882599023447 130128228818993823898535171)
    ·
      refine ⟨195192343228490735847802757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130128228818993823898535171 195192343228490735847802757)
      ·
        refine ⟨36598564355342012971463017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 195192343228490735847802757 36598564355342012971463017)
        ·
          refine ⟨27448923266506509728597263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36598564355342012971463017 27448923266506509728597263)
          ·
            refine ⟨41173384899759764592895895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27448923266506509728597263 41173384899759764592895895)
            ·
              refine ⟨61760077349639646889343843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41173384899759764592895895 61760077349639646889343843)
              ·
                refine ⟨92640116024459470334015765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61760077349639646889343843 92640116024459470334015765)
                ·
                  refine ⟨4342505438646537671906989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 92640116024459470334015765 4342505438646537671906989)
                  ·
                    refine ⟨1628439539492451626965121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4342505438646537671906989 1628439539492451626965121)
                    ·
                      refine ⟨1221329654619338720223841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1628439539492451626965121 1221329654619338720223841)
                      ·
                        rfl

theorem cell23_2378531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 6, 3, 2].length) (baseStart_2378531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2378531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2378531 prefixEnd_2378531 := by exact prefixLift 2378531
  have htrace : WordTrace (prefixWord ++ tailWord_2378531) baseStart_2378531 baseEnd_2378531 := by
    simpa [prefixWord, tailWord_2378531, baseEnd_2378531] using wordTrace_append hprefix tailTrace_2378531
  have hstable : (prefixWord ++ tailWord_2378531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378531).length < 2 ^ (prefixWord ++ tailWord_2378531).sum := by decide
  have hdescent : baseEnd_2378531 < baseStart_2378531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378566 : List Nat := [6, 1, 1, 2, 2, 2, 2, 2, 1, 4]
def baseStart_2378566 : Nat := 118140960795 + 2378566 * 2 ^ 59
def prefixEnd_2378566 : Nat := 4983230072969 + 3 ^ 40 * 2378566 * 2
def baseEnd_2378566 : Nat := 407115875480748694428727

theorem tailTrace_2378566 : CollatzResearch.WordTrace tailWord_2378566 prefixEnd_2378566 407115875480748694428727 := by
  unfold tailWord_2378566
  simp only [CollatzResearch.WordTrace]
  refine ⟨2711044659402158861767111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 57835619400579389051031701 2711044659402158861767111)
  ·
    refine ⟨4066566989103238292650667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2711044659402158861767111 4066566989103238292650667)
    ·
      refine ⟨6099850483654857438976001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4066566989103238292650667 6099850483654857438976001)
      ·
        refine ⟨4574887862741143079232001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6099850483654857438976001 4574887862741143079232001)
        ·
          refine ⟨3431165897055857309424001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4574887862741143079232001 3431165897055857309424001)
          ·
            refine ⟨2573374422791892982068001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3431165897055857309424001 2573374422791892982068001)
            ·
              refine ⟨1930030817093919736551001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2573374422791892982068001 1930030817093919736551001)
              ·
                refine ⟨1447523112820439802413251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1930030817093919736551001 1447523112820439802413251)
                ·
                  refine ⟨2171284669230659703619877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1447523112820439802413251 2171284669230659703619877)
                  ·
                    refine ⟨407115875480748694428727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2171284669230659703619877 407115875480748694428727)
                    ·
                      rfl

theorem cell23_2378566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_2378566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2378566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2378566 prefixEnd_2378566 := by exact prefixLift 2378566
  have htrace : WordTrace (prefixWord ++ tailWord_2378566) baseStart_2378566 baseEnd_2378566 := by
    simpa [prefixWord, tailWord_2378566, baseEnd_2378566] using wordTrace_append hprefix tailTrace_2378566
  have hstable : (prefixWord ++ tailWord_2378566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378566).length < 2 ^ (prefixWord ++ tailWord_2378566).sum := by decide
  have hdescent : baseEnd_2378566 < baseStart_2378566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378572 : List Nat := [2, 2, 1, 3, 3, 1, 4, 2, 1, 1, 3]
def baseStart_2378572 : Nat := 118140960795 + 2378572 * 2 ^ 59
def prefixEnd_2378572 : Nat := 4983230072969 + 3 ^ 40 * 2378572 * 2
def baseEnd_2378572 : Nat := 1221350707326173059811153

theorem tailTrace_2378572 : CollatzResearch.WordTrace tailWord_2378572 prefixEnd_2378572 1221350707326173059811153 := by
  unfold tailWord_2378572
  simp only [CollatzResearch.WordTrace]
  refine ⟨43376823969423673300632985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57835765292564897734177313 43376823969423673300632985)
  ·
    refine ⟨32532617977067754975474739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43376823969423673300632985 32532617977067754975474739)
    ·
      refine ⟨48798926965601632463212109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32532617977067754975474739 48798926965601632463212109)
      ·
        refine ⟨18299597612100612173704541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48798926965601632463212109 18299597612100612173704541)
        ·
          refine ⟨6862349104537729565139203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18299597612100612173704541 6862349104537729565139203)
          ·
            refine ⟨10293523656806594347708805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6862349104537729565139203 10293523656806594347708805)
            ·
              refine ⟨1930035685651236440195401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10293523656806594347708805 1930035685651236440195401)
              ·
                refine ⟨1447526764238427330146551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1930035685651236440195401 1447526764238427330146551)
                ·
                  refine ⟨2171290146357640995219827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1447526764238427330146551 2171290146357640995219827)
                  ·
                    refine ⟨3256935219536461492829741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2171290146357640995219827 3256935219536461492829741)
                    ·
                      refine ⟨1221350707326173059811153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3256935219536461492829741 1221350707326173059811153)
                      ·
                        rfl

theorem cell23_2378572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 2, 1, 1, 3].length) (baseStart_2378572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2378572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2378572 prefixEnd_2378572 := by exact prefixLift 2378572
  have htrace : WordTrace (prefixWord ++ tailWord_2378572) baseStart_2378572 baseEnd_2378572 := by
    simpa [prefixWord, tailWord_2378572, baseEnd_2378572] using wordTrace_append hprefix tailTrace_2378572
  have hstable : (prefixWord ++ tailWord_2378572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378572).length < 2 ^ (prefixWord ++ tailWord_2378572).sum := by decide
  have hdescent : baseEnd_2378572 < baseStart_2378572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378574 : List Nat := [4, 1, 1, 1, 1, 1, 1, 3, 3, 1, 6]
def baseStart_2378574 : Nat := 118140960795 + 2378574 * 2 ^ 59
def prefixEnd_2378574 : Nat := 4983230072969 + 3 ^ 40 * 2378574 * 2
def baseEnd_2378574 : Nat := 1221351734287482051986143

theorem tailTrace_2378574 : CollatzResearch.WordTrace tailWord_2378574 prefixEnd_2378574 1221351734287482051986143 := by
  unfold tailWord_2378574
  simp only [CollatzResearch.WordTrace]
  refine ⟨10844215110605012617854847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57835813923226733961892517 10844215110605012617854847)
  ·
    refine ⟨16266322665907518926782271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10844215110605012617854847 16266322665907518926782271)
    ·
      refine ⟨24399483998861278390173407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16266322665907518926782271 24399483998861278390173407)
      ·
        refine ⟨36599225998291917585260111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24399483998861278390173407 36599225998291917585260111)
        ·
          refine ⟨54898838997437876377890167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36599225998291917585260111 54898838997437876377890167)
          ·
            refine ⟨82348258496156814566835251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54898838997437876377890167 82348258496156814566835251)
            ·
              refine ⟨123522387744235221850252877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82348258496156814566835251 123522387744235221850252877)
              ·
                refine ⟨46320895404088208193844829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123522387744235221850252877 46320895404088208193844829)
                ·
                  refine ⟨17370335776533078072691811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46320895404088208193844829 17370335776533078072691811)
                  ·
                    refine ⟨26055503664799617109037717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17370335776533078072691811 26055503664799617109037717)
                    ·
                      refine ⟨1221351734287482051986143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26055503664799617109037717 1221351734287482051986143)
                      ·
                        rfl

theorem cell23_2378574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_2378574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2378574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2378574 prefixEnd_2378574 := by exact prefixLift 2378574
  have htrace : WordTrace (prefixWord ++ tailWord_2378574) baseStart_2378574 baseEnd_2378574 := by
    simpa [prefixWord, tailWord_2378574, baseEnd_2378574] using wordTrace_append hprefix tailTrace_2378574
  have hstable : (prefixWord ++ tailWord_2378574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378574).length < 2 ^ (prefixWord ++ tailWord_2378574).sum := by decide
  have hdescent : baseEnd_2378574 < baseStart_2378574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378581 : List Nat := [1, 3, 2, 2, 2, 1, 1, 1, 5, 2, 3]
def baseStart_2378581 : Nat := 118140960795 + 2378581 * 2 ^ 59
def prefixEnd_2378581 : Nat := 4983230072969 + 3 ^ 40 * 2378581 * 2
def baseEnd_2378581 : Nat := 1221355328652063524598611

theorem tailTrace_2378581 : CollatzResearch.WordTrace tailWord_2378581 prefixEnd_2378581 1221355328652063524598611 := by
  unfold tailWord_2378581
  simp only [CollatzResearch.WordTrace]
  refine ⟨86753976195814741138343597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57835984130543160758895731 86753976195814741138343597)
  ·
    refine ⟨32532741073430527926878849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86753976195814741138343597 32532741073430527926878849)
    ·
      refine ⟨24399555805072895945159137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32532741073430527926878849 24399555805072895945159137)
      ·
        refine ⟨18299666853804671958869353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24399555805072895945159137 18299666853804671958869353)
        ·
          refine ⟨13724750140353503969152015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18299666853804671958869353 13724750140353503969152015)
          ·
            refine ⟨20587125210530255953728023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13724750140353503969152015 20587125210530255953728023)
            ·
              refine ⟨30880687815795383930592035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20587125210530255953728023 30880687815795383930592035)
              ·
                refine ⟨46321031723693075895888053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30880687815795383930592035 46321031723693075895888053)
                ·
                  refine ⟨4342596724096225865239505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46321031723693075895888053 4342596724096225865239505)
                  ·
                    refine ⟨3256947543072169398929629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4342596724096225865239505 3256947543072169398929629)
                    ·
                      refine ⟨1221355328652063524598611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3256947543072169398929629 1221355328652063524598611)
                      ·
                        rfl

theorem cell23_2378581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_2378581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2378581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2378581 prefixEnd_2378581 := by exact prefixLift 2378581
  have htrace : WordTrace (prefixWord ++ tailWord_2378581) baseStart_2378581 baseEnd_2378581 := by
    simpa [prefixWord, tailWord_2378581, baseEnd_2378581] using wordTrace_append hprefix tailTrace_2378581
  have hstable : (prefixWord ++ tailWord_2378581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378581).length < 2 ^ (prefixWord ++ tailWord_2378581).sum := by decide
  have hdescent : baseEnd_2378581 < baseStart_2378581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378588 : List Nat := [2, 2, 4, 2, 1, 2, 2, 1, 1, 6]
def baseStart_2378588 : Nat := 118140960795 + 2378588 * 2 ^ 59
def prefixEnd_2378588 : Nat := 4983230072969 + 3 ^ 40 * 2378588 * 2
def baseEnd_2378588 : Nat := 407119641005548332403693

theorem tailTrace_2378588 : CollatzResearch.WordTrace tailWord_2378588 prefixEnd_2378588 407119641005548332403693 := by
  unfold tailWord_2378588
  simp only [CollatzResearch.WordTrace]
  refine ⟨43377115753394690666924209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57836154337859587555898945 43377115753394690666924209)
  ·
    refine ⟨32532836815046018000193157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43377115753394690666924209 32532836815046018000193157)
    ·
      refine ⟨6099906902821128375036217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32532836815046018000193157 6099906902821128375036217)
      ·
        refine ⟨4574930177115846281277163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6099906902821128375036217 4574930177115846281277163)
        ·
          refine ⟨6862395265673769421915745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4574930177115846281277163 6862395265673769421915745)
          ·
            refine ⟨5146796449255327066436809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6862395265673769421915745 5146796449255327066436809)
            ·
              refine ⟨3860097336941495299827607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5146796449255327066436809 3860097336941495299827607)
              ·
                refine ⟨5790146005412242949741411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3860097336941495299827607 5790146005412242949741411)
                ·
                  refine ⟨8685219008118364424612117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5790146005412242949741411 8685219008118364424612117)
                  ·
                    refine ⟨407119641005548332403693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8685219008118364424612117 407119641005548332403693)
                    ·
                      rfl

theorem cell23_2378588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_2378588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2378588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2378588 prefixEnd_2378588 := by exact prefixLift 2378588
  have htrace : WordTrace (prefixWord ++ tailWord_2378588) baseStart_2378588 baseEnd_2378588 := by
    simpa [prefixWord, tailWord_2378588, baseEnd_2378588] using wordTrace_append hprefix tailTrace_2378588
  have hstable : (prefixWord ++ tailWord_2378588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378588).length < 2 ^ (prefixWord ++ tailWord_2378588).sum := by decide
  have hdescent : baseEnd_2378588 < baseStart_2378588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378591 : List Nat := [1, 1, 2, 3, 1, 3, 4, 1, 1, 2, 4]
def baseStart_2378591 : Nat := 118140960795 + 2378591 * 2 ^ 59
def prefixEnd_2378591 : Nat := 4983230072969 + 3 ^ 40 * 2378591 * 2
def baseEnd_2378591 : Nat := 1221360463458608485473565

theorem tailTrace_2378591 : CollatzResearch.WordTrace tailWord_2378591 prefixEnd_2378591 1221360463458608485473565 := by
  unfold tailWord_2378591
  simp only [CollatzResearch.WordTrace]
  refine ⟨86754340925778512846207627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57836227283852341897471751 86754340925778512846207627)
  ·
    refine ⟨130131511388667769269311441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86754340925778512846207627 130131511388667769269311441)
    ·
      refine ⟨97598633541500826951983581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130131511388667769269311441 97598633541500826951983581)
      ·
        refine ⟨36599487578062810106993843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97598633541500826951983581 36599487578062810106993843)
        ·
          refine ⟨54899231367094215160490765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36599487578062810106993843 54899231367094215160490765)
          ·
            refine ⟨20587211762660330685184037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54899231367094215160490765 20587211762660330685184037)
            ·
              refine ⟨3860102205498812003472007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20587211762660330685184037 3860102205498812003472007)
              ·
                refine ⟨5790153308248218005208011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3860102205498812003472007 5790153308248218005208011)
                ·
                  refine ⟨8685229962372327007812017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5790153308248218005208011 8685229962372327007812017)
                  ·
                    refine ⟨6513922471779245255859013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8685229962372327007812017 6513922471779245255859013)
                    ·
                      refine ⟨1221360463458608485473565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6513922471779245255859013 1221360463458608485473565)
                      ·
                        rfl

theorem cell23_2378591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 2, 4].length) (baseStart_2378591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2378591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2378591 prefixEnd_2378591 := by exact prefixLift 2378591
  have htrace : WordTrace (prefixWord ++ tailWord_2378591) baseStart_2378591 baseEnd_2378591 := by
    simpa [prefixWord, tailWord_2378591, baseEnd_2378591] using wordTrace_append hprefix tailTrace_2378591
  have hstable : (prefixWord ++ tailWord_2378591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378591).length < 2 ^ (prefixWord ++ tailWord_2378591).sum := by decide
  have hdescent : baseEnd_2378591 < baseStart_2378591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378595 : List Nat := [1, 1, 1, 5, 3, 2, 1, 2, 3, 2, 2]
def baseStart_2378595 : Nat := 118140960795 + 2378595 * 2 ^ 59
def prefixEnd_2378595 : Nat := 4983230072969 + 3 ^ 40 * 2378595 * 2
def baseEnd_2378595 : Nat := 1221362517381226469823547

theorem tailTrace_2378595 : CollatzResearch.WordTrace tailWord_2378595 prefixEnd_2378595 1221362517381226469823547 := by
  unfold tailWord_2378595
  simp only [CollatzResearch.WordTrace]
  refine ⟨86754486817764021529353239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57836324545176014352902159 86754486817764021529353239)
  ·
    refine ⟨130131730226646032294029859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86754486817764021529353239 130131730226646032294029859)
    ·
      refine ⟨195197595339969048441044789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130131730226646032294029859 195197595339969048441044789)
      ·
        refine ⟨18299774563122098291347949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 195197595339969048441044789 18299774563122098291347949)
        ·
          refine ⟨6862415461170786859255481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18299774563122098291347949 6862415461170786859255481)
          ·
            refine ⟨5146811595878090144441611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6862415461170786859255481 5146811595878090144441611)
            ·
              refine ⟨7720217393817135216662417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5146811595878090144441611 7720217393817135216662417)
              ·
                refine ⟨5790163045362851412496813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7720217393817135216662417 5790163045362851412496813)
                ·
                  refine ⟨2171311142011069279686305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5790163045362851412496813 2171311142011069279686305)
                  ·
                    refine ⟨1628483356508301959764729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2171311142011069279686305 1628483356508301959764729)
                    ·
                      refine ⟨1221362517381226469823547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1628483356508301959764729 1221362517381226469823547)
                      ·
                        rfl

theorem cell23_2378595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 3, 2, 2].length) (baseStart_2378595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2378595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2378595 prefixEnd_2378595 := by exact prefixLift 2378595
  have htrace : WordTrace (prefixWord ++ tailWord_2378595) baseStart_2378595 baseEnd_2378595 := by
    simpa [prefixWord, tailWord_2378595, baseEnd_2378595] using wordTrace_append hprefix tailTrace_2378595
  have hstable : (prefixWord ++ tailWord_2378595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378595).length < 2 ^ (prefixWord ++ tailWord_2378595).sum := by decide
  have hdescent : baseEnd_2378595 < baseStart_2378595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378611 : List Nat := [1, 1, 1, 2, 2, 1, 6, 2, 1, 3, 3]
def baseStart_2378611 : Nat := 118140960795 + 2378611 * 2 ^ 59
def prefixEnd_2378611 : Nat := 4983230072969 + 3 ^ 40 * 2378611 * 2
def baseEnd_2378611 : Nat := 1221370733071698407223473

theorem tailTrace_2378611 : CollatzResearch.WordTrace tailWord_2378611 prefixEnd_2378611 1221370733071698407223473 := by
  unfold tailWord_2378611
  simp only [CollatzResearch.WordTrace]
  refine ⟨86755070385706056261935687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57836713590470704174623791 86755070385706056261935687)
  ·
    refine ⟨130132605578559084392903531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86755070385706056261935687 130132605578559084392903531)
    ·
      refine ⟨195198908367838626589355297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130132605578559084392903531 195198908367838626589355297)
      ·
        refine ⟨146399181275878969942016473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195198908367838626589355297 146399181275878969942016473)
        ·
          refine ⟨109799385956909227456512355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146399181275878969942016473 109799385956909227456512355)
          ·
            refine ⟨164699078935363841184768533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109799385956909227456512355 164699078935363841184768533)
            ·
              refine ⟨7720269325095180055536025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 164699078935363841184768533 7720269325095180055536025)
              ·
                refine ⟨5790201993821385041652019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7720269325095180055536025 5790201993821385041652019)
                ·
                  refine ⟨8685302990732077562478029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5790201993821385041652019 8685302990732077562478029)
                  ·
                    refine ⟨3256988621524529085929261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8685302990732077562478029 3256988621524529085929261)
                    ·
                      refine ⟨1221370733071698407223473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3256988621524529085929261 1221370733071698407223473)
                      ·
                        rfl

theorem cell23_2378611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 3, 3].length) (baseStart_2378611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2378611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2378611 prefixEnd_2378611 := by exact prefixLift 2378611
  have htrace : WordTrace (prefixWord ++ tailWord_2378611) baseStart_2378611 baseEnd_2378611 := by
    simpa [prefixWord, tailWord_2378611, baseEnd_2378611] using wordTrace_append hprefix tailTrace_2378611
  have hstable : (prefixWord ++ tailWord_2378611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378611).length < 2 ^ (prefixWord ++ tailWord_2378611).sum := by decide
  have hdescent : baseEnd_2378611 < baseStart_2378611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378624 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 5]
def baseStart_2378624 : Nat := 118140960795 + 2378624 * 2 ^ 59
def prefixEnd_2378624 : Nat := 4983230072969 + 3 ^ 40 * 2378624 * 2
def baseEnd_2378624 : Nat := 1221377408320206856360913

theorem tailTrace_2378624 : CollatzResearch.WordTrace tailWord_2378624 prefixEnd_2378624 1221377408320206856360913 := by
  unfold tailWord_2378624
  simp only [CollatzResearch.WordTrace]
  refine ⟨43377772267329479741079463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57837029689772639654772617 43377772267329479741079463)
  ·
    refine ⟨65066658400994219611619195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43377772267329479741079463 65066658400994219611619195)
    ·
      refine ⟨97599987601491329417428793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65066658400994219611619195 97599987601491329417428793)
      ·
        refine ⟨73199990701118497063071595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97599987601491329417428793 73199990701118497063071595)
        ·
          refine ⟨109799986051677745594607393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73199990701118497063071595 109799986051677745594607393)
          ·
            refine ⟨82349989538758309195955545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109799986051677745594607393 82349989538758309195955545)
            ·
              refine ⟨61762492154068731896966659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82349989538758309195955545 61762492154068731896966659)
              ·
                refine ⟨92643738231103097845449989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61762492154068731896966659 92643738231103097845449989)
                ·
                  refine ⟨17370700918331830846021873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 92643738231103097845449989 17370700918331830846021873)
                  ·
                    refine ⟨13028025688748873134516405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17370700918331830846021873 13028025688748873134516405)
                    ·
                      refine ⟨1221377408320206856360913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13028025688748873134516405 1221377408320206856360913)
                      ·
                        rfl

theorem cell23_2378624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 5].length) (baseStart_2378624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2378624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2378624 prefixEnd_2378624 := by exact prefixLift 2378624
  have htrace : WordTrace (prefixWord ++ tailWord_2378624) baseStart_2378624 baseEnd_2378624 := by
    simpa [prefixWord, tailWord_2378624, baseEnd_2378624] using wordTrace_append hprefix tailTrace_2378624
  have hstable : (prefixWord ++ tailWord_2378624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378624).length < 2 ^ (prefixWord ++ tailWord_2378624).sum := by decide
  have hdescent : baseEnd_2378624 < baseStart_2378624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378642 : List Nat := [3, 2, 3, 2, 3, 1, 1, 1, 1, 2, 4]
def baseStart_2378642 : Nat := 118140960795 + 2378642 * 2 ^ 59
def prefixEnd_2378642 : Nat := 4983230072969 + 3 ^ 40 * 2378642 * 2
def baseEnd_2378642 : Nat := 1221386650971987785935831

theorem tailTrace_2378642 : CollatzResearch.WordTrace tailWord_2378642 prefixEnd_2378642 1221386650971987785935831 := by
  unfold tailWord_2378642
  simp only [CollatzResearch.WordTrace]
  refine ⟨21689050262148437139078545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57837467365729165704209453 21689050262148437139078545)
  ·
    refine ⟨16266787696611327854308909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21689050262148437139078545 16266787696611327854308909)
    ·
      refine ⟨6100045386229247945365841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16266787696611327854308909 6100045386229247945365841)
      ·
        refine ⟨4575034039671935959024381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6100045386229247945365841 4575034039671935959024381)
        ·
          refine ⟨1715637764876975984634143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4575034039671935959024381 1715637764876975984634143)
          ·
            refine ⟨2573456647315463976951215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1715637764876975984634143 2573456647315463976951215)
            ·
              refine ⟨3860184970973195965426823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2573456647315463976951215 3860184970973195965426823)
              ·
                refine ⟨5790277456459793948140235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3860184970973195965426823 5790277456459793948140235)
                ·
                  refine ⟨8685416184689690922210353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5790277456459793948140235 8685416184689690922210353)
                  ·
                    refine ⟨6514062138517268191657765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8685416184689690922210353 6514062138517268191657765)
                    ·
                      refine ⟨1221386650971987785935831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6514062138517268191657765 1221386650971987785935831)
                      ·
                        rfl

theorem cell23_2378642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_2378642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2378642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2378642 prefixEnd_2378642 := by exact prefixLift 2378642
  have htrace : WordTrace (prefixWord ++ tailWord_2378642) baseStart_2378642 baseEnd_2378642 := by
    simpa [prefixWord, tailWord_2378642, baseEnd_2378642] using wordTrace_append hprefix tailTrace_2378642
  have hstable : (prefixWord ++ tailWord_2378642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378642).length < 2 ^ (prefixWord ++ tailWord_2378642).sum := by decide
  have hdescent : baseEnd_2378642 < baseStart_2378642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378655 : List Nat := [1, 1, 2, 5, 2, 1, 1, 4, 1, 3, 2]
def baseStart_2378655 : Nat := 118140960795 + 2378655 * 2 ^ 59
def prefixEnd_2378655 : Nat := 4983230072969 + 3 ^ 40 * 2378655 * 2
def baseEnd_2378655 : Nat := 1221393326220496235073271

theorem tailTrace_2378655 : CollatzResearch.WordTrace tailWord_2378655 prefixEnd_2378655 1221393326220496235073271 := by
  unfold tailWord_2378655
  simp only [CollatzResearch.WordTrace]
  refine ⟨86756675197546651776537419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57837783465031101184358279 86756675197546651776537419)
  ·
    refine ⟨130135012796319977664806129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86756675197546651776537419 130135012796319977664806129)
    ·
      refine ⟨97601259597239983248604597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130135012796319977664806129 97601259597239983248604597)
      ·
        refine ⟨9150118087241248429556681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 97601259597239983248604597 9150118087241248429556681)
        ·
          refine ⟨6862588565430936322167511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9150118087241248429556681 6862588565430936322167511)
          ·
            refine ⟨10293882848146404483251267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6862588565430936322167511 10293882848146404483251267)
            ·
              refine ⟨15440824272219606724876901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10293882848146404483251267 15440824272219606724876901)
              ·
                refine ⟨2895154551041176260914419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15440824272219606724876901 2895154551041176260914419)
                ·
                  refine ⟨4342731826561764391371629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2895154551041176260914419 4342731826561764391371629)
                  ·
                    refine ⟨1628524434960661646764361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4342731826561764391371629 1628524434960661646764361)
                    ·
                      refine ⟨1221393326220496235073271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1628524434960661646764361 1221393326220496235073271)
                      ·
                        rfl

theorem cell23_2378655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_2378655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2378655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2378655 prefixEnd_2378655 := by exact prefixLift 2378655
  have htrace : WordTrace (prefixWord ++ tailWord_2378655) baseStart_2378655 baseEnd_2378655 := by
    simpa [prefixWord, tailWord_2378655, baseEnd_2378655] using wordTrace_append hprefix tailTrace_2378655
  have hstable : (prefixWord ++ tailWord_2378655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378655).length < 2 ^ (prefixWord ++ tailWord_2378655).sum := by decide
  have hdescent : baseEnd_2378655 < baseStart_2378655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378702 : List Nat := [4, 1, 1, 1, 2, 4, 1, 3, 2, 2, 2]
def baseStart_2378702 : Nat := 118140960795 + 2378702 * 2 ^ 59
def prefixEnd_2378702 : Nat := 4983230072969 + 3 ^ 40 * 2378702 * 2
def baseEnd_2378702 : Nat := 1221417459811257551185555

theorem tailTrace_2378702 : CollatzResearch.WordTrace tailWord_2378702 prefixEnd_2378702 1221417459811257551185555 := by
  unfold tailWord_2378702
  simp only [CollatzResearch.WordTrace]
  refine ⟨10844798678547047350437295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57838926285584252535665573 10844798678547047350437295)
  ·
    refine ⟨16267198017820571025655943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10844798678547047350437295 16267198017820571025655943)
    ·
      refine ⟨24400797026730856538483915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16267198017820571025655943 24400797026730856538483915)
      ·
        refine ⟨36601195540096284807725873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24400797026730856538483915 36601195540096284807725873)
        ·
          refine ⟨27450896655072213605794405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36601195540096284807725873 27450896655072213605794405)
          ·
            refine ⟨5147043122826040051086451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27450896655072213605794405 5147043122826040051086451)
            ·
              refine ⟨7720564684239060076629677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5147043122826040051086451 7720564684239060076629677)
              ·
                refine ⟨2895211756589647528736129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7720564684239060076629677 2895211756589647528736129)
                ·
                  refine ⟨2171408817442235646552097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2895211756589647528736129 2171408817442235646552097)
                  ·
                    refine ⟨1628556613081676734914073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2171408817442235646552097 1628556613081676734914073)
                    ·
                      refine ⟨1221417459811257551185555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1628556613081676734914073 1221417459811257551185555)
                      ·
                        rfl

theorem cell23_2378702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 3, 2, 2, 2].length) (baseStart_2378702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2378702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2378702 prefixEnd_2378702 := by exact prefixLift 2378702
  have htrace : WordTrace (prefixWord ++ tailWord_2378702) baseStart_2378702 baseEnd_2378702 := by
    simpa [prefixWord, tailWord_2378702, baseEnd_2378702] using wordTrace_append hprefix tailTrace_2378702
  have hstable : (prefixWord ++ tailWord_2378702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378702).length < 2 ^ (prefixWord ++ tailWord_2378702).sum := by decide
  have hdescent : baseEnd_2378702 < baseStart_2378702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378742 : List Nat := [5, 1, 1, 1, 3, 1, 4, 2, 5]
def baseStart_2378742 : Nat := 118140960795 + 2378742 * 2 ^ 59
def prefixEnd_2378742 : Nat := 4983230072969 + 3 ^ 40 * 2378742 * 2
def baseEnd_2378742 : Nat := 135715333226381932742819

theorem tailTrace_2378742 : CollatzResearch.WordTrace tailWord_2378742 prefixEnd_2378742 135715333226381932742819 := by
  unfold tailWord_2378742
  simp only [CollatzResearch.WordTrace]
  refine ⟨5422490521764466602184655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57839898898820977089969653 5422490521764466602184655)
  ·
    refine ⟨8133735782646699903276983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5422490521764466602184655 8133735782646699903276983)
    ·
      refine ⟨12200603673970049854915475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8133735782646699903276983 12200603673970049854915475)
      ·
        refine ⟨18300905510955074782373213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12200603673970049854915475 18300905510955074782373213)
        ·
          refine ⟨6862839566608153043389955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18300905510955074782373213 6862839566608153043389955)
          ·
            refine ⟨10294259349912229565084933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6862839566608153043389955 10294259349912229565084933)
            ·
              refine ⟨1930173628108543043453425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10294259349912229565084933 1930173628108543043453425)
              ·
                refine ⟨1447630221081407282590069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1930173628108543043453425 1447630221081407282590069)
                ·
                  refine ⟨135715333226381932742819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1447630221081407282590069 135715333226381932742819)
                  ·
                    rfl

theorem cell23_2378742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 2, 5].length) (baseStart_2378742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2378742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2378742 prefixEnd_2378742 := by exact prefixLift 2378742
  have htrace : WordTrace (prefixWord ++ tailWord_2378742) baseStart_2378742 baseEnd_2378742 := by
    simpa [prefixWord, tailWord_2378742, baseEnd_2378742] using wordTrace_append hprefix tailTrace_2378742
  have hstable : (prefixWord ++ tailWord_2378742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378742).length < 2 ^ (prefixWord ++ tailWord_2378742).sum := by decide
  have hdescent : baseEnd_2378742 < baseStart_2378742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378775 : List Nat := [1, 1, 3, 5, 1, 1, 3, 1, 2, 1, 4]
def baseStart_2378775 : Nat := 118140960795 + 2378775 * 2 ^ 59
def prefixEnd_2378775 : Nat := 4983230072969 + 3 ^ 40 * 2378775 * 2
def baseEnd_2378775 : Nat := 1221454943899035765572719

theorem tailTrace_2378775 : CollatzResearch.WordTrace tailWord_2378775 prefixEnd_2378775 1221454943899035765572719 := by
  unfold tailWord_2378775
  simp only [CollatzResearch.WordTrace]
  refine ⟨86761051957111912270905779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57840701304741274847270519 86761051957111912270905779)
  ·
    refine ⟨130141577935667868406358669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86761051957111912270905779 130141577935667868406358669)
    ·
      refine ⟨48803091725875450652384501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130141577935667868406358669 48803091725875450652384501)
      ·
        refine ⟨4575289849300823498661047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48803091725875450652384501 4575289849300823498661047)
        ·
          refine ⟨6862934773951235247991571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4575289849300823498661047 6862934773951235247991571)
          ·
            refine ⟨10294402160926852871987357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6862934773951235247991571 10294402160926852871987357)
            ·
              refine ⟨3860400810347569826995259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10294402160926852871987357 3860400810347569826995259)
              ·
                refine ⟨5790601215521354740492889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3860400810347569826995259 5790601215521354740492889)
                ·
                  refine ⟨4342950911641016055369667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5790601215521354740492889 4342950911641016055369667)
                  ·
                    refine ⟨6514426367461524083054501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4342950911641016055369667 6514426367461524083054501)
                    ·
                      refine ⟨1221454943899035765572719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6514426367461524083054501 1221454943899035765572719)
                      ·
                        rfl

theorem cell23_2378775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_2378775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2378775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2378775 prefixEnd_2378775 := by exact prefixLift 2378775
  have htrace : WordTrace (prefixWord ++ tailWord_2378775) baseStart_2378775 baseEnd_2378775 := by
    simpa [prefixWord, tailWord_2378775, baseEnd_2378775] using wordTrace_append hprefix tailTrace_2378775
  have hstable : (prefixWord ++ tailWord_2378775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378775).length < 2 ^ (prefixWord ++ tailWord_2378775).sum := by decide
  have hdescent : baseEnd_2378775 < baseStart_2378775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378778 : List Nat := [3, 1, 1, 3, 1, 2, 3, 1, 1, 4, 3]
def baseStart_2378778 : Nat := 118140960795 + 2378778 * 2 ^ 59
def prefixEnd_2378778 : Nat := 4983230072969 + 3 ^ 40 * 2378778 * 2
def baseEnd_2378778 : Nat := 1221456484340999253835205

theorem tailTrace_2378778 : CollatzResearch.WordTrace tailWord_2378778 prefixEnd_2378778 1221456484340999253835205 := by
  unfold tailWord_2378778
  simp only [CollatzResearch.WordTrace]
  refine ⟨21690290344025260945816247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57840774250734029188843325 21690290344025260945816247)
  ·
    refine ⟨32535435516037891418724371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21690290344025260945816247 32535435516037891418724371)
    ·
      refine ⟨48803153274056837128086557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32535435516037891418724371 48803153274056837128086557)
      ·
        refine ⟨18301182477771313923032459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48803153274056837128086557 18301182477771313923032459)
        ·
          refine ⟨27451773716656970884548689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18301182477771313923032459 27451773716656970884548689)
          ·
            refine ⟨20588830287492728163411517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27451773716656970884548689 20588830287492728163411517)
            ·
              refine ⟨7720811357809773061279319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20588830287492728163411517 7720811357809773061279319)
              ·
                refine ⟨11581217036714659591918979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7720811357809773061279319 11581217036714659591918979)
                ·
                  refine ⟨17371825555071989387878469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11581217036714659591918979 17371825555071989387878469)
                  ·
                    refine ⟨3257217291575998010227213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17371825555071989387878469 3257217291575998010227213)
                    ·
                      refine ⟨1221456484340999253835205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3257217291575998010227213 1221456484340999253835205)
                      ·
                        rfl

theorem cell23_2378778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_2378778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2378778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2378778 prefixEnd_2378778 := by exact prefixLift 2378778
  have htrace : WordTrace (prefixWord ++ tailWord_2378778) baseStart_2378778 baseEnd_2378778 := by
    simpa [prefixWord, tailWord_2378778, baseEnd_2378778] using wordTrace_append hprefix tailTrace_2378778
  have hstable : (prefixWord ++ tailWord_2378778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378778).length < 2 ^ (prefixWord ++ tailWord_2378778).sum := by decide
  have hdescent : baseEnd_2378778 < baseStart_2378778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378788 : List Nat := [2, 3, 1, 4, 1, 1, 1, 1, 2, 1, 6]
def baseStart_2378788 : Nat := 118140960795 + 2378788 * 2 ^ 59
def prefixEnd_2378788 : Nat := 4983230072969 + 3 ^ 40 * 2378788 * 2
def baseEnd_2378788 : Nat := 1221461619147544214710159

theorem tailTrace_2378788 : CollatzResearch.WordTrace tailWord_2378788 prefixEnd_2378788 1221461619147544214710159 := by
  unfold tailWord_2378788
  simp only [CollatzResearch.WordTrace]
  refine ⟨43380763053032407745564509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57841017404043210327419345 43380763053032407745564509)
  ·
    refine ⟨16267786144887152904586691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43380763053032407745564509 16267786144887152904586691)
    ·
      refine ⟨24401679217330729356880037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16267786144887152904586691 24401679217330729356880037)
      ·
        refine ⟨4575314853249511754415007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24401679217330729356880037 4575314853249511754415007)
        ·
          refine ⟨6862972279874267631622511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4575314853249511754415007 6862972279874267631622511)
          ·
            refine ⟨10294458419811401447433767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6862972279874267631622511 10294458419811401447433767)
            ·
              refine ⟨15441687629717102171150651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10294458419811401447433767 15441687629717102171150651)
              ·
                refine ⟨23162531444575653256725977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15441687629717102171150651 23162531444575653256725977)
                ·
                  refine ⟨17371898583431739942544483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23162531444575653256725977 17371898583431739942544483)
                  ·
                    refine ⟨26057847875147609913816725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17371898583431739942544483 26057847875147609913816725)
                    ·
                      refine ⟨1221461619147544214710159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26057847875147609913816725 1221461619147544214710159)
                      ·
                        rfl

theorem cell23_2378788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_2378788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2378788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2378788 prefixEnd_2378788 := by exact prefixLift 2378788
  have htrace : WordTrace (prefixWord ++ tailWord_2378788) baseStart_2378788 baseEnd_2378788 := by
    simpa [prefixWord, tailWord_2378788, baseEnd_2378788] using wordTrace_append hprefix tailTrace_2378788
  have hstable : (prefixWord ++ tailWord_2378788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378788).length < 2 ^ (prefixWord ++ tailWord_2378788).sum := by decide
  have hdescent : baseEnd_2378788 < baseStart_2378788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378798 : List Nat := [4, 1, 3, 1, 1, 1, 3, 1, 8]
def baseStart_2378798 : Nat := 118140960795 + 2378798 * 2 ^ 59
def prefixEnd_2378798 : Nat := 4983230072969 + 3 ^ 40 * 2378798 * 2
def baseEnd_2378798 : Nat := 135718528217121019509457

theorem tailTrace_2378798 : CollatzResearch.WordTrace tailWord_2378798 prefixEnd_2378798 135718528217121019509457 := by
  unfold tailWord_2378798
  simp only [CollatzResearch.WordTrace]
  refine ⟨10845236354503573399874131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57841260557352391465995365 10845236354503573399874131)
  ·
    refine ⟨16267854531755360099811197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10845236354503573399874131 16267854531755360099811197)
    ·
      refine ⟨6100445449408260037429199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16267854531755360099811197 6100445449408260037429199)
      ·
        refine ⟨9150668174112390056143799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6100445449408260037429199 9150668174112390056143799)
        ·
          refine ⟨13726002261168585084215699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9150668174112390056143799 13726002261168585084215699)
          ·
            refine ⟨20589003391752877626323549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13726002261168585084215699 20589003391752877626323549)
            ·
              refine ⟨7720876271907329109871331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20589003391752877626323549 7720876271907329109871331)
              ·
                refine ⟨11581314407860993664806997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7720876271907329109871331 11581314407860993664806997)
                ·
                  refine ⟨135718528217121019509457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11581314407860993664806997 135718528217121019509457)
                  ·
                    rfl

theorem cell23_2378798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 8].length) (baseStart_2378798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2378798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2378798 prefixEnd_2378798 := by exact prefixLift 2378798
  have htrace : WordTrace (prefixWord ++ tailWord_2378798) baseStart_2378798 baseEnd_2378798 := by
    simpa [prefixWord, tailWord_2378798, baseEnd_2378798] using wordTrace_append hprefix tailTrace_2378798
  have hstable : (prefixWord ++ tailWord_2378798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378798).length < 2 ^ (prefixWord ++ tailWord_2378798).sum := by decide
  have hdescent : baseEnd_2378798 < baseStart_2378798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378801 : List Nat := [1, 2, 2, 3, 1, 2, 1, 1, 1, 1, 8]
def baseStart_2378801 : Nat := 118140960795 + 2378801 * 2 ^ 59
def prefixEnd_2378801 : Nat := 4983230072969 + 3 ^ 40 * 2378801 * 2
def baseEnd_2378801 : Nat := 1221468294396052663847599

theorem tailTrace_2378801 : CollatzResearch.WordTrace tailWord_2378801 prefixEnd_2378801 1221468294396052663847599 := by
  unfold tailWord_2378801
  simp only [CollatzResearch.WordTrace]
  refine ⟨86762000255017718711352257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57841333503345145807568171 86762000255017718711352257)
  ·
    refine ⟨65071500191263289033514193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86762000255017718711352257 65071500191263289033514193)
    ·
      refine ⟨48803625143447466775135645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65071500191263289033514193 48803625143447466775135645)
      ·
        refine ⟨18301359428792800040675867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48803625143447466775135645 18301359428792800040675867)
        ·
          refine ⟨27452039143189200061013801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18301359428792800040675867 27452039143189200061013801)
          ·
            refine ⟨20589029357391900045760351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27452039143189200061013801 20589029357391900045760351)
            ·
              refine ⟨30883544036087850068640527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20589029357391900045760351 30883544036087850068640527)
              ·
                refine ⟨46325316054131775102960791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30883544036087850068640527 46325316054131775102960791)
                ·
                  refine ⟨69487974081197662654441187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46325316054131775102960791 69487974081197662654441187)
                  ·
                    refine ⟨104231961121796493981661781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 69487974081197662654441187 104231961121796493981661781)
                    ·
                      refine ⟨1221468294396052663847599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 104231961121796493981661781 1221468294396052663847599)
                      ·
                        rfl

theorem cell23_2378801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_2378801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2378801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2378801 prefixEnd_2378801 := by exact prefixLift 2378801
  have htrace : WordTrace (prefixWord ++ tailWord_2378801) baseStart_2378801 baseEnd_2378801 := by
    simpa [prefixWord, tailWord_2378801, baseEnd_2378801] using wordTrace_append hprefix tailTrace_2378801
  have hstable : (prefixWord ++ tailWord_2378801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378801).length < 2 ^ (prefixWord ++ tailWord_2378801).sum := by decide
  have hdescent : baseEnd_2378801 < baseStart_2378801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378821 : List Nat := [1, 3, 1, 1, 1, 3, 2, 1, 2, 1, 7]
def baseStart_2378821 : Nat := 118140960795 + 2378821 * 2 ^ 59
def prefixEnd_2378821 : Nat := 4983230072969 + 3 ^ 40 * 2378821 * 2
def baseEnd_2378821 : Nat := 1221478564009142585597507

theorem tailTrace_2378821 : CollatzResearch.WordTrace tailWord_2378821 prefixEnd_2378821 1221478564009142585597507 := by
  unfold tailWord_2378821
  simp only [CollatzResearch.WordTrace]
  refine ⟨86762729714945262127080317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57841819809963508084720211 86762729714945262127080317)
  ·
    refine ⟨32536023643104473297655119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86762729714945262127080317 32536023643104473297655119)
    ·
      refine ⟨48804035464656709946482679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32536023643104473297655119 48804035464656709946482679)
      ·
        refine ⟨73206053196985064919724019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48804035464656709946482679 73206053196985064919724019)
        ·
          refine ⟨109809079795477597379586029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73206053196985064919724019 109809079795477597379586029)
          ·
            refine ⟨41178404923304099017344761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109809079795477597379586029 41178404923304099017344761)
            ·
              refine ⟨30883803692478074263008571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41178404923304099017344761 30883803692478074263008571)
              ·
                refine ⟨46325705538717111394512857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30883803692478074263008571 46325705538717111394512857)
                ·
                  refine ⟨34744279154037833545884643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46325705538717111394512857 34744279154037833545884643)
                  ·
                    refine ⟨52116418731056750318826965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34744279154037833545884643 52116418731056750318826965)
                    ·
                      refine ⟨1221478564009142585597507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 52116418731056750318826965 1221478564009142585597507)
                      ·
                        rfl

theorem cell23_2378821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 1, 7].length) (baseStart_2378821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2378821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2378821 prefixEnd_2378821 := by exact prefixLift 2378821
  have htrace : WordTrace (prefixWord ++ tailWord_2378821) baseStart_2378821 baseEnd_2378821 := by
    simpa [prefixWord, tailWord_2378821, baseEnd_2378821] using wordTrace_append hprefix tailTrace_2378821
  have hstable : (prefixWord ++ tailWord_2378821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378821).length < 2 ^ (prefixWord ++ tailWord_2378821).sum := by decide
  have hdescent : baseEnd_2378821 < baseStart_2378821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378842 : List Nat := [3, 1, 1, 2, 1, 1, 2, 7, 1, 1, 3]
def baseStart_2378842 : Nat := 118140960795 + 2378842 * 2 ^ 59
def prefixEnd_2378842 : Nat := 4983230072969 + 3 ^ 40 * 2378842 * 2
def baseEnd_2378842 : Nat := 1221489347102887003434911

theorem tailTrace_2378842 : CollatzResearch.WordTrace tailWord_2378842 prefixEnd_2378842 1221489347102887003434911 := by
  unfold tailWord_2378842
  simp only [CollatzResearch.WordTrace]
  refine ⟨21690873911967295678398695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57842330431912788475729853 21690873911967295678398695)
  ·
    refine ⟨32536310867950943517598043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21690873911967295678398695 32536310867950943517598043)
    ·
      refine ⟨48804466301926415276397065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32536310867950943517598043 48804466301926415276397065)
      ·
        refine ⟨36603349726444811457297799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48804466301926415276397065 36603349726444811457297799)
        ·
          refine ⟨54905024589667217185946699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36603349726444811457297799 54905024589667217185946699)
          ·
            refine ⟨82357536884500825778920049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54905024589667217185946699 82357536884500825778920049)
            ·
              refine ⟨61768152663375619334190037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82357536884500825778920049 61768152663375619334190037)
              ·
                refine ⟨1447691078047866078145079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 61768152663375619334190037 1447691078047866078145079)
                ·
                  refine ⟨2171536617071799117217619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1447691078047866078145079 2171536617071799117217619)
                  ·
                    refine ⟨3257304925607698675826429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2171536617071799117217619 3257304925607698675826429)
                    ·
                      refine ⟨1221489347102887003434911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3257304925607698675826429 1221489347102887003434911)
                      ·
                        rfl

theorem cell23_2378842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 7, 1, 1, 3].length) (baseStart_2378842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2378842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2378842 prefixEnd_2378842 := by exact prefixLift 2378842
  have htrace : WordTrace (prefixWord ++ tailWord_2378842) baseStart_2378842 baseEnd_2378842 := by
    simpa [prefixWord, tailWord_2378842, baseEnd_2378842] using wordTrace_append hprefix tailTrace_2378842
  have hstable : (prefixWord ++ tailWord_2378842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378842).length < 2 ^ (prefixWord ++ tailWord_2378842).sum := by decide
  have hdescent : baseEnd_2378842 < baseStart_2378842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378915 : List Nat := [1, 1, 1, 4, 1, 1, 1, 5, 4, 1, 3]
def baseStart_2378915 : Nat := 118140960795 + 2378915 * 2 ^ 59
def prefixEnd_2378915 : Nat := 4983230072969 + 3 ^ 40 * 2378915 * 2
def baseEnd_2378915 : Nat := 1221526831190665217822075

theorem tailTrace_2378915 : CollatzResearch.WordTrace tailWord_2378915 prefixEnd_2378915 1221526831190665217822075 := by
  unfold tailWord_2378915
  simp only [CollatzResearch.WordTrace]
  refine ⟨86766158176604716181002199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57844105451069810787334799 86766158176604716181002199)
  ·
    refine ⟨130149237264907074271503299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86766158176604716181002199 130149237264907074271503299)
    ·
      refine ⟨195223855897360611407254949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130149237264907074271503299 195223855897360611407254949)
      ·
        refine ⟨36604472980755114638860303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 195223855897360611407254949 36604472980755114638860303)
        ·
          refine ⟨54906709471132671958290455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36604472980755114638860303 54906709471132671958290455)
          ·
            refine ⟨82360064206699007937435683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54906709471132671958290455 82360064206699007937435683)
            ·
              refine ⟨123540096310048511906153525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82360064206699007937435683 123540096310048511906153525)
              ·
                refine ⟨11581884029067047991201893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 123540096310048511906153525 11581884029067047991201893)
                ·
                  refine ⟨2171603255450071498350355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11581884029067047991201893 2171603255450071498350355)
                  ·
                    refine ⟨3257404883175107247525533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2171603255450071498350355 3257404883175107247525533)
                    ·
                      refine ⟨1221526831190665217822075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3257404883175107247525533 1221526831190665217822075)
                      ·
                        rfl

theorem cell23_2378915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 4, 1, 3].length) (baseStart_2378915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2378915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2378915 prefixEnd_2378915 := by exact prefixLift 2378915
  have htrace : WordTrace (prefixWord ++ tailWord_2378915) baseStart_2378915 baseEnd_2378915 := by
    simpa [prefixWord, tailWord_2378915, baseEnd_2378915] using wordTrace_append hprefix tailTrace_2378915
  have hstable : (prefixWord ++ tailWord_2378915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378915).length < 2 ^ (prefixWord ++ tailWord_2378915).sum := by decide
  have hdescent : baseEnd_2378915 < baseStart_2378915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378916 : List Nat := [2, 3, 1, 2, 3, 2, 1, 4, 1, 2, 2]
def baseStart_2378916 : Nat := 118140960795 + 2378916 * 2 ^ 59
def prefixEnd_2378916 : Nat := 4983230072969 + 3 ^ 40 * 2378916 * 2
def baseEnd_2378916 : Nat := 1221527344671319713909571

theorem tailTrace_2378916 : CollatzResearch.WordTrace tailWord_2378916 prefixEnd_2378916 1221527344671319713909571 := by
  unfold tailWord_2378916
  simp only [CollatzResearch.WordTrace]
  refine ⟨43383097324800546675894301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57844129766400728901192401 43383097324800546675894301)
  ·
    refine ⟨16268661496800205003460363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43383097324800546675894301 16268661496800205003460363)
    ·
      refine ⟨24402992245200307505190545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16268661496800205003460363 24402992245200307505190545)
      ·
        refine ⟨18302244183900230628892909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24402992245200307505190545 18302244183900230628892909)
        ·
          refine ⟨6863341568962586485834841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18302244183900230628892909 6863341568962586485834841)
          ·
            refine ⟨5147506176721939864376131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6863341568962586485834841 5147506176721939864376131)
            ·
              refine ⟨7721259265082909796564197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5147506176721939864376131 7721259265082909796564197)
              ·
                refine ⟨1447736112203045586855787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7721259265082909796564197 1447736112203045586855787)
                ·
                  refine ⟨2171604168304568380283681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1447736112203045586855787 2171604168304568380283681)
                  ·
                    refine ⟨1628703126228426285212761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2171604168304568380283681 1628703126228426285212761)
                    ·
                      refine ⟨1221527344671319713909571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1628703126228426285212761 1221527344671319713909571)
                      ·
                        rfl

theorem cell23_2378916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 4, 1, 2, 2].length) (baseStart_2378916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2378916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2378916 prefixEnd_2378916 := by exact prefixLift 2378916
  have htrace : WordTrace (prefixWord ++ tailWord_2378916) baseStart_2378916 baseEnd_2378916 := by
    simpa [prefixWord, tailWord_2378916, baseEnd_2378916] using wordTrace_append hprefix tailTrace_2378916
  have hstable : (prefixWord ++ tailWord_2378916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378916).length < 2 ^ (prefixWord ++ tailWord_2378916).sum := by decide
  have hdescent : baseEnd_2378916 < baseStart_2378916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378922 : List Nat := [3, 1, 5, 1, 1, 3, 1, 8]
def baseStart_2378922 : Nat := 118140960795 + 2378922 * 2 ^ 59
def prefixEnd_2378922 : Nat := 4983230072969 + 3 ^ 40 * 2378922 * 2
def baseEnd_2378922 : Nat := 45241867613157284830909

theorem tailTrace_2378922 : CollatzResearch.WordTrace tailWord_2378922 prefixEnd_2378922 45241867613157284830909 := by
  unfold tailWord_2378922
  simp only [CollatzResearch.WordTrace]
  refine ⟨21691603371894839094126755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57844275658386237584338013 21691603371894839094126755)
  ·
    refine ⟨32537405057842258641190133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21691603371894839094126755 32537405057842258641190133)
    ·
      refine ⟨3050381724172711747611575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32537405057842258641190133 3050381724172711747611575)
      ·
        refine ⟨4575572586259067621417363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3050381724172711747611575 4575572586259067621417363)
        ·
          refine ⟨6863358879388601432126045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4575572586259067621417363 6863358879388601432126045)
          ·
            refine ⟨2573759579770725537047267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6863358879388601432126045 2573759579770725537047267)
            ·
              refine ⟨3860639369656088305570901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2573759579770725537047267 3860639369656088305570901)
              ·
                refine ⟨45241867613157284830909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3860639369656088305570901 45241867613157284830909)
                ·
                  rfl

theorem cell23_2378922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 8].length) (baseStart_2378922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2378922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2378922 prefixEnd_2378922 := by exact prefixLift 2378922
  have htrace : WordTrace (prefixWord ++ tailWord_2378922) baseStart_2378922 baseEnd_2378922 := by
    simpa [prefixWord, tailWord_2378922, baseEnd_2378922] using wordTrace_append hprefix tailTrace_2378922
  have hstable : (prefixWord ++ tailWord_2378922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378922).length < 2 ^ (prefixWord ++ tailWord_2378922).sum := by decide
  have hdescent : baseEnd_2378922 < baseStart_2378922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378938 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 4, 3, 4]
def baseStart_2378938 : Nat := 118140960795 + 2378938 * 2 ^ 59
def prefixEnd_2378938 : Nat := 4983230072969 + 3 ^ 40 * 2378938 * 2
def baseEnd_2378938 : Nat := 1221538641245718627834469

theorem tailTrace_2378938 : CollatzResearch.WordTrace tailWord_2378938 prefixEnd_2378938 1221538641245718627834469 := by
  unfold tailWord_2378938
  simp only [CollatzResearch.WordTrace]
  refine ⟨21691749263880347777272367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57844664703680927406059645 21691749263880347777272367)
  ·
    refine ⟨32537623895820521665908551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21691749263880347777272367 32537623895820521665908551)
    ·
      refine ⟨48806435843730782498862827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32537623895820521665908551 48806435843730782498862827)
      ·
        refine ⟨73209653765596173748294241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48806435843730782498862827 73209653765596173748294241)
        ·
          refine ⟨54907240324197130311220681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73209653765596173748294241 54907240324197130311220681)
          ·
            refine ⟨41180430243147847733415511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54907240324197130311220681 41180430243147847733415511)
            ·
              refine ⟨61770645364721771600123267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41180430243147847733415511 61770645364721771600123267)
              ·
                refine ⟨92655968047082657400184901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61770645364721771600123267 92655968047082657400184901)
                ·
                  refine ⟨17372994008827998262534669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 92655968047082657400184901 17372994008827998262534669)
                  ·
                    refine ⟨6514872753310499348450501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17372994008827998262534669 6514872753310499348450501)
                    ·
                      refine ⟨1221538641245718627834469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6514872753310499348450501 1221538641245718627834469)
                      ·
                        rfl

theorem cell23_2378938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 4, 3, 4].length) (baseStart_2378938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2378938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2378938 prefixEnd_2378938 := by exact prefixLift 2378938
  have htrace : WordTrace (prefixWord ++ tailWord_2378938) baseStart_2378938 baseEnd_2378938 := by
    simpa [prefixWord, tailWord_2378938, baseEnd_2378938] using wordTrace_append hprefix tailTrace_2378938
  have hstable : (prefixWord ++ tailWord_2378938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378938).length < 2 ^ (prefixWord ++ tailWord_2378938).sum := by decide
  have hdescent : baseEnd_2378938 < baseStart_2378938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378950 : List Nat := [6, 1, 2, 2, 1, 2, 2, 1, 1, 1, 4]
def baseStart_2378950 : Nat := 118140960795 + 2378950 * 2 ^ 59
def prefixEnd_2378950 : Nat := 4983230072969 + 3 ^ 40 * 2378950 * 2
def baseEnd_2378950 : Nat := 1221544803013572580884415

theorem tailTrace_2378950 : CollatzResearch.WordTrace tailWord_2378950 prefixEnd_2378950 1221544803013572580884415 := by
  unfold tailWord_2378950
  simp only [CollatzResearch.WordTrace]
  refine ⟨2711482335358684911203947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 57844956487651944772350869 2711482335358684911203947)
  ·
    refine ⟨4067223503038027366805921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2711482335358684911203947 4067223503038027366805921)
    ·
      refine ⟨3050417627278520525104441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4067223503038027366805921 3050417627278520525104441)
      ·
        refine ⟨2287813220458890393828331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3050417627278520525104441 2287813220458890393828331)
        ·
          refine ⟨3431719830688335590742497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2287813220458890393828331 3431719830688335590742497)
          ·
            refine ⟨2573789873016251693056873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3431719830688335590742497 2573789873016251693056873)
            ·
              refine ⟨1930342404762188769792655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2573789873016251693056873 1930342404762188769792655)
              ·
                refine ⟨2895513607143283154688983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1930342404762188769792655 2895513607143283154688983)
                ·
                  refine ⟨4343270410714924732033475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2895513607143283154688983 4343270410714924732033475)
                  ·
                    refine ⟨6514905616072387098050213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4343270410714924732033475 6514905616072387098050213)
                    ·
                      refine ⟨1221544803013572580884415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6514905616072387098050213 1221544803013572580884415)
                      ·
                        rfl

theorem cell23_2378950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_2378950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2378950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2378950 prefixEnd_2378950 := by exact prefixLift 2378950
  have htrace : WordTrace (prefixWord ++ tailWord_2378950) baseStart_2378950 baseEnd_2378950 := by
    simpa [prefixWord, tailWord_2378950, baseEnd_2378950] using wordTrace_append hprefix tailTrace_2378950
  have hstable : (prefixWord ++ tailWord_2378950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378950).length < 2 ^ (prefixWord ++ tailWord_2378950).sum := by decide
  have hdescent : baseEnd_2378950 < baseStart_2378950 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378955 : List Nat := [1, 1, 1, 1, 3, 2, 2, 3, 3, 4, 2]
def baseStart_2378955 : Nat := 118140960795 + 2378955 * 2 ^ 59
def prefixEnd_2378955 : Nat := 4983230072969 + 3 ^ 40 * 2378955 * 2
def baseEnd_2378955 : Nat := 1221547370416845061321891

theorem tailTrace_2378955 : CollatzResearch.WordTrace tailWord_2378955 prefixEnd_2378955 1221547370416845061321891 := by
  unfold tailWord_2378955
  simp only [CollatzResearch.WordTrace]
  refine ⟨86767617096459803012458319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57845078064306535341638879 86767617096459803012458319)
  ·
    refine ⟨130151425644689704518687479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86767617096459803012458319 130151425644689704518687479)
    ·
      refine ⟨195227138467034556778031219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130151425644689704518687479 195227138467034556778031219)
      ·
        refine ⟨292840707700551835167046829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195227138467034556778031219 292840707700551835167046829)
        ·
          refine ⟨109815265387706938187642561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 292840707700551835167046829 109815265387706938187642561)
          ·
            refine ⟨82361449040780203640731921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109815265387706938187642561 82361449040780203640731921)
            ·
              refine ⟨61771086780585152730548941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82361449040780203640731921 61771086780585152730548941)
              ·
                refine ⟨23164157542719432273955853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61771086780585152730548941 23164157542719432273955853)
                ·
                  refine ⟨8686559078519787102733445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23164157542719432273955853 8686559078519787102733445)
                  ·
                    refine ⟨1628729827222460081762521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8686559078519787102733445 1628729827222460081762521)
                    ·
                      refine ⟨1221547370416845061321891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1628729827222460081762521 1221547370416845061321891)
                      ·
                        rfl

theorem cell23_2378955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 4, 2].length) (baseStart_2378955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2378955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2378955 prefixEnd_2378955 := by exact prefixLift 2378955
  have htrace : WordTrace (prefixWord ++ tailWord_2378955) baseStart_2378955 baseEnd_2378955 := by
    simpa [prefixWord, tailWord_2378955, baseEnd_2378955] using wordTrace_append hprefix tailTrace_2378955
  have hstable : (prefixWord ++ tailWord_2378955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378955).length < 2 ^ (prefixWord ++ tailWord_2378955).sum := by decide
  have hdescent : baseEnd_2378955 < baseStart_2378955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378965 : List Nat := [1, 3, 2, 4, 1, 1, 1, 2, 2, 6]
def baseStart_2378965 : Nat := 118140960795 + 2378965 * 2 ^ 59
def prefixEnd_2378965 : Nat := 4983230072969 + 3 ^ 40 * 2378965 * 2
def baseEnd_2378965 : Nat := 407184168407796674065615

theorem tailTrace_2378965 : CollatzResearch.WordTrace tailWord_2378965 prefixEnd_2378965 407184168407796674065615 := by
  unfold tailWord_2378965
  simp only [CollatzResearch.WordTrace]
  refine ⟨86767981826423574720322349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57845321217615716480214899 86767981826423574720322349)
  ·
    refine ⟨32537993184908840520120881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86767981826423574720322349 32537993184908840520120881)
    ·
      refine ⟨24403494888681630390090661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32537993184908840520120881 24403494888681630390090661)
      ·
        refine ⟨4575655291627805698141999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24403494888681630390090661 4575655291627805698141999)
        ·
          refine ⟨6863482937441708547212999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4575655291627805698141999 6863482937441708547212999)
          ·
            refine ⟨10295224406162562820819499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6863482937441708547212999 10295224406162562820819499)
            ·
              refine ⟨15442836609243844231229249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10295224406162562820819499 15442836609243844231229249)
              ·
                refine ⟨11582127456932883173421937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15442836609243844231229249 11582127456932883173421937)
                ·
                  refine ⟨8686595592699662380066453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11582127456932883173421937 8686595592699662380066453)
                  ·
                    refine ⟨407184168407796674065615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8686595592699662380066453 407184168407796674065615)
                    ·
                      rfl

theorem cell23_2378965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 6].length) (baseStart_2378965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2378965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2378965 prefixEnd_2378965 := by exact prefixLift 2378965
  have htrace : WordTrace (prefixWord ++ tailWord_2378965) baseStart_2378965 baseEnd_2378965 := by
    simpa [prefixWord, tailWord_2378965, baseEnd_2378965] using wordTrace_append hprefix tailTrace_2378965
  have hstable : (prefixWord ++ tailWord_2378965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378965).length < 2 ^ (prefixWord ++ tailWord_2378965).sum := by decide
  have hdescent : baseEnd_2378965 < baseStart_2378965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378966 : List Nat := [5, 2, 1, 2, 2, 1, 1, 1, 4, 1, 3]
def baseStart_2378966 : Nat := 118140960795 + 2378966 * 2 ^ 59
def prefixEnd_2378966 : Nat := 4983230072969 + 3 ^ 40 * 2378966 * 2
def baseEnd_2378966 : Nat := 1221553018704044518284341

theorem tailTrace_2378966 : CollatzResearch.WordTrace tailWord_2378966 prefixEnd_2378966 1221553018704044518284341 := by
  unfold tailWord_2378966
  simp only [CollatzResearch.WordTrace]
  refine ⟨5423001143713746993194297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57845345532946634594072501 5423001143713746993194297)
  ·
    refine ⟨4067250857785310244895723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5423001143713746993194297 4067250857785310244895723)
    ·
      refine ⟨6100876286677965367343585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4067250857785310244895723 6100876286677965367343585)
      ·
        refine ⟨4575657215008474025507689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6100876286677965367343585 4575657215008474025507689)
        ·
          refine ⟨3431742911256355519130767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4575657215008474025507689 3431742911256355519130767)
          ·
            refine ⟨5147614366884533278696151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3431742911256355519130767 5147614366884533278696151)
            ·
              refine ⟨7721421550326799918044227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5147614366884533278696151 7721421550326799918044227)
              ·
                refine ⟨11582132325490199877066341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7721421550326799918044227 11582132325490199877066341)
                ·
                  refine ⟨2171649811029412476949939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11582132325490199877066341 2171649811029412476949939)
                  ·
                    refine ⟨3257474716544118715424909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2171649811029412476949939 3257474716544118715424909)
                    ·
                      refine ⟨1221553018704044518284341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3257474716544118715424909 1221553018704044518284341)
                      ·
                        rfl

theorem cell23_2378966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_2378966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2378966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2378966 prefixEnd_2378966 := by exact prefixLift 2378966
  have htrace : WordTrace (prefixWord ++ tailWord_2378966) baseStart_2378966 baseEnd_2378966 := by
    simpa [prefixWord, tailWord_2378966, baseEnd_2378966] using wordTrace_append hprefix tailTrace_2378966
  have hstable : (prefixWord ++ tailWord_2378966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378966).length < 2 ^ (prefixWord ++ tailWord_2378966).sum := by decide
  have hdescent : baseEnd_2378966 < baseStart_2378966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378989 : List Nat := [1, 5, 1, 2, 2, 1, 3, 1, 1, 4, 2]
def baseStart_2378989 : Nat := 118140960795 + 2378989 * 2 ^ 59
def prefixEnd_2378989 : Nat := 4983230072969 + 3 ^ 40 * 2378989 * 2
def baseEnd_2378989 : Nat := 1221564828759097928296735

theorem tailTrace_2378989 : CollatzResearch.WordTrace tailWord_2378989 prefixEnd_2378989 1221564828759097928296735 := by
  unfold tailWord_2378989
  simp only [CollatzResearch.WordTrace]
  refine ⟨86768857178336626819196021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57845904785557751212797347 86768857178336626819196021)
  ·
    refine ⟨8134580360469058764299627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 86768857178336626819196021 8134580360469058764299627)
    ·
      refine ⟨12201870540703588146449441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8134580360469058764299627 12201870540703588146449441)
      ·
        refine ⟨9151402905527691109837081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12201870540703588146449441 9151402905527691109837081)
        ·
          refine ⟨6863552179145768332377811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9151402905527691109837081 6863552179145768332377811)
          ·
            refine ⟨10295328268718652498566717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6863552179145768332377811 10295328268718652498566717)
            ·
              refine ⟨3860748100769494686962519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10295328268718652498566717 3860748100769494686962519)
              ·
                refine ⟨5791122151154242030443779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3860748100769494686962519 5791122151154242030443779)
                ·
                  refine ⟨8686683226731363045665669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5791122151154242030443779 8686683226731363045665669)
                  ·
                    refine ⟨1628753105012130571062313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8686683226731363045665669 1628753105012130571062313)
                    ·
                      refine ⟨1221564828759097928296735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1628753105012130571062313 1221564828759097928296735)
                      ·
                        rfl

theorem cell23_2378989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_2378989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2378989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2378989 prefixEnd_2378989 := by exact prefixLift 2378989
  have htrace : WordTrace (prefixWord ++ tailWord_2378989) baseStart_2378989 baseEnd_2378989 := by
    simpa [prefixWord, tailWord_2378989, baseEnd_2378989] using wordTrace_append hprefix tailTrace_2378989
  have hstable : (prefixWord ++ tailWord_2378989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378989).length < 2 ^ (prefixWord ++ tailWord_2378989).sum := by decide
  have hdescent : baseEnd_2378989 < baseStart_2378989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379025 : List Nat := [1, 2, 2, 1, 1, 4, 3, 2, 2, 5]
def baseStart_2379025 : Nat := 118140960795 + 2379025 * 2 ^ 59
def prefixEnd_2379025 : Nat := 4983230072969 + 3 ^ 40 * 2379025 * 2
def baseEnd_2379025 : Nat := 407194438020886595815523

theorem tailTrace_2379025 : CollatzResearch.WordTrace tailWord_2379025 prefixEnd_2379025 407194438020886595815523 := by
  unfold tailWord_2379025
  simp only [CollatzResearch.WordTrace]
  refine ⟨86770170206206204967506529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57846780137470803311671019 86770170206206204967506529)
  ·
    refine ⟨65077627654654653725629897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86770170206206204967506529 65077627654654653725629897)
    ·
      refine ⟨48808220740990990294222423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65077627654654653725629897 48808220740990990294222423)
      ·
        refine ⟨73212331111486485441333635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48808220740990990294222423 73212331111486485441333635)
        ·
          refine ⟨109818496667229728162000453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73212331111486485441333635 109818496667229728162000453)
          ·
            refine ⟨20590968125105574030375085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109818496667229728162000453 20590968125105574030375085)
            ·
              refine ⟨7721613046914590261390657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20590968125105574030375085 7721613046914590261390657)
              ·
                refine ⟨5791209785185942696042993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7721613046914590261390657 5791209785185942696042993)
                ·
                  refine ⟨4343407338889457022032245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5791209785185942696042993 4343407338889457022032245)
                  ·
                    refine ⟨407194438020886595815523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4343407338889457022032245 407194438020886595815523)
                    ·
                      rfl

theorem cell23_2379025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 5].length) (baseStart_2379025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2379025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2379025 prefixEnd_2379025 := by exact prefixLift 2379025
  have htrace : WordTrace (prefixWord ++ tailWord_2379025) baseStart_2379025 baseEnd_2379025 := by
    simpa [prefixWord, tailWord_2379025, baseEnd_2379025] using wordTrace_append hprefix tailTrace_2379025
  have hstable : (prefixWord ++ tailWord_2379025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379025).length < 2 ^ (prefixWord ++ tailWord_2379025).sum := by decide
  have hdescent : baseEnd_2379025 < baseStart_2379025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379040 : List Nat := [2, 1, 1, 5, 4, 1, 2, 1, 2, 2, 2]
def baseStart_2379040 : Nat := 118140960795 + 2379040 * 2 ^ 59
def prefixEnd_2379040 : Nat := 4983230072969 + 3 ^ 40 * 2379040 * 2
def baseEnd_2379040 : Nat := 1221591016272477228759001

theorem tailTrace_2379040 : CollatzResearch.WordTrace tailWord_2379040 prefixEnd_2379040 1221591016272477228759001 := by
  unfold tailWord_2379040
  simp only [CollatzResearch.WordTrace]
  refine ⟨43385358650575931264651287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57847144867434575019535049 43385358650575931264651287)
  ·
    refine ⟨65078037975863896896976931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43385358650575931264651287 65078037975863896896976931)
    ·
      refine ⟨97617056963795845345465397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65078037975863896896976931 97617056963795845345465397)
      ·
        refine ⟨9151599090355860501137381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 97617056963795845345465397 9151599090355860501137381)
        ·
          refine ⟨1715924829441723843963259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9151599090355860501137381 1715924829441723843963259)
          ·
            refine ⟨2573887244162585765944889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1715924829441723843963259 2573887244162585765944889)
            ·
              refine ⟨1930415433121939324458667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2573887244162585765944889 1930415433121939324458667)
              ·
                refine ⟨2895623149682908986688001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1930415433121939324458667 2895623149682908986688001)
                ·
                  refine ⟨2171717362262181740016001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2895623149682908986688001 2171717362262181740016001)
                  ·
                    refine ⟨1628788021696636305012001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2171717362262181740016001 1628788021696636305012001)
                    ·
                      refine ⟨1221591016272477228759001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1628788021696636305012001 1221591016272477228759001)
                      ·
                        rfl

theorem cell23_2379040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_2379040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2379040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2379040 prefixEnd_2379040 := by exact prefixLift 2379040
  have htrace : WordTrace (prefixWord ++ tailWord_2379040) baseStart_2379040 baseEnd_2379040 := by
    simpa [prefixWord, tailWord_2379040, baseEnd_2379040] using wordTrace_append hprefix tailTrace_2379040
  have hstable : (prefixWord ++ tailWord_2379040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379040).length < 2 ^ (prefixWord ++ tailWord_2379040).sum := by decide
  have hdescent : baseEnd_2379040 < baseStart_2379040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379055 : List Nat := [1, 1, 2, 1, 2, 1, 3, 3, 5, 4]
def baseStart_2379055 : Nat := 118140960795 + 2379055 * 2 ^ 59
def prefixEnd_2379055 : Nat := 4983230072969 + 3 ^ 40 * 2379055 * 2
def baseEnd_2379055 : Nat := 407199572827431556690477

theorem tailTrace_2379055 : CollatzResearch.WordTrace tailWord_2379055 prefixEnd_2379055 407199572827431556690477 := by
  unfold tailWord_2379055
  simp only [CollatzResearch.WordTrace]
  refine ⟨86771264396097520091098619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57847509597398346727399079 86771264396097520091098619)
  ·
    refine ⟨130156896594146280136647929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86771264396097520091098619 130156896594146280136647929)
    ·
      refine ⟨97617672445609710102485947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130156896594146280136647929 97617672445609710102485947)
      ·
        refine ⟨146426508668414565153728921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97617672445609710102485947 146426508668414565153728921)
        ·
          refine ⟨109819881501310923865296691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146426508668414565153728921 109819881501310923865296691)
          ·
            refine ⟨164729822251966385797945037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109819881501310923865296691 164729822251966385797945037)
            ·
              refine ⟨61773683344487394674229389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 164729822251966385797945037 61773683344487394674229389)
              ·
                refine ⟨23165131254182773002836021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61773683344487394674229389 23165131254182773002836021)
                ·
                  refine ⟨2171731055079634969015877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23165131254182773002836021 2171731055079634969015877)
                  ·
                    refine ⟨407199572827431556690477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2171731055079634969015877 407199572827431556690477)
                    ·
                      rfl

theorem cell23_2379055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 5, 4].length) (baseStart_2379055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2379055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2379055 prefixEnd_2379055 := by exact prefixLift 2379055
  have htrace : WordTrace (prefixWord ++ tailWord_2379055) baseStart_2379055 baseEnd_2379055 := by
    simpa [prefixWord, tailWord_2379055, baseEnd_2379055] using wordTrace_append hprefix tailTrace_2379055
  have hstable : (prefixWord ++ tailWord_2379055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379055).length < 2 ^ (prefixWord ++ tailWord_2379055).sum := by decide
  have hdescent : baseEnd_2379055 < baseStart_2379055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379089 : List Nat := [1, 2, 2, 1, 4, 1, 3, 4, 1, 4]
def baseStart_2379089 : Nat := 118140960795 + 2379089 * 2 ^ 59
def prefixEnd_2379089 : Nat := 4983230072969 + 3 ^ 40 * 2379089 * 2
def baseEnd_2379089 : Nat := 407205392274849179015425

theorem tailTrace_2379089 : CollatzResearch.WordTrace tailWord_2379089 prefixEnd_2379089 407205392274849179015425 := by
  unfold tailWord_2379089
  simp only [CollatzResearch.WordTrace]
  refine ⟨86772504477974343897836321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57848336318649562598557547 86772504477974343897836321)
  ·
    refine ⟨65079378358480757923377241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86772504477974343897836321 65079378358480757923377241)
    ·
      refine ⟨48809533768860568442532931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65079378358480757923377241 48809533768860568442532931)
      ·
        refine ⟨73214300653290852663799397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48809533768860568442532931 73214300653290852663799397)
        ·
          refine ⟨13727681372492034874462387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73214300653290852663799397 13727681372492034874462387)
          ·
            refine ⟨20591522058738052311693581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13727681372492034874462387 20591522058738052311693581)
            ·
              refine ⟨7721820772026769616885093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20591522058738052311693581 7721820772026769616885093)
              ·
                refine ⟨1447841394755019303165955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7721820772026769616885093 1447841394755019303165955)
                ·
                  refine ⟨2171762092132528954748933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1447841394755019303165955 2171762092132528954748933)
                  ·
                    refine ⟨407205392274849179015425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2171762092132528954748933 407205392274849179015425)
                    ·
                      rfl

theorem cell23_2379089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 4, 1, 4].length) (baseStart_2379089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2379089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2379089 prefixEnd_2379089 := by exact prefixLift 2379089
  have htrace : WordTrace (prefixWord ++ tailWord_2379089) baseStart_2379089 baseEnd_2379089 := by
    simpa [prefixWord, tailWord_2379089, baseEnd_2379089] using wordTrace_append hprefix tailTrace_2379089
  have hstable : (prefixWord ++ tailWord_2379089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379089).length < 2 ^ (prefixWord ++ tailWord_2379089).sum := by decide
  have hdescent : baseEnd_2379089 < baseStart_2379089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379132 : List Nat := [2, 2, 2, 1, 1, 1, 5, 3, 1, 5]
def baseStart_2379132 : Nat := 118140960795 + 2379132 * 2 ^ 59
def prefixEnd_2379132 : Nat := 4983230072969 + 3 ^ 40 * 2379132 * 2
def baseEnd_2379132 : Nat := 407212752164230289602859

theorem tailTrace_2379132 : CollatzResearch.WordTrace tailWord_2379132 prefixEnd_2379132 407212752164230289602859 := by
  unfold tailWord_2379132
  simp only [CollatzResearch.WordTrace]
  refine ⟨43387036408409281120825825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57849381877879041494434433 43387036408409281120825825)
  ·
    refine ⟨32540277306306960840619369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43387036408409281120825825 32540277306306960840619369)
    ·
      refine ⟨24405207979730220630464527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32540277306306960840619369 24405207979730220630464527)
      ·
        refine ⟨36607811969595330945696791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24405207979730220630464527 36607811969595330945696791)
        ·
          refine ⟨54911717954392996418545187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36607811969595330945696791 54911717954392996418545187)
          ·
            refine ⟨82367576931589494627817781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54911717954392996418545187 82367576931589494627817781)
            ·
              refine ⟨7721960337336515121357917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82367576931589494627817781 7721960337336515121357917)
              ·
                refine ⟨2895735126501193170509219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7721960337336515121357917 2895735126501193170509219)
                ·
                  refine ⟨4343602689751789755763829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2895735126501193170509219 4343602689751789755763829)
                  ·
                    refine ⟨407212752164230289602859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4343602689751789755763829 407212752164230289602859)
                    ·
                      rfl

theorem cell23_2379132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 3, 1, 5].length) (baseStart_2379132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2379132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2379132 prefixEnd_2379132 := by exact prefixLift 2379132
  have htrace : WordTrace (prefixWord ++ tailWord_2379132) baseStart_2379132 baseEnd_2379132 := by
    simpa [prefixWord, tailWord_2379132, baseEnd_2379132] using wordTrace_append hprefix tailTrace_2379132
  have hstable : (prefixWord ++ tailWord_2379132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379132).length < 2 ^ (prefixWord ++ tailWord_2379132).sum := by decide
  have hdescent : baseEnd_2379132 < baseStart_2379132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379189 : List Nat := [1, 3, 3, 2, 2, 2, 2, 1, 1, 1, 5]
def baseStart_2379189 : Nat := 118140960795 + 2379189 * 2 ^ 59
def prefixEnd_2379189 : Nat := 4983230072969 + 3 ^ 40 * 2379189 * 2
def baseEnd_2379189 : Nat := 1221667524889997145795815

theorem tailTrace_2379189 : CollatzResearch.WordTrace tailWord_2379189 prefixEnd_2379189 1221667524889997145795815 := by
  unfold tailWord_2379189
  simp only [CollatzResearch.WordTrace]
  refine ⟨86776151777612060976476621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57850767851741373984317747 86776151777612060976476621)
  ·
    refine ⟨32541056916604522866178733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86776151777612060976476621 32541056916604522866178733)
    ·
      refine ⟨12202896343726696074817025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32541056916604522866178733 12202896343726696074817025)
      ·
        refine ⟨9152172257795022056112769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12202896343726696074817025 9152172257795022056112769)
        ·
          refine ⟨6864129193346266542084577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9152172257795022056112769 6864129193346266542084577)
          ·
            refine ⟨5148096895009699906563433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6864129193346266542084577 5148096895009699906563433)
            ·
              refine ⟨3861072671257274929922575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5148096895009699906563433 3861072671257274929922575)
              ·
                refine ⟨5791609006885912394883863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3861072671257274929922575 5791609006885912394883863)
                ·
                  refine ⟨8687413510328868592325795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5791609006885912394883863 8687413510328868592325795)
                  ·
                    refine ⟨13031120265493302888488693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8687413510328868592325795 13031120265493302888488693)
                    ·
                      refine ⟨1221667524889997145795815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13031120265493302888488693 1221667524889997145795815)
                      ·
                        rfl

theorem cell23_2379189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_2379189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2379189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2379189 prefixEnd_2379189 := by exact prefixLift 2379189
  have htrace : WordTrace (prefixWord ++ tailWord_2379189) baseStart_2379189 baseEnd_2379189 := by
    simpa [prefixWord, tailWord_2379189, baseEnd_2379189] using wordTrace_append hprefix tailTrace_2379189
  have hstable : (prefixWord ++ tailWord_2379189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379189).length < 2 ^ (prefixWord ++ tailWord_2379189).sum := by decide
  have hdescent : baseEnd_2379189 < baseStart_2379189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379253 : List Nat := [1, 3, 5, 1, 1, 1, 1, 4, 2, 1, 3]
def baseStart_2379253 : Nat := 118140960795 + 2379253 * 2 ^ 59
def prefixEnd_2379253 : Nat := 4983230072969 + 3 ^ 40 * 2379253 * 2
def baseEnd_2379253 : Nat := 1221700387651884895395521

theorem tailTrace_2379253 : CollatzResearch.WordTrace tailWord_2379253 prefixEnd_2379253 1221700387651884895395521 := by
  unfold tailWord_2379253
  simp only [CollatzResearch.WordTrace]
  refine ⟨86778486049380199906806413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57852324032920133271204275 86778486049380199906806413)
  ·
    refine ⟨32541932268517574965052405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86778486049380199906806413 32541932268517574965052405)
    ·
      refine ⟨3050806150173522652973663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32541932268517574965052405 3050806150173522652973663)
      ·
        refine ⟨4576209225260283979460495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3050806150173522652973663 4576209225260283979460495)
        ·
          refine ⟨6864313837890425969190743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4576209225260283979460495 6864313837890425969190743)
          ·
            refine ⟨10296470756835638953786115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6864313837890425969190743 10296470756835638953786115)
            ·
              refine ⟨15444706135253458430679173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10296470756835638953786115 15444706135253458430679173)
              ·
                refine ⟨2895882400360023455752345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15444706135253458430679173 2895882400360023455752345)
                ·
                  refine ⟨2171911800270017591814259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2895882400360023455752345 2171911800270017591814259)
                  ·
                    refine ⟨3257867700405026387721389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2171911800270017591814259 3257867700405026387721389)
                    ·
                      refine ⟨1221700387651884895395521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3257867700405026387721389 1221700387651884895395521)
                      ·
                        rfl

theorem cell23_2379253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_2379253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2379253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2379253 prefixEnd_2379253 := by exact prefixLift 2379253
  have htrace : WordTrace (prefixWord ++ tailWord_2379253) baseStart_2379253 baseEnd_2379253 := by
    simpa [prefixWord, tailWord_2379253, baseEnd_2379253] using wordTrace_append hprefix tailTrace_2379253
  have hstable : (prefixWord ++ tailWord_2379253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379253).length < 2 ^ (prefixWord ++ tailWord_2379253).sum := by decide
  have hdescent : baseEnd_2379253 < baseStart_2379253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379272 : List Nat := [2, 1, 3, 2, 1, 1, 3, 1, 1, 4, 4]
def baseStart_2379272 : Nat := 118140960795 + 2379272 * 2 ^ 59
def prefixEnd_2379272 : Nat := 4983230072969 + 3 ^ 40 * 2379272 * 2
def baseEnd_2379272 : Nat := 1221710143784320321057933

theorem tailTrace_2379272 : CollatzResearch.WordTrace tailWord_2379272 prefixEnd_2379272 1221710143784320321057933 := by
  unfold tailWord_2379272
  simp only [CollatzResearch.WordTrace]
  refine ⟨43389589518155683075874035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57852786024207577434498713 43389589518155683075874035)
  ·
    refine ⟨65084384277233524613811053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43389589518155683075874035 65084384277233524613811053)
    ·
      refine ⟨24406644103962571730179145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65084384277233524613811053 24406644103962571730179145)
      ·
        refine ⟨18304983077971928797634359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24406644103962571730179145 18304983077971928797634359)
        ·
          refine ⟨27457474616957893196451539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18304983077971928797634359 27457474616957893196451539)
          ·
            refine ⟨41186211925436839794677309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27457474616957893196451539 41186211925436839794677309)
            ·
              refine ⟨15444829472038814923003991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41186211925436839794677309 15444829472038814923003991)
              ·
                refine ⟨23167244208058222384505987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15444829472038814923003991 23167244208058222384505987)
                ·
                  refine ⟨34750866312087333576758981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23167244208058222384505987 34750866312087333576758981)
                  ·
                    refine ⟨6515787433516375045642309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34750866312087333576758981 6515787433516375045642309)
                    ·
                      refine ⟨1221710143784320321057933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6515787433516375045642309 1221710143784320321057933)
                      ·
                        rfl

theorem cell23_2379272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_2379272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2379272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2379272 prefixEnd_2379272 := by exact prefixLift 2379272
  have htrace : WordTrace (prefixWord ++ tailWord_2379272) baseStart_2379272 baseEnd_2379272 := by
    simpa [prefixWord, tailWord_2379272, baseEnd_2379272] using wordTrace_append hprefix tailTrace_2379272
  have hstable : (prefixWord ++ tailWord_2379272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379272).length < 2 ^ (prefixWord ++ tailWord_2379272).sum := by decide
  have hdescent : baseEnd_2379272 < baseStart_2379272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379310 : List Nat := [4, 1, 3, 1, 2, 1, 3, 2, 2, 2, 2]
def baseStart_2379310 : Nat := 118140960795 + 2379310 * 2 ^ 59
def prefixEnd_2379310 : Nat := 4983230072969 + 3 ^ 40 * 2379310 * 2
def baseEnd_2379310 : Nat := 1221729656049191172382759

theorem tailTrace_2379310 : CollatzResearch.WordTrace tailWord_2379310 prefixEnd_2379310 1221729656049191172382759 := by
  unfold tailWord_2379310
  simp only [CollatzResearch.WordTrace]
  refine ⟨10847570626271712330203923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57853710006782465761087589 10847570626271712330203923)
  ·
    refine ⟨16271355939407568495305885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10847570626271712330203923 16271355939407568495305885)
    ·
      refine ⟨6101758477277838185739707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16271355939407568495305885 6101758477277838185739707)
      ·
        refine ⟨9152637715916757278609561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6101758477277838185739707 9152637715916757278609561)
        ·
          refine ⟨6864478286937567958957171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9152637715916757278609561 6864478286937567958957171)
          ·
            refine ⟨10296717430406351938435757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6864478286937567958957171 10296717430406351938435757)
            ·
              refine ⟨3861269036402381976913409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10296717430406351938435757 3861269036402381976913409)
              ·
                refine ⟨2895951777301786482685057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3861269036402381976913409 2895951777301786482685057)
                ·
                  refine ⟨2171963832976339862013793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2895951777301786482685057 2171963832976339862013793)
                  ·
                    refine ⟨1628972874732254896510345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2171963832976339862013793 1628972874732254896510345)
                    ·
                      refine ⟨1221729656049191172382759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1628972874732254896510345 1221729656049191172382759)
                      ·
                        rfl

theorem cell23_2379310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_2379310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2379310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2379310 prefixEnd_2379310 := by exact prefixLift 2379310
  have htrace : WordTrace (prefixWord ++ tailWord_2379310) baseStart_2379310 baseEnd_2379310 := by
    simpa [prefixWord, tailWord_2379310, baseEnd_2379310] using wordTrace_append hprefix tailTrace_2379310
  have hstable : (prefixWord ++ tailWord_2379310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379310).length < 2 ^ (prefixWord ++ tailWord_2379310).sum := by decide
  have hdescent : baseEnd_2379310 < baseStart_2379310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379312 : List Nat := [2, 1, 1, 1, 2, 3, 1, 3, 4, 5]
def baseStart_2379312 : Nat := 118140960795 + 2379312 * 2 ^ 59
def prefixEnd_2379312 : Nat := 4983230072969 + 3 ^ 40 * 2379312 * 2
def baseEnd_2379312 : Nat := 407243561003500054852583

theorem tailTrace_2379312 : CollatzResearch.WordTrace tailWord_2379312 prefixEnd_2379312 407243561003500054852583 := by
  unfold tailWord_2379312
  simp only [CollatzResearch.WordTrace]
  refine ⟨43390318978083226491602095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57853758637444301988802793 43390318978083226491602095)
  ·
    refine ⟨65085478467124839737403143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43390318978083226491602095 65085478467124839737403143)
    ·
      refine ⟨97628217700687259606104715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65085478467124839737403143 97628217700687259606104715)
      ·
        refine ⟨146442326551030889409157073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97628217700687259606104715 146442326551030889409157073)
        ·
          refine ⟨109831744913273167056867805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146442326551030889409157073 109831744913273167056867805)
          ·
            refine ⟨41186904342477437646325427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109831744913273167056867805 41186904342477437646325427)
            ·
              refine ⟨61780356513716156469488141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41186904342477437646325427 61780356513716156469488141)
              ·
                refine ⟨23167633692643558676058053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61780356513716156469488141 23167633692643558676058053)
                ·
                  refine ⟨4343931317370667251760885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23167633692643558676058053 4343931317370667251760885)
                  ·
                    refine ⟨407243561003500054852583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4343931317370667251760885 407243561003500054852583)
                    ·
                      rfl

theorem cell23_2379312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 4, 5].length) (baseStart_2379312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2379312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2379312 prefixEnd_2379312 := by exact prefixLift 2379312
  have htrace : WordTrace (prefixWord ++ tailWord_2379312) baseStart_2379312 baseEnd_2379312 := by
    simpa [prefixWord, tailWord_2379312, baseEnd_2379312] using wordTrace_append hprefix tailTrace_2379312
  have hstable : (prefixWord ++ tailWord_2379312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379312).length < 2 ^ (prefixWord ++ tailWord_2379312).sum := by decide
  have hdescent : baseEnd_2379312 < baseStart_2379312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379322 : List Nat := [3, 1, 1, 1, 3, 2, 2, 1, 1, 1, 7]
def baseStart_2379322 : Nat := 118140960795 + 2379322 * 2 ^ 59
def prefixEnd_2379322 : Nat := 4983230072969 + 3 ^ 40 * 2379322 * 2
def baseEnd_2379322 : Nat := 1221735817817045125432703

theorem tailTrace_2379322 : CollatzResearch.WordTrace tailWord_2379322 prefixEnd_2379322 1221735817817045125432703 := by
  unfold tailWord_2379322
  simp only [CollatzResearch.WordTrace]
  refine ⟨21695250671532556172767055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57854001790753483127378813 21695250671532556172767055)
  ·
    refine ⟨32542876007298834259150583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21695250671532556172767055 32542876007298834259150583)
    ·
      refine ⟨48814314010948251388725875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32542876007298834259150583 48814314010948251388725875)
      ·
        refine ⟨73221471016422377083088813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48814314010948251388725875 73221471016422377083088813)
        ·
          refine ⟨27458051631158391406158305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73221471016422377083088813 27458051631158391406158305)
          ·
            refine ⟨20593538723368793554618729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27458051631158391406158305 20593538723368793554618729)
            ·
              refine ⟨15445154042526595165964047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20593538723368793554618729 15445154042526595165964047)
              ·
                refine ⟨23167731063789892748946071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15445154042526595165964047 23167731063789892748946071)
                ·
                  refine ⟨34751596595684839123419107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23167731063789892748946071 34751596595684839123419107)
                  ·
                    refine ⟨52127394893527258685128661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34751596595684839123419107 52127394893527258685128661)
                    ·
                      refine ⟨1221735817817045125432703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 52127394893527258685128661 1221735817817045125432703)
                      ·
                        rfl

theorem cell23_2379322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 1, 1, 7].length) (baseStart_2379322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2379322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2379322 prefixEnd_2379322 := by exact prefixLift 2379322
  have htrace : WordTrace (prefixWord ++ tailWord_2379322) baseStart_2379322 baseEnd_2379322 := by
    simpa [prefixWord, tailWord_2379322, baseEnd_2379322] using wordTrace_append hprefix tailTrace_2379322
  have hstable : (prefixWord ++ tailWord_2379322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379322).length < 2 ^ (prefixWord ++ tailWord_2379322).sum := by decide
  have hdescent : baseEnd_2379322 < baseStart_2379322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379342 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 1, 10]
def baseStart_2379342 : Nat := 118140960795 + 2379342 * 2 ^ 59
def prefixEnd_2379342 : Nat := 4983230072969 + 3 ^ 40 * 2379342 * 2
def baseEnd_2379342 : Nat := 407248695810045015727537

theorem tailTrace_2379342 : CollatzResearch.WordTrace tailWord_2379342 prefixEnd_2379342 407248695810045015727537 := by
  unfold tailWord_2379342
  simp only [CollatzResearch.WordTrace]
  refine ⟨10847716518257221013349535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57854488097371845404530853 10847716518257221013349535)
  ·
    refine ⟨16271574777385831520024303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10847716518257221013349535 16271574777385831520024303)
    ·
      refine ⟨24407362166078747280036455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16271574777385831520024303 24407362166078747280036455)
      ·
        refine ⟨36611043249118120920054683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24407362166078747280036455 36611043249118120920054683)
        ·
          refine ⟨54916564873677181380082025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36611043249118120920054683 54916564873677181380082025)
          ·
            refine ⟨41187423655257886035061519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54916564873677181380082025 41187423655257886035061519)
            ·
              refine ⟨61781135482886829052592279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41187423655257886035061519 61781135482886829052592279)
              ·
                refine ⟨92671703224330243578888419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61781135482886829052592279 92671703224330243578888419)
                ·
                  refine ⟨139007554836495365368332629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92671703224330243578888419 139007554836495365368332629)
                  ·
                    refine ⟨407248695810045015727537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 139007554836495365368332629 407248695810045015727537)
                    ·
                      rfl

theorem cell23_2379342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 1, 10].length) (baseStart_2379342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2379342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2379342 prefixEnd_2379342 := by exact prefixLift 2379342
  have htrace : WordTrace (prefixWord ++ tailWord_2379342) baseStart_2379342 baseEnd_2379342 := by
    simpa [prefixWord, tailWord_2379342, baseEnd_2379342] using wordTrace_append hprefix tailTrace_2379342
  have hstable : (prefixWord ++ tailWord_2379342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379342).length < 2 ^ (prefixWord ++ tailWord_2379342).sum := by decide
  have hdescent : baseEnd_2379342 < baseStart_2379342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379349 : List Nat := [1, 3, 2, 2, 1, 1, 1, 5, 2, 1, 4]
def baseStart_2379349 : Nat := 118140960795 + 2379349 * 2 ^ 59
def prefixEnd_2379349 : Nat := 4983230072969 + 3 ^ 40 * 2379349 * 2
def baseEnd_2379349 : Nat := 1221749681794716519795079

theorem tailTrace_2379349 : CollatzResearch.WordTrace tailWord_2379349 prefixEnd_2379349 1221749681794716519795079 := by
  unfold tailWord_2379349
  simp only [CollatzResearch.WordTrace]
  refine ⟨86781987457032408302301101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57854658304688272201534067 86781987457032408302301101)
  ·
    refine ⟨32543245296387153113362913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86781987457032408302301101 32543245296387153113362913)
    ·
      refine ⟨24407433972290364835022185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32543245296387153113362913 24407433972290364835022185)
      ·
        refine ⟨18305575479217773626266639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24407433972290364835022185 18305575479217773626266639)
        ·
          refine ⟨27458363218826660439399959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18305575479217773626266639 27458363218826660439399959)
          ·
            refine ⟨41187544828239990659099939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27458363218826660439399959 41187544828239990659099939)
            ·
              refine ⟨61781317242359985988649909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41187544828239990659099939 61781317242359985988649909)
              ·
                refine ⟨5791998491471248686435929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61781317242359985988649909 5791998491471248686435929)
                ·
                  refine ⟨4343998868603436514826947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5791998491471248686435929 4343998868603436514826947)
                  ·
                    refine ⟨6515998302905154772240421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4343998868603436514826947 6515998302905154772240421)
                    ·
                      refine ⟨1221749681794716519795079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6515998302905154772240421 1221749681794716519795079)
                      ·
                        rfl

theorem cell23_2379349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_2379349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2379349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2379349 prefixEnd_2379349 := by exact prefixLift 2379349
  have htrace : WordTrace (prefixWord ++ tailWord_2379349) baseStart_2379349 baseEnd_2379349 := by
    simpa [prefixWord, tailWord_2379349, baseEnd_2379349] using wordTrace_append hprefix tailTrace_2379349
  have hstable : (prefixWord ++ tailWord_2379349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379349).length < 2 ^ (prefixWord ++ tailWord_2379349).sum := by decide
  have hdescent : baseEnd_2379349 < baseStart_2379349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379352 : List Nat := [2, 1, 2, 2, 1, 2, 1, 2, 2, 3, 5]
def baseStart_2379352 : Nat := 118140960795 + 2379352 * 2 ^ 59
def prefixEnd_2379352 : Nat := 4983230072969 + 3 ^ 40 * 2379352 * 2
def baseEnd_2379352 : Nat := 1221751222236680008057565

theorem tailTrace_2379352 : CollatzResearch.WordTrace tailWord_2379352 prefixEnd_2379352 1221751222236680008057565 := by
  unfold tailWord_2379352
  simp only [CollatzResearch.WordTrace]
  refine ⟨43391048438010769907330155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57854731250681026543106873 43391048438010769907330155)
  ·
    refine ⟨65086572657016154860995233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43391048438010769907330155 65086572657016154860995233)
    ·
      refine ⟨48814929492762116145746425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65086572657016154860995233 48814929492762116145746425)
      ·
        refine ⟨36611197119571587109309819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48814929492762116145746425 36611197119571587109309819)
        ·
          refine ⟨54916795679357380663964729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36611197119571587109309819 54916795679357380663964729)
          ·
            refine ⟨41187596759518035497973547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54916795679357380663964729 41187596759518035497973547)
            ·
              refine ⟨61781395139277053246960321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41187596759518035497973547 61781395139277053246960321)
              ·
                refine ⟨46336046354457789935220241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61781395139277053246960321 46336046354457789935220241)
                ·
                  refine ⟨34752034765843342451415181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46336046354457789935220241 34752034765843342451415181)
                  ·
                    refine ⟨13032013037191253419280693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34752034765843342451415181 13032013037191253419280693)
                    ·
                      refine ⟨1221751222236680008057565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13032013037191253419280693 1221751222236680008057565)
                      ·
                        rfl

theorem cell23_2379352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_2379352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2379352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2379352 prefixEnd_2379352 := by exact prefixLift 2379352
  have htrace : WordTrace (prefixWord ++ tailWord_2379352) baseStart_2379352 baseEnd_2379352 := by
    simpa [prefixWord, tailWord_2379352, baseEnd_2379352] using wordTrace_append hprefix tailTrace_2379352
  have hstable : (prefixWord ++ tailWord_2379352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379352).length < 2 ^ (prefixWord ++ tailWord_2379352).sum := by decide
  have hdescent : baseEnd_2379352 < baseStart_2379352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379369 : List Nat := [1, 2, 1, 1, 1, 4, 3, 1, 4, 2, 3]
def baseStart_2379369 : Nat := 118140960795 + 2379369 * 2 ^ 59
def prefixEnd_2379369 : Nat := 4983230072969 + 3 ^ 40 * 2379369 * 2
def baseEnd_2379369 : Nat := 1221759951407806441544987

theorem tailTrace_2379369 : CollatzResearch.WordTrace tailWord_2379369 prefixEnd_2379369 1221759951407806441544987 := by
  unfold tailWord_2379369
  simp only [CollatzResearch.WordTrace]
  refine ⟨86782716916959951718029161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57855144611306634478686107 86782716916959951718029161)
  ·
    refine ⟨65087037687719963788521871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86782716916959951718029161 65087037687719963788521871)
    ·
      refine ⟨97630556531579945682782807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65087037687719963788521871 97630556531579945682782807)
      ·
        refine ⟨146445834797369918524174211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97630556531579945682782807 146445834797369918524174211)
        ·
          refine ⟨219668752196054877786261317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146445834797369918524174211 219668752196054877786261317)
          ·
            refine ⟨41187891036760289584923997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 219668752196054877786261317 41187891036760289584923997)
            ·
              refine ⟨15445459138785108594346499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41187891036760289584923997 15445459138785108594346499)
              ·
                refine ⟨23168188708177662891519749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15445459138785108594346499 23168188708177662891519749)
                ·
                  refine ⟨4344035382783311792159953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23168188708177662891519749 4344035382783311792159953)
                  ·
                    refine ⟨3258026537087483844119965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4344035382783311792159953 3258026537087483844119965)
                    ·
                      refine ⟨1221759951407806441544987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3258026537087483844119965 1221759951407806441544987)
                      ·
                        rfl

theorem cell23_2379369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 4, 2, 3].length) (baseStart_2379369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2379369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2379369 prefixEnd_2379369 := by exact prefixLift 2379369
  have htrace : WordTrace (prefixWord ++ tailWord_2379369) baseStart_2379369 baseEnd_2379369 := by
    simpa [prefixWord, tailWord_2379369, baseEnd_2379369] using wordTrace_append hprefix tailTrace_2379369
  have hstable : (prefixWord ++ tailWord_2379369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379369).length < 2 ^ (prefixWord ++ tailWord_2379369).sum := by decide
  have hdescent : baseEnd_2379369 < baseStart_2379369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379376 : List Nat := [2, 1, 1, 1, 6, 1, 3, 1, 3, 4]
def baseStart_2379376 : Nat := 118140960795 + 2379376 * 2 ^ 59
def prefixEnd_2379376 : Nat := 4983230072969 + 3 ^ 40 * 2379376 * 2
def baseEnd_2379376 : Nat := 407254515257462638052485

theorem tailTrace_2379376 : CollatzResearch.WordTrace tailWord_2379376 prefixEnd_2379376 407254515257462638052485 := by
  unfold tailWord_2379376
  simp only [CollatzResearch.WordTrace]
  refine ⟨43391486113967295956766991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57855314818623061275689321 43391486113967295956766991)
  ·
    refine ⟨65087229170950943935150487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43391486113967295956766991 65087229170950943935150487)
    ·
      refine ⟨97630843756426415902725731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65087229170950943935150487 97630843756426415902725731)
      ·
        refine ⟨146446265634639623854088597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97630843756426415902725731 146446265634639623854088597)
        ·
          refine ⟨6864668701623732368160403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 146446265634639623854088597 6864668701623732368160403)
          ·
            refine ⟨10297003052435598552240605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6864668701623732368160403 10297003052435598552240605)
            ·
              refine ⟨3861376144663349457090227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10297003052435598552240605 3861376144663349457090227)
              ·
                refine ⟨5792064216995024185635341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3861376144663349457090227 5792064216995024185635341)
                ·
                  refine ⟨2172024081373134069613253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5792064216995024185635341 2172024081373134069613253)
                  ·
                    refine ⟨407254515257462638052485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2172024081373134069613253 407254515257462638052485)
                    ·
                      rfl

theorem cell23_2379376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 3, 4].length) (baseStart_2379376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2379376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2379376 prefixEnd_2379376 := by exact prefixLift 2379376
  have htrace : WordTrace (prefixWord ++ tailWord_2379376) baseStart_2379376 baseEnd_2379376 := by
    simpa [prefixWord, tailWord_2379376, baseEnd_2379376] using wordTrace_append hprefix tailTrace_2379376
  have hstable : (prefixWord ++ tailWord_2379376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379376).length < 2 ^ (prefixWord ++ tailWord_2379376).sum := by decide
  have hdescent : baseEnd_2379376 < baseStart_2379376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379423 : List Nat := [1, 1, 2, 7, 1, 1, 2, 2, 6]
def baseStart_2379423 : Nat := 118140960795 + 2379423 * 2 ^ 59
def prefixEnd_2379423 : Nat := 4983230072969 + 3 ^ 40 * 2379423 * 2
def baseEnd_2379423 : Nat := 135754186595905470029971

theorem tailTrace_2379423 : CollatzResearch.WordTrace tailWord_2379423 prefixEnd_2379423 135754186595905470029971 := by
  unfold tailWord_2379423
  simp only [CollatzResearch.WordTrace]
  refine ⟨86784686458764318940494923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57856457639176212626996615 86784686458764318940494923)
  ·
    refine ⟨130177029688146478410742385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86784686458764318940494923 130177029688146478410742385)
    ·
      refine ⟨97632772266109858808056789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130177029688146478410742385 97632772266109858808056789)
      ·
        refine ⟨2288268099986949815813831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 97632772266109858808056789 2288268099986949815813831)
        ·
          refine ⟨3432402149980424723720747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2288268099986949815813831 3432402149980424723720747)
          ·
            refine ⟨5148603224970637085581121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3432402149980424723720747 5148603224970637085581121)
            ·
              refine ⟨3861452418727977814185841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5148603224970637085581121 3861452418727977814185841)
              ·
                refine ⟨2896089314045983360639381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3861452418727977814185841 2896089314045983360639381)
                ·
                  refine ⟨135754186595905470029971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2896089314045983360639381 135754186595905470029971)
                  ·
                    rfl

theorem cell23_2379423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 2, 6].length) (baseStart_2379423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2379423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2379423 prefixEnd_2379423 := by exact prefixLift 2379423
  have htrace : WordTrace (prefixWord ++ tailWord_2379423) baseStart_2379423 baseEnd_2379423 := by
    simpa [prefixWord, tailWord_2379423, baseEnd_2379423] using wordTrace_append hprefix tailTrace_2379423
  have hstable : (prefixWord ++ tailWord_2379423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379423).length < 2 ^ (prefixWord ++ tailWord_2379423).sum := by decide
  have hdescent : baseEnd_2379423 < baseStart_2379423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379439 : List Nat := [1, 1, 2, 1, 2, 4, 1, 1, 5, 1, 4]
def baseStart_2379439 : Nat := 118140960795 + 2379439 * 2 ^ 59
def prefixEnd_2379439 : Nat := 4983230072969 + 3 ^ 40 * 2379439 * 2
def baseEnd_2379439 : Nat := 1221795895053621167669665

theorem tailTrace_2379439 : CollatzResearch.WordTrace tailWord_2379439 prefixEnd_2379439 1221795895053621167669665 := by
  unfold tailWord_2379439
  simp only [CollatzResearch.WordTrace]
  refine ⟨86785270026706353673077371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57856846684470902448718247 86785270026706353673077371)
  ·
    refine ⟨130177905040059530509616057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86785270026706353673077371 130177905040059530509616057)
    ·
      refine ⟨97633428780044647882212043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130177905040059530509616057 97633428780044647882212043)
      ·
        refine ⟨146450143170066971823318065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97633428780044647882212043 146450143170066971823318065)
        ·
          refine ⟨109837607377550228867488549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146450143170066971823318065 109837607377550228867488549)
          ·
            refine ⟨20594551383290667912654103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109837607377550228867488549 20594551383290667912654103)
            ·
              refine ⟨30891827074936001868981155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20594551383290667912654103 30891827074936001868981155)
              ·
                refine ⟨46337740612404002803471733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30891827074936001868981155 46337740612404002803471733)
                ·
                  refine ⟨4344163182412875262825475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46337740612404002803471733 4344163182412875262825475)
                  ·
                    refine ⟨6516244773619312894238213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4344163182412875262825475 6516244773619312894238213)
                    ·
                      refine ⟨1221795895053621167669665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6516244773619312894238213 1221795895053621167669665)
                      ·
                        rfl

theorem cell23_2379439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 5, 1, 4].length) (baseStart_2379439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2379439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2379439 prefixEnd_2379439 := by exact prefixLift 2379439
  have htrace : WordTrace (prefixWord ++ tailWord_2379439) baseStart_2379439 baseEnd_2379439 := by
    simpa [prefixWord, tailWord_2379439, baseEnd_2379439] using wordTrace_append hprefix tailTrace_2379439
  have hstable : (prefixWord ++ tailWord_2379439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379439).length < 2 ^ (prefixWord ++ tailWord_2379439).sum := by decide
  have hdescent : baseEnd_2379439 < baseStart_2379439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379449 : List Nat := [1, 2, 1, 4, 1, 1, 3, 3, 1, 6]
def baseStart_2379449 : Nat := 118140960795 + 2379449 * 2 ^ 59
def prefixEnd_2379449 : Nat := 4983230072969 + 3 ^ 40 * 2379449 * 2
def baseEnd_2379449 : Nat := 407267009953388709514873

theorem tailTrace_2379449 : CollatzResearch.WordTrace tailWord_2379449 prefixEnd_2379449 407267009953388709514873 := by
  unfold tailWord_2379449
  simp only [CollatzResearch.WordTrace]
  refine ⟨86785634756670125380941401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57857089837780083587294267 86785634756670125380941401)
  ·
    refine ⟨65089226067502594035706051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86785634756670125380941401 65089226067502594035706051)
    ·
      refine ⟨97633839101253891053559077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65089226067502594035706051 97633839101253891053559077)
      ·
        refine ⟨18306344831485104572542327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97633839101253891053559077 18306344831485104572542327)
        ·
          refine ⟨27459517247227656858813491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18306344831485104572542327 27459517247227656858813491)
          ·
            refine ⟨41189275870841485288220237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27459517247227656858813491 41189275870841485288220237)
            ·
              refine ⟨15445978451565556983082589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41189275870841485288220237 15445978451565556983082589)
              ·
                refine ⟨5792241919337083868655971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15445978451565556983082589 5792241919337083868655971)
                ·
                  refine ⟨8688362879005625802983957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5792241919337083868655971 8688362879005625802983957)
                  ·
                    refine ⟨407267009953388709514873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8688362879005625802983957 407267009953388709514873)
                    ·
                      rfl

theorem cell23_2379449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 6].length) (baseStart_2379449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2379449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2379449 prefixEnd_2379449 := by exact prefixLift 2379449
  have htrace : WordTrace (prefixWord ++ tailWord_2379449) baseStart_2379449 baseEnd_2379449 := by
    simpa [prefixWord, tailWord_2379449, baseEnd_2379449] using wordTrace_append hprefix tailTrace_2379449
  have hstable : (prefixWord ++ tailWord_2379449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379449).length < 2 ^ (prefixWord ++ tailWord_2379449).sum := by decide
  have hdescent : baseEnd_2379449 < baseStart_2379449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379456 : List Nat := [2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 4]
def baseStart_2379456 : Nat := 118140960795 + 2379456 * 2 ^ 59
def prefixEnd_2379456 : Nat := 4983230072969 + 3 ^ 40 * 2379456 * 2
def baseEnd_2379456 : Nat := 1221804624224747601157087

theorem tailTrace_2379456 : CollatzResearch.WordTrace tailWord_2379456 prefixEnd_2379456 1221804624224747601157087 := by
  unfold tailWord_2379456
  simp only [CollatzResearch.WordTrace]
  refine ⟨43392945033822382788223111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57857260045096510384297481 43392945033822382788223111)
  ·
    refine ⟨65089417550733574182334667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43392945033822382788223111 65089417550733574182334667)
    ·
      refine ⟨97634126326100361273502001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65089417550733574182334667 97634126326100361273502001)
      ·
        refine ⟨73225594744575270955126501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97634126326100361273502001 73225594744575270955126501)
        ·
          refine ⟨13729799014607863304086219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73225594744575270955126501 13729799014607863304086219)
          ·
            refine ⟨20594698521911794956129329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13729799014607863304086219 20594698521911794956129329)
            ·
              refine ⟨15446023891433846217096997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20594698521911794956129329 15446023891433846217096997)
              ·
                refine ⟨2896129479643846165705687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15446023891433846217096997 2896129479643846165705687)
                ·
                  refine ⟨4344194219465769248558531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2896129479643846165705687 4344194219465769248558531)
                  ·
                    refine ⟨6516291329198653872837797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4344194219465769248558531 6516291329198653872837797)
                    ·
                      refine ⟨1221804624224747601157087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6516291329198653872837797 1221804624224747601157087)
                      ·
                        rfl

theorem cell23_2379456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 4].length) (baseStart_2379456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2379456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2379456 prefixEnd_2379456 := by exact prefixLift 2379456
  have htrace : WordTrace (prefixWord ++ tailWord_2379456) baseStart_2379456 baseEnd_2379456 := by
    simpa [prefixWord, tailWord_2379456, baseEnd_2379456] using wordTrace_append hprefix tailTrace_2379456
  have hstable : (prefixWord ++ tailWord_2379456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379456).length < 2 ^ (prefixWord ++ tailWord_2379456).sum := by decide
  have hdescent : baseEnd_2379456 < baseStart_2379456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379473 : List Nat := [1, 2, 2, 1, 2, 4, 4, 1, 1, 1, 4]
def baseStart_2379473 : Nat := 118140960795 + 2379473 * 2 ^ 59
def prefixEnd_2379473 : Nat := 4983230072969 + 3 ^ 40 * 2379473 * 2
def baseEnd_2379473 : Nat := 1221813353395874034644509

theorem tailTrace_2379473 : CollatzResearch.WordTrace tailWord_2379473 prefixEnd_2379473 1221813353395874034644509 := by
  unfold tailWord_2379473
  simp only [CollatzResearch.WordTrace]
  refine ⟨86786510108583177479815073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57857673405722118319876715 86786510108583177479815073)
  ·
    refine ⟨65089882581437383109861305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86786510108583177479815073 65089882581437383109861305)
    ·
      refine ⟨48817411936078037332395979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65089882581437383109861305 48817411936078037332395979)
      ·
        refine ⟨73226117904117055998593969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48817411936078037332395979 73226117904117055998593969)
        ·
          refine ⟨54919588428087791998945477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73226117904117055998593969 54919588428087791998945477)
          ·
            refine ⟨10297422830266460999802277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54919588428087791998945477 10297422830266460999802277)
            ·
              refine ⟨1930766780674961437462927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10297422830266460999802277 1930766780674961437462927)
              ·
                refine ⟨2896150171012442156194391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1930766780674961437462927 2896150171012442156194391)
                ·
                  refine ⟨4344225256518663234291587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2896150171012442156194391 4344225256518663234291587)
                  ·
                    refine ⟨6516337884777994851437381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4344225256518663234291587 6516337884777994851437381)
                    ·
                      refine ⟨1221813353395874034644509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6516337884777994851437381 1221813353395874034644509)
                      ·
                        rfl

theorem cell23_2379473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 1, 1, 1, 4].length) (baseStart_2379473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2379473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2379473 prefixEnd_2379473 := by exact prefixLift 2379473
  have htrace : WordTrace (prefixWord ++ tailWord_2379473) baseStart_2379473 baseEnd_2379473 := by
    simpa [prefixWord, tailWord_2379473, baseEnd_2379473] using wordTrace_append hprefix tailTrace_2379473
  have hstable : (prefixWord ++ tailWord_2379473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379473).length < 2 ^ (prefixWord ++ tailWord_2379473).sum := by decide
  have hdescent : baseEnd_2379473 < baseStart_2379473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379510 : List Nat := [5, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3]
def baseStart_2379510 : Nat := 118140960795 + 2379510 * 2 ^ 59
def prefixEnd_2379510 : Nat := 4983230072969 + 3 ^ 40 * 2379510 * 2
def baseEnd_2379510 : Nat := 1221832352180090389881839

theorem tailTrace_2379510 : CollatzResearch.WordTrace tailWord_2379510 prefixEnd_2379510 1221832352180090389881839 := by
  unfold tailWord_2379510
  simp only [CollatzResearch.WordTrace]
  refine ⟨5424241225590570799931999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57858573072966088532607989 5424241225590570799931999)
  ·
    refine ⟨8136361838385856199897999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5424241225590570799931999 8136361838385856199897999)
    ·
      refine ⟨12204542757578784299846999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8136361838385856199897999 12204542757578784299846999)
      ·
        refine ⟨18306814136368176449770499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12204542757578784299846999 18306814136368176449770499)
        ·
          refine ⟨27460221204552264674655749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18306814136368176449770499 27460221204552264674655749)
          ·
            refine ⟨5148791475853549626497953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27460221204552264674655749 5148791475853549626497953)
            ·
              refine ⟨3861593606890162219873465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5148791475853549626497953 3861593606890162219873465)
              ·
                refine ⟨2896195205167621664905099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3861593606890162219873465 2896195205167621664905099)
                ·
                  refine ⟨4344292807751432497357649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2896195205167621664905099 4344292807751432497357649)
                  ·
                    refine ⟨3258219605813574373018237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4344292807751432497357649 3258219605813574373018237)
                    ·
                      refine ⟨1221832352180090389881839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3258219605813574373018237 1221832352180090389881839)
                      ·
                        rfl

theorem cell23_2379510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_2379510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2379510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2379510 prefixEnd_2379510 := by exact prefixLift 2379510
  have htrace : WordTrace (prefixWord ++ tailWord_2379510) baseStart_2379510 baseEnd_2379510 := by
    simpa [prefixWord, tailWord_2379510, baseEnd_2379510] using wordTrace_append hprefix tailTrace_2379510
  have hstable : (prefixWord ++ tailWord_2379510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379510).length < 2 ^ (prefixWord ++ tailWord_2379510).sum := by decide
  have hdescent : baseEnd_2379510 < baseStart_2379510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379519 : List Nat := [1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 5]
def baseStart_2379519 : Nat := 118140960795 + 2379519 * 2 ^ 59
def prefixEnd_2379519 : Nat := 4983230072969 + 3 ^ 40 * 2379519 * 2
def baseEnd_2379519 : Nat := 1221836973505980854669297

theorem tailTrace_2379519 : CollatzResearch.WordTrace tailWord_2379519 prefixEnd_2379519 1221836973505980854669297 := by
  unfold tailWord_2379519
  simp only [CollatzResearch.WordTrace]
  refine ⟨86788187866416527335989611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57858791910944351557326407 86788187866416527335989611)
  ·
    refine ⟨130182281799624791003984417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86788187866416527335989611 130182281799624791003984417)
    ·
      refine ⟨97636711349718593252988313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130182281799624791003984417 97636711349718593252988313)
      ·
        refine ⟨73227533512288944939741235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97636711349718593252988313 73227533512288944939741235)
        ·
          refine ⟨109841300268433417409611853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73227533512288944939741235 109841300268433417409611853)
          ·
            refine ⟨41190487600662531528604445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109841300268433417409611853 41190487600662531528604445)
            ·
              refine ⟨15446432850248449323226667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41190487600662531528604445 15446432850248449323226667)
              ·
                refine ⟨23169649275372673984840001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15446432850248449323226667 23169649275372673984840001)
                ·
                  refine ⟨17377236956529505488630001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23169649275372673984840001 17377236956529505488630001)
                  ·
                    refine ⟨13032927717397129116472501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17377236956529505488630001 13032927717397129116472501)
                    ·
                      refine ⟨1221836973505980854669297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13032927717397129116472501 1221836973505980854669297)
                      ·
                        rfl

theorem cell23_2379519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 5].length) (baseStart_2379519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2379519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2379519 prefixEnd_2379519 := by exact prefixLift 2379519
  have htrace : WordTrace (prefixWord ++ tailWord_2379519) baseStart_2379519 baseEnd_2379519 := by
    simpa [prefixWord, tailWord_2379519, baseEnd_2379519] using wordTrace_append hprefix tailTrace_2379519
  have hstable : (prefixWord ++ tailWord_2379519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379519).length < 2 ^ (prefixWord ++ tailWord_2379519).sum := by decide
  have hdescent : baseEnd_2379519 < baseStart_2379519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379524 : List Nat := [2, 3, 2, 2, 1, 4, 1, 3, 1, 2, 2]
def baseStart_2379524 : Nat := 118140960795 + 2379524 * 2 ^ 59
def prefixEnd_2379524 : Nat := 4983230072969 + 3 ^ 40 * 2379524 * 2
def baseEnd_2379524 : Nat := 1221839540909253335106775

theorem tailTrace_2379524 : CollatzResearch.WordTrace tailWord_2379524 prefixEnd_2379524 1221839540909253335106775 := by
  unfold tailWord_2379524
  simp only [CollatzResearch.WordTrace]
  refine ⟨43394185115699206594960813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57858913487598942126614417 43394185115699206594960813)
  ·
    refine ⟨16272819418387202473110305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43394185115699206594960813 16272819418387202473110305)
    ·
      refine ⟨12204614563790401854832729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16272819418387202473110305 12204614563790401854832729)
      ·
        refine ⟨9153460922842801391124547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12204614563790401854832729 9153460922842801391124547)
        ·
          refine ⟨13730191384264202086686821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9153460922842801391124547 13730191384264202086686821)
          ·
            refine ⟨2574410884549537891253779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13730191384264202086686821 2574410884549537891253779)
            ·
              refine ⟨3861616326824306836880669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2574410884549537891253779 3861616326824306836880669)
              ·
                refine ⟨1448106122559115063830251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3861616326824306836880669 1448106122559115063830251)
                ·
                  refine ⟨2172159183838672595745377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1448106122559115063830251 2172159183838672595745377)
                  ·
                    refine ⟨1629119387879004446809033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2172159183838672595745377 1629119387879004446809033)
                    ·
                      refine ⟨1221839540909253335106775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1629119387879004446809033 1221839540909253335106775)
                      ·
                        rfl

theorem cell23_2379524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_2379524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2379524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2379524 prefixEnd_2379524 := by exact prefixLift 2379524
  have htrace : WordTrace (prefixWord ++ tailWord_2379524) baseStart_2379524 baseEnd_2379524 := by
    simpa [prefixWord, tailWord_2379524, baseEnd_2379524] using wordTrace_append hprefix tailTrace_2379524
  have hstable : (prefixWord ++ tailWord_2379524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379524).length < 2 ^ (prefixWord ++ tailWord_2379524).sum := by decide
  have hdescent : baseEnd_2379524 < baseStart_2379524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379529 : List Nat := [1, 2, 1, 1, 3, 2, 1, 2, 1, 5, 4]
def baseStart_2379529 : Nat := 118140960795 + 2379529 * 2 ^ 59
def prefixEnd_2379529 : Nat := 4983230072969 + 3 ^ 40 * 2379529 * 2
def baseEnd_2379529 : Nat := 1221842108312525815544251

theorem tailTrace_2379529 : CollatzResearch.WordTrace tailWord_2379529 prefixEnd_2379529 1221842108312525815544251 := by
  unfold tailWord_2379529
  simp only [CollatzResearch.WordTrace]
  refine ⟨86788552596380299043853641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57859035064253532695902427 86788552596380299043853641)
  ·
    refine ⟨65091414447285224282890231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86788552596380299043853641 65091414447285224282890231)
    ·
      refine ⟨97637121670927836424335347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65091414447285224282890231 97637121670927836424335347)
      ·
        refine ⟨146455682506391754636503021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97637121670927836424335347 146455682506391754636503021)
        ·
          refine ⟨54920880939896907988688633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146455682506391754636503021 54920880939896907988688633)
          ·
            refine ⟨41190660704922680991516475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54920880939896907988688633 41190660704922680991516475)
            ·
              refine ⟨61785991057384021487274713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41190660704922680991516475 61785991057384021487274713)
              ·
                refine ⟨46339493293038016115456035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61785991057384021487274713 46339493293038016115456035)
                ·
                  refine ⟨69509239939557024173184053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46339493293038016115456035 69509239939557024173184053)
                  ·
                    refine ⟨6516491244333471016236005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 69509239939557024173184053 6516491244333471016236005)
                    ·
                      refine ⟨1221842108312525815544251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6516491244333471016236005 1221842108312525815544251)
                      ·
                        rfl

theorem cell23_2379529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 5, 4].length) (baseStart_2379529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2379529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2379529 prefixEnd_2379529 := by exact prefixLift 2379529
  have htrace : WordTrace (prefixWord ++ tailWord_2379529) baseStart_2379529 baseEnd_2379529 := by
    simpa [prefixWord, tailWord_2379529, baseEnd_2379529] using wordTrace_append hprefix tailTrace_2379529
  have hstable : (prefixWord ++ tailWord_2379529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379529).length < 2 ^ (prefixWord ++ tailWord_2379529).sum := by decide
  have hdescent : baseEnd_2379529 < baseStart_2379529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379539 : List Nat := [1, 1, 1, 2, 1, 3, 2, 4, 2, 6]
def baseStart_2379539 : Nat := 118140960795 + 2379539 * 2 ^ 59
def prefixEnd_2379539 : Nat := 4983230072969 + 3 ^ 40 * 2379539 * 2
def baseEnd_2379539 : Nat := 407282414373023592139735

theorem tailTrace_2379539 : CollatzResearch.WordTrace tailWord_2379539 prefixEnd_2379539 407282414373023592139735 := by
  unfold tailWord_2379539
  simp only [CollatzResearch.WordTrace]
  refine ⟨86788917326344070751717671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57859278217562713834478447 86788917326344070751717671)
  ·
    refine ⟨130183375989516106127576507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86788917326344070751717671 130183375989516106127576507)
    ·
      refine ⟨195275063984274159191364761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130183375989516106127576507 195275063984274159191364761)
      ·
        refine ⟨146456297988205619393523571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195275063984274159191364761 146456297988205619393523571)
        ·
          refine ⟨219684446982308429090285357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146456297988205619393523571 219684446982308429090285357)
          ·
            refine ⟨82381667618365660908857009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 219684446982308429090285357 82381667618365660908857009)
            ·
              refine ⟨61786250713774245681642757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82381667618365660908857009 61786250713774245681642757)
              ·
                refine ⟨11584922008832671065308017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61786250713774245681642757 11584922008832671065308017)
                ·
                  refine ⟨8688691506624503298981013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11584922008832671065308017 8688691506624503298981013)
                  ·
                    refine ⟨407282414373023592139735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8688691506624503298981013 407282414373023592139735)
                    ·
                      rfl

theorem cell23_2379539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 6].length) (baseStart_2379539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2379539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2379539 prefixEnd_2379539 := by exact prefixLift 2379539
  have htrace : WordTrace (prefixWord ++ tailWord_2379539) baseStart_2379539 baseEnd_2379539 := by
    simpa [prefixWord, tailWord_2379539, baseEnd_2379539] using wordTrace_append hprefix tailTrace_2379539
  have hstable : (prefixWord ++ tailWord_2379539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379539).length < 2 ^ (prefixWord ++ tailWord_2379539).sum := by decide
  have hdescent : baseEnd_2379539 < baseStart_2379539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379557 : List Nat := [1, 3, 1, 2, 3, 4, 2, 1, 2, 1, 3]
def baseStart_2379557 : Nat := 118140960795 + 2379557 * 2 ^ 59
def prefixEnd_2379557 : Nat := 4983230072969 + 3 ^ 40 * 2379557 * 2
def baseEnd_2379557 : Nat := 1221856485770851705994123

theorem tailTrace_2379557 : CollatzResearch.WordTrace tailWord_2379557 prefixEnd_2379557 1221856485770851705994123 := by
  unfold tailWord_2379557
  simp only [CollatzResearch.WordTrace]
  refine ⟨86789573840278859825872925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57859715893519239883915283 86789573840278859825872925)
  ·
    refine ⟨32546090190104572434702347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86789573840278859825872925 32546090190104572434702347)
    ·
      refine ⟨48819135285156858652053521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32546090190104572434702347 48819135285156858652053521)
      ·
        refine ⟨36614351463867643989040141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48819135285156858652053521 36614351463867643989040141)
        ·
          refine ⟨13730381798950366495890053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36614351463867643989040141 13730381798950366495890053)
          ·
            refine ⟨2574446587303193717979385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13730381798950366495890053 2574446587303193717979385)
            ·
              refine ⟨1930834940477395288484539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2574446587303193717979385 1930834940477395288484539)
              ·
                refine ⟨2896252410716092932726809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1930834940477395288484539 2896252410716092932726809)
                ·
                  refine ⟨2172189308037069699545107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2896252410716092932726809 2172189308037069699545107)
                  ·
                    refine ⟨3258283962055604549317661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2172189308037069699545107 3258283962055604549317661)
                    ·
                      refine ⟨1221856485770851705994123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3258283962055604549317661 1221856485770851705994123)
                      ·
                        rfl

theorem cell23_2379557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 1, 2, 1, 3].length) (baseStart_2379557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2379557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2379557 prefixEnd_2379557 := by exact prefixLift 2379557
  have htrace : WordTrace (prefixWord ++ tailWord_2379557) baseStart_2379557 baseEnd_2379557 := by
    simpa [prefixWord, tailWord_2379557, baseEnd_2379557] using wordTrace_append hprefix tailTrace_2379557
  have hstable : (prefixWord ++ tailWord_2379557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379557).length < 2 ^ (prefixWord ++ tailWord_2379557).sum := by decide
  have hdescent : baseEnd_2379557 < baseStart_2379557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379623 : List Nat := [1, 1, 5, 1, 2, 1, 1, 2, 2, 5, 2]
def baseStart_2379623 : Nat := 118140960795 + 2379623 * 2 ^ 59
def prefixEnd_2379623 : Nat := 4983230072969 + 3 ^ 40 * 2379623 * 2
def baseEnd_2379623 : Nat := 1221890375494048447768819

theorem tailTrace_2379623 : CollatzResearch.WordTrace tailWord_2379623 prefixEnd_2379623 1221890375494048447768819 := by
  unfold tailWord_2379623
  simp only [CollatzResearch.WordTrace]
  refine ⟨86791981058039753097775523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57861320705359835398517015 86791981058039753097775523)
  ·
    refine ⟨130187971587059629646663285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86791981058039753097775523 130187971587059629646663285)
    ·
      refine ⟨12205122336286840279374683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 130187971587059629646663285 12205122336286840279374683)
      ·
        refine ⟨18307683504430260419062025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12205122336286840279374683 18307683504430260419062025)
        ·
          refine ⟨13730762628322695314296519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18307683504430260419062025 13730762628322695314296519)
          ·
            refine ⟨20596143942484042971444779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13730762628322695314296519 20596143942484042971444779)
            ·
              refine ⟨30894215913726064457167169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20596143942484042971444779 30894215913726064457167169)
              ·
                refine ⟨23170661935294548342875377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30894215913726064457167169 23170661935294548342875377)
                ·
                  refine ⟨17377996451470911257156533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23170661935294548342875377 17377996451470911257156533)
                  ·
                    refine ⟨1629187167325397930358425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17377996451470911257156533 1629187167325397930358425)
                    ·
                      refine ⟨1221890375494048447768819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1629187167325397930358425 1221890375494048447768819)
                      ·
                        rfl

theorem cell23_2379623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 5, 2].length) (baseStart_2379623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2379623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2379623 prefixEnd_2379623 := by exact prefixLift 2379623
  have htrace : WordTrace (prefixWord ++ tailWord_2379623) baseStart_2379623 baseEnd_2379623 := by
    simpa [prefixWord, tailWord_2379623, baseEnd_2379623] using wordTrace_append hprefix tailTrace_2379623
  have hstable : (prefixWord ++ tailWord_2379623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379623).length < 2 ^ (prefixWord ++ tailWord_2379623).sum := by decide
  have hdescent : baseEnd_2379623 < baseStart_2379623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379653 : List Nat := [1, 3, 1, 1, 3, 2, 1, 1, 4, 4, 2]
def baseStart_2379653 : Nat := 118140960795 + 2379653 * 2 ^ 59
def prefixEnd_2379653 : Nat := 4983230072969 + 3 ^ 40 * 2379653 * 2
def baseEnd_2379653 : Nat := 1221905779913683330393681

theorem tailTrace_2379653 : CollatzResearch.WordTrace tailWord_2379653 prefixEnd_2379653 1221905779913683330393681 := by
  unfold tailWord_2379653
  simp only [CollatzResearch.WordTrace]
  refine ⟨86793075247931068221367613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57862050165287378814245075 86793075247931068221367613)
  ·
    refine ⟨32547403217974150583012855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86793075247931068221367613 32547403217974150583012855)
    ·
      refine ⟨48821104826961225874519283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32547403217974150583012855 48821104826961225874519283)
      ·
        refine ⟨73231657240441838811778925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48821104826961225874519283 73231657240441838811778925)
        ·
          refine ⟨27461871465165689554417097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73231657240441838811778925 27461871465165689554417097)
          ·
            refine ⟨20596403598874267165812823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27461871465165689554417097 20596403598874267165812823)
            ·
              refine ⟨30894605398311400748719235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20596403598874267165812823 30894605398311400748719235)
              ·
                refine ⟨46341908097467101123078853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30894605398311400748719235 46341908097467101123078853)
                ·
                  refine ⟨8689107768275081460577285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46341908097467101123078853 8689107768275081460577285)
                  ·
                    refine ⟨1629207706551577773858241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8689107768275081460577285 1629207706551577773858241)
                    ·
                      refine ⟨1221905779913683330393681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1629207706551577773858241 1221905779913683330393681)
                      ·
                        rfl

theorem cell23_2379653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 4, 2].length) (baseStart_2379653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2379653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2379653 prefixEnd_2379653 := by exact prefixLift 2379653
  have htrace : WordTrace (prefixWord ++ tailWord_2379653) baseStart_2379653 baseEnd_2379653 := by
    simpa [prefixWord, tailWord_2379653, baseEnd_2379653] using wordTrace_append hprefix tailTrace_2379653
  have hstable : (prefixWord ++ tailWord_2379653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379653).length < 2 ^ (prefixWord ++ tailWord_2379653).sum := by decide
  have hdescent : baseEnd_2379653 < baseStart_2379653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379697 : List Nat := [1, 2, 2, 4, 2, 1, 3, 3, 1, 4]
def baseStart_2379697 : Nat := 118140960795 + 2379697 * 2 ^ 59
def prefixEnd_2379697 : Nat := 4983230072969 + 3 ^ 40 * 2379697 * 2
def baseEnd_2379697 : Nat := 407309457687493719414493

theorem tailTrace_2379697 : CollatzResearch.WordTrace tailWord_2379697 prefixEnd_2379697 407309457687493719414493 := by
  unfold tailWord_2379697
  simp only [CollatzResearch.WordTrace]
  refine ⟨86794680059771663735969345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57863120039847775823979563 86794680059771663735969345)
  ·
    refine ⟨65096010044828747801977009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86794680059771663735969345 65096010044828747801977009)
    ·
      refine ⟨48822007533621560851482757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65096010044828747801977009 48822007533621560851482757)
      ·
        refine ⟨9154126412554042659653017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48822007533621560851482757 9154126412554042659653017)
        ·
          refine ⟨6865594809415531994739763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9154126412554042659653017 6865594809415531994739763)
          ·
            refine ⟨10298392214123297992109645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6865594809415531994739763 10298392214123297992109645)
            ·
              refine ⟨3861897080296236747041117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10298392214123297992109645 3861897080296236747041117)
              ·
                refine ⟨1448211405111088780140419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3861897080296236747041117 1448211405111088780140419)
                ·
                  refine ⟨2172317107666633170210629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1448211405111088780140419 2172317107666633170210629)
                  ·
                    refine ⟨407309457687493719414493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2172317107666633170210629 407309457687493719414493)
                    ·
                      rfl

theorem cell23_2379697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 3, 1, 4].length) (baseStart_2379697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2379697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2379697 prefixEnd_2379697 := by exact prefixLift 2379697
  have htrace : WordTrace (prefixWord ++ tailWord_2379697) baseStart_2379697 baseEnd_2379697 := by
    simpa [prefixWord, tailWord_2379697, baseEnd_2379697] using wordTrace_append hprefix tailTrace_2379697
  have hstable : (prefixWord ++ tailWord_2379697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379697).length < 2 ^ (prefixWord ++ tailWord_2379697).sum := by decide
  have hdescent : baseEnd_2379697 < baseStart_2379697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379747 : List Nat := [1, 1, 1, 6, 1, 3, 2, 1, 2, 3, 2]
def baseStart_2379747 : Nat := 118140960795 + 2379747 * 2 ^ 59
def prefixEnd_2379747 : Nat := 4983230072969 + 3 ^ 40 * 2379747 * 2
def baseEnd_2379747 : Nat := 1221954047095205962618249

theorem tailTrace_2379747 : CollatzResearch.WordTrace tailWord_2379747 prefixEnd_2379747 1221954047095205962618249 := by
  unfold tailWord_2379747
  simp only [CollatzResearch.WordTrace]
  refine ⟨86796503709590522275289495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57864335806393681516859663 86796503709590522275289495)
  ·
    refine ⟨130194755564385783412934243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86796503709590522275289495 130194755564385783412934243)
    ·
      refine ⟨195292133346578675119401365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130194755564385783412934243 195292133346578675119401365)
      ·
        refine ⟨9154318750620875396221939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 195292133346578675119401365 9154318750620875396221939)
        ·
          refine ⟨13731478125931313094332909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9154318750620875396221939 13731478125931313094332909)
          ·
            refine ⟨5149304297224242410374841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13731478125931313094332909 5149304297224242410374841)
            ·
              refine ⟨3861978222918181807781131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5149304297224242410374841 3861978222918181807781131)
              ·
                refine ⟨5792967334377272711671697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3861978222918181807781131 5792967334377272711671697)
                ·
                  refine ⟨4344725500782954533753773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5792967334377272711671697 4344725500782954533753773)
                  ·
                    refine ⟨1629272062793607950157665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4344725500782954533753773 1629272062793607950157665)
                    ·
                      refine ⟨1221954047095205962618249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1629272062793607950157665 1221954047095205962618249)
                      ·
                        rfl

theorem cell23_2379747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_2379747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2379747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2379747 prefixEnd_2379747 := by exact prefixLift 2379747
  have htrace : WordTrace (prefixWord ++ tailWord_2379747) baseStart_2379747 baseEnd_2379747 := by
    simpa [prefixWord, tailWord_2379747, baseEnd_2379747] using wordTrace_append hprefix tailTrace_2379747
  have hstable : (prefixWord ++ tailWord_2379747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379747).length < 2 ^ (prefixWord ++ tailWord_2379747).sum := by decide
  have hdescent : baseEnd_2379747 < baseStart_2379747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379776 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 7]
def baseStart_2379776 : Nat := 118140960795 + 2379776 * 2 ^ 59
def prefixEnd_2379776 : Nat := 4983230072969 + 3 ^ 40 * 2379776 * 2
def baseEnd_2379776 : Nat := 1221968938034186349155615

theorem tailTrace_2379776 : CollatzResearch.WordTrace tailWord_2379776 prefixEnd_2379776 1221968938034186349155615 := by
  unfold tailWord_2379776
  simp only [CollatzResearch.WordTrace]
  refine ⟨43398780713242730114047591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57865040950990306818730121 43398780713242730114047591)
  ·
    refine ⟨65098171069864095171071387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43398780713242730114047591 65098171069864095171071387)
    ·
      refine ⟨97647256604796142756607081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65098171069864095171071387 97647256604796142756607081)
      ·
        refine ⟨73235442453597107067455311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97647256604796142756607081 73235442453597107067455311)
        ·
          refine ⟨109853163680395660601182967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73235442453597107067455311 109853163680395660601182967)
          ·
            refine ⟨164779745520593490901774451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109853163680395660601182967 164779745520593490901774451)
            ·
              refine ⟨247169618280890236352661677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164779745520593490901774451 247169618280890236352661677)
              ·
                refine ⟨92688606855333838632248129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 247169618280890236352661677 92688606855333838632248129)
                ·
                  refine ⟨69516455141500378974186097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92688606855333838632248129 69516455141500378974186097)
                  ·
                    refine ⟨52137341356125284230639573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 69516455141500378974186097 52137341356125284230639573)
                    ·
                      refine ⟨1221968938034186349155615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 52137341356125284230639573 1221968938034186349155615)
                      ·
                        rfl

theorem cell23_2379776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 7].length) (baseStart_2379776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2379776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2379776 prefixEnd_2379776 := by exact prefixLift 2379776
  have htrace : WordTrace (prefixWord ++ tailWord_2379776) baseStart_2379776 baseEnd_2379776 := by
    simpa [prefixWord, tailWord_2379776, baseEnd_2379776] using wordTrace_append hprefix tailTrace_2379776
  have hstable : (prefixWord ++ tailWord_2379776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379776).length < 2 ^ (prefixWord ++ tailWord_2379776).sum := by decide
  have hdescent : baseEnd_2379776 < baseStart_2379776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379777 : List Nat := [1, 2, 4, 1, 2, 1, 2, 3, 3, 2, 2]
def baseStart_2379777 : Nat := 118140960795 + 2379777 * 2 ^ 59
def prefixEnd_2379777 : Nat := 4983230072969 + 3 ^ 40 * 2379777 * 2
def baseEnd_2379777 : Nat := 1221969451514840845243111

theorem tailTrace_2379777 : CollatzResearch.WordTrace tailWord_2379777 prefixEnd_2379777 1221969451514840845243111 := by
  unfold tailWord_2379777
  simp only [CollatzResearch.WordTrace]
  refine ⟨86797597899481837398881585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57865065266321224932587723 86797597899481837398881585)
  ·
    refine ⟨65098198424611378049161189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86797597899481837398881585 65098198424611378049161189)
    ·
      refine ⟨12205912204614633384217723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65098198424611378049161189 12205912204614633384217723)
      ·
        refine ⟨18308868306921950076326585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12205912204614633384217723 18308868306921950076326585)
        ·
          refine ⟨13731651230191462557244939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18308868306921950076326585 13731651230191462557244939)
          ·
            refine ⟨20597476845287193835867409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13731651230191462557244939 20597476845287193835867409)
            ·
              refine ⟨15448107633965395376900557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20597476845287193835867409 15448107633965395376900557)
              ·
                refine ⟨5793040362737023266337709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15448107633965395376900557 5793040362737023266337709)
                ·
                  refine ⟨2172390136026383724876641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5793040362737023266337709 2172390136026383724876641)
                  ·
                    refine ⟨1629292602019787793657481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2172390136026383724876641 1629292602019787793657481)
                    ·
                      refine ⟨1221969451514840845243111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1629292602019787793657481 1221969451514840845243111)
                      ·
                        rfl

theorem cell23_2379777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 3, 2, 2].length) (baseStart_2379777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2379777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2379777 prefixEnd_2379777 := by exact prefixLift 2379777
  have htrace : WordTrace (prefixWord ++ tailWord_2379777) baseStart_2379777 baseEnd_2379777 := by
    simpa [prefixWord, tailWord_2379777, baseEnd_2379777] using wordTrace_append hprefix tailTrace_2379777
  have hstable : (prefixWord ++ tailWord_2379777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379777).length < 2 ^ (prefixWord ++ tailWord_2379777).sum := by decide
  have hdescent : baseEnd_2379777 < baseStart_2379777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379783 : List Nat := [1, 1, 4, 3, 1, 2, 3, 8]
def baseStart_2379783 : Nat := 118140960795 + 2379783 * 2 ^ 59
def prefixEnd_2379783 : Nat := 4983230072969 + 3 ^ 40 * 2379783 * 2
def baseEnd_2379783 : Nat := 45258241940695104509929

theorem tailTrace_2379783 : CollatzResearch.WordTrace tailWord_2379783 prefixEnd_2379783 45258241940695104509929 := by
  unfold tailWord_2379783
  simp only [CollatzResearch.WordTrace]
  refine ⟨86797816737460100423600003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57865211158306733615733335 86797816737460100423600003)
  ·
    refine ⟨130196725106190150635400005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86797816737460100423600003 130196725106190150635400005)
    ·
      refine ⟨24411885957410653244137501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130196725106190150635400005 24411885957410653244137501)
      ·
        refine ⟨9154457234028994966551563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24411885957410653244137501 9154457234028994966551563)
        ·
          refine ⟨13731685851043492449827345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9154457234028994966551563 13731685851043492449827345)
          ·
            refine ⟨10298764388282619337370509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13731685851043492449827345 10298764388282619337370509)
            ·
              refine ⟨3862036645605982251513941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10298764388282619337370509 3862036645605982251513941)
              ·
                refine ⟨45258241940695104509929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3862036645605982251513941 45258241940695104509929)
                ·
                  rfl

theorem cell23_2379783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 8].length) (baseStart_2379783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2379783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2379783 prefixEnd_2379783 := by exact prefixLift 2379783
  have htrace : WordTrace (prefixWord ++ tailWord_2379783) baseStart_2379783 baseEnd_2379783 := by
    simpa [prefixWord, tailWord_2379783, baseEnd_2379783] using wordTrace_append hprefix tailTrace_2379783
  have hstable : (prefixWord ++ tailWord_2379783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379783).length < 2 ^ (prefixWord ++ tailWord_2379783).sum := by decide
  have hdescent : baseEnd_2379783 < baseStart_2379783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379790 : List Nat := [4, 1, 1, 2, 2, 1, 4, 1, 1, 2, 4]
def baseStart_2379790 : Nat := 118140960795 + 2379790 * 2 ^ 59
def prefixEnd_2379790 : Nat := 4983230072969 + 3 ^ 40 * 2379790 * 2
def baseEnd_2379790 : Nat := 1221976126763349294380551

theorem tailTrace_2379790 : CollatzResearch.WordTrace tailWord_2379790 prefixEnd_2379790 1221976126763349294380551 := by
  unfold tailWord_2379790
  simp only [CollatzResearch.WordTrace]
  refine ⟨10849759006054342577388103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57865381365623160412736549 10849759006054342577388103)
  ·
    refine ⟨16274638509081513866082155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10849759006054342577388103 16274638509081513866082155)
    ·
      refine ⟨24411957763622270799123233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16274638509081513866082155 24411957763622270799123233)
      ·
        refine ⟨18308968322716703099342425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24411957763622270799123233 18308968322716703099342425)
        ·
          refine ⟨13731726242037527324506819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18308968322716703099342425 13731726242037527324506819)
          ·
            refine ⟨20597589363056290986760229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13731726242037527324506819 20597589363056290986760229)
            ·
              refine ⟨3862048005573054560017543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20597589363056290986760229 3862048005573054560017543)
              ·
                refine ⟨5793072008359581840026315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3862048005573054560017543 5793072008359581840026315)
                ·
                  refine ⟨8689608012539372760039473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5793072008359581840026315 8689608012539372760039473)
                  ·
                    refine ⟨6517206009404529570029605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8689608012539372760039473 6517206009404529570029605)
                    ·
                      refine ⟨1221976126763349294380551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6517206009404529570029605 1221976126763349294380551)
                      ·
                        rfl

theorem cell23_2379790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_2379790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2379790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2379790 prefixEnd_2379790 := by exact prefixLift 2379790
  have htrace : WordTrace (prefixWord ++ tailWord_2379790) baseStart_2379790 baseEnd_2379790 := by
    simpa [prefixWord, tailWord_2379790, baseEnd_2379790] using wordTrace_append hprefix tailTrace_2379790
  have hstable : (prefixWord ++ tailWord_2379790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379790).length < 2 ^ (prefixWord ++ tailWord_2379790).sum := by decide
  have hdescent : baseEnd_2379790 < baseStart_2379790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379810 : List Nat := [3, 3, 1, 1, 1, 2, 1, 4, 1, 3, 3]
def baseStart_2379810 : Nat := 118140960795 + 2379810 * 2 ^ 59
def prefixEnd_2379810 : Nat := 4983230072969 + 3 ^ 40 * 2379810 * 2
def baseEnd_2379810 : Nat := 1221986396376439216130459

theorem tailTrace_2379810 : CollatzResearch.WordTrace tailWord_2379810 prefixEnd_2379810 1221986396376439216130459 := by
  unfold tailWord_2379810
  simp only [CollatzResearch.WordTrace]
  refine ⟨21699700377090571008708221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57865867672241522689888589 21699700377090571008708221)
  ·
    refine ⟨8137387641408964128265583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21699700377090571008708221 8137387641408964128265583)
    ·
      refine ⟨12206081462113446192398375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8137387641408964128265583 12206081462113446192398375)
      ·
        refine ⟨18309122193170169288597563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12206081462113446192398375 18309122193170169288597563)
        ·
          refine ⟨27463683289755253932896345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18309122193170169288597563 27463683289755253932896345)
          ·
            refine ⟨20597762467316440449672259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27463683289755253932896345 20597762467316440449672259)
            ·
              refine ⟨30896643700974660674508389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20597762467316440449672259 30896643700974660674508389)
              ·
                refine ⟨5793120693932748876470323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30896643700974660674508389 5793120693932748876470323)
                ·
                  refine ⟨8689681040899123314705485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5793120693932748876470323 8689681040899123314705485)
                  ·
                    refine ⟨3258630390337171243014557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8689681040899123314705485 3258630390337171243014557)
                    ·
                      refine ⟨1221986396376439216130459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3258630390337171243014557 1221986396376439216130459)
                      ·
                        rfl

theorem cell23_2379810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_2379810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2379810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2379810 prefixEnd_2379810 := by exact prefixLift 2379810
  have htrace : WordTrace (prefixWord ++ tailWord_2379810) baseStart_2379810 baseEnd_2379810 := by
    simpa [prefixWord, tailWord_2379810, baseEnd_2379810] using wordTrace_append hprefix tailTrace_2379810
  have hstable : (prefixWord ++ tailWord_2379810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379810).length < 2 ^ (prefixWord ++ tailWord_2379810).sum := by decide
  have hdescent : baseEnd_2379810 < baseStart_2379810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379820 : List Nat := [2, 2, 1, 1, 1, 2, 2, 2, 5, 3, 2]
def baseStart_2379820 : Nat := 118140960795 + 2379820 * 2 ^ 59
def prefixEnd_2379820 : Nat := 4983230072969 + 3 ^ 40 * 2379820 * 2
def baseEnd_2379820 : Nat := 1221991531182984177005413

theorem tailTrace_2379820 : CollatzResearch.WordTrace tailWord_2379820 prefixEnd_2379820 1221991531182984177005413 := by
  unfold tailWord_2379820
  simp only [CollatzResearch.WordTrace]
  refine ⟨43399583119163027871348457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57866110825550703828464609 43399583119163027871348457)
  ·
    refine ⟨32549687339372270903511343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43399583119163027871348457 32549687339372270903511343)
    ·
      refine ⟨48824531009058406355267015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32549687339372270903511343 48824531009058406355267015)
      ·
        refine ⟨73236796513587609532900523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48824531009058406355267015 73236796513587609532900523)
        ·
          refine ⟨109855194770381414299350785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73236796513587609532900523 109855194770381414299350785)
          ·
            refine ⟨82391396077786060724513089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109855194770381414299350785 82391396077786060724513089)
            ·
              refine ⟨61793547058339545543384817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82391396077786060724513089 61793547058339545543384817)
              ·
                refine ⟨46345160293754659157538613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61793547058339545543384817 46345160293754659157538613)
                ·
                  refine ⟨4344858777539499296019245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46345160293754659157538613 4344858777539499296019245)
                  ·
                    refine ⟨1629322041577312236007217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4344858777539499296019245 1629322041577312236007217)
                    ·
                      refine ⟨1221991531182984177005413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1629322041577312236007217 1221991531182984177005413)
                      ·
                        rfl

theorem cell23_2379820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 3, 2].length) (baseStart_2379820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2379820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2379820 prefixEnd_2379820 := by exact prefixLift 2379820
  have htrace : WordTrace (prefixWord ++ tailWord_2379820) baseStart_2379820 baseEnd_2379820 := by
    simpa [prefixWord, tailWord_2379820, baseEnd_2379820] using wordTrace_append hprefix tailTrace_2379820
  have hstable : (prefixWord ++ tailWord_2379820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379820).length < 2 ^ (prefixWord ++ tailWord_2379820).sum := by decide
  have hdescent : baseEnd_2379820 < baseStart_2379820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379827 : List Nat := [1, 1, 1, 2, 4, 1, 5, 2, 2, 1, 3]
def baseStart_2379827 : Nat := 118140960795 + 2379827 * 2 ^ 59
def prefixEnd_2379827 : Nat := 4983230072969 + 3 ^ 40 * 2379827 * 2
def baseEnd_2379827 : Nat := 1221995125547565649617881

theorem tailTrace_2379827 : CollatzResearch.WordTrace tailWord_2379827 prefixEnd_2379827 1221995125547565649617881 := by
  unfold tailWord_2379827
  simp only [CollatzResearch.WordTrace]
  refine ⟨86799421549300695938201735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57866281032867130625467823 86799421549300695938201735)
  ·
    refine ⟨130199132323951043907302603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86799421549300695938201735 130199132323951043907302603)
    ·
      refine ⟨195298698485926565860953905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130199132323951043907302603 195298698485926565860953905)
      ·
        refine ⟨146474023864444924395715429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195298698485926565860953905 146474023864444924395715429)
        ·
          refine ⟨27463879474583423324196643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 146474023864444924395715429 27463879474583423324196643)
          ·
            refine ⟨41195819211875134986294965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27463879474583423324196643 41195819211875134986294965)
            ·
              refine ⟨3862108051113293904965153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41195819211875134986294965 3862108051113293904965153)
              ·
                refine ⟨2896581038334970428723865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3862108051113293904965153 2896581038334970428723865)
                ·
                  refine ⟨2172435778751227821542899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2896581038334970428723865 2172435778751227821542899)
                  ·
                    refine ⟨3258653668126841732314349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2172435778751227821542899 3258653668126841732314349)
                    ·
                      refine ⟨1221995125547565649617881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3258653668126841732314349 1221995125547565649617881)
                      ·
                        rfl

theorem cell23_2379827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 2, 2, 1, 3].length) (baseStart_2379827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2379827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2379827 prefixEnd_2379827 := by exact prefixLift 2379827
  have htrace : WordTrace (prefixWord ++ tailWord_2379827) baseStart_2379827 baseEnd_2379827 := by
    simpa [prefixWord, tailWord_2379827, baseEnd_2379827] using wordTrace_append hprefix tailTrace_2379827
  have hstable : (prefixWord ++ tailWord_2379827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379827).length < 2 ^ (prefixWord ++ tailWord_2379827).sum := by decide
  have hdescent : baseEnd_2379827 < baseStart_2379827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379854 : List Nat := [4, 1, 1, 1, 1, 5, 2, 2, 1, 3, 2]
def baseStart_2379854 : Nat := 118140960795 + 2379854 * 2 ^ 59
def prefixEnd_2379854 : Nat := 4983230072969 + 3 ^ 40 * 2379854 * 2
def baseEnd_2379854 : Nat := 1222008989525237043980257

theorem tailTrace_2379854 : CollatzResearch.WordTrace tailWord_2379854 prefixEnd_2379854 1222008989525237043980257 := by
  unfold tailWord_2379854
  simp only [CollatzResearch.WordTrace]
  refine ⟨10850050790025359943679327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57866937546801919699623077 10850050790025359943679327)
  ·
    refine ⟨16275076185038039915518991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10850050790025359943679327 16275076185038039915518991)
    ·
      refine ⟨24412614277557059873278487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16275076185038039915518991 24412614277557059873278487)
      ·
        refine ⟨36618921416335589809917731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24412614277557059873278487 36618921416335589809917731)
        ·
          refine ⟨54928382124503384714876597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36618921416335589809917731 54928382124503384714876597)
          ·
            refine ⟨5149535824172192317019681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54928382124503384714876597 5149535824172192317019681)
            ·
              refine ⟨3862151868129144237764761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5149535824172192317019681 3862151868129144237764761)
              ·
                refine ⟨2896613901096858178323571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3862151868129144237764761 2896613901096858178323571)
                ·
                  refine ⟨4344920851645287267485357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2896613901096858178323571 4344920851645287267485357)
                  ·
                    refine ⟨1629345319366982725307009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4344920851645287267485357 1629345319366982725307009)
                    ·
                      refine ⟨1222008989525237043980257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1629345319366982725307009 1222008989525237043980257)
                      ·
                        rfl

theorem cell23_2379854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 2, 1, 3, 2].length) (baseStart_2379854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2379854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2379854 prefixEnd_2379854 := by exact prefixLift 2379854
  have htrace : WordTrace (prefixWord ++ tailWord_2379854) baseStart_2379854 baseEnd_2379854 := by
    simpa [prefixWord, tailWord_2379854, baseEnd_2379854] using wordTrace_append hprefix tailTrace_2379854
  have hstable : (prefixWord ++ tailWord_2379854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379854).length < 2 ^ (prefixWord ++ tailWord_2379854).sum := by decide
  have hdescent : baseEnd_2379854 < baseStart_2379854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379863 : List Nat := [1, 1, 3, 2, 2, 1, 2, 2, 1, 4, 4]
def baseStart_2379863 : Nat := 118140960795 + 2379863 * 2 ^ 59
def prefixEnd_2379863 : Nat := 4983230072969 + 3 ^ 40 * 2379863 * 2
def baseEnd_2379863 : Nat := 1222013610851127508767715

theorem tailTrace_2379863 : CollatzResearch.WordTrace tailWord_2379863 prefixEnd_2379863 1222013610851127508767715 := by
  unfold tailWord_2379863
  simp only [CollatzResearch.WordTrace]
  refine ⟨86800734577170274086512243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57867156384780182724341495 86800734577170274086512243)
  ·
    refine ⟨130201101865755411129768365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86800734577170274086512243 130201101865755411129768365)
    ·
      refine ⟨48825413199658279173663137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130201101865755411129768365 48825413199658279173663137)
      ·
        refine ⟨36619059899743709380247353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48825413199658279173663137 36619059899743709380247353)
        ·
          refine ⟨27464294924807782035185515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36619059899743709380247353 27464294924807782035185515)
          ·
            refine ⟨41196442387211673052778273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27464294924807782035185515 41196442387211673052778273)
            ·
              refine ⟨30897331790408754789583705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41196442387211673052778273 30897331790408754789583705)
              ·
                refine ⟨23172998842806566092187779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30897331790408754789583705 23172998842806566092187779)
                ·
                  refine ⟨34759498264209849138281669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23172998842806566092187779 34759498264209849138281669)
                  ·
                    refine ⟨6517405924539346713427813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34759498264209849138281669 6517405924539346713427813)
                    ·
                      refine ⟨1222013610851127508767715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6517405924539346713427813 1222013610851127508767715)
                      ·
                        rfl

theorem cell23_2379863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_2379863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2379863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2379863 prefixEnd_2379863 := by exact prefixLift 2379863
  have htrace : WordTrace (prefixWord ++ tailWord_2379863) baseStart_2379863 baseEnd_2379863 := by
    simpa [prefixWord, tailWord_2379863, baseEnd_2379863] using wordTrace_append hprefix tailTrace_2379863
  have hstable : (prefixWord ++ tailWord_2379863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379863).length < 2 ^ (prefixWord ++ tailWord_2379863).sum := by decide
  have hdescent : baseEnd_2379863 < baseStart_2379863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379890 : List Nat := [3, 2, 1, 2, 2, 2, 3, 1, 7]
def baseStart_2379890 : Nat := 118140960795 + 2379890 * 2 ^ 59
def prefixEnd_2379890 : Nat := 4983230072969 + 3 ^ 40 * 2379890 * 2
def baseEnd_2379890 : Nat := 135780830536533211458899

theorem tailTrace_2379890 : CollatzResearch.WordTrace tailWord_2379890 prefixEnd_2379890 135780830536533211458899 := by
  unfold tailWord_2379890
  simp only [CollatzResearch.WordTrace]
  refine ⟨21700429837018114424436281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57867812898714971798496749 21700429837018114424436281)
  ·
    refine ⟨16275322377763585818327211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21700429837018114424436281 16275322377763585818327211)
    ·
      refine ⟨24412983566645378727490817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16275322377763585818327211 24412983566645378727490817)
      ·
        refine ⟨18309737674984034045618113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24412983566645378727490817 18309737674984034045618113)
        ·
          refine ⟨13732303256238025534213585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18309737674984034045618113 13732303256238025534213585)
          ·
            refine ⟨10299227442178519150660189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13732303256238025534213585 10299227442178519150660189)
            ·
              refine ⟨3862210290816944681497571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10299227442178519150660189 3862210290816944681497571)
              ·
                refine ⟨5793315436225417022246357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3862210290816944681497571 5793315436225417022246357)
                ·
                  refine ⟨135780830536533211458899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5793315436225417022246357 135780830536533211458899)
                  ·
                    rfl

theorem cell23_2379890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 7].length) (baseStart_2379890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2379890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2379890 prefixEnd_2379890 := by exact prefixLift 2379890
  have htrace : WordTrace (prefixWord ++ tailWord_2379890) baseStart_2379890 baseEnd_2379890 := by
    simpa [prefixWord, tailWord_2379890, baseEnd_2379890] using wordTrace_append hprefix tailTrace_2379890
  have hstable : (prefixWord ++ tailWord_2379890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379890).length < 2 ^ (prefixWord ++ tailWord_2379890).sum := by decide
  have hdescent : baseEnd_2379890 < baseStart_2379890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379901 : List Nat := [1, 4, 1, 1, 3, 2, 4, 1, 2, 2, 2]
def baseStart_2379901 : Nat := 118140960795 + 2379901 * 2 ^ 59
def prefixEnd_2379901 : Nat := 4983230072969 + 3 ^ 40 * 2379901 * 2
def baseEnd_2379901 : Nat := 1222033123115998360092541

theorem tailTrace_2379901 : CollatzResearch.WordTrace tailWord_2379901 prefixEnd_2379901 1222033123115998360092541 := by
  unfold tailWord_2379901
  simp only [CollatzResearch.WordTrace]
  refine ⟨86802120551032606576395557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57868080367355071050930371 86802120551032606576395557)
  ·
    refine ⟨16275397603318613733074167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86802120551032606576395557 16275397603318613733074167)
    ·
      refine ⟨24413096404977920599611251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16275397603318613733074167 24413096404977920599611251)
      ·
        refine ⟨36619644607466880899416877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24413096404977920599611251 36619644607466880899416877)
        ·
          refine ⟨13732366727800080337281329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36619644607466880899416877 13732366727800080337281329)
          ·
            refine ⟨10299275045850060252960997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13732366727800080337281329 10299275045850060252960997)
            ·
              refine ⟨1931114071096886297430187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10299275045850060252960997 1931114071096886297430187)
              ·
                refine ⟨2896671106645329446145281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1931114071096886297430187 2896671106645329446145281)
                ·
                  refine ⟨2172503329983997084608961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2896671106645329446145281 2172503329983997084608961)
                  ·
                    refine ⟨1629377497487997813456721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2172503329983997084608961 1629377497487997813456721)
                    ·
                      refine ⟨1222033123115998360092541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1629377497487997813456721 1222033123115998360092541)
                      ·
                        rfl

theorem cell23_2379901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 1, 2, 2, 2].length) (baseStart_2379901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2379901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2379901 prefixEnd_2379901 := by exact prefixLift 2379901
  have htrace : WordTrace (prefixWord ++ tailWord_2379901) baseStart_2379901 baseEnd_2379901 := by
    simpa [prefixWord, tailWord_2379901, baseEnd_2379901] using wordTrace_append hprefix tailTrace_2379901
  have hstable : (prefixWord ++ tailWord_2379901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379901).length < 2 ^ (prefixWord ++ tailWord_2379901).sum := by decide
  have hdescent : baseEnd_2379901 < baseStart_2379901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379913 : List Nat := [1, 2, 1, 1, 4, 2, 1, 2, 1, 1, 7]
def baseStart_2379913 : Nat := 118140960795 + 2379913 * 2 ^ 59
def prefixEnd_2379913 : Nat := 4983230072969 + 3 ^ 40 * 2379913 * 2
def baseEnd_2379913 : Nat := 1222039284883852313142485

theorem tailTrace_2379913 : CollatzResearch.WordTrace tailWord_2379913 prefixEnd_2379913 1222039284883852313142485 := by
  unfold tailWord_2379913
  simp only [CollatzResearch.WordTrace]
  refine ⟨86802558226989132625832393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57868372151326088417221595 86802558226989132625832393)
  ·
    refine ⟨65101918670241849469374295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86802558226989132625832393 65101918670241849469374295)
    ·
      refine ⟨97652878005362774204061443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65101918670241849469374295 97652878005362774204061443)
      ·
        refine ⟨146479317008044161306092165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97652878005362774204061443 146479317008044161306092165)
        ·
          refine ⟨27464871939008280244892281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 146479317008044161306092165 27464871939008280244892281)
          ·
            refine ⟨20598653954256210183669211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27464871939008280244892281 20598653954256210183669211)
            ·
              refine ⟨30897980931384315275503817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20598653954256210183669211 30897980931384315275503817)
              ·
                refine ⟨23173485698538236456627863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30897980931384315275503817 23173485698538236456627863)
                ·
                  refine ⟨34760228547807354684941795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23173485698538236456627863 34760228547807354684941795)
                  ·
                    refine ⟨52140342821711032027412693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34760228547807354684941795 52140342821711032027412693)
                    ·
                      refine ⟨1222039284883852313142485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 52140342821711032027412693 1222039284883852313142485)
                      ·
                        rfl

theorem cell23_2379913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 1, 7].length) (baseStart_2379913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2379913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2379913 prefixEnd_2379913 := by exact prefixLift 2379913
  have htrace : WordTrace (prefixWord ++ tailWord_2379913) baseStart_2379913 baseEnd_2379913 := by
    simpa [prefixWord, tailWord_2379913, baseEnd_2379913] using wordTrace_append hprefix tailTrace_2379913
  have hstable : (prefixWord ++ tailWord_2379913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379913).length < 2 ^ (prefixWord ++ tailWord_2379913).sum := by decide
  have hdescent : baseEnd_2379913 < baseStart_2379913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379920 : List Nat := [2, 1, 1, 1, 1, 1, 8, 1, 2, 5]
def baseStart_2379920 : Nat := 118140960795 + 2379920 * 2 ^ 59
def prefixEnd_2379920 : Nat := 4983230072969 + 3 ^ 40 * 2379920 * 2
def baseEnd_2379920 : Nat := 407347626416144595251651

theorem tailTrace_2379920 : CollatzResearch.WordTrace tailWord_2379920 prefixEnd_2379920 407347626416144595251651 := by
  unfold tailWord_2379920
  simp only [CollatzResearch.WordTrace]
  refine ⟨43401406768981886410668607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57868542358642515214224809 43401406768981886410668607)
  ·
    refine ⟨65102110153472829616002911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43401406768981886410668607 65102110153472829616002911)
    ·
      refine ⟨97653165230209244424004367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65102110153472829616002911 97653165230209244424004367)
      ·
        refine ⟨146479747845313866636006551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97653165230209244424004367 146479747845313866636006551)
        ·
          refine ⟨219719621767970799954009827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146479747845313866636006551 219719621767970799954009827)
          ·
            refine ⟨329579432651956199931014741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219719621767970799954009827 329579432651956199931014741)
            ·
              refine ⟨3862258976390111717941579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 329579432651956199931014741 3862258976390111717941579)
              ·
                refine ⟨5793388464585167576912369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3862258976390111717941579 5793388464585167576912369)
                ·
                  refine ⟨4345041348438875682684277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5793388464585167576912369 4345041348438875682684277)
                  ·
                    refine ⟨407347626416144595251651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4345041348438875682684277 407347626416144595251651)
                    ·
                      rfl

theorem cell23_2379920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 2, 5].length) (baseStart_2379920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2379920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2379920 prefixEnd_2379920 := by exact prefixLift 2379920
  have htrace : WordTrace (prefixWord ++ tailWord_2379920) baseStart_2379920 baseEnd_2379920 := by
    simpa [prefixWord, tailWord_2379920, baseEnd_2379920] using wordTrace_append hprefix tailTrace_2379920
  have hstable : (prefixWord ++ tailWord_2379920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379920).length < 2 ^ (prefixWord ++ tailWord_2379920).sum := by decide
  have hdescent : baseEnd_2379920 < baseStart_2379920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379960 : List Nat := [2, 1, 2, 1, 2, 1, 4, 2, 1, 4, 3]
def baseStart_2379960 : Nat := 118140960795 + 2379960 * 2 ^ 59
def prefixEnd_2379960 : Nat := 4983230072969 + 3 ^ 40 * 2379960 * 2
def baseEnd_2379960 : Nat := 1222063418474613629254769

theorem tailTrace_2379960 : CollatzResearch.WordTrace tailWord_2379960 prefixEnd_2379960 1222063418474613629254769 := by
  unfold tailWord_2379960
  simp only [CollatzResearch.WordTrace]
  refine ⟨43402136228909429826396667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57869514971879239768528889 43402136228909429826396667)
  ·
    refine ⟨65103204343364144739595001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43402136228909429826396667 65103204343364144739595001)
    ·
      refine ⟨48827403257523108554696251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65103204343364144739595001 48827403257523108554696251)
      ·
        refine ⟨73241104886284662832044377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48827403257523108554696251 73241104886284662832044377)
        ·
          refine ⟨54930828664713497124033283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73241104886284662832044377 54930828664713497124033283)
          ·
            refine ⟨82396242997070245686049925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54930828664713497124033283 82396242997070245686049925)
            ·
              refine ⟨15449295561950671066134361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82396242997070245686049925 15449295561950671066134361)
              ·
                refine ⟨11586971671463003299600771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15449295561950671066134361 11586971671463003299600771)
                ·
                  refine ⟨17380457507194504949401157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11586971671463003299600771 17380457507194504949401157)
                  ·
                    refine ⟨3258835782598969678012717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17380457507194504949401157 3258835782598969678012717)
                    ·
                      refine ⟨1222063418474613629254769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3258835782598969678012717 1222063418474613629254769)
                      ·
                        rfl

theorem cell23_2379960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 1, 4, 3].length) (baseStart_2379960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2379960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2379960 prefixEnd_2379960 := by exact prefixLift 2379960
  have htrace : WordTrace (prefixWord ++ tailWord_2379960) baseStart_2379960 baseEnd_2379960 := by
    simpa [prefixWord, tailWord_2379960, baseEnd_2379960] using wordTrace_append hprefix tailTrace_2379960
  have hstable : (prefixWord ++ tailWord_2379960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379960).length < 2 ^ (prefixWord ++ tailWord_2379960).sum := by decide
  have hdescent : baseEnd_2379960 < baseStart_2379960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379997 : List Nat := [1, 4, 3, 2, 1, 2, 1, 1, 8]
def baseStart_2379997 : Nat := 118140960795 + 2379997 * 2 ^ 59
def prefixEnd_2379997 : Nat := 4983230072969 + 3 ^ 40 * 2379997 * 2
def baseEnd_2379997 : Nat := 135786935250981109388011

theorem tailTrace_2379997 : CollatzResearch.WordTrace tailWord_2379997 prefixEnd_2379997 135786935250981109388011 := by
  unfold tailWord_2379997
  simp only [CollatzResearch.WordTrace]
  refine ⟨86805621958684814971890245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57870414639123209981260163 86805621958684814971890245)
  ·
    refine ⟨16276054117253402807229421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86805621958684814971890245 16276054117253402807229421)
    ·
      refine ⟨6103520293970026052711033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16276054117253402807229421 6103520293970026052711033)
      ·
        refine ⟨4577640220477519539533275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6103520293970026052711033 4577640220477519539533275)
        ·
          refine ⟨6866460330716279309299913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4577640220477519539533275 6866460330716279309299913)
          ·
            refine ⟨5149845248037209481974935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6866460330716279309299913 5149845248037209481974935)
            ·
              refine ⟨7724767872055814222962403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5149845248037209481974935 7724767872055814222962403)
              ·
                refine ⟨11587151808083721334443605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7724767872055814222962403 11587151808083721334443605)
                ·
                  refine ⟨135786935250981109388011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11587151808083721334443605 135786935250981109388011)
                  ·
                    rfl

theorem cell23_2379997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 8].length) (baseStart_2379997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2379997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2379997 prefixEnd_2379997 := by exact prefixLift 2379997
  have htrace : WordTrace (prefixWord ++ tailWord_2379997) baseStart_2379997 baseEnd_2379997 := by
    simpa [prefixWord, tailWord_2379997, baseEnd_2379997] using wordTrace_append hprefix tailTrace_2379997
  have hstable : (prefixWord ++ tailWord_2379997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379997).length < 2 ^ (prefixWord ++ tailWord_2379997).sum := by decide
  have hdescent : baseEnd_2379997 < baseStart_2379997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380017 : List Nat := [1, 2, 2, 2, 2, 1, 3, 2, 1, 5, 2]
def baseStart_2380017 : Nat := 118140960795 + 2380017 * 2 ^ 59
def prefixEnd_2380017 : Nat := 4983230072969 + 3 ^ 40 * 2380017 * 2
def baseEnd_2380017 : Nat := 1222092686871919906242007

theorem tailTrace_2380017 : CollatzResearch.WordTrace tailWord_2380017 prefixEnd_2380017 1222092686871919906242007 := by
  unfold tailWord_2380017
  simp only [CollatzResearch.WordTrace]
  refine ⟨86806351418612358387618305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57870900945741572258412203 86806351418612358387618305)
  ·
    refine ⟨65104763563959268790713729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86806351418612358387618305 65104763563959268790713729)
    ·
      refine ⟨48828572672969451593035297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65104763563959268790713729 48828572672969451593035297)
      ·
        refine ⟨36621429504727088694776473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48828572672969451593035297 36621429504727088694776473)
        ·
          refine ⟨27466072128545316521082355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36621429504727088694776473 27466072128545316521082355)
          ·
            refine ⟨41199108192817974781623533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27466072128545316521082355 41199108192817974781623533)
            ·
              refine ⟨15449665572306740543108825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41199108192817974781623533 15449665572306740543108825)
              ·
                refine ⟨11587249179230055407331619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15449665572306740543108825 11587249179230055407331619)
                ·
                  refine ⟨17380873768845083110997429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11587249179230055407331619 17380873768845083110997429)
                  ·
                    refine ⟨1629456915829226541656009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17380873768845083110997429 1629456915829226541656009)
                    ·
                      refine ⟨1222092686871919906242007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1629456915829226541656009 1222092686871919906242007)
                      ·
                        rfl

theorem cell23_2380017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 5, 2].length) (baseStart_2380017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2380017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2380017 prefixEnd_2380017 := by exact prefixLift 2380017
  have htrace : WordTrace (prefixWord ++ tailWord_2380017) baseStart_2380017 baseEnd_2380017 := by
    simpa [prefixWord, tailWord_2380017, baseEnd_2380017] using wordTrace_append hprefix tailTrace_2380017
  have hstable : (prefixWord ++ tailWord_2380017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380017).length < 2 ^ (prefixWord ++ tailWord_2380017).sum := by decide
  have hdescent : baseEnd_2380017 < baseStart_2380017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380041 : List Nat := [1, 2, 1, 1, 3, 4, 3, 3, 1, 1, 3]
def baseStart_2380041 : Nat := 118140960795 + 2380041 * 2 ^ 59
def prefixEnd_2380041 : Nat := 4983230072969 + 3 ^ 40 * 2380041 * 2
def baseEnd_2380041 : Nat := 1222105010407627812341897

theorem tailTrace_2380041 : CollatzResearch.WordTrace tailWord_2380041 prefixEnd_2380041 1222105010407627812341897 := by
  unfold tailWord_2380041
  simp only [CollatzResearch.WordTrace]
  refine ⟨86807226770525410486491977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57871484513683606990994651 86807226770525410486491977)
  ·
    refine ⟨65105420077894057864868983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86807226770525410486491977 65105420077894057864868983)
    ·
      refine ⟨97658130116841086797303475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65105420077894057864868983 97658130116841086797303475)
      ·
        refine ⟨146487195175261630195955213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97658130116841086797303475 146487195175261630195955213)
        ·
          refine ⟨54932698190723111323483205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146487195175261630195955213 54932698190723111323483205)
          ·
            refine ⟨10299880910760583373153101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54932698190723111323483205 10299880910760583373153101)
            ·
              refine ⟨3862455341535218764932413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10299880910760583373153101 3862455341535218764932413)
              ·
                refine ⟨1448420753075707036849655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3862455341535218764932413 1448420753075707036849655)
                ·
                  refine ⟨2172631129613560555274483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1448420753075707036849655 2172631129613560555274483)
                  ·
                    refine ⟨3258946694420340832911725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2172631129613560555274483 3258946694420340832911725)
                    ·
                      refine ⟨1222105010407627812341897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3258946694420340832911725 1222105010407627812341897)
                      ·
                        rfl

theorem cell23_2380041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 3, 1, 1, 3].length) (baseStart_2380041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2380041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2380041 prefixEnd_2380041 := by exact prefixLift 2380041
  have htrace : WordTrace (prefixWord ++ tailWord_2380041) baseStart_2380041 baseEnd_2380041 := by
    simpa [prefixWord, tailWord_2380041, baseEnd_2380041] using wordTrace_append hprefix tailTrace_2380041
  have hstable : (prefixWord ++ tailWord_2380041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380041).length < 2 ^ (prefixWord ++ tailWord_2380041).sum := by decide
  have hdescent : baseEnd_2380041 < baseStart_2380041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380058 : List Nat := [3, 1, 1, 3, 5, 1, 1, 1, 3, 1, 3]
def baseStart_2380058 : Nat := 118140960795 + 2380058 * 2 ^ 59
def prefixEnd_2380058 : Nat := 4983230072969 + 3 ^ 40 * 2380058 * 2
def baseEnd_2380058 : Nat := 1222113739578754245829319

theorem tailTrace_2380058 : CollatzResearch.WordTrace tailWord_2380058 prefixEnd_2380058 1222113739578754245829319 := by
  unfold tailWord_2380058
  simp only [CollatzResearch.WordTrace]
  refine ⟨21701961702865955597465207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57871897874309214926573885 21701961702865955597465207)
  ·
    refine ⟨32552942554298933396197811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21701961702865955597465207 32552942554298933396197811)
    ·
      refine ⟨48829413831448400094296717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32552942554298933396197811 48829413831448400094296717)
      ·
        refine ⟨18311030186793150035361269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48829413831448400094296717 18311030186793150035361269)
        ·
          refine ⟨1716659080011857815815119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18311030186793150035361269 1716659080011857815815119)
          ·
            refine ⟨2574988620017786723722679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1716659080011857815815119 2574988620017786723722679)
            ·
              refine ⟨3862482930026680085584019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2574988620017786723722679 3862482930026680085584019)
              ·
                refine ⟨5793724395040020128376029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3862482930026680085584019 5793724395040020128376029)
                ·
                  refine ⟨2172646648140007548141011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5793724395040020128376029 2172646648140007548141011)
                  ·
                    refine ⟨3258969972210011322211517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2172646648140007548141011 3258969972210011322211517)
                    ·
                      refine ⟨1222113739578754245829319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3258969972210011322211517 1222113739578754245829319)
                      ·
                        rfl

theorem cell23_2380058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 3, 1, 3].length) (baseStart_2380058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2380058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2380058 prefixEnd_2380058 := by exact prefixLift 2380058
  have htrace : WordTrace (prefixWord ++ tailWord_2380058) baseStart_2380058 baseEnd_2380058 := by
    simpa [prefixWord, tailWord_2380058, baseEnd_2380058] using wordTrace_append hprefix tailTrace_2380058
  have hstable : (prefixWord ++ tailWord_2380058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380058).length < 2 ^ (prefixWord ++ tailWord_2380058).sum := by decide
  have hdescent : baseEnd_2380058 < baseStart_2380058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380067 : List Nat := [1, 1, 1, 4, 2, 2, 2, 2, 3, 2, 3]
def baseStart_2380067 : Nat := 118140960795 + 2380067 * 2 ^ 59
def prefixEnd_2380067 : Nat := 4983230072969 + 3 ^ 40 * 2380067 * 2
def baseEnd_2380067 : Nat := 1222118360904644710616777

theorem tailTrace_2380067 : CollatzResearch.WordTrace tailWord_2380067 prefixEnd_2380067 1222118360904644710616777 := by
  unfold tailWord_2380067
  simp only [CollatzResearch.WordTrace]
  refine ⟨86808175068431216926938455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57872116712287477951292303 86808175068431216926938455)
  ·
    refine ⟨130212262602646825390407683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86808175068431216926938455 130212262602646825390407683)
    ·
      refine ⟨195318393903970238085611525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130212262602646825390407683 195318393903970238085611525)
      ·
        refine ⟨36622198856994419641052161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 195318393903970238085611525 36622198856994419641052161)
        ·
          refine ⟨27466649142745814730789121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36622198856994419641052161 27466649142745814730789121)
          ·
            refine ⟨20599986857059361048091841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27466649142745814730789121 20599986857059361048091841)
            ·
              refine ⟨15449990142794520786068881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20599986857059361048091841 15449990142794520786068881)
              ·
                refine ⟨11587492607095890589551661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15449990142794520786068881 11587492607095890589551661)
                ·
                  refine ⟨4345309727660958971081873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11587492607095890589551661 4345309727660958971081873)
                  ·
                    refine ⟨3258982295745719228311405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4345309727660958971081873 3258982295745719228311405)
                    ·
                      refine ⟨1222118360904644710616777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3258982295745719228311405 1222118360904644710616777)
                      ·
                        rfl

theorem cell23_2380067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 3, 2, 3].length) (baseStart_2380067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2380067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2380067 prefixEnd_2380067 := by exact prefixLift 2380067
  have htrace : WordTrace (prefixWord ++ tailWord_2380067) baseStart_2380067 baseEnd_2380067 := by
    simpa [prefixWord, tailWord_2380067, baseEnd_2380067] using wordTrace_append hprefix tailTrace_2380067
  have hstable : (prefixWord ++ tailWord_2380067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380067).length < 2 ^ (prefixWord ++ tailWord_2380067).sum := by decide
  have hdescent : baseEnd_2380067 < baseStart_2380067 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380078 : List Nat := [4, 1, 3, 3, 1, 2, 1, 2, 1, 5]
def baseStart_2380078 : Nat := 118140960795 + 2380078 * 2 ^ 59
def prefixEnd_2380078 : Nat := 4983230072969 + 3 ^ 40 * 2380078 * 2
def baseEnd_2380078 : Nat := 407374669730614722526409

theorem tailTrace_2380078 : CollatzResearch.WordTrace tailWord_2380078 prefixEnd_2380078 407374669730614722526409 := by
  unfold tailWord_2380078
  simp only [CollatzResearch.WordTrace]
  refine ⟨10851072033923920725698611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57872384180927577203725925 10851072033923920725698611)
  ·
    refine ⟨16276608050885881088547917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10851072033923920725698611 16276608050885881088547917)
    ·
      refine ⟨6103728019082205408205469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16276608050885881088547917 6103728019082205408205469)
      ·
        refine ⟨2288898007155827028077051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6103728019082205408205469 2288898007155827028077051)
        ·
          refine ⟨3433347010733740542115577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2288898007155827028077051 3433347010733740542115577)
          ·
            refine ⟨2575010258050305406586683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3433347010733740542115577 2575010258050305406586683)
            ·
              refine ⟨3862515387075458109880025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2575010258050305406586683 3862515387075458109880025)
              ·
                refine ⟨2896886540306593582410019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3862515387075458109880025 2896886540306593582410019)
                ·
                  refine ⟨4345329810459890373615029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2896886540306593582410019 4345329810459890373615029)
                  ·
                    refine ⟨407374669730614722526409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4345329810459890373615029 407374669730614722526409)
                    ·
                      rfl

theorem cell23_2380078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_2380078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2380078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2380078 prefixEnd_2380078 := by exact prefixLift 2380078
  have htrace : WordTrace (prefixWord ++ tailWord_2380078) baseStart_2380078 baseEnd_2380078 := by
    simpa [prefixWord, tailWord_2380078, baseEnd_2380078] using wordTrace_append hprefix tailTrace_2380078
  have hstable : (prefixWord ++ tailWord_2380078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380078).length < 2 ^ (prefixWord ++ tailWord_2380078).sum := by decide
  have hdescent : baseEnd_2380078 < baseStart_2380078 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380081 : List Nat := [1, 2, 2, 3, 4, 2, 1, 2, 1, 1, 4]
def baseStart_2380081 : Nat := 118140960795 + 2380081 * 2 ^ 59
def prefixEnd_2380081 : Nat := 4983230072969 + 3 ^ 40 * 2380081 * 2
def baseEnd_2380081 : Nat := 1222125549633807655841713

theorem tailTrace_2380081 : CollatzResearch.WordTrace tailWord_2380081 prefixEnd_2380081 1222125549633807655841713 := by
  unfold tailWord_2380081
  simp only [CollatzResearch.WordTrace]
  refine ⟨86808685690380497317948097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57872457126920331545298731 86808685690380497317948097)
  ·
    refine ⟨65106514267785372988461073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86808685690380497317948097 65106514267785372988461073)
    ·
      refine ⟨48829885700839029741345805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65106514267785372988461073 48829885700839029741345805)
      ·
        refine ⟨18311207137814636153004677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48829885700839029741345805 18311207137814636153004677)
        ·
          refine ⟨3433351338340244278688377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18311207137814636153004677 3433351338340244278688377)
          ·
            refine ⟨2575013503755183209016283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3433351338340244278688377 2575013503755183209016283)
            ·
              refine ⟨3862520255632774813524425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2575013503755183209016283 3862520255632774813524425)
              ·
                refine ⟨2896890191724581110143319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3862520255632774813524425 2896890191724581110143319)
                ·
                  refine ⟨4345335287586871665214979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2896890191724581110143319 4345335287586871665214979)
                  ·
                    refine ⟨6518002931380307497822469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4345335287586871665214979 6518002931380307497822469)
                    ·
                      refine ⟨1222125549633807655841713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6518002931380307497822469 1222125549633807655841713)
                      ·
                        rfl

theorem cell23_2380081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_2380081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2380081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2380081 prefixEnd_2380081 := by exact prefixLift 2380081
  have htrace : WordTrace (prefixWord ++ tailWord_2380081) baseStart_2380081 baseEnd_2380081 := by
    simpa [prefixWord, tailWord_2380081, baseEnd_2380081] using wordTrace_append hprefix tailTrace_2380081
  have hstable : (prefixWord ++ tailWord_2380081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380081).length < 2 ^ (prefixWord ++ tailWord_2380081).sum := by decide
  have hdescent : baseEnd_2380081 < baseStart_2380081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380094 : List Nat := [4, 2, 1, 2, 1, 3, 1, 2, 1, 2, 4]
def baseStart_2380094 : Nat := 118140960795 + 2380094 * 2 ^ 59
def prefixEnd_2380094 : Nat := 4983230072969 + 3 ^ 40 * 2380094 * 2
def baseEnd_2380094 : Nat := 1222132224882316104979153

theorem tailTrace_2380094 : CollatzResearch.WordTrace tailWord_2380094 prefixEnd_2380094 1222132224882316104979153 := by
  unfold tailWord_2380094
  simp only [CollatzResearch.WordTrace]
  refine ⟨10851144979916675067271417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57872773226222267025447557 10851144979916675067271417)
  ·
    refine ⟨8138358734937506300453563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10851144979916675067271417 8138358734937506300453563)
    ·
      refine ⟨12207538102406259450680345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8138358734937506300453563 12207538102406259450680345)
      ·
        refine ⟨9155653576804694588010259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12207538102406259450680345 9155653576804694588010259)
        ·
          refine ⟨13733480365207041882015389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9155653576804694588010259 13733480365207041882015389)
          ·
            refine ⟨5150055136952640705755771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13733480365207041882015389 5150055136952640705755771)
            ·
              refine ⟨7725082705428961058633657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5150055136952640705755771 7725082705428961058633657)
              ·
                refine ⟨5793812029071720793975243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7725082705428961058633657 5793812029071720793975243)
                ·
                  refine ⟨8690718043607581190962865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5793812029071720793975243 8690718043607581190962865)
                  ·
                    refine ⟨6518038532705685893222149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8690718043607581190962865 6518038532705685893222149)
                    ·
                      refine ⟨1222132224882316104979153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6518038532705685893222149 1222132224882316104979153)
                      ·
                        rfl

theorem cell23_2380094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_2380094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2380094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2380094 prefixEnd_2380094 := by exact prefixLift 2380094
  have htrace : WordTrace (prefixWord ++ tailWord_2380094) baseStart_2380094 baseEnd_2380094 := by
    simpa [prefixWord, tailWord_2380094, baseEnd_2380094] using wordTrace_append hprefix tailTrace_2380094
  have hstable : (prefixWord ++ tailWord_2380094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380094).length < 2 ^ (prefixWord ++ tailWord_2380094).sum := by decide
  have hdescent : baseEnd_2380094 < baseStart_2380094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380114 : List Nat := [3, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3]
def baseStart_2380114 : Nat := 118140960795 + 2380114 * 2 ^ 59
def prefixEnd_2380114 : Nat := 4983230072969 + 3 ^ 40 * 2380114 * 2
def baseEnd_2380114 : Nat := 1222142494495406026729061

theorem tailTrace_2380114 : CollatzResearch.WordTrace tailWord_2380114 prefixEnd_2380114 1222142494495406026729061 := by
  unfold tailWord_2380114
  simp only [CollatzResearch.WordTrace]
  refine ⟨21702472324815235988474849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57873259532840629302599597 21702472324815235988474849)
  ·
    refine ⟨16276854243611426991356137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21702472324815235988474849 16276854243611426991356137)
    ·
      refine ⟨12207640682708570243517103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16276854243611426991356137 12207640682708570243517103)
      ·
        refine ⟨18311461024062855365275655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12207640682708570243517103 18311461024062855365275655)
        ·
          refine ⟨27467191536094283047913483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18311461024062855365275655 27467191536094283047913483)
          ·
            refine ⟨41200787304141424571870225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27467191536094283047913483 41200787304141424571870225)
            ·
              refine ⟨30900590478106068428902669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41200787304141424571870225 30900590478106068428902669)
              ·
                refine ⟨11587721429289775660838501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30900590478106068428902669 11587721429289775660838501)
                ·
                  refine ⟨2172697767991832936407219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11587721429289775660838501 2172697767991832936407219)
                  ·
                    refine ⟨3259046651987749404610829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2172697767991832936407219 3259046651987749404610829)
                    ·
                      refine ⟨1222142494495406026729061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3259046651987749404610829 1222142494495406026729061)
                      ·
                        rfl

theorem cell23_2380114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_2380114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2380114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2380114 prefixEnd_2380114 := by exact prefixLift 2380114
  have htrace : WordTrace (prefixWord ++ tailWord_2380114) baseStart_2380114 baseEnd_2380114 := by
    simpa [prefixWord, tailWord_2380114, baseEnd_2380114] using wordTrace_append hprefix tailTrace_2380114
  have hstable : (prefixWord ++ tailWord_2380114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380114).length < 2 ^ (prefixWord ++ tailWord_2380114).sum := by decide
  have hdescent : baseEnd_2380114 < baseStart_2380114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380141 : List Nat := [1, 5, 1, 1, 1, 2, 2, 4, 1, 3, 2]
def baseStart_2380141 : Nat := 118140960795 + 2380141 * 2 ^ 59
def prefixEnd_2380141 : Nat := 4983230072969 + 3 ^ 40 * 2380141 * 2
def baseEnd_2380141 : Nat := 1222156358473077421091437

theorem tailTrace_2380141 : CollatzResearch.WordTrace tailWord_2380141 prefixEnd_2380141 1222156358473077421091437 := by
  unfold tailWord_2380141
  simp only [CollatzResearch.WordTrace]
  refine ⟨86810874070163127565132277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57873916046775418376754851 86810874070163127565132277)
  ·
    refine ⟨8138519444077793209231151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 86810874070163127565132277 8138519444077793209231151)
    ·
      refine ⟨12207779166116689813846727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8138519444077793209231151 12207779166116689813846727)
      ·
        refine ⟨18311668749175034720770091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12207779166116689813846727 18311668749175034720770091)
        ·
          refine ⟨27467503123762552081155137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18311668749175034720770091 27467503123762552081155137)
          ·
            refine ⟨20600627342821914060866353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27467503123762552081155137 20600627342821914060866353)
            ·
              refine ⟨15450470507116435545649765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20600627342821914060866353 15450470507116435545649765)
              ·
                refine ⟨2896963220084331664809331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15450470507116435545649765 2896963220084331664809331)
                ·
                  refine ⟨4345444830126497497213997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2896963220084331664809331 4345444830126497497213997)
                  ·
                    refine ⟨1629541811297436561455249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4345444830126497497213997 1629541811297436561455249)
                    ·
                      refine ⟨1222156358473077421091437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1629541811297436561455249 1222156358473077421091437)
                      ·
                        rfl

theorem cell23_2380141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 4, 1, 3, 2].length) (baseStart_2380141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2380141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2380141 prefixEnd_2380141 := by exact prefixLift 2380141
  have htrace : WordTrace (prefixWord ++ tailWord_2380141) baseStart_2380141 baseEnd_2380141 := by
    simpa [prefixWord, tailWord_2380141, baseEnd_2380141] using wordTrace_append hprefix tailTrace_2380141
  have hstable : (prefixWord ++ tailWord_2380141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380141).length < 2 ^ (prefixWord ++ tailWord_2380141).sum := by decide
  have hdescent : baseEnd_2380141 < baseStart_2380141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380167 : List Nat := [1, 1, 4, 2, 2, 1, 1, 1, 4, 2, 4]
def baseStart_2380167 : Nat := 118140960795 + 2380167 * 2 ^ 59
def prefixEnd_2380167 : Nat := 4983230072969 + 3 ^ 40 * 2380167 * 2
def baseEnd_2380167 : Nat := 1222169708970094319366317

theorem tailTrace_2380167 : CollatzResearch.WordTrace tailWord_2380167 prefixEnd_2380167 1222169708970094319366317 := by
  unfold tailWord_2380167
  simp only [CollatzResearch.WordTrace]
  refine ⟨86811822368068934005578755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57874548245379289337052503 86811822368068934005578755)
  ·
    refine ⟨130217733552103401008368133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86811822368068934005578755 130217733552103401008368133)
    ·
      refine ⟨24415825041019387689069025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130217733552103401008368133 24415825041019387689069025)
      ·
        refine ⟨18311868780764540766801769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24415825041019387689069025 18311868780764540766801769)
        ·
          refine ⟨13733901585573405575101327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18311868780764540766801769 13733901585573405575101327)
          ·
            refine ⟨20600852378360108362651991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13733901585573405575101327 20600852378360108362651991)
            ·
              refine ⟨30901278567540162543977987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20600852378360108362651991 30901278567540162543977987)
              ·
                refine ⟨46351917851310243815966981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30901278567540162543977987 46351917851310243815966981)
                ·
                  refine ⟨8690984597120670715493809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46351917851310243815966981 8690984597120670715493809)
                  ·
                    refine ⟨6518238447840503036620357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8690984597120670715493809 6518238447840503036620357)
                    ·
                      refine ⟨1222169708970094319366317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6518238447840503036620357 1222169708970094319366317)
                      ·
                        rfl

theorem cell23_2380167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_2380167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2380167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2380167 prefixEnd_2380167 := by exact prefixLift 2380167
  have htrace : WordTrace (prefixWord ++ tailWord_2380167) baseStart_2380167 baseEnd_2380167 := by
    simpa [prefixWord, tailWord_2380167, baseEnd_2380167] using wordTrace_append hprefix tailTrace_2380167
  have hstable : (prefixWord ++ tailWord_2380167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380167).length < 2 ^ (prefixWord ++ tailWord_2380167).sum := by decide
  have hdescent : baseEnd_2380167 < baseStart_2380167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380171 : List Nat := [1, 1, 1, 1, 4, 5, 1, 1, 4, 2, 2]
def baseStart_2380171 : Nat := 118140960795 + 2380171 * 2 ^ 59
def prefixEnd_2380171 : Nat := 4983230072969 + 3 ^ 40 * 2380171 * 2
def baseEnd_2380171 : Nat := 1222171762892712303716299

theorem tailTrace_2380171 : CollatzResearch.WordTrace tailWord_2380171 prefixEnd_2380171 1222171762892712303716299 := by
  unfold tailWord_2380171
  simp only [CollatzResearch.WordTrace]
  refine ⟨86811968260054442688724367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57874645506702961792482911 86811968260054442688724367)
  ·
    refine ⟨130217952390081664033086551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86811968260054442688724367 130217952390081664033086551)
    ·
      refine ⟨195326928585122496049629827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130217952390081664033086551 195326928585122496049629827)
      ·
        refine ⟨292990392877683744074444741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195326928585122496049629827 292990392877683744074444741)
        ·
          refine ⟨54935698664565702013958389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 292990392877683744074444741 54935698664565702013958389)
          ·
            refine ⟨5150221749803034563808599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54935698664565702013958389 5150221749803034563808599)
            ·
              refine ⟨7725332624704551845712899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5150221749803034563808599 7725332624704551845712899)
              ·
                refine ⟨11587998937056827768569349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7725332624704551845712899 11587998937056827768569349)
                ·
                  refine ⟨2172749800698155206606753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11587998937056827768569349 2172749800698155206606753)
                  ·
                    refine ⟨1629562350523616404955065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2172749800698155206606753 1629562350523616404955065)
                    ·
                      refine ⟨1222171762892712303716299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1629562350523616404955065 1222171762892712303716299)
                      ·
                        rfl

theorem cell23_2380171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 4, 2, 2].length) (baseStart_2380171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2380171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2380171 prefixEnd_2380171 := by exact prefixLift 2380171
  have htrace : WordTrace (prefixWord ++ tailWord_2380171) baseStart_2380171 baseEnd_2380171 := by
    simpa [prefixWord, tailWord_2380171, baseEnd_2380171] using wordTrace_append hprefix tailTrace_2380171
  have hstable : (prefixWord ++ tailWord_2380171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380171).length < 2 ^ (prefixWord ++ tailWord_2380171).sum := by decide
  have hdescent : baseEnd_2380171 < baseStart_2380171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380182 : List Nat := [5, 3, 1, 2, 1, 2, 1, 1, 1, 3, 3]
def baseStart_2380182 : Nat := 118140960795 + 2380182 * 2 ^ 59
def prefixEnd_2380182 : Nat := 4983230072969 + 3 ^ 40 * 2380182 * 2
def baseEnd_2380182 : Nat := 1222177411179911760678749

theorem tailTrace_2380182 : CollatzResearch.WordTrace tailWord_2380182 prefixEnd_2380182 1222177411179911760678749 := by
  unfold tailWord_2380182
  simp only [CollatzResearch.WordTrace]
  refine ⟨5425773091438411972960925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57874912975343061044916533 5425773091438411972960925)
  ·
    refine ⟨2034664909289404489860347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5425773091438411972960925 2034664909289404489860347)
    ·
      refine ⟨3051997363934106734790521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2034664909289404489860347 3051997363934106734790521)
      ·
        refine ⟨2288998022950580051092891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3051997363934106734790521 2288998022950580051092891)
        ·
          refine ⟨3433497034425870076639337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2288998022950580051092891 3433497034425870076639337)
          ·
            refine ⟨2575122775819402557479503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3433497034425870076639337 2575122775819402557479503)
            ·
              refine ⟨3862684163729103836219255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2575122775819402557479503 3862684163729103836219255)
              ·
                refine ⟨5794026245593655754328883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3862684163729103836219255 5794026245593655754328883)
                ·
                  refine ⟨8691039368390483631493325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5794026245593655754328883 8691039368390483631493325)
                  ·
                    refine ⟨3259139763146431361809997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8691039368390483631493325 3259139763146431361809997)
                    ·
                      refine ⟨1222177411179911760678749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3259139763146431361809997 1222177411179911760678749)
                      ·
                        rfl

theorem cell23_2380182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_2380182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2380182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2380182 prefixEnd_2380182 := by exact prefixLift 2380182
  have htrace : WordTrace (prefixWord ++ tailWord_2380182) baseStart_2380182 baseEnd_2380182 := by
    simpa [prefixWord, tailWord_2380182, baseEnd_2380182] using wordTrace_append hprefix tailTrace_2380182
  have hstable : (prefixWord ++ tailWord_2380182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380182).length < 2 ^ (prefixWord ++ tailWord_2380182).sum := by decide
  have hdescent : baseEnd_2380182 < baseStart_2380182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380184 : List Nat := [2, 1, 2, 5, 1, 1, 2, 1, 2, 2, 4]
def baseStart_2380184 : Nat := 118140960795 + 2380184 * 2 ^ 59
def prefixEnd_2380184 : Nat := 4983230072969 + 3 ^ 40 * 2380184 * 2
def baseEnd_2380184 : Nat := 1222178438141220752853739

theorem tailTrace_2380184 : CollatzResearch.WordTrace tailWord_2380184 prefixEnd_2380184 1222178438141220752853739 := by
  unfold tailWord_2380184
  simp only [CollatzResearch.WordTrace]
  refine ⟨43406221204503672954473803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57874961606004897272631737 43406221204503672954473803)
  ·
    refine ⟨65109331806755509431710705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43406221204503672954473803 65109331806755509431710705)
    ·
      refine ⟨48831998855066632073783029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65109331806755509431710705 48831998855066632073783029)
      ·
        refine ⟨4577999892662496756917159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48831998855066632073783029 4577999892662496756917159)
        ·
          refine ⟨6866999838993745135375739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4577999892662496756917159 6866999838993745135375739)
          ·
            refine ⟨10300499758490617703063609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6866999838993745135375739 10300499758490617703063609)
            ·
              refine ⟨7725374818867963277297707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10300499758490617703063609 7725374818867963277297707)
              ·
                refine ⟨11588062228301944915946561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7725374818867963277297707 11588062228301944915946561)
                ·
                  refine ⟨8691046671226458686959921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11588062228301944915946561 8691046671226458686959921)
                  ·
                    refine ⟨6518285003419844015219941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8691046671226458686959921 6518285003419844015219941)
                    ·
                      refine ⟨1222178438141220752853739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6518285003419844015219941 1222178438141220752853739)
                      ·
                        rfl

theorem cell23_2380184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_2380184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2380184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2380184 prefixEnd_2380184 := by exact prefixLift 2380184
  have htrace : WordTrace (prefixWord ++ tailWord_2380184) baseStart_2380184 baseEnd_2380184 := by
    simpa [prefixWord, tailWord_2380184, baseEnd_2380184] using wordTrace_append hprefix tailTrace_2380184
  have hstable : (prefixWord ++ tailWord_2380184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380184).length < 2 ^ (prefixWord ++ tailWord_2380184).sum := by decide
  have hdescent : baseEnd_2380184 < baseStart_2380184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380228 : List Nat := [2, 3, 3, 2, 3, 1, 1, 1, 7]
def baseStart_2380228 : Nat := 118140960795 + 2380228 * 2 ^ 59
def prefixEnd_2380228 : Nat := 4983230072969 + 3 ^ 40 * 2380228 * 2
def baseEnd_2380228 : Nat := 135800114587779842300393

theorem tailTrace_2380228 : CollatzResearch.WordTrace tailWord_2380228 prefixEnd_2380228 135800114587779842300393 := by
  unfold tailWord_2380228
  simp only [CollatzResearch.WordTrace]
  refine ⟨43407023610423970711774669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57876031480565294282366225 43407023610423970711774669)
  ·
    refine ⟨16277633853908989016915501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43407023610423970711774669 16277633853908989016915501)
    ·
      refine ⟨6104112695215870881343313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16277633853908989016915501 6104112695215870881343313)
      ·
        refine ⟨4578084521411903161007485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6104112695215870881343313 4578084521411903161007485)
        ·
          refine ⟨1716781695529463685377807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4578084521411903161007485 1716781695529463685377807)
          ·
            refine ⟨2575172543294195528066711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1716781695529463685377807 2575172543294195528066711)
            ·
              refine ⟨3862758814941293292100067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2575172543294195528066711 3862758814941293292100067)
              ·
                refine ⟨5794138222411939938150101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3862758814941293292100067 5794138222411939938150101)
                ·
                  refine ⟨135800114587779842300393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5794138222411939938150101 135800114587779842300393)
                  ·
                    rfl

theorem cell23_2380228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 7].length) (baseStart_2380228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2380228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2380228 prefixEnd_2380228 := by exact prefixLift 2380228
  have htrace : WordTrace (prefixWord ++ tailWord_2380228) baseStart_2380228 baseEnd_2380228 := by
    simpa [prefixWord, tailWord_2380228, baseEnd_2380228] using wordTrace_append hprefix tailTrace_2380228
  have hstable : (prefixWord ++ tailWord_2380228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380228).length < 2 ^ (prefixWord ++ tailWord_2380228).sum := by decide
  have hdescent : baseEnd_2380228 < baseStart_2380228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380271 : List Nat := [1, 1, 2, 1, 4, 1, 1, 7, 1, 4]
def baseStart_2380271 : Nat := 118140960795 + 2380271 * 2 ^ 59
def prefixEnd_2380271 : Nat := 4983230072969 + 3 ^ 40 * 2380271 * 2
def baseEnd_2380271 : Nat := 407407703652720637488613

theorem tailTrace_2380271 : CollatzResearch.WordTrace tailWord_2380271 prefixEnd_2380271 407407703652720637488613 := by
  unfold tailWord_2380271
  simp only [CollatzResearch.WordTrace]
  refine ⟨86815615559692159767364667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57877077039794773178243111 86815615559692159767364667)
  ·
    refine ⟨130223423339538239651047001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86815615559692159767364667 130223423339538239651047001)
    ·
      refine ⟨97667567504653679738285251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130223423339538239651047001 97667567504653679738285251)
      ·
        refine ⟨146501351256980519607427877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97667567504653679738285251 146501351256980519607427877)
        ·
          refine ⟨27469003360683847426392727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 146501351256980519607427877 27469003360683847426392727)
          ·
            refine ⟨41203505041025771139589091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27469003360683847426392727 41203505041025771139589091)
            ·
              refine ⟨61805257561538656709383637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41203505041025771139589091 61805257561538656709383637)
              ·
                refine ⟨1448560724098562266626179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 61805257561538656709383637 1448560724098562266626179)
                ·
                  refine ⟨2172841086147843399939269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1448560724098562266626179 2172841086147843399939269)
                  ·
                    refine ⟨407407703652720637488613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2172841086147843399939269 407407703652720637488613)
                    ·
                      rfl

theorem cell23_2380271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 7, 1, 4].length) (baseStart_2380271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2380271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2380271 prefixEnd_2380271 := by exact prefixLift 2380271
  have htrace : WordTrace (prefixWord ++ tailWord_2380271) baseStart_2380271 baseEnd_2380271 := by
    simpa [prefixWord, tailWord_2380271, baseEnd_2380271] using wordTrace_append hprefix tailTrace_2380271
  have hstable : (prefixWord ++ tailWord_2380271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380271).length < 2 ^ (prefixWord ++ tailWord_2380271).sum := by decide
  have hdescent : baseEnd_2380271 < baseStart_2380271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380287 : List Nat := [1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 6]
def baseStart_2380287 : Nat := 118140960795 + 2380287 * 2 ^ 59
def prefixEnd_2380287 : Nat := 4983230072969 + 3 ^ 40 * 2380287 * 2
def baseEnd_2380287 : Nat := 1222231326648633849865765

theorem tailTrace_2380287 : CollatzResearch.WordTrace tailWord_2380287 prefixEnd_2380287 1222231326648633849865765 := by
  unfold tailWord_2380287
  simp only [CollatzResearch.WordTrace]
  refine ⟨86816199127634194499947115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57877466085089462999964743 86816199127634194499947115)
  ·
    refine ⟨130224298691451291749920673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86816199127634194499947115 130224298691451291749920673)
    ·
      refine ⟨97668224018588468812440505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130224298691451291749920673 97668224018588468812440505)
      ·
        refine ⟨73251168013941351609330379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97668224018588468812440505 73251168013941351609330379)
        ·
          refine ⟨109876752020912027413995569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73251168013941351609330379 109876752020912027413995569)
          ·
            refine ⟨82407564015684020560496677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109876752020912027413995569 82407564015684020560496677)
            ·
              refine ⟨15451418252940753855093127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82407564015684020560496677 15451418252940753855093127)
              ·
                refine ⟨23177127379411130782639691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15451418252940753855093127 23177127379411130782639691)
                ·
                  refine ⟨34765691069116696173959537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23177127379411130782639691 34765691069116696173959537)
                  ·
                    refine ⟨26074268301837522130469653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34765691069116696173959537 26074268301837522130469653)
                    ·
                      refine ⟨1222231326648633849865765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26074268301837522130469653 1222231326648633849865765)
                      ·
                        rfl

theorem cell23_2380287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 6].length) (baseStart_2380287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2380287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2380287 prefixEnd_2380287 := by exact prefixLift 2380287
  have htrace : WordTrace (prefixWord ++ tailWord_2380287) baseStart_2380287 baseEnd_2380287 := by
    simpa [prefixWord, tailWord_2380287, baseEnd_2380287] using wordTrace_append hprefix tailTrace_2380287
  have hstable : (prefixWord ++ tailWord_2380287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380287).length < 2 ^ (prefixWord ++ tailWord_2380287).sum := by decide
  have hdescent : baseEnd_2380287 < baseStart_2380287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380304 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 2, 9, 2]
def baseStart_2380304 : Nat := 118140960795 + 2380304 * 2 ^ 59
def prefixEnd_2380304 : Nat := 4983230072969 + 3 ^ 40 * 2380304 * 2
def baseEnd_2380304 : Nat := 1222240055819760283353187

theorem tailTrace_2380304 : CollatzResearch.WordTrace tailWord_2380304 prefixEnd_2380304 1222240055819760283353187 := by
  unfold tailWord_2380304
  simp only [CollatzResearch.WordTrace]
  refine ⟨43408409584286303201657983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57877879445715070935543977 43408409584286303201657983)
  ·
    refine ⟨65112614376429454802486975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43408409584286303201657983 65112614376429454802486975)
    ·
      refine ⟨97668921564644182203730463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65112614376429454802486975 97668921564644182203730463)
      ·
        refine ⟨146503382346966273305595695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97668921564644182203730463 146503382346966273305595695)
        ·
          refine ⟨219755073520449409958393543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146503382346966273305595695 219755073520449409958393543)
          ·
            refine ⟨329632610280674114937590315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219755073520449409958393543 329632610280674114937590315)
            ·
              refine ⟨494448915421011172406385473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 329632610280674114937590315 494448915421011172406385473)
              ·
                refine ⟨370836686565758379304789105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 494448915421011172406385473 370836686565758379304789105)
                ·
                  refine ⟨278127514924318784478591829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 370836686565758379304789105 278127514924318784478591829)
                  ·
                    refine ⟨1629653407759680377804249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 278127514924318784478591829 1629653407759680377804249)
                    ·
                      refine ⟨1222240055819760283353187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1629653407759680377804249 1222240055819760283353187)
                      ·
                        rfl

theorem cell23_2380304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 2, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 2, 9, 2].length) (baseStart_2380304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2380304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2380304 prefixEnd_2380304 := by exact prefixLift 2380304
  have htrace : WordTrace (prefixWord ++ tailWord_2380304) baseStart_2380304 baseEnd_2380304 := by
    simpa [prefixWord, tailWord_2380304, baseEnd_2380304] using wordTrace_append hprefix tailTrace_2380304
  have hstable : (prefixWord ++ tailWord_2380304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380304).length < 2 ^ (prefixWord ++ tailWord_2380304).sum := by decide
  have hdescent : baseEnd_2380304 < baseStart_2380304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380307 : List Nat := [1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 7]
def baseStart_2380307 : Nat := 118140960795 + 2380307 * 2 ^ 59
def prefixEnd_2380307 : Nat := 4983230072969 + 3 ^ 40 * 2380307 * 2
def baseEnd_2380307 : Nat := 1222241596261723771615673

theorem tailTrace_2380307 : CollatzResearch.WordTrace tailWord_2380307 prefixEnd_2380307 1222241596261723771615673 := by
  unfold tailWord_2380307
  simp only [CollatzResearch.WordTrace]
  refine ⟨86816928587561737915675175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57877952391707825277116783 86816928587561737915675175)
  ·
    refine ⟨130225392881342606873512763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86816928587561737915675175 130225392881342606873512763)
    ·
      refine ⟨195338089322013910310269145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130225392881342606873512763 195338089322013910310269145)
      ·
        refine ⟨146503566991510432732701859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195338089322013910310269145 146503566991510432732701859)
        ·
          refine ⟨219755350487265649099052789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146503566991510432732701859 219755350487265649099052789)
          ·
            refine ⟨20602064108181154603036199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 219755350487265649099052789 20602064108181154603036199)
            ·
              refine ⟨30903096162271731904554299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20602064108181154603036199 30903096162271731904554299)
              ·
                refine ⟨46354644243407597856831449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30903096162271731904554299 46354644243407597856831449)
                ·
                  refine ⟨34765983182555698392623587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46354644243407597856831449 34765983182555698392623587)
                  ·
                    refine ⟨52148974773833547588935381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34765983182555698392623587 52148974773833547588935381)
                    ·
                      refine ⟨1222241596261723771615673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 52148974773833547588935381 1222241596261723771615673)
                      ·
                        rfl

theorem cell23_2380307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 7].length) (baseStart_2380307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2380307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2380307 prefixEnd_2380307 := by exact prefixLift 2380307
  have htrace : WordTrace (prefixWord ++ tailWord_2380307) baseStart_2380307 baseEnd_2380307 := by
    simpa [prefixWord, tailWord_2380307, baseEnd_2380307] using wordTrace_append hprefix tailTrace_2380307
  have hstable : (prefixWord ++ tailWord_2380307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380307).length < 2 ^ (prefixWord ++ tailWord_2380307).sum := by decide
  have hdescent : baseEnd_2380307 < baseStart_2380307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380314 : List Nat := [3, 1, 1, 3, 1, 1, 4, 1, 3, 5]
def baseStart_2380314 : Nat := 118140960795 + 2380314 * 2 ^ 59
def prefixEnd_2380314 : Nat := 4983230072969 + 3 ^ 40 * 2380314 * 2
def baseEnd_2380314 : Nat := 407415063542101748076047

theorem tailTrace_2380314 : CollatzResearch.WordTrace tailWord_2380314 prefixEnd_2380314 407415063542101748076047 := by
  unfold tailWord_2380314
  simp only [CollatzResearch.WordTrace]
  refine ⟨21704295974634094527794999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57878122599024252074119997 21704295974634094527794999)
  ·
    refine ⟨32556443961951141791692499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21704295974634094527794999 32556443961951141791692499)
    ·
      refine ⟨48834665942926712687538749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32556443961951141791692499 48834665942926712687538749)
      ·
        refine ⟨18312999728597517257827031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48834665942926712687538749 18312999728597517257827031)
        ·
          refine ⟨27469499592896275886740547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18312999728597517257827031 27469499592896275886740547)
          ·
            refine ⟨41204249389344413830110821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27469499592896275886740547 41204249389344413830110821)
            ·
              refine ⟨7725796760502077593145779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41204249389344413830110821 7725796760502077593145779)
              ·
                refine ⟨11588695140753116389718669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7725796760502077593145779 11588695140753116389718669)
                ·
                  refine ⟨4345760677782418646144501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11588695140753116389718669 4345760677782418646144501)
                  ·
                    refine ⟨407415063542101748076047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4345760677782418646144501 407415063542101748076047)
                    ·
                      rfl

theorem cell23_2380314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 3, 5].length) (baseStart_2380314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2380314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2380314 prefixEnd_2380314 := by exact prefixLift 2380314
  have htrace : WordTrace (prefixWord ++ tailWord_2380314) baseStart_2380314 baseEnd_2380314 := by
    simpa [prefixWord, tailWord_2380314, baseEnd_2380314] using wordTrace_append hprefix tailTrace_2380314
  have hstable : (prefixWord ++ tailWord_2380314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380314).length < 2 ^ (prefixWord ++ tailWord_2380314).sum := by decide
  have hdescent : baseEnd_2380314 < baseStart_2380314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380321 : List Nat := [1, 2, 3, 2, 2, 1, 3, 1, 1, 5, 2]
def baseStart_2380321 : Nat := 118140960795 + 2380321 * 2 ^ 59
def prefixEnd_2380321 : Nat := 4983230072969 + 3 ^ 40 * 2380321 * 2
def baseEnd_2380321 : Nat := 1222248784990886716840609

theorem tailTrace_2380321 : CollatzResearch.WordTrace tailWord_2380321 prefixEnd_2380321 1222248784990886716840609 := by
  unfold tailWord_2380321
  simp only [CollatzResearch.WordTrace]
  refine ⟨86817439209511018306684817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57878292806340678871123211 86817439209511018306684817)
  ·
    refine ⟨65113079407133263730013613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86817439209511018306684817 65113079407133263730013613)
    ·
      refine ⟨24417404777674973898755105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65113079407133263730013613 24417404777674973898755105)
      ·
        refine ⟨18313053583256230424066329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24417404777674973898755105 18313053583256230424066329)
        ·
          refine ⟨13734790187442172818049747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18313053583256230424066329 13734790187442172818049747)
          ·
            refine ⟨20602185281163259227074621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13734790187442172818049747 20602185281163259227074621)
            ·
              refine ⟨7725819480436222210152983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20602185281163259227074621 7725819480436222210152983)
              ·
                refine ⟨11588729220654333315229475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7725819480436222210152983 11588729220654333315229475)
                ·
                  refine ⟨17383093830981499972844213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11588729220654333315229475 17383093830981499972844213)
                  ·
                    refine ⟨1629665046654515622454145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17383093830981499972844213 1629665046654515622454145)
                    ·
                      refine ⟨1222248784990886716840609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1629665046654515622454145 1222248784990886716840609)
                      ·
                        rfl

theorem cell23_2380321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 5, 2].length) (baseStart_2380321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2380321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2380321 prefixEnd_2380321 := by exact prefixLift 2380321
  have htrace : WordTrace (prefixWord ++ tailWord_2380321) baseStart_2380321 baseEnd_2380321 := by
    simpa [prefixWord, tailWord_2380321, baseEnd_2380321] using wordTrace_append hprefix tailTrace_2380321
  have hstable : (prefixWord ++ tailWord_2380321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380321).length < 2 ^ (prefixWord ++ tailWord_2380321).sum := by decide
  have hdescent : baseEnd_2380321 < baseStart_2380321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380347 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 6]
def baseStart_2380347 : Nat := 118140960795 + 2380347 * 2 ^ 59
def prefixEnd_2380347 : Nat := 4983230072969 + 3 ^ 40 * 2380347 * 2
def baseEnd_2380347 : Nat := 1222262135487903615115489

theorem tailTrace_2380347 : CollatzResearch.WordTrace tailWord_2380347 prefixEnd_2380347 1222262135487903615115489 := by
  unfold tailWord_2380347
  simp only [CollatzResearch.WordTrace]
  refine ⟨86818387507416824747131295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57878925004944549831420863 86818387507416824747131295)
  ·
    refine ⟨130227581261125237120696943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86818387507416824747131295 130227581261125237120696943)
    ·
      refine ⟨195341371891687855681045415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130227581261125237120696943 195341371891687855681045415)
      ·
        refine ⟨293012057837531783521568123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195341371891687855681045415 293012057837531783521568123)
        ·
          refine ⟨439518086756297675282352185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293012057837531783521568123 439518086756297675282352185)
          ·
            refine ⟨329638565067223256461764139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 439518086756297675282352185 329638565067223256461764139)
            ·
              refine ⟨494457847600834884692646209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 329638565067223256461764139 494457847600834884692646209)
              ·
                refine ⟨370843385700626163519484657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 494457847600834884692646209 370843385700626163519484657)
                ·
                  refine ⟨278132539275469622639613493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 370843385700626163519484657 278132539275469622639613493)
                  ·
                    refine ⟨26074925557075277122463765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 278132539275469622639613493 26074925557075277122463765)
                    ·
                      refine ⟨1222262135487903615115489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26074925557075277122463765 1222262135487903615115489)
                      ·
                        rfl

theorem cell23_2380347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 6].length) (baseStart_2380347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2380347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2380347 prefixEnd_2380347 := by exact prefixLift 2380347
  have htrace : WordTrace (prefixWord ++ tailWord_2380347) baseStart_2380347 baseEnd_2380347 := by
    simpa [prefixWord, tailWord_2380347, baseEnd_2380347] using wordTrace_append hprefix tailTrace_2380347
  have hstable : (prefixWord ++ tailWord_2380347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380347).length < 2 ^ (prefixWord ++ tailWord_2380347).sum := by decide
  have hdescent : baseEnd_2380347 < baseStart_2380347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380364 : List Nat := [2, 2, 1, 3, 1, 2, 3, 1, 1, 1, 6]
def baseStart_2380364 : Nat := 118140960795 + 2380364 * 2 ^ 59
def prefixEnd_2380364 : Nat := 4983230072969 + 3 ^ 40 * 2380364 * 2
def baseEnd_2380364 : Nat := 1222270864659030048602911

theorem tailTrace_2380364 : CollatzResearch.WordTrace tailWord_2380364 prefixEnd_2380364 1222270864659030048602911 := by
  unfold tailWord_2380364
  simp only [CollatzResearch.WordTrace]
  refine ⟨43409503774177618325250073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57879338365570157767000097 43409503774177618325250073)
  ·
    refine ⟨32557127830633213743937555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43409503774177618325250073 32557127830633213743937555)
    ·
      refine ⟨48835691745949820615906333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32557127830633213743937555 48835691745949820615906333)
      ·
        refine ⟨18313384404731182730964875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48835691745949820615906333 18313384404731182730964875)
        ·
          refine ⟨27470076607096774096447313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18313384404731182730964875 27470076607096774096447313)
          ·
            refine ⟨20602557455322580572335485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27470076607096774096447313 20602557455322580572335485)
            ·
              refine ⟨7725959045745967714625807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20602557455322580572335485 7725959045745967714625807)
              ·
                refine ⟨11588938568618951571938711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7725959045745967714625807 11588938568618951571938711)
                ·
                  refine ⟨17383407852928427357908067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11588938568618951571938711 17383407852928427357908067)
                  ·
                    refine ⟨26075111779392641036862101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17383407852928427357908067 26075111779392641036862101)
                    ·
                      refine ⟨1222270864659030048602911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26075111779392641036862101 1222270864659030048602911)
                      ·
                        rfl

theorem cell23_2380364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_2380364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2380364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2380364 prefixEnd_2380364 := by exact prefixLift 2380364
  have htrace : WordTrace (prefixWord ++ tailWord_2380364) baseStart_2380364 baseEnd_2380364 := by
    simpa [prefixWord, tailWord_2380364, baseEnd_2380364] using wordTrace_append hprefix tailTrace_2380364
  have hstable : (prefixWord ++ tailWord_2380364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380364).length < 2 ^ (prefixWord ++ tailWord_2380364).sum := by decide
  have hdescent : baseEnd_2380364 < baseStart_2380364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380402 : List Nat := [3, 2, 1, 2, 4, 2, 1, 1, 3, 2, 2]
def baseStart_2380402 : Nat := 118140960795 + 2380402 * 2 ^ 59
def prefixEnd_2380402 : Nat := 4983230072969 + 3 ^ 40 * 2380402 * 2
def baseEnd_2380402 : Nat := 1222290376923900899927737

theorem tailTrace_2380402 : CollatzResearch.WordTrace tailWord_2380402 prefixEnd_2380402 1222290376923900899927737 := by
  unfold tailWord_2380402
  simp only [CollatzResearch.WordTrace]
  refine ⟨21705098380554392285095865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57880262348145046093588973 21705098380554392285095865)
  ·
    refine ⟨16278823785415794213821899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21705098380554392285095865 16278823785415794213821899)
    ·
      refine ⟨24418235678123691320732849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16278823785415794213821899 24418235678123691320732849)
      ·
        refine ⟨18313676758592768490549637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24418235678123691320732849 18313676758592768490549637)
        ·
          refine ⟨3433814392236144091978057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18313676758592768490549637 3433814392236144091978057)
          ·
            refine ⟨2575360794177108068983543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3433814392236144091978057 2575360794177108068983543)
            ·
              refine ⟨3863041191265662103475315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2575360794177108068983543 3863041191265662103475315)
              ·
                refine ⟨5794561786898493155212973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3863041191265662103475315 5794561786898493155212973)
                ·
                  refine ⟨2172960670086934933204865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5794561786898493155212973 2172960670086934933204865)
                  ·
                    refine ⟨1629720502565201199903649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2172960670086934933204865 1629720502565201199903649)
                    ·
                      refine ⟨1222290376923900899927737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1629720502565201199903649 1222290376923900899927737)
                      ·
                        rfl

theorem cell23_2380402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 3, 2, 2].length) (baseStart_2380402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2380402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2380402 prefixEnd_2380402 := by exact prefixLift 2380402
  have htrace : WordTrace (prefixWord ++ tailWord_2380402) baseStart_2380402 baseEnd_2380402 := by
    simpa [prefixWord, tailWord_2380402, baseEnd_2380402] using wordTrace_append hprefix tailTrace_2380402
  have hstable : (prefixWord ++ tailWord_2380402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380402).length < 2 ^ (prefixWord ++ tailWord_2380402).sum := by decide
  have hdescent : baseEnd_2380402 < baseStart_2380402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380428 : List Nat := [2, 2, 1, 2, 1, 1, 2, 6, 1, 3, 2]
def baseStart_2380428 : Nat := 118140960795 + 2380428 * 2 ^ 59
def prefixEnd_2380428 : Nat := 4983230072969 + 3 ^ 40 * 2380428 * 2
def baseEnd_2380428 : Nat := 1222303727420917798202617

theorem tailTrace_2380428 : CollatzResearch.WordTrace tailWord_2380428 prefixEnd_2380428 1222303727420917798202617 := by
  unfold tailWord_2380428
  simp only [CollatzResearch.WordTrace]
  refine ⟨43410670910061687790414969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57880894546748917053886625 43410670910061687790414969)
  ·
    refine ⟨32558003182546265842811227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43410670910061687790414969 32558003182546265842811227)
    ·
      refine ⟨48837004773819398764216841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32558003182546265842811227 48837004773819398764216841)
      ·
        refine ⟨36627753580364549073162631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48837004773819398764216841 36627753580364549073162631)
        ·
          refine ⟨54941630370546823609743947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36627753580364549073162631 54941630370546823609743947)
          ·
            refine ⟨82412445555820235414615921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54941630370546823609743947 82412445555820235414615921)
            ·
              refine ⟨61809334166865176560961941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82412445555820235414615921 61809334166865176560961941)
              ·
                refine ⟨2897312539071805151295091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 61809334166865176560961941 2897312539071805151295091)
                ·
                  refine ⟨4345968808607707726942637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2897312539071805151295091 4345968808607707726942637)
                  ·
                    refine ⟨1629738303227890397603489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4345968808607707726942637 1629738303227890397603489)
                    ·
                      refine ⟨1222303727420917798202617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1629738303227890397603489 1222303727420917798202617)
                      ·
                        rfl

theorem cell23_2380428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 6, 1, 3, 2].length) (baseStart_2380428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2380428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2380428 prefixEnd_2380428 := by exact prefixLift 2380428
  have htrace : WordTrace (prefixWord ++ tailWord_2380428) baseStart_2380428 baseEnd_2380428 := by
    simpa [prefixWord, tailWord_2380428, baseEnd_2380428] using wordTrace_append hprefix tailTrace_2380428
  have hstable : (prefixWord ++ tailWord_2380428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380428).length < 2 ^ (prefixWord ++ tailWord_2380428).sum := by decide
  have hdescent : baseEnd_2380428 < baseStart_2380428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380464 : List Nat := [2, 1, 1, 1, 2, 1, 3, 5, 7]
def baseStart_2380464 : Nat := 118140960795 + 2380464 * 2 ^ 59
def prefixEnd_2380464 : Nat := 4983230072969 + 3 ^ 40 * 2380464 * 2
def baseEnd_2380464 : Nat := 135813579191608850816939

theorem tailTrace_2380464 : CollatzResearch.WordTrace tailWord_2380464 prefixEnd_2380464 135813579191608850816939 := by
  unfold tailWord_2380464
  simp only [CollatzResearch.WordTrace]
  refine ⟨43411327423996476864570223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57881769898661969152760297 43411327423996476864570223)
  ·
    refine ⟨65116991135994715296855335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43411327423996476864570223 65116991135994715296855335)
    ·
      refine ⟨97675486703992072945283003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65116991135994715296855335 97675486703992072945283003)
      ·
        refine ⟨146513230055988109417924505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97675486703992072945283003 146513230055988109417924505)
        ·
          refine ⟨109884922541991082063443379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146513230055988109417924505 109884922541991082063443379)
          ·
            refine ⟨164827383812986623095165069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109884922541991082063443379 164827383812986623095165069)
            ·
              refine ⟨61810268929869983660686901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 164827383812986623095165069 61810268929869983660686901)
              ·
                refine ⟨5794712712175310968189397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61810268929869983660686901 5794712712175310968189397)
                ·
                  refine ⟨135813579191608850816939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5794712712175310968189397 135813579191608850816939)
                  ·
                    rfl

theorem cell23_2380464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 7].length) (baseStart_2380464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2380464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2380464 prefixEnd_2380464 := by exact prefixLift 2380464
  have htrace : WordTrace (prefixWord ++ tailWord_2380464) baseStart_2380464 baseEnd_2380464 := by
    simpa [prefixWord, tailWord_2380464, baseEnd_2380464] using wordTrace_append hprefix tailTrace_2380464
  have hstable : (prefixWord ++ tailWord_2380464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380464).length < 2 ^ (prefixWord ++ tailWord_2380464).sum := by decide
  have hdescent : baseEnd_2380464 < baseStart_2380464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380548 : List Nat := [2, 3, 2, 2, 1, 1, 2, 3, 2, 1, 4]
def baseStart_2380548 : Nat := 118140960795 + 2380548 * 2 ^ 59
def prefixEnd_2380548 : Nat := 4983230072969 + 3 ^ 40 * 2380548 * 2
def baseEnd_2380548 : Nat := 1222365345099457328702065

theorem tailTrace_2380548 : CollatzResearch.WordTrace tailWord_2380548 prefixEnd_2380548 1222365345099457328702065 := by
  unfold tailWord_2380548
  simp only [CollatzResearch.WordTrace]
  refine ⟨43412859289844318037599149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57883812386459090716798865 43412859289844318037599149)
  ·
    refine ⟨16279822233691619264099681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43412859289844318037599149 16279822233691619264099681)
    ·
      refine ⟨12209866675268714448074761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16279822233691619264099681 12209866675268714448074761)
      ·
        refine ⟨9157400006451535836056071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12209866675268714448074761 9157400006451535836056071)
        ·
          refine ⟨13736100009677303754084107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9157400006451535836056071 13736100009677303754084107)
          ·
            refine ⟨20604150014515955631126161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13736100009677303754084107 20604150014515955631126161)
            ·
              refine ⟨15453112510886966723344621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20604150014515955631126161 15453112510886966723344621)
              ·
                refine ⟨5794917191582612521254233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15453112510886966723344621 5794917191582612521254233)
                ·
                  refine ⟨4346187893686959390940675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5794917191582612521254233 4346187893686959390940675)
                  ·
                    refine ⟨6519281840530439086411013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4346187893686959390940675 6519281840530439086411013)
                    ·
                      refine ⟨1222365345099457328702065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6519281840530439086411013 1222365345099457328702065)
                      ·
                        rfl

theorem cell23_2380548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_2380548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2380548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2380548 prefixEnd_2380548 := by exact prefixLift 2380548
  have htrace : WordTrace (prefixWord ++ tailWord_2380548) baseStart_2380548 baseEnd_2380548 := by
    simpa [prefixWord, tailWord_2380548, baseEnd_2380548] using wordTrace_append hprefix tailTrace_2380548
  have hstable : (prefixWord ++ tailWord_2380548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380548).length < 2 ^ (prefixWord ++ tailWord_2380548).sum := by decide
  have hdescent : baseEnd_2380548 < baseStart_2380548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380575 : List Nat := [1, 1, 2, 4, 2, 4, 1, 1, 3, 4]
def baseStart_2380575 : Nat := 118140960795 + 2380575 * 2 ^ 59
def prefixEnd_2380575 : Nat := 4983230072969 + 3 ^ 40 * 2380575 * 2
def baseEnd_2380575 : Nat := 407459736359042907688147

theorem tailTrace_2380575 : CollatzResearch.WordTrace tailWord_2380575 prefixEnd_2380575 407459736359042907688147 := by
  unfold tailWord_2380575
  simp only [CollatzResearch.WordTrace]
  refine ⟨86826703350590819686431179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57884468900393879790954119 86826703350590819686431179)
  ·
    refine ⟨130240055025886229529646769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86826703350590819686431179 130240055025886229529646769)
    ·
      refine ⟨97680041269414672147235077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130240055025886229529646769 97680041269414672147235077)
      ·
        refine ⟨18315007738015251027606577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97680041269414672147235077 18315007738015251027606577)
        ·
          refine ⟨13736255803511438270704933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18315007738015251027606577 13736255803511438270704933)
          ·
            refine ⟨2575547963158394675757175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13736255803511438270704933 2575547963158394675757175)
            ·
              refine ⟨3863321944737592013635763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2575547963158394675757175 3863321944737592013635763)
              ·
                refine ⟨5794982917106388020453645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3863321944737592013635763 5794982917106388020453645)
                ·
                  refine ⟨2173118593914895507670117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5794982917106388020453645 2173118593914895507670117)
                  ·
                    refine ⟨407459736359042907688147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2173118593914895507670117 407459736359042907688147)
                    ·
                      rfl

theorem cell23_2380575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 3, 4].length) (baseStart_2380575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2380575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2380575 prefixEnd_2380575 := by exact prefixLift 2380575
  have htrace : WordTrace (prefixWord ++ tailWord_2380575) baseStart_2380575 baseEnd_2380575 := by
    simpa [prefixWord, tailWord_2380575, baseEnd_2380575] using wordTrace_append hprefix tailTrace_2380575
  have hstable : (prefixWord ++ tailWord_2380575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380575).length < 2 ^ (prefixWord ++ tailWord_2380575).sum := by decide
  have hdescent : baseEnd_2380575 < baseStart_2380575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380608 : List Nat := [2, 1, 1, 2, 2, 1, 1, 5, 1, 5, 2]
def baseStart_2380608 : Nat := 118140960795 + 2380608 * 2 ^ 59
def prefixEnd_2380608 : Nat := 4983230072969 + 3 ^ 40 * 2380608 * 2
def baseEnd_2380608 : Nat := 1222396153938727093951789

theorem tailTrace_2380608 : CollatzResearch.WordTrace tailWord_2380608 prefixEnd_2380608 1222396153938727093951789 := by
  unfold tailWord_2380608
  simp only [CollatzResearch.WordTrace]
  refine ⟨43413953479735633161191239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57885271306314177548254985 43413953479735633161191239)
  ·
    refine ⟨65120930219603449741786859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43413953479735633161191239 65120930219603449741786859)
    ·
      refine ⟨97681395329405174612680289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65120930219603449741786859 97681395329405174612680289)
      ·
        refine ⟨73261046497053880959510217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97681395329405174612680289 73261046497053880959510217)
        ·
          refine ⟨54945784872790410719632663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73261046497053880959510217 54945784872790410719632663)
          ·
            refine ⟨82418677309185616079448995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54945784872790410719632663 82418677309185616079448995)
            ·
              refine ⟨123628015963778424119173493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82418677309185616079448995 123628015963778424119173493)
              ·
                refine ⟨11590126496604227261172515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 123628015963778424119173493 11590126496604227261172515)
                ·
                  refine ⟨17385189744906340891758773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11590126496604227261172515 17385189744906340891758773)
                  ·
                    refine ⟨1629861538584969458602385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17385189744906340891758773 1629861538584969458602385)
                    ·
                      refine ⟨1222396153938727093951789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1629861538584969458602385 1222396153938727093951789)
                      ·
                        rfl

theorem cell23_2380608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 1, 5, 2].length) (baseStart_2380608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2380608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2380608 prefixEnd_2380608 := by exact prefixLift 2380608
  have htrace : WordTrace (prefixWord ++ tailWord_2380608) baseStart_2380608 baseEnd_2380608 := by
    simpa [prefixWord, tailWord_2380608, baseEnd_2380608] using wordTrace_append hprefix tailTrace_2380608
  have hstable : (prefixWord ++ tailWord_2380608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380608).length < 2 ^ (prefixWord ++ tailWord_2380608).sum := by decide
  have hdescent : baseEnd_2380608 < baseStart_2380608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380648 : List Nat := [2, 1, 4, 2, 1, 2, 1, 3, 1, 6]
def baseStart_2380648 : Nat := 118140960795 + 2380648 * 2 ^ 59
def prefixEnd_2380648 : Nat := 4983230072969 + 3 ^ 40 * 2380648 * 2
def baseEnd_2380648 : Nat := 407472231054968979150535

theorem tailTrace_2380648 : CollatzResearch.WordTrace tailWord_2380648 prefixEnd_2380648 407472231054968979150535 := by
  unfold tailWord_2380648
  simp only [CollatzResearch.WordTrace]
  refine ⟨43414682939663176576919299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57886243919550902102559065 43414682939663176576919299)
  ·
    refine ⟨65122024409494764865378949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43414682939663176576919299 65122024409494764865378949)
    ·
      refine ⟨12210379576780268412258553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65122024409494764865378949 12210379576780268412258553)
      ·
        refine ⟨9157784682585201309193915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12210379576780268412258553 9157784682585201309193915)
        ·
          refine ⟨13736677023877801963790873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9157784682585201309193915 13736677023877801963790873)
          ·
            refine ⟨10302507767908351472843155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13736677023877801963790873 10302507767908351472843155)
            ·
              refine ⟨15453761651862527209264733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10302507767908351472843155 15453761651862527209264733)
              ·
                refine ⟨5795160619448447703474275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15453761651862527209264733 5795160619448447703474275)
                ·
                  refine ⟨8692740929172671555211413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5795160619448447703474275 8692740929172671555211413)
                  ·
                    refine ⟨407472231054968979150535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8692740929172671555211413 407472231054968979150535)
                    ·
                      rfl

theorem cell23_2380648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_2380648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2380648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2380648 prefixEnd_2380648 := by exact prefixLift 2380648
  have htrace : WordTrace (prefixWord ++ tailWord_2380648) baseStart_2380648 baseEnd_2380648 := by
    simpa [prefixWord, tailWord_2380648, baseEnd_2380648] using wordTrace_append hprefix tailTrace_2380648
  have hstable : (prefixWord ++ tailWord_2380648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380648).length < 2 ^ (prefixWord ++ tailWord_2380648).sum := by decide
  have hdescent : baseEnd_2380648 < baseStart_2380648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380651 : List Nat := [1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 6]
def baseStart_2380651 : Nat := 118140960795 + 2380651 * 2 ^ 59
def prefixEnd_2380651 : Nat := 4983230072969 + 3 ^ 40 * 2380651 * 2
def baseEnd_2380651 : Nat := 1222418233606870425714091

theorem tailTrace_2380651 : CollatzResearch.WordTrace tailWord_2380651 prefixEnd_2380651 1222418233606870425714091 := by
  unfold tailWord_2380651
  simp only [CollatzResearch.WordTrace]
  refine ⟨86829475298315484666197807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57886316865543656444131871 86829475298315484666197807)
  ·
    refine ⟨130244212947473226999296711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86829475298315484666197807 130244212947473226999296711)
    ·
      refine ⟨195366319421209840498945067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130244212947473226999296711 195366319421209840498945067)
      ·
        refine ⟨293049479131814760748417601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195366319421209840498945067 293049479131814760748417601)
        ·
          refine ⟨219787109348861070561313201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 293049479131814760748417601 219787109348861070561313201)
          ·
            refine ⟨164840332011645802920984901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 219787109348861070561313201 164840332011645802920984901)
            ·
              refine ⟨30907562252183588047684669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 164840332011645802920984901 30907562252183588047684669)
              ·
                refine ⟨11590335844568845517881751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30907562252183588047684669 11590335844568845517881751)
                ·
                  refine ⟨17385503766853268276822627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11590335844568845517881751 17385503766853268276822627)
                  ·
                    refine ⟨26078255650279902415233941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17385503766853268276822627 26078255650279902415233941)
                    ·
                      refine ⟨1222418233606870425714091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26078255650279902415233941 1222418233606870425714091)
                      ·
                        rfl

theorem cell23_2380651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 6].length) (baseStart_2380651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2380651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2380651 prefixEnd_2380651 := by exact prefixLift 2380651
  have htrace : WordTrace (prefixWord ++ tailWord_2380651) baseStart_2380651 baseEnd_2380651 := by
    simpa [prefixWord, tailWord_2380651, baseEnd_2380651] using wordTrace_append hprefix tailTrace_2380651
  have hstable : (prefixWord ++ tailWord_2380651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380651).length < 2 ^ (prefixWord ++ tailWord_2380651).sum := by decide
  have hdescent : baseEnd_2380651 < baseStart_2380651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380675 : List Nat := [1, 1, 1, 3, 4, 1, 3, 3, 1, 2, 3]
def baseStart_2380675 : Nat := 118140960795 + 2380675 * 2 ^ 59
def prefixEnd_2380675 : Nat := 4983230072969 + 3 ^ 40 * 2380675 * 2
def baseEnd_2380675 : Nat := 1222430557142578331813981

theorem tailTrace_2380675 : CollatzResearch.WordTrace tailWord_2380675 prefixEnd_2380675 1222430557142578331813981 := by
  unfold tailWord_2380675
  simp only [CollatzResearch.WordTrace]
  refine ⟨86830350650228536765071479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57886900433485691176714319 86830350650228536765071479)
  ·
    refine ⟨130245525975342805147607219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86830350650228536765071479 130245525975342805147607219)
    ·
      refine ⟨195368288963014207721410829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130245525975342805147607219 195368288963014207721410829)
      ·
        refine ⟨73263108361130327895529061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 195368288963014207721410829 73263108361130327895529061)
        ·
          refine ⟨13736832817711936480411699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73263108361130327895529061 13736832817711936480411699)
          ·
            refine ⟨20605249226567904720617549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13736832817711936480411699 20605249226567904720617549)
            ·
              refine ⟨7726968459962964270231581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20605249226567904720617549 7726968459962964270231581)
              ·
                refine ⟨2897613172486111601336843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7726968459962964270231581 2897613172486111601336843)
                ·
                  refine ⟨4346419758729167402005265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2897613172486111601336843 4346419758729167402005265)
                  ·
                    refine ⟨3259814819046875551503949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4346419758729167402005265 3259814819046875551503949)
                    ·
                      refine ⟨1222430557142578331813981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3259814819046875551503949 1222430557142578331813981)
                      ·
                        rfl

theorem cell23_2380675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 3, 1, 2, 3].length) (baseStart_2380675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2380675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2380675 prefixEnd_2380675 := by exact prefixLift 2380675
  have htrace : WordTrace (prefixWord ++ tailWord_2380675) baseStart_2380675 baseEnd_2380675 := by
    simpa [prefixWord, tailWord_2380675, baseEnd_2380675] using wordTrace_append hprefix tailTrace_2380675
  have hstable : (prefixWord ++ tailWord_2380675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380675).length < 2 ^ (prefixWord ++ tailWord_2380675).sum := by decide
  have hdescent : baseEnd_2380675 < baseStart_2380675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380682 : List Nat := [3, 1, 2, 4, 1, 1, 3, 2, 2, 4]
def baseStart_2380682 : Nat := 118140960795 + 2380682 * 2 ^ 59
def prefixEnd_2380682 : Nat := 4983230072969 + 3 ^ 40 * 2380682 * 2
def baseEnd_2380682 : Nat := 407478050502386601475483

theorem tailTrace_2380682 : CollatzResearch.WordTrace tailWord_2380682 prefixEnd_2380682 407478050502386601475483 := by
  unfold tailWord_2380682
  simp only [CollatzResearch.WordTrace]
  refine ⟨21707651490300794240144075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57887070640802117973717533 21707651490300794240144075)
  ·
    refine ⟨32561477235451191360216113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21707651490300794240144075 32561477235451191360216113)
    ·
      refine ⟨24421107926588393520162085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32561477235451191360216113 24421107926588393520162085)
      ·
        refine ⟨4578957736235323785030391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24421107926588393520162085 4578957736235323785030391)
        ·
          refine ⟨6868436604352985677545587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4578957736235323785030391 6868436604352985677545587)
          ·
            refine ⟨10302654906529478516318381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6868436604352985677545587 10302654906529478516318381)
            ·
              refine ⟨3863495589948554443619393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10302654906529478516318381 3863495589948554443619393)
              ·
                refine ⟨2897621692461415832714545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3863495589948554443619393 2897621692461415832714545)
                ·
                  refine ⟨2173216269346061874535909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2897621692461415832714545 2173216269346061874535909)
                  ·
                    refine ⟨407478050502386601475483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2173216269346061874535909 407478050502386601475483)
                    ·
                      rfl

theorem cell23_2380682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 2, 2, 4].length) (baseStart_2380682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2380682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2380682 prefixEnd_2380682 := by exact prefixLift 2380682
  have htrace : WordTrace (prefixWord ++ tailWord_2380682) baseStart_2380682 baseEnd_2380682 := by
    simpa [prefixWord, tailWord_2380682, baseEnd_2380682] using wordTrace_append hprefix tailTrace_2380682
  have hstable : (prefixWord ++ tailWord_2380682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380682).length < 2 ^ (prefixWord ++ tailWord_2380682).sum := by decide
  have hdescent : baseEnd_2380682 < baseStart_2380682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380691 : List Nat := [1, 1, 1, 2, 1, 2, 1, 5, 2, 7]
def baseStart_2380691 : Nat := 118140960795 + 2380691 * 2 ^ 59
def prefixEnd_2380691 : Nat := 4983230072969 + 3 ^ 40 * 2380691 * 2
def baseEnd_2380691 : Nat := 407479590944350089737969

theorem tailTrace_2380691 : CollatzResearch.WordTrace tailWord_2380691 prefixEnd_2380691 407479590944350089737969 := by
  unfold tailWord_2380691
  simp only [CollatzResearch.WordTrace]
  refine ⟨86830934218170571497653927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57887289478780380998435951 86830934218170571497653927)
  ·
    refine ⟨130246401327255857246480891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86830934218170571497653927 130246401327255857246480891)
    ·
      refine ⟨195369601990883785869721337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130246401327255857246480891 195369601990883785869721337)
      ·
        refine ⟨146527201493162839402291003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195369601990883785869721337 146527201493162839402291003)
        ·
          refine ⟨219790802239744259103436505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146527201493162839402291003 219790802239744259103436505)
          ·
            refine ⟨164843101679808194327577379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 219790802239744259103436505 164843101679808194327577379)
            ·
              refine ⟨247264652519712291491366069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164843101679808194327577379 247264652519712291491366069)
              ·
                refine ⟨23181061173723027327315569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 247264652519712291491366069 23181061173723027327315569)
                ·
                  refine ⟨17385795880292270495486677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23181061173723027327315569 17385795880292270495486677)
                  ·
                    refine ⟨407479590944350089737969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17385795880292270495486677 407479590944350089737969)
                    ·
                      rfl

theorem cell23_2380691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 7].length) (baseStart_2380691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2380691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2380691 prefixEnd_2380691 := by exact prefixLift 2380691
  have htrace : WordTrace (prefixWord ++ tailWord_2380691) baseStart_2380691 baseEnd_2380691 := by
    simpa [prefixWord, tailWord_2380691, baseEnd_2380691] using wordTrace_append hprefix tailTrace_2380691
  have hstable : (prefixWord ++ tailWord_2380691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380691).length < 2 ^ (prefixWord ++ tailWord_2380691).sum := by decide
  have hdescent : baseEnd_2380691 < baseStart_2380691 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380726 : List Nat := [5, 1, 4, 1, 1, 1, 2, 1, 1, 1, 5]
def baseStart_2380726 : Nat := 118140960795 + 2380726 * 2 ^ 59
def prefixEnd_2380726 : Nat := 4983230072969 + 3 ^ 40 * 2380726 * 2
def baseEnd_2380726 : Nat := 1222456744655957632276247

theorem tailTrace_2380726 : CollatzResearch.WordTrace tailWord_2380726 prefixEnd_2380726 1222456744655957632276247 := by
  unfold tailWord_2380726
  simp only [CollatzResearch.WordTrace]
  refine ⟨5427013173315235779698627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57888140515362514983452021 5427013173315235779698627)
  ·
    refine ⟨8140519759972853669547941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5427013173315235779698627 8140519759972853669547941)
    ·
      refine ⟨1526347454994910063040239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8140519759972853669547941 1526347454994910063040239)
      ·
        refine ⟨2289521182492365094560359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1526347454994910063040239 2289521182492365094560359)
        ·
          refine ⟨3434281773738547641840539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2289521182492365094560359 3434281773738547641840539)
          ·
            refine ⟨5151422660607821462760809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3434281773738547641840539 5151422660607821462760809)
            ·
              refine ⟨3863566995455866097070607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5151422660607821462760809 3863566995455866097070607)
              ·
                refine ⟨5795350493183799145605911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3863566995455866097070607 5795350493183799145605911)
                ·
                  refine ⟨8693025739775698718408867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5795350493183799145605911 8693025739775698718408867)
                  ·
                    refine ⟨13039538609663548077613301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8693025739775698718408867 13039538609663548077613301)
                    ·
                      refine ⟨1222456744655957632276247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13039538609663548077613301 1222456744655957632276247)
                      ·
                        rfl

theorem cell23_2380726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_2380726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2380726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2380726 prefixEnd_2380726 := by exact prefixLift 2380726
  have htrace : WordTrace (prefixWord ++ tailWord_2380726) baseStart_2380726 baseEnd_2380726 := by
    simpa [prefixWord, tailWord_2380726, baseEnd_2380726] using wordTrace_append hprefix tailTrace_2380726
  have hstable : (prefixWord ++ tailWord_2380726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380726).length < 2 ^ (prefixWord ++ tailWord_2380726).sum := by decide
  have hdescent : baseEnd_2380726 < baseStart_2380726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380740 : List Nat := [2, 3, 3, 3, 1, 1, 3, 2, 1, 2, 2]
def baseStart_2380740 : Nat := 118140960795 + 2380740 * 2 ^ 59
def prefixEnd_2380740 : Nat := 4983230072969 + 3 ^ 40 * 2380740 * 2
def baseEnd_2380740 : Nat := 1222463933385120577501183

theorem tailTrace_2380740 : CollatzResearch.WordTrace tailWord_2380740 prefixEnd_2380740 1222463933385120577501183 := by
  unfold tailWord_2380740
  simp only [CollatzResearch.WordTrace]
  refine ⟨43416360697496526433093837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57888480929995368577458449 43416360697496526433093837)
  ·
    refine ⟨16281135261561197412410189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43416360697496526433093837 16281135261561197412410189)
    ·
      refine ⟨6105425723085449029653821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16281135261561197412410189 6105425723085449029653821)
      ·
        refine ⟨2289534646157043386120183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6105425723085449029653821 2289534646157043386120183)
        ·
          refine ⟨3434301969235565079180275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2289534646157043386120183 3434301969235565079180275)
          ·
            refine ⟨5151452953853347618770413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3434301969235565079180275 5151452953853347618770413)
            ·
              refine ⟨1931794857695005357038905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5151452953853347618770413 1931794857695005357038905)
              ·
                refine ⟨1448846143271254017779179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1931794857695005357038905 1448846143271254017779179)
                ·
                  refine ⟨2173269214906881026668769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1448846143271254017779179 2173269214906881026668769)
                  ·
                    refine ⟨1629951911180160770001577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2173269214906881026668769 1629951911180160770001577)
                    ·
                      refine ⟨1222463933385120577501183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1629951911180160770001577 1222463933385120577501183)
                      ·
                        rfl

theorem cell23_2380740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_2380740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2380740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2380740 prefixEnd_2380740 := by exact prefixLift 2380740
  have htrace : WordTrace (prefixWord ++ tailWord_2380740) baseStart_2380740 baseEnd_2380740 := by
    simpa [prefixWord, tailWord_2380740, baseEnd_2380740] using wordTrace_append hprefix tailTrace_2380740
  have hstable : (prefixWord ++ tailWord_2380740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380740).length < 2 ^ (prefixWord ++ tailWord_2380740).sum := by decide
  have hdescent : baseEnd_2380740 < baseStart_2380740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380748 : List Nat := [2, 2, 1, 4, 1, 1, 1, 2, 1, 3, 5]
def baseStart_2380748 : Nat := 118140960795 + 2380748 * 2 ^ 59
def prefixEnd_2380748 : Nat := 4983230072969 + 3 ^ 40 * 2380748 * 2
def baseEnd_2380748 : Nat := 1222468041230356546201145

theorem tailTrace_2380748 : CollatzResearch.WordTrace tailWord_2380748 prefixEnd_2380748 1222468041230356546201145 := by
  unfold tailWord_2380748
  simp only [CollatzResearch.WordTrace]
  refine ⟨43416506589482035116239449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57888675452642713488319265 43416506589482035116239449)
  ·
    refine ⟨32562379942111526337179587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43416506589482035116239449 32562379942111526337179587)
    ·
      refine ⟨48843569913167289505769381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32562379942111526337179587 48843569913167289505769381)
      ·
        refine ⟨9158169358718866782331759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48843569913167289505769381 9158169358718866782331759)
        ·
          refine ⟨13737254038078300173497639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9158169358718866782331759 13737254038078300173497639)
          ·
            refine ⟨20605881057117450260246459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13737254038078300173497639 20605881057117450260246459)
            ·
              refine ⟨30908821585676175390369689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20605881057117450260246459 30908821585676175390369689)
              ·
                refine ⟨23181616189257131542777267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30908821585676175390369689 23181616189257131542777267)
                ·
                  refine ⟨34772424283885697314165901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23181616189257131542777267 34772424283885697314165901)
                  ·
                    refine ⟨13039659106457136492812213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34772424283885697314165901 13039659106457136492812213)
                    ·
                      refine ⟨1222468041230356546201145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13039659106457136492812213 1222468041230356546201145)
                      ·
                        rfl

theorem cell23_2380748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_2380748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2380748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2380748 prefixEnd_2380748 := by exact prefixLift 2380748
  have htrace : WordTrace (prefixWord ++ tailWord_2380748) baseStart_2380748 baseEnd_2380748 := by
    simpa [prefixWord, tailWord_2380748, baseEnd_2380748] using wordTrace_append hprefix tailTrace_2380748
  have hstable : (prefixWord ++ tailWord_2380748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380748).length < 2 ^ (prefixWord ++ tailWord_2380748).sum := by decide
  have hdescent : baseEnd_2380748 < baseStart_2380748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380756 : List Nat := [2, 4, 1, 2, 1, 4, 2, 1, 2, 1, 3]
def baseStart_2380756 : Nat := 118140960795 + 2380756 * 2 ^ 59
def prefixEnd_2380756 : Nat := 4983230072969 + 3 ^ 40 * 2380756 * 2
def baseEnd_2380756 : Nat := 1222472149075592514901109

theorem tailTrace_2380756 : CollatzResearch.WordTrace tailWord_2380756 prefixEnd_2380756 1222472149075592514901109 := by
  unfold tailWord_2380756
  simp only [CollatzResearch.WordTrace]
  refine ⟨43416652481467543799385061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57888869975290058399180081 43416652481467543799385061)
  ·
    refine ⟨8140622340275164462384699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43416652481467543799385061 8140622340275164462384699)
    ·
      refine ⟨12210933510412746693577049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8140622340275164462384699 12210933510412746693577049)
      ·
        refine ⟨9158200132809560020182787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12210933510412746693577049 9158200132809560020182787)
        ·
          refine ⟨13737300199214340030274181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9158200132809560020182787 13737300199214340030274181)
          ·
            refine ⟨2575743787352688755676409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13737300199214340030274181 2575743787352688755676409)
            ·
              refine ⟨1931807840514516566757307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2575743787352688755676409 1931807840514516566757307)
              ·
                refine ⟨2897711760771774850135961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1931807840514516566757307 2897711760771774850135961)
                ·
                  refine ⟨2173283820578831137601971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2897711760771774850135961 2173283820578831137601971)
                  ·
                    refine ⟨3259925730868246706402957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2173283820578831137601971 3259925730868246706402957)
                    ·
                      refine ⟨1222472149075592514901109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3259925730868246706402957 1222472149075592514901109)
                      ·
                        rfl

theorem cell23_2380756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_2380756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2380756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2380756 prefixEnd_2380756 := by exact prefixLift 2380756
  have htrace : WordTrace (prefixWord ++ tailWord_2380756) baseStart_2380756 baseEnd_2380756 := by
    simpa [prefixWord, tailWord_2380756, baseEnd_2380756] using wordTrace_append hprefix tailTrace_2380756
  have hstable : (prefixWord ++ tailWord_2380756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380756).length < 2 ^ (prefixWord ++ tailWord_2380756).sum := by decide
  have hdescent : baseEnd_2380756 < baseStart_2380756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380765 : List Nat := [1, 4, 3, 1, 2, 1, 1, 2, 2, 1, 5]
def baseStart_2380765 : Nat := 118140960795 + 2380765 * 2 ^ 59
def prefixEnd_2380765 : Nat := 4983230072969 + 3 ^ 40 * 2380765 * 2
def baseEnd_2380765 : Nat := 1222476770401482979688567

theorem tailTrace_2380765 : CollatzResearch.WordTrace tailWord_2380765 prefixEnd_2380765 1222476770401482979688567 := by
  unfold tailWord_2380765
  simp only [CollatzResearch.WordTrace]
  refine ⟨86833633219902482135847749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57889088813268321423898499 86833633219902482135847749)
  ·
    refine ⟨16281306228731715400471453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86833633219902482135847749 16281306228731715400471453)
    ·
      refine ⟨6105489835774393275176795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16281306228731715400471453 6105489835774393275176795)
      ·
        refine ⟨9158234753661589912765193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6105489835774393275176795 9158234753661589912765193)
        ·
          refine ⟨6868676065246192434573895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9158234753661589912765193 6868676065246192434573895)
          ·
            refine ⟨10303014097869288651860843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6868676065246192434573895 10303014097869288651860843)
            ·
              refine ⟨15454521146803932977791265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10303014097869288651860843 15454521146803932977791265)
              ·
                refine ⟨11590890860102949733343449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15454521146803932977791265 11590890860102949733343449)
                ·
                  refine ⟨8693168145077212300007587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11590890860102949733343449 8693168145077212300007587)
                  ·
                    refine ⟨13039752217615818450011381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8693168145077212300007587 13039752217615818450011381)
                    ·
                      refine ⟨1222476770401482979688567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13039752217615818450011381 1222476770401482979688567)
                      ·
                        rfl

theorem cell23_2380765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_2380765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2380765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2380765 prefixEnd_2380765 := by exact prefixLift 2380765
  have htrace : WordTrace (prefixWord ++ tailWord_2380765) baseStart_2380765 baseEnd_2380765 := by
    simpa [prefixWord, tailWord_2380765, baseEnd_2380765] using wordTrace_append hprefix tailTrace_2380765
  have hstable : (prefixWord ++ tailWord_2380765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380765).length < 2 ^ (prefixWord ++ tailWord_2380765).sum := by decide
  have hdescent : baseEnd_2380765 < baseStart_2380765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380805 : List Nat := [1, 3, 1, 1, 2, 3, 1, 1, 1, 7, 2]
def baseStart_2380805 : Nat := 118140960795 + 2380805 * 2 ^ 59
def prefixEnd_2380805 : Nat := 4983230072969 + 3 ^ 40 * 2380805 * 2
def baseEnd_2380805 : Nat := 1222497309627662823188383

theorem tailTrace_2380805 : CollatzResearch.WordTrace tailWord_2380805 prefixEnd_2380805 1222497309627662823188383 := by
  unfold tailWord_2380805
  simp only [CollatzResearch.WordTrace]
  refine ⟨86835092139757568967303869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57890061426505045978202579 86835092139757568967303869)
  ·
    refine ⟨32563159552409088362738951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86835092139757568967303869 32563159552409088362738951)
    ·
      refine ⟨48844739328613632544108427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32563159552409088362738951 48844739328613632544108427)
      ·
        refine ⟨73267108992920448816162641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48844739328613632544108427 73267108992920448816162641)
        ·
          refine ⟨54950331744690336612121981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73267108992920448816162641 54950331744690336612121981)
          ·
            refine ⟨20606374404258876229545743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54950331744690336612121981 20606374404258876229545743)
            ·
              refine ⟨30909561606388314344318615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20606374404258876229545743 30909561606388314344318615)
              ·
                refine ⟨46364342409582471516477923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30909561606388314344318615 46364342409582471516477923)
                ·
                  refine ⟨69546513614373707274716885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46364342409582471516477923 69546513614373707274716885)
                  ·
                    refine ⟨1629996412836883764251177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 69546513614373707274716885 1629996412836883764251177)
                    ·
                      refine ⟨1222497309627662823188383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1629996412836883764251177 1222497309627662823188383)
                      ·
                        rfl

theorem cell23_2380805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 7, 2].length) (baseStart_2380805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2380805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2380805 prefixEnd_2380805 := by exact prefixLift 2380805
  have htrace : WordTrace (prefixWord ++ tailWord_2380805) baseStart_2380805 baseEnd_2380805 := by
    simpa [prefixWord, tailWord_2380805, baseEnd_2380805] using wordTrace_append hprefix tailTrace_2380805
  have hstable : (prefixWord ++ tailWord_2380805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380805).length < 2 ^ (prefixWord ++ tailWord_2380805).sum := by decide
  have hdescent : baseEnd_2380805 < baseStart_2380805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380832 : List Nat := [2, 1, 1, 7, 1, 1, 1, 1, 1, 7]
def baseStart_2380832 : Nat := 118140960795 + 2380832 * 2 ^ 59
def prefixEnd_2380832 : Nat := 4983230072969 + 3 ^ 40 * 2380832 * 2
def baseEnd_2380832 : Nat := 407503724535111405850253

theorem tailTrace_2380832 : CollatzResearch.WordTrace tailWord_2380832 prefixEnd_2380832 407503724535111405850253 := by
  unfold tailWord_2380832
  simp only [CollatzResearch.WordTrace]
  refine ⟨43418038455329876289268375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57890717940439835052357833 43418038455329876289268375)
  ·
    refine ⟨65127057682994814433902563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43418038455329876289268375 65127057682994814433902563)
    ·
      refine ⟨97690586524492221650853845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65127057682994814433902563 97690586524492221650853845)
      ·
        refine ⟨2289623121667786444941887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 97690586524492221650853845 2289623121667786444941887)
        ·
          refine ⟨3434434682501679667412831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2289623121667786444941887 3434434682501679667412831)
          ·
            refine ⟨5151652023752519501119247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3434434682501679667412831 5151652023752519501119247)
            ·
              refine ⟨7727478035628779251678871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5151652023752519501119247 7727478035628779251678871)
              ·
                refine ⟨11591217053443168877518307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7727478035628779251678871 11591217053443168877518307)
                ·
                  refine ⟨17386825580164753316277461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11591217053443168877518307 17386825580164753316277461)
                  ·
                    refine ⟨407503724535111405850253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17386825580164753316277461 407503724535111405850253)
                    ·
                      rfl

theorem cell23_2380832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 1, 7].length) (baseStart_2380832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2380832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2380832 prefixEnd_2380832 := by exact prefixLift 2380832
  have htrace : WordTrace (prefixWord ++ tailWord_2380832) baseStart_2380832 baseEnd_2380832 := by
    simpa [prefixWord, tailWord_2380832, baseEnd_2380832] using wordTrace_append hprefix tailTrace_2380832
  have hstable : (prefixWord ++ tailWord_2380832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380832).length < 2 ^ (prefixWord ++ tailWord_2380832).sum := by decide
  have hdescent : baseEnd_2380832 < baseStart_2380832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380835 : List Nat := [1, 1, 1, 4, 3, 3, 1, 1, 1, 3, 4]
def baseStart_2380835 : Nat := 118140960795 + 2380835 * 2 ^ 59
def prefixEnd_2380835 : Nat := 4983230072969 + 3 ^ 40 * 2380835 * 2
def baseEnd_2380835 : Nat := 1222512714047297705813245

theorem tailTrace_2380835 : CollatzResearch.WordTrace tailWord_2380835 prefixEnd_2380835 1222512714047297705813245 := by
  unfold tailWord_2380835
  simp only [CollatzResearch.WordTrace]
  refine ⟨86836186329648884090895959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57890790886432589393930639 86836186329648884090895959)
  ·
    refine ⟨130254279494473326136343939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86836186329648884090895959 130254279494473326136343939)
    ·
      refine ⟨195381419241709989204515909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130254279494473326136343939 195381419241709989204515909)
      ·
        refine ⟨36634016107820622975846733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 195381419241709989204515909 36634016107820622975846733)
        ·
          refine ⟨13737756040432733615942525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36634016107820622975846733 13737756040432733615942525)
          ·
            refine ⟨5151658515162275105978447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13737756040432733615942525 5151658515162275105978447)
            ·
              refine ⟨7727487772743412658967671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5151658515162275105978447 7727487772743412658967671)
              ·
                refine ⟨11591231659115118988451507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7727487772743412658967671 11591231659115118988451507)
                ·
                  refine ⟨17386847488672678482677261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11591231659115118988451507 17386847488672678482677261)
                  ·
                    refine ⟨6520067808252254431003973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17386847488672678482677261 6520067808252254431003973)
                    ·
                      refine ⟨1222512714047297705813245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6520067808252254431003973 1222512714047297705813245)
                      ·
                        rfl

theorem cell23_2380835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_2380835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2380835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2380835 prefixEnd_2380835 := by exact prefixLift 2380835
  have htrace : WordTrace (prefixWord ++ tailWord_2380835) baseStart_2380835 baseEnd_2380835 := by
    simpa [prefixWord, tailWord_2380835, baseEnd_2380835] using wordTrace_append hprefix tailTrace_2380835
  have hstable : (prefixWord ++ tailWord_2380835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380835).length < 2 ^ (prefixWord ++ tailWord_2380835).sum := by decide
  have hdescent : baseEnd_2380835 < baseStart_2380835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380848 : List Nat := [2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 6]
def baseStart_2380848 : Nat := 118140960795 + 2380848 * 2 ^ 59
def prefixEnd_2380848 : Nat := 4983230072969 + 3 ^ 40 * 2380848 * 2
def baseEnd_2380848 : Nat := 1222519389295806154950685

theorem tailTrace_2380848 : CollatzResearch.WordTrace tailWord_2380848 prefixEnd_2380848 1222519389295806154950685 := by
  unfold tailWord_2380848
  simp only [CollatzResearch.WordTrace]
  refine ⟨43418330239300893655559599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57891106985734524874079465 43418330239300893655559599)
  ·
    refine ⟨65127495358951340483339399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43418330239300893655559599 65127495358951340483339399)
    ·
      refine ⟨97691243038427010725009099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65127495358951340483339399 97691243038427010725009099)
      ·
        refine ⟨146536864557640516087513649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97691243038427010725009099 146536864557640516087513649)
        ·
          refine ⟨109902648418230387065635237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146536864557640516087513649 109902648418230387065635237)
          ·
            refine ⟨20606746578418197574806607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109902648418230387065635237 20606746578418197574806607)
            ·
              refine ⟨30910119867627296362209911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20606746578418197574806607 30910119867627296362209911)
              ·
                refine ⟨46365179801440944543314867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30910119867627296362209911 46365179801440944543314867)
                ·
                  refine ⟨69547769702161416814972301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46365179801440944543314867 69547769702161416814972301)
                  ·
                    refine ⟨26080413638310531305614613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 69547769702161416814972301 26080413638310531305614613)
                    ·
                      refine ⟨1222519389295806154950685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26080413638310531305614613 1222519389295806154950685)
                      ·
                        rfl

theorem cell23_2380848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 6].length) (baseStart_2380848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2380848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2380848 prefixEnd_2380848 := by exact prefixLift 2380848
  have htrace : WordTrace (prefixWord ++ tailWord_2380848) baseStart_2380848 baseEnd_2380848 := by
    simpa [prefixWord, tailWord_2380848, baseEnd_2380848] using wordTrace_append hprefix tailTrace_2380848
  have hstable : (prefixWord ++ tailWord_2380848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380848).length < 2 ^ (prefixWord ++ tailWord_2380848).sum := by decide
  have hdescent : baseEnd_2380848 < baseStart_2380848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380855 : List Nat := [1, 1, 3, 1, 2, 2, 1, 3, 4, 2, 3]
def baseStart_2380855 : Nat := 118140960795 + 2380855 * 2 ^ 59
def prefixEnd_2380855 : Nat := 4983230072969 + 3 ^ 40 * 2380855 * 2
def baseEnd_2380855 : Nat := 1222522983660387627563153

theorem tailTrace_2380855 : CollatzResearch.WordTrace tailWord_2380855 prefixEnd_2380855 1222522983660387627563153 := by
  unfold tailWord_2380855
  simp only [CollatzResearch.WordTrace]
  refine ⟨86836915789576427506624019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57891277193050951671082679 86836915789576427506624019)
  ·
    refine ⟨130255373684364641259936029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86836915789576427506624019 130255373684364641259936029)
    ·
      refine ⟨48845765131636740472476011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130255373684364641259936029 48845765131636740472476011)
      ·
        refine ⟨73268647697455110708714017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48845765131636740472476011 73268647697455110708714017)
        ·
          refine ⟨54951485773091333031535513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73268647697455110708714017 54951485773091333031535513)
          ·
            refine ⟨41213614329818499773651635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54951485773091333031535513 41213614329818499773651635)
            ·
              refine ⟨61820421494727749660477453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41213614329818499773651635 61820421494727749660477453)
              ·
                refine ⟨23182658060522906122679045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61820421494727749660477453 23182658060522906122679045)
                ·
                  refine ⟨4346748386348044898002321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23182658060522906122679045 4346748386348044898002321)
                  ·
                    refine ⟨3260061289761033673501741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4346748386348044898002321 3260061289761033673501741)
                    ·
                      refine ⟨1222522983660387627563153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3260061289761033673501741 1222522983660387627563153)
                      ·
                        rfl

theorem cell23_2380855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 4, 2, 3].length) (baseStart_2380855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2380855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2380855 prefixEnd_2380855 := by exact prefixLift 2380855
  have htrace : WordTrace (prefixWord ++ tailWord_2380855) baseStart_2380855 baseEnd_2380855 := by
    simpa [prefixWord, tailWord_2380855, baseEnd_2380855] using wordTrace_append hprefix tailTrace_2380855
  have hstable : (prefixWord ++ tailWord_2380855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380855).length < 2 ^ (prefixWord ++ tailWord_2380855).sum := by decide
  have hdescent : baseEnd_2380855 < baseStart_2380855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380885 : List Nat := [1, 3, 2, 2, 1, 2, 1, 1, 2, 5, 3]
def baseStart_2380885 : Nat := 118140960795 + 2380885 * 2 ^ 59
def prefixEnd_2380885 : Nat := 4983230072969 + 3 ^ 40 * 2380885 * 2
def baseEnd_2380885 : Nat := 1222538388080022510188015

theorem tailTrace_2380885 : CollatzResearch.WordTrace tailWord_2380885 prefixEnd_2380885 1222538388080022510188015 := by
  unfold tailWord_2380885
  simp only [CollatzResearch.WordTrace]
  refine ⟨86838009979467742630216109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57892006652978495086810739 86838009979467742630216109)
  ·
    refine ⟨32564253742300403486331041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86838009979467742630216109 32564253742300403486331041)
    ·
      refine ⟨24423190306725302614748281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32564253742300403486331041 24423190306725302614748281)
      ·
        refine ⟨18317392730043976961061211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24423190306725302614748281 18317392730043976961061211)
        ·
          refine ⟨27476089095065965441591817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18317392730043976961061211 27476089095065965441591817)
          ·
            refine ⟨20607066821299474081193863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27476089095065965441591817 20607066821299474081193863)
            ·
              refine ⟨30910600231949211121790795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20607066821299474081193863 30910600231949211121790795)
              ·
                refine ⟨46365900347923816682686193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30910600231949211121790795 46365900347923816682686193)
                ·
                  refine ⟨34774425260942862512014645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46365900347923816682686193 34774425260942862512014645)
                  ·
                    refine ⟨3260102368213393360501373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34774425260942862512014645 3260102368213393360501373)
                    ·
                      refine ⟨1222538388080022510188015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3260102368213393360501373 1222538388080022510188015)
                      ·
                        rfl

theorem cell23_2380885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_2380885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2380885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2380885 prefixEnd_2380885 := by exact prefixLift 2380885
  have htrace : WordTrace (prefixWord ++ tailWord_2380885) baseStart_2380885 baseEnd_2380885 := by
    simpa [prefixWord, tailWord_2380885, baseEnd_2380885] using wordTrace_append hprefix tailTrace_2380885
  have hstable : (prefixWord ++ tailWord_2380885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380885).length < 2 ^ (prefixWord ++ tailWord_2380885).sum := by decide
  have hdescent : baseEnd_2380885 < baseStart_2380885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380935 : List Nat := [1, 1, 4, 2, 1, 1, 1, 5, 1, 6]
def baseStart_2380935 : Nat := 118140960795 + 2380935 * 2 ^ 59
def prefixEnd_2380935 : Nat := 4983230072969 + 3 ^ 40 * 2380935 * 2
def baseEnd_2380935 : Nat := 407521354037582438187595

theorem tailTrace_2380935 : CollatzResearch.WordTrace tailWord_2380935 prefixEnd_2380935 407521354037582438187595 := by
  unfold tailWord_2380935
  simp only [CollatzResearch.WordTrace]
  refine ⟨86839833629286601169536259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57893222419524400779690839 86839833629286601169536259)
  ·
    refine ⟨130259750443929901754304389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86839833629286601169536259 130259750443929901754304389)
    ·
      refine ⟨24423703208236856578932073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130259750443929901754304389 24423703208236856578932073)
      ·
        refine ⟨18317777406177642434199055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24423703208236856578932073 18317777406177642434199055)
        ·
          refine ⟨27476666109266463651298583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18317777406177642434199055 27476666109266463651298583)
          ·
            refine ⟨41214999163899695476947875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27476666109266463651298583 41214999163899695476947875)
            ·
              refine ⟨61822498745849543215421813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41214999163899695476947875 61822498745849543215421813)
              ·
                refine ⟨5795859257423394676445795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61822498745849543215421813 5795859257423394676445795)
                ·
                  refine ⟨8693788886135092014668693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5795859257423394676445795 8693788886135092014668693)
                  ·
                    refine ⟨407521354037582438187595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8693788886135092014668693 407521354037582438187595)
                    ·
                      rfl

theorem cell23_2380935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 6].length) (baseStart_2380935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2380935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2380935 prefixEnd_2380935 := by exact prefixLift 2380935
  have htrace : WordTrace (prefixWord ++ tailWord_2380935) baseStart_2380935 baseEnd_2380935 := by
    simpa [prefixWord, tailWord_2380935, baseEnd_2380935] using wordTrace_append hprefix tailTrace_2380935
  have hstable : (prefixWord ++ tailWord_2380935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380935).length < 2 ^ (prefixWord ++ tailWord_2380935).sum := by decide
  have hdescent : baseEnd_2380935 < baseStart_2380935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380946 : List Nat := [3, 2, 3, 1, 1, 3, 2, 1, 2, 3, 2]
def baseStart_2380946 : Nat := 118140960795 + 2380946 * 2 ^ 59
def prefixEnd_2380946 : Nat := 4983230072969 + 3 ^ 40 * 2380946 * 2
def baseEnd_2380946 : Nat := 1222569710399946771525235

theorem tailTrace_2380946 : CollatzResearch.WordTrace tailWord_2380946 prefixEnd_2380946 1222569710399946771525235 := by
  unfold tailWord_2380946
  simp only [CollatzResearch.WordTrace]
  refine ⟨21710058708061687512046673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57893489888164500032124461 21710058708061687512046673)
  ·
    refine ⟨16282544031046265634035005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21710058708061687512046673 16282544031046265634035005)
    ·
      refine ⟨6105954011642349612763127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16282544031046265634035005 6105954011642349612763127)
      ·
        refine ⟨9158931017463524419144691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6105954011642349612763127 9158931017463524419144691)
        ·
          refine ⟨13738396526195286628717037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9158931017463524419144691 13738396526195286628717037)
          ·
            refine ⟨5151898697323232485768889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13738396526195286628717037 5151898697323232485768889)
            ·
              refine ⟨3863924022992424364326667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5151898697323232485768889 3863924022992424364326667)
              ·
                refine ⟨5795886034488636546490001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3863924022992424364326667 5795886034488636546490001)
                ·
                  refine ⟨4346914525866477409867501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5795886034488636546490001 4346914525866477409867501)
                  ·
                    refine ⟨1630092947199929028700313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4346914525866477409867501 1630092947199929028700313)
                    ·
                      refine ⟨1222569710399946771525235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1630092947199929028700313 1222569710399946771525235)
                      ·
                        rfl

theorem cell23_2380946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_2380946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2380946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2380946 prefixEnd_2380946 := by exact prefixLift 2380946
  have htrace : WordTrace (prefixWord ++ tailWord_2380946) baseStart_2380946 baseEnd_2380946 := by
    simpa [prefixWord, tailWord_2380946, baseEnd_2380946] using wordTrace_append hprefix tailTrace_2380946
  have hstable : (prefixWord ++ tailWord_2380946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380946).length < 2 ^ (prefixWord ++ tailWord_2380946).sum := by decide
  have hdescent : baseEnd_2380946 < baseStart_2380946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380952 : List Nat := [2, 1, 2, 4, 2, 2, 1, 2, 1, 6]
def baseStart_2380952 : Nat := 118140960795 + 2380952 * 2 ^ 59
def prefixEnd_2380952 : Nat := 4983230072969 + 3 ^ 40 * 2380952 * 2
def baseEnd_2380952 : Nat := 407524263761291249350069

theorem tailTrace_2380952 : CollatzResearch.WordTrace tailWord_2380952 prefixEnd_2380952 407524263761291249350069 := by
  unfold tailWord_2380952
  simp only [CollatzResearch.WordTrace]
  refine ⟨43420226835112506536452555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57893635780150008715270073 43420226835112506536452555)
  ·
    refine ⟨65130340252668759804678833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43420226835112506536452555 65130340252668759804678833)
    ·
      refine ⟨48847755189501569853509125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65130340252668759804678833 48847755189501569853509125)
      ·
        refine ⟨9158954098031544347532961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48847755189501569853509125 9158954098031544347532961)
        ·
          refine ⟨6869215573523658260649721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9158954098031544347532961 6869215573523658260649721)
          ·
            refine ⟨5151911680142743695487291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6869215573523658260649721 5151911680142743695487291)
            ·
              refine ⟨7727867520214115543230937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5151911680142743695487291 7727867520214115543230937)
              ·
                refine ⟨5795900640160586657423203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7727867520214115543230937 5795900640160586657423203)
                ·
                  refine ⟨8693850960240879986134805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5795900640160586657423203 8693850960240879986134805)
                  ·
                    refine ⟨407524263761291249350069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8693850960240879986134805 407524263761291249350069)
                    ·
                      rfl

theorem cell23_2380952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 1, 6].length) (baseStart_2380952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2380952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2380952 prefixEnd_2380952 := by exact prefixLift 2380952
  have htrace : WordTrace (prefixWord ++ tailWord_2380952) baseStart_2380952 baseEnd_2380952 := by
    simpa [prefixWord, tailWord_2380952, baseEnd_2380952] using wordTrace_append hprefix tailTrace_2380952
  have hstable : (prefixWord ++ tailWord_2380952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380952).length < 2 ^ (prefixWord ++ tailWord_2380952).sum := by decide
  have hdescent : baseEnd_2380952 < baseStart_2380952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380970 : List Nat := [3, 1, 5, 1, 1, 1, 4, 2, 1, 1, 3]
def baseStart_2380970 : Nat := 118140960795 + 2380970 * 2 ^ 59
def prefixEnd_2380970 : Nat := 4983230072969 + 3 ^ 40 * 2380970 * 2
def baseEnd_2380970 : Nat := 1222582033935654677625125

theorem tailTrace_2380970 : CollatzResearch.WordTrace tailWord_2380970 prefixEnd_2380970 1222582033935654677625125 := by
  unfold tailWord_2380970
  simp only [CollatzResearch.WordTrace]
  refine ⟨21710277546039950536765091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57894073456106534764706909 21710277546039950536765091)
  ·
    refine ⟨32565416319059925805147637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21710277546039950536765091 32565416319059925805147637)
    ·
      refine ⟨3053007779911868044232591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32565416319059925805147637 3053007779911868044232591)
      ·
        refine ⟨4579511669867802066348887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3053007779911868044232591 4579511669867802066348887)
        ·
          refine ⟨6869267504801703099523331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4579511669867802066348887 6869267504801703099523331)
          ·
            refine ⟨10303901257202554649284997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6869267504801703099523331 10303901257202554649284997)
            ·
              refine ⟨1931981485725478996740937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10303901257202554649284997 1931981485725478996740937)
              ·
                refine ⟨1448986114294109247555703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1931981485725478996740937 1448986114294109247555703)
                ·
                  refine ⟨2173479171441163871333555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1448986114294109247555703 2173479171441163871333555)
                  ·
                    refine ⟨3260218757161745807000333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2173479171441163871333555 3260218757161745807000333)
                    ·
                      refine ⟨1222582033935654677625125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3260218757161745807000333 1222582033935654677625125)
                      ·
                        rfl

theorem cell23_2380970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_2380970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2380970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2380970 prefixEnd_2380970 := by exact prefixLift 2380970
  have htrace : WordTrace (prefixWord ++ tailWord_2380970) baseStart_2380970 baseEnd_2380970 := by
    simpa [prefixWord, tailWord_2380970, baseEnd_2380970] using wordTrace_append hprefix tailTrace_2380970
  have hstable : (prefixWord ++ tailWord_2380970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380970).length < 2 ^ (prefixWord ++ tailWord_2380970).sum := by decide
  have hdescent : baseEnd_2380970 < baseStart_2380970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380976 : List Nat := [2, 1, 1, 1, 2, 1, 2, 8, 1, 2, 2]
def baseStart_2380976 : Nat := 118140960795 + 2380976 * 2 ^ 59
def prefixEnd_2380976 : Nat := 4983230072969 + 3 ^ 40 * 2380976 * 2
def baseEnd_2380976 : Nat := 1222585114819581654150097

theorem tailTrace_2380976 : CollatzResearch.WordTrace tailWord_2380976 prefixEnd_2380976 1222585114819581654150097 := by
  unfold tailWord_2380976
  simp only [CollatzResearch.WordTrace]
  refine ⟨43420664511069032585889391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57894219348092043447852521 43420664511069032585889391)
  ·
    refine ⟨65130996766603548878834087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43420664511069032585889391 65130996766603548878834087)
    ·
      refine ⟨97696495149905323318251131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65130996766603548878834087 97696495149905323318251131)
      ·
        refine ⟨146544742724857984977376697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97696495149905323318251131 146544742724857984977376697)
        ·
          refine ⟨109908557043643488733032523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146544742724857984977376697 109908557043643488733032523)
          ·
            refine ⟨164862835565465233099548785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109908557043643488733032523 164862835565465233099548785)
            ·
              refine ⟨123647126674098924824661589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164862835565465233099548785 123647126674098924824661589)
              ·
                refine ⟨1448989765712096775289003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 123647126674098924824661589 1448989765712096775289003)
                ·
                  refine ⟨2173484648568145162933505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1448989765712096775289003 2173484648568145162933505)
                  ·
                    refine ⟨1630113486426108872200129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2173484648568145162933505 1630113486426108872200129)
                    ·
                      refine ⟨1222585114819581654150097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1630113486426108872200129 1222585114819581654150097)
                      ·
                        rfl

theorem cell23_2380976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 8, 1, 2, 2].length) (baseStart_2380976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2380976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2380976 prefixEnd_2380976 := by exact prefixLift 2380976
  have htrace : WordTrace (prefixWord ++ tailWord_2380976) baseStart_2380976 baseEnd_2380976 := by
    simpa [prefixWord, tailWord_2380976, baseEnd_2380976] using wordTrace_append hprefix tailTrace_2380976
  have hstable : (prefixWord ++ tailWord_2380976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380976).length < 2 ^ (prefixWord ++ tailWord_2380976).sum := by decide
  have hdescent : baseEnd_2380976 < baseStart_2380976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380993 : List Nat := [1, 2, 6, 1, 1, 2, 1, 2, 3, 2, 2]
def baseStart_2380993 : Nat := 118140960795 + 2380993 * 2 ^ 59
def prefixEnd_2380993 : Nat := 4983230072969 + 3 ^ 40 * 2380993 * 2
def baseEnd_2380993 : Nat := 1222593843990708087637519

theorem tailTrace_2380993 : CollatzResearch.WordTrace tailWord_2380993 prefixEnd_2380993 1222593843990708087637519 := by
  unfold tailWord_2380993
  simp only [CollatzResearch.WordTrace]
  refine ⟨86841949063076477075147633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57894632708717651383431755 86841949063076477075147633)
  ·
    refine ⟨65131461797307357806360725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86841949063076477075147633 65131461797307357806360725)
    ·
      refine ⟨3053037271748782397173159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 65131461797307357806360725 3053037271748782397173159)
      ·
        refine ⟨4579555907623173595759739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3053037271748782397173159 4579555907623173595759739)
        ·
          refine ⟨6869333861434760393639609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4579555907623173595759739 6869333861434760393639609)
          ·
            refine ⟨5152000396076070295229707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6869333861434760393639609 5152000396076070295229707)
            ·
              refine ⟨7728000594114105442844561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5152000396076070295229707 7728000594114105442844561)
              ·
                refine ⟨5796000445585579082133421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7728000594114105442844561 5796000445585579082133421)
                ·
                  refine ⟨2173500167094592155800033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5796000445585579082133421 2173500167094592155800033)
                  ·
                    refine ⟨1630125125320944116850025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2173500167094592155800033 1630125125320944116850025)
                    ·
                      refine ⟨1222593843990708087637519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1630125125320944116850025 1222593843990708087637519)
                      ·
                        rfl

theorem cell23_2380993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_2380993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2380993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2380993 prefixEnd_2380993 := by exact prefixLift 2380993
  have htrace : WordTrace (prefixWord ++ tailWord_2380993) baseStart_2380993 baseEnd_2380993 := by
    simpa [prefixWord, tailWord_2380993, baseEnd_2380993] using wordTrace_append hprefix tailTrace_2380993
  have hstable : (prefixWord ++ tailWord_2380993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380993).length < 2 ^ (prefixWord ++ tailWord_2380993).sum := by decide
  have hdescent : baseEnd_2380993 < baseStart_2380993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381013 : List Nat := [1, 3, 2, 4, 1, 3, 2, 1, 1, 2, 3]
def baseStart_2381013 : Nat := 118140960795 + 2381013 * 2 ^ 59
def prefixEnd_2381013 : Nat := 4983230072969 + 3 ^ 40 * 2381013 * 2
def baseEnd_2381013 : Nat := 1222604113603798009387427

theorem tailTrace_2381013 : CollatzResearch.WordTrace tailWord_2381013 prefixEnd_2381013 1222604113603798009387427 := by
  unfold tailWord_2381013
  simp only [CollatzResearch.WordTrace]
  refine ⟨86842678523004020490875693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57895119015336013660583795 86842678523004020490875693)
  ·
    refine ⟨32566004446126507684078385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86842678523004020490875693 32566004446126507684078385)
    ·
      refine ⟨24424503334594880763058789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32566004446126507684078385 24424503334594880763058789)
      ·
        refine ⟨4579594375236540143073523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24424503334594880763058789 4579594375236540143073523)
        ·
          refine ⟨6869391562854810214610285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4579594375236540143073523 6869391562854810214610285)
          ·
            refine ⟨2576021836070553830478857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6869391562854810214610285 2576021836070553830478857)
            ·
              refine ⟨1932016377052915372859143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2576021836070553830478857 1932016377052915372859143)
              ·
                refine ⟨2898024565579373059288715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1932016377052915372859143 2898024565579373059288715)
                ·
                  refine ⟨4347036848369059588933073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2898024565579373059288715 4347036848369059588933073)
                  ·
                    refine ⟨3260277636276794691699805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4347036848369059588933073 3260277636276794691699805)
                    ·
                      refine ⟨1222604113603798009387427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3260277636276794691699805 1222604113603798009387427)
                      ·
                        rfl

theorem cell23_2381013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_2381013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2381013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2381013 prefixEnd_2381013 := by exact prefixLift 2381013
  have htrace : WordTrace (prefixWord ++ tailWord_2381013) baseStart_2381013 baseEnd_2381013 := by
    simpa [prefixWord, tailWord_2381013, baseEnd_2381013] using wordTrace_append hprefix tailTrace_2381013
  have hstable : (prefixWord ++ tailWord_2381013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381013).length < 2 ^ (prefixWord ++ tailWord_2381013).sum := by decide
  have hdescent : baseEnd_2381013 < baseStart_2381013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381075 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 6]
def baseStart_2381075 : Nat := 118140960795 + 2381075 * 2 ^ 59
def prefixEnd_2381075 : Nat := 4983230072969 + 3 ^ 40 * 2381075 * 2
def baseEnd_2381075 : Nat := 1222635949404376766812141

theorem tailTrace_2381075 : CollatzResearch.WordTrace tailWord_2381075 prefixEnd_2381075 1222635949404376766812141 := by
  unfold tailWord_2381075
  simp only [CollatzResearch.WordTrace]
  refine ⟨86844939848779405079632679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57896626565852936719755119 86844939848779405079632679)
  ·
    refine ⟨130267409773169107619449019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86844939848779405079632679 130267409773169107619449019)
    ·
      refine ⟨195401114659753661429173529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130267409773169107619449019 195401114659753661429173529)
      ·
        refine ⟨146550835994815246071880147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195401114659753661429173529 146550835994815246071880147)
        ·
          refine ⟨219826253992222869107820221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146550835994815246071880147 219826253992222869107820221)
          ·
            refine ⟨82434845247083575915432583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 219826253992222869107820221 82434845247083575915432583)
            ·
              refine ⟨123652267870625363873148875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82434845247083575915432583 123652267870625363873148875)
              ·
                refine ⟨185478401805938045809723313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123652267870625363873148875 185478401805938045809723313)
                ·
                  refine ⟨139108801354453534357292485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 185478401805938045809723313 139108801354453534357292485)
                  ·
                    refine ⟨26082900253960037691992341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 139108801354453534357292485 26082900253960037691992341)
                    ·
                      refine ⟨1222635949404376766812141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26082900253960037691992341 1222635949404376766812141)
                      ·
                        rfl

theorem cell23_2381075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 6].length) (baseStart_2381075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2381075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2381075 prefixEnd_2381075 := by exact prefixLift 2381075
  have htrace : WordTrace (prefixWord ++ tailWord_2381075) baseStart_2381075 baseEnd_2381075 := by
    simpa [prefixWord, tailWord_2381075, baseEnd_2381075] using wordTrace_append hprefix tailTrace_2381075
  have hstable : (prefixWord ++ tailWord_2381075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381075).length < 2 ^ (prefixWord ++ tailWord_2381075).sum := by decide
  have hdescent : baseEnd_2381075 < baseStart_2381075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381119 : List Nat := [1, 1, 2, 2, 4, 3, 2, 1, 2, 5]
def baseStart_2381119 : Nat := 118140960795 + 2381119 * 2 ^ 59
def prefixEnd_2381119 : Nat := 4983230072969 + 3 ^ 40 * 2381119 * 2
def baseEnd_2381119 : Nat := 407552847517724864887313

theorem tailTrace_2381119 : CollatzResearch.WordTrace tailWord_2381119 prefixEnd_2381119 407552847517724864887313 := by
  unfold tailWord_2381119
  simp only [CollatzResearch.WordTrace]
  refine ⟨86846544660620000594234411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57897696440413333729489607 86846544660620000594234411)
  ·
    refine ⟨130269816990930000891351617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86846544660620000594234411 130269816990930000891351617)
    ·
      refine ⟨97702362743197500668513713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130269816990930000891351617 97702362743197500668513713)
      ·
        refine ⟨73276772057398125501385285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97702362743197500668513713 73276772057398125501385285)
        ·
          refine ⟨13739394760762148531509741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73276772057398125501385285 13739394760762148531509741)
          ·
            refine ⟨5152273035285805699316153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13739394760762148531509741 5152273035285805699316153)
            ·
              refine ⟨3864204776464354274487115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5152273035285805699316153 3864204776464354274487115)
              ·
                refine ⟨5796307164696531411730673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3864204776464354274487115 5796307164696531411730673)
                ·
                  refine ⟨4347230373522398558798005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5796307164696531411730673 4347230373522398558798005)
                  ·
                    refine ⟨407552847517724864887313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4347230373522398558798005 407552847517724864887313)
                    ·
                      rfl

theorem cell23_2381119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 2, 5].length) (baseStart_2381119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2381119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2381119 prefixEnd_2381119 := by exact prefixLift 2381119
  have htrace : WordTrace (prefixWord ++ tailWord_2381119) baseStart_2381119 baseEnd_2381119 := by
    simpa [prefixWord, tailWord_2381119, baseEnd_2381119] using wordTrace_append hprefix tailTrace_2381119
  have hstable : (prefixWord ++ tailWord_2381119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381119).length < 2 ^ (prefixWord ++ tailWord_2381119).sum := by decide
  have hdescent : baseEnd_2381119 < baseStart_2381119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381139 : List Nat := [1, 1, 1, 2, 1, 1, 6, 2, 2, 4, 2]
def baseStart_2381139 : Nat := 118140960795 + 2381139 * 2 ^ 59
def prefixEnd_2381139 : Nat := 4983230072969 + 3 ^ 40 * 2381139 * 2
def baseEnd_2381139 : Nat := 1222668812166264516411847

theorem tailTrace_2381139 : CollatzResearch.WordTrace tailWord_2381139 prefixEnd_2381139 1222668812166264516411847 := by
  unfold tailWord_2381139
  simp only [CollatzResearch.WordTrace]
  refine ⟨86847274120547544009962471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57898182747031696006641647 86847274120547544009962471)
  ·
    refine ⟨130270911180821316014943707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86847274120547544009962471 130270911180821316014943707)
    ·
      refine ⟨195406366771231974022415561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130270911180821316014943707 195406366771231974022415561)
      ·
        refine ⟨146554775078423980516811671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195406366771231974022415561 146554775078423980516811671)
        ·
          refine ⟨219832162617635970775217507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146554775078423980516811671 219832162617635970775217507)
          ·
            refine ⟨329748243926453956162826261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219832162617635970775217507 329748243926453956162826261)
            ·
              refine ⟨15456948934052529195132481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 329748243926453956162826261 15456948934052529195132481)
              ·
                refine ⟨11592711700539396896349361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15456948934052529195132481 11592711700539396896349361)
                ·
                  refine ⟨8694533775404547672262021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11592711700539396896349361 8694533775404547672262021)
                  ·
                    refine ⟨1630225082888352688549129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8694533775404547672262021 1630225082888352688549129)
                    ·
                      refine ⟨1222668812166264516411847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1630225082888352688549129 1222668812166264516411847)
                      ·
                        rfl

theorem cell23_2381139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 4, 2].length) (baseStart_2381139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2381139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2381139 prefixEnd_2381139 := by exact prefixLift 2381139
  have htrace : WordTrace (prefixWord ++ tailWord_2381139) baseStart_2381139 baseEnd_2381139 := by
    simpa [prefixWord, tailWord_2381139, baseEnd_2381139] using wordTrace_append hprefix tailTrace_2381139
  have hstable : (prefixWord ++ tailWord_2381139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381139).length < 2 ^ (prefixWord ++ tailWord_2381139).sum := by decide
  have hdescent : baseEnd_2381139 < baseStart_2381139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381156 : List Nat := [2, 3, 1, 1, 3, 3, 1, 1, 2, 4, 2]
def baseStart_2381156 : Nat := 118140960795 + 2381156 * 2 ^ 59
def prefixEnd_2381156 : Nat := 4983230072969 + 3 ^ 40 * 2381156 * 2
def baseEnd_2381156 : Nat := 1222677541337390949899269

theorem tailTrace_2381156 : CollatzResearch.WordTrace tailWord_2381156 prefixEnd_2381156 1222677541337390949899269 := by
  unfold tailWord_2381156
  simp only [CollatzResearch.WordTrace]
  refine ⟨43423947080742977956665661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57898596107657303942220881 43423947080742977956665661)
  ·
    refine ⟨16283980155278616733749623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43423947080742977956665661 16283980155278616733749623)
    ·
      refine ⟨24425970232917925100624435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16283980155278616733749623 24425970232917925100624435)
      ·
        refine ⟨36638955349376887650936653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24425970232917925100624435 36638955349376887650936653)
        ·
          refine ⟨13739608256016332869101245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36638955349376887650936653 13739608256016332869101245)
          ·
            refine ⟨5152353096006124825912967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13739608256016332869101245 5152353096006124825912967)
            ·
              refine ⟨7728529644009187238869451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5152353096006124825912967 7728529644009187238869451)
              ·
                refine ⟨11592794466013780858304177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7728529644009187238869451 11592794466013780858304177)
                ·
                  refine ⟨8694595849510335643728133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11592794466013780858304177 8694595849510335643728133)
                  ·
                    refine ⟨1630236721783187933199025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8694595849510335643728133 1630236721783187933199025)
                    ·
                      refine ⟨1222677541337390949899269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1630236721783187933199025 1222677541337390949899269)
                      ·
                        rfl

theorem cell23_2381156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 2, 4, 2].length) (baseStart_2381156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2381156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2381156 prefixEnd_2381156 := by exact prefixLift 2381156
  have htrace : WordTrace (prefixWord ++ tailWord_2381156) baseStart_2381156 baseEnd_2381156 := by
    simpa [prefixWord, tailWord_2381156, baseEnd_2381156] using wordTrace_append hprefix tailTrace_2381156
  have hstable : (prefixWord ++ tailWord_2381156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381156).length < 2 ^ (prefixWord ++ tailWord_2381156).sum := by decide
  have hdescent : baseEnd_2381156 < baseStart_2381156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381173 : List Nat := [1, 3, 4, 1, 3, 2, 1, 1, 2, 1, 4]
def baseStart_2381173 : Nat := 118140960795 + 2381173 * 2 ^ 59
def prefixEnd_2381173 : Nat := 4983230072969 + 3 ^ 40 * 2381173 * 2
def baseEnd_2381173 : Nat := 1222686270508517383386691

theorem tailTrace_2381173 : CollatzResearch.WordTrace tailWord_2381173 prefixEnd_2381173 1222686270508517383386691 := by
  unfold tailWord_2381173
  simp only [CollatzResearch.WordTrace]
  refine ⟨86848514202424367816700173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57899009468282911877800115 86848514202424367816700173)
  ·
    refine ⟨32568192825909137931262565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86848514202424367816700173 32568192825909137931262565)
    ·
      refine ⟨6106536154857963362111731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32568192825909137931262565 6106536154857963362111731)
      ·
        refine ⟨9159804232286945043167597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6106536154857963362111731 9159804232286945043167597)
        ·
          refine ⟨3434926587107604391187849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9159804232286945043167597 3434926587107604391187849)
          ·
            refine ⟨2576194940330703293390887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3434926587107604391187849 2576194940330703293390887)
            ·
              refine ⟨3864292410496054940086331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2576194940330703293390887 3864292410496054940086331)
              ·
                refine ⟨5796438615744082410129497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3864292410496054940086331 5796438615744082410129497)
                ·
                  refine ⟨4347328961808061807597123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5796438615744082410129497 4347328961808061807597123)
                  ·
                    refine ⟨6520993442712092711395685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4347328961808061807597123 6520993442712092711395685)
                    ·
                      refine ⟨1222686270508517383386691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6520993442712092711395685 1222686270508517383386691)
                      ·
                        rfl

theorem cell23_2381173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_2381173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2381173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2381173 prefixEnd_2381173 := by exact prefixLift 2381173
  have htrace : WordTrace (prefixWord ++ tailWord_2381173) baseStart_2381173 baseEnd_2381173 := by
    simpa [prefixWord, tailWord_2381173, baseEnd_2381173] using wordTrace_append hprefix tailTrace_2381173
  have hstable : (prefixWord ++ tailWord_2381173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381173).length < 2 ^ (prefixWord ++ tailWord_2381173).sum := by decide
  have hdescent : baseEnd_2381173 < baseStart_2381173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381186 : List Nat := [3, 4, 2, 1, 1, 1, 1, 1, 2, 1, 6]
def baseStart_2381186 : Nat := 118140960795 + 2381186 * 2 ^ 59
def prefixEnd_2381186 : Nat := 4983230072969 + 3 ^ 40 * 2381186 * 2
def baseEnd_2381186 : Nat := 1222692945757025832524131

theorem tailTrace_2381186 : CollatzResearch.WordTrace tailWord_2381186 prefixEnd_2381186 1222692945757025832524131 := by
  unfold tailWord_2381186
  simp only [CollatzResearch.WordTrace]
  refine ⟨21712247087844317759230853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57899325567584847357948941 21712247087844317759230853)
  ·
    refine ⟨4071046328970809579855785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21712247087844317759230853 4071046328970809579855785)
    ·
      refine ⟨3053284746728107184891839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4071046328970809579855785 3053284746728107184891839)
      ·
        refine ⟨4579927120092160777337759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3053284746728107184891839 4579927120092160777337759)
        ·
          refine ⟨6869890680138241166006639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4579927120092160777337759 6869890680138241166006639)
          ·
            refine ⟨10304836020207361749009959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6869890680138241166006639 10304836020207361749009959)
            ·
              refine ⟨15457254030311042623514939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10304836020207361749009959 15457254030311042623514939)
              ·
                refine ⟨23185881045466563935272409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15457254030311042623514939 23185881045466563935272409)
                ·
                  refine ⟨17389410784099922951454307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23185881045466563935272409 17389410784099922951454307)
                  ·
                    refine ⟨26084116176149884427181461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17389410784099922951454307 26084116176149884427181461)
                    ·
                      refine ⟨1222692945757025832524131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26084116176149884427181461 1222692945757025832524131)
                      ·
                        rfl

theorem cell23_2381186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_2381186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2381186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2381186 prefixEnd_2381186 := by exact prefixLift 2381186
  have htrace : WordTrace (prefixWord ++ tailWord_2381186) baseStart_2381186 baseEnd_2381186 := by
    simpa [prefixWord, tailWord_2381186, baseEnd_2381186] using wordTrace_append hprefix tailTrace_2381186
  have hstable : (prefixWord ++ tailWord_2381186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381186).length < 2 ^ (prefixWord ++ tailWord_2381186).sum := by decide
  have hdescent : baseEnd_2381186 < baseStart_2381186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381239 : List Nat := [1, 1, 3, 1, 3, 2, 1, 1, 6, 4]
def baseStart_2381239 : Nat := 118140960795 + 2381239 * 2 ^ 59
def prefixEnd_2381239 : Nat := 4983230072969 + 3 ^ 40 * 2381239 * 2
def baseEnd_2381239 : Nat := 407573386743904708387129

theorem tailTrace_2381239 : CollatzResearch.WordTrace tailWord_2381239 prefixEnd_2381239 407573386743904708387129 := by
  unfold tailWord_2381239
  simp only [CollatzResearch.WordTrace]
  refine ⟨86850921420185261088602771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57900614280123507392401847 86850921420185261088602771)
  ·
    refine ⟨130276382130277891632904157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86850921420185261088602771 130276382130277891632904157)
    ·
      refine ⟨48853643298854209362339059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130276382130277891632904157 48853643298854209362339059)
      ·
        refine ⟨73280464948281314043508589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48853643298854209362339059 73280464948281314043508589)
        ·
          refine ⟨27480174355605492766315721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73280464948281314043508589 27480174355605492766315721)
          ·
            refine ⟨20610130766704119574736791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27480174355605492766315721 20610130766704119574736791)
            ·
              refine ⟨30915196150056179362105187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20610130766704119574736791 30915196150056179362105187)
              ·
                refine ⟨46372794225084269043157781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30915196150056179362105187 46372794225084269043157781)
                ·
                  refine ⟨2173724729300825111398021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 46372794225084269043157781 2173724729300825111398021)
                  ·
                    refine ⟨407573386743904708387129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2173724729300825111398021 407573386743904708387129)
                    ·
                      rfl

theorem cell23_2381239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 6, 4].length) (baseStart_2381239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2381239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2381239 prefixEnd_2381239 := by exact prefixLift 2381239
  have htrace : WordTrace (prefixWord ++ tailWord_2381239) baseStart_2381239 baseEnd_2381239 := by
    simpa [prefixWord, tailWord_2381239, baseEnd_2381239] using wordTrace_append hprefix tailTrace_2381239
  have hstable : (prefixWord ++ tailWord_2381239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381239).length < 2 ^ (prefixWord ++ tailWord_2381239).sum := by decide
  have hdescent : baseEnd_2381239 < baseStart_2381239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381256 : List Nat := [2, 1, 3, 1, 3, 1, 2, 4, 2, 4]
def baseStart_2381256 : Nat := 118140960795 + 2381256 * 2 ^ 59
def prefixEnd_2381256 : Nat := 4983230072969 + 3 ^ 40 * 2381256 * 2
def baseEnd_2381256 : Nat := 407576296467613519549603

theorem tailTrace_2381256 : CollatzResearch.WordTrace tailWord_2381256 prefixEnd_2381256 407576296467613519549603 := by
  unfold tailWord_2381256
  simp only [CollatzResearch.WordTrace]
  refine ⟨43425770730561836495985811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57901027640749115327981081 43425770730561836495985811)
  ·
    refine ⟨65138656095842754743978717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43425770730561836495985811 65138656095842754743978717)
    ·
      refine ⟨24426996035941033028992019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65138656095842754743978717 24426996035941033028992019)
      ·
        refine ⟨36640494053911549543488029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24426996035941033028992019 36640494053911549543488029)
        ·
          refine ⟨13740185270216831078808011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36640494053911549543488029 13740185270216831078808011)
          ·
            refine ⟨20610277905325246618212017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13740185270216831078808011 20610277905325246618212017)
            ·
              refine ⟨15457708428993934963659013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20610277905325246618212017 15457708428993934963659013)
              ·
                refine ⟨2898320330436362805686065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15457708428993934963659013 2898320330436362805686065)
                ·
                  refine ⟨2173740247827272104264549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2898320330436362805686065 2173740247827272104264549)
                  ·
                    refine ⟨407576296467613519549603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2173740247827272104264549 407576296467613519549603)
                    ·
                      rfl

theorem cell23_2381256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 4, 2, 4].length) (baseStart_2381256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2381256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2381256 prefixEnd_2381256 := by exact prefixLift 2381256
  have htrace : WordTrace (prefixWord ++ tailWord_2381256) baseStart_2381256 baseEnd_2381256 := by
    simpa [prefixWord, tailWord_2381256, baseEnd_2381256] using wordTrace_append hprefix tailTrace_2381256
  have hstable : (prefixWord ++ tailWord_2381256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381256).length < 2 ^ (prefixWord ++ tailWord_2381256).sum := by decide
  have hdescent : baseEnd_2381256 < baseStart_2381256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381263 : List Nat := [1, 1, 2, 1, 1, 4, 5, 1, 3, 2, 2]
def baseStart_2381263 : Nat := 118140960795 + 2381263 * 2 ^ 59
def prefixEnd_2381263 : Nat := 4983230072969 + 3 ^ 40 * 2381263 * 2
def baseEnd_2381263 : Nat := 1222732483767422031261277

theorem tailTrace_2381263 : CollatzResearch.WordTrace tailWord_2381263 prefixEnd_2381263 1222732483767422031261277 := by
  unfold tailWord_2381263
  simp only [CollatzResearch.WordTrace]
  refine ⟨86851796772098313187476443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57901197848065542124984295 86851796772098313187476443)
  ·
    refine ⟨130277695158147469781214665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86851796772098313187476443 130277695158147469781214665)
    ·
      refine ⟨97708271368610602335910999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130277695158147469781214665 97708271368610602335910999)
      ·
        refine ⟨146562407052915903503866499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97708271368610602335910999 146562407052915903503866499)
        ·
          refine ⟨219843610579373855255799749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146562407052915903503866499 219843610579373855255799749)
          ·
            refine ⟨41220676983632597860462453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 219843610579373855255799749 41220676983632597860462453)
            ·
              refine ⟨3864438467215556049418355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41220676983632597860462453 3864438467215556049418355)
              ·
                refine ⟨5796657700823334074127533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3864438467215556049418355 5796657700823334074127533)
                ·
                  refine ⟨2173746637808750277797825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5796657700823334074127533 2173746637808750277797825)
                  ·
                    refine ⟨1630309978356562708348369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2173746637808750277797825 1630309978356562708348369)
                    ·
                      refine ⟨1222732483767422031261277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1630309978356562708348369 1222732483767422031261277)
                      ·
                        rfl

theorem cell23_2381263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 3, 2, 2].length) (baseStart_2381263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2381263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2381263 prefixEnd_2381263 := by exact prefixLift 2381263
  have htrace : WordTrace (prefixWord ++ tailWord_2381263) baseStart_2381263 baseEnd_2381263 := by
    simpa [prefixWord, tailWord_2381263, baseEnd_2381263] using wordTrace_append hprefix tailTrace_2381263
  have hstable : (prefixWord ++ tailWord_2381263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381263).length < 2 ^ (prefixWord ++ tailWord_2381263).sum := by decide
  have hdescent : baseEnd_2381263 < baseStart_2381263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381269 : List Nat := [1, 3, 2, 3, 1, 1, 4, 8]
def baseStart_2381269 : Nat := 118140960795 + 2381269 * 2 ^ 59
def prefixEnd_2381269 : Nat := 4983230072969 + 3 ^ 40 * 2381269 * 2
def baseEnd_2381269 : Nat := 45286502394494407695787

theorem tailTrace_2381269 : CollatzResearch.WordTrace tailWord_2381269 prefixEnd_2381269 45286502394494407695787 := by
  unfold tailWord_2381269
  simp only [CollatzResearch.WordTrace]
  refine ⟨86852015610076576212194861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57901343740051050808129907 86852015610076576212194861)
  ·
    refine ⟨32569505853778716079573073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86852015610076576212194861 32569505853778716079573073)
    ·
      refine ⟨24427129390334037059679805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32569505853778716079573073 24427129390334037059679805)
      ·
        refine ⟨9160173521375263897379927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24427129390334037059679805 9160173521375263897379927)
        ·
          refine ⟨13740260282062895846069891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9160173521375263897379927 13740260282062895846069891)
          ·
            refine ⟨20610390423094343769104837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13740260282062895846069891 20610390423094343769104837)
            ·
              refine ⟨3864448204330189456707157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20610390423094343769104837 3864448204330189456707157)
              ·
                refine ⟨45286502394494407695787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3864448204330189456707157 45286502394494407695787)
                ·
                  rfl

theorem cell23_2381269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 8].length) (baseStart_2381269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2381269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2381269 prefixEnd_2381269 := by exact prefixLift 2381269
  have htrace : WordTrace (prefixWord ++ tailWord_2381269) baseStart_2381269 baseEnd_2381269 := by
    simpa [prefixWord, tailWord_2381269, baseEnd_2381269] using wordTrace_append hprefix tailTrace_2381269
  have hstable : (prefixWord ++ tailWord_2381269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381269).length < 2 ^ (prefixWord ++ tailWord_2381269).sum := by decide
  have hdescent : baseEnd_2381269 < baseStart_2381269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381273 : List Nat := [1, 2, 1, 2, 4, 2, 4, 1, 2, 4]
def baseStart_2381273 : Nat := 118140960795 + 2381273 * 2 ^ 59
def prefixEnd_2381273 : Nat := 4983230072969 + 3 ^ 40 * 2381273 * 2
def baseEnd_2381273 : Nat := 407579206191322330712077

theorem tailTrace_2381273 : CollatzResearch.WordTrace tailWord_2381273 prefixEnd_2381273 407579206191322330712077 := by
  unfold tailWord_2381273
  simp only [CollatzResearch.WordTrace]
  refine ⟨86852161502062084895340473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57901441001374723263560315 86852161502062084895340473)
  ·
    refine ⟨65139121126546563671505355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86852161502062084895340473 65139121126546563671505355)
    ·
      refine ⟨97708681689819845507258033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65139121126546563671505355 97708681689819845507258033)
      ·
        refine ⟨73281511267364884130443525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97708681689819845507258033 73281511267364884130443525)
        ·
          refine ⟨13740283362630915774458161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73281511267364884130443525 13740283362630915774458161)
          ·
            refine ⟨10305212521973186830843621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13740283362630915774458161 10305212521973186830843621)
            ·
              refine ⟨1932227347869972530783179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10305212521973186830843621 1932227347869972530783179)
              ·
                refine ⟨2898341021804958796174769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1932227347869972530783179 2898341021804958796174769)
                ·
                  refine ⟨2173755766353719097131077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2898341021804958796174769 2173755766353719097131077)
                  ·
                    refine ⟨407579206191322330712077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2173755766353719097131077 407579206191322330712077)
                    ·
                      rfl

theorem cell23_2381273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 1, 2, 4].length) (baseStart_2381273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2381273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2381273 prefixEnd_2381273 := by exact prefixLift 2381273
  have htrace : WordTrace (prefixWord ++ tailWord_2381273) baseStart_2381273 baseEnd_2381273 := by
    simpa [prefixWord, tailWord_2381273, baseEnd_2381273] using wordTrace_append hprefix tailTrace_2381273
  have hstable : (prefixWord ++ tailWord_2381273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381273).length < 2 ^ (prefixWord ++ tailWord_2381273).sum := by decide
  have hdescent : baseEnd_2381273 < baseStart_2381273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381283 : List Nat := [1, 1, 1, 6, 2, 1, 3, 2, 1, 2, 3]
def baseStart_2381283 : Nat := 118140960795 + 2381283 * 2 ^ 59
def prefixEnd_2381283 : Nat := 4983230072969 + 3 ^ 40 * 2381283 * 2
def baseEnd_2381283 : Nat := 1222742753380511953011185

theorem tailTrace_2381283 : CollatzResearch.WordTrace tailWord_2381283 prefixEnd_2381283 1222742753380511953011185 := by
  unfold tailWord_2381283
  simp only [CollatzResearch.WordTrace]
  refine ⟨86852526232025856603204503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57901684154683904402136335 86852526232025856603204503)
  ·
    refine ⟨130278789348038784904806755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86852526232025856603204503 130278789348038784904806755)
    ·
      refine ⟨195418184022058177357210133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130278789348038784904806755 195418184022058177357210133)
      ·
        refine ⟨9160227376033977063619225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 195418184022058177357210133 9160227376033977063619225)
        ·
          refine ⟨6870170532025482797714419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9160227376033977063619225 6870170532025482797714419)
          ·
            refine ⟨10305255798038224196571629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6870170532025482797714419 10305255798038224196571629)
            ·
              refine ⟨3864470924264334073714361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10305255798038224196571629 3864470924264334073714361)
              ·
                refine ⟨2898353193198250555285771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3864470924264334073714361 2898353193198250555285771)
                ·
                  refine ⟨4347529789797375832928657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2898353193198250555285771 4347529789797375832928657)
                  ·
                    refine ⟨3260647342348031874696493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4347529789797375832928657 3260647342348031874696493)
                    ·
                      refine ⟨1222742753380511953011185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3260647342348031874696493 1222742753380511953011185)
                      ·
                        rfl

theorem cell23_2381283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_2381283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2381283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2381283 prefixEnd_2381283 := by exact prefixLift 2381283
  have htrace : WordTrace (prefixWord ++ tailWord_2381283) baseStart_2381283 baseEnd_2381283 := by
    simpa [prefixWord, tailWord_2381283, baseEnd_2381283] using wordTrace_append hprefix tailTrace_2381283
  have hstable : (prefixWord ++ tailWord_2381283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381283).length < 2 ^ (prefixWord ++ tailWord_2381283).sum := by decide
  have hdescent : baseEnd_2381283 < baseStart_2381283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381293 : List Nat := [1, 5, 1, 3, 2, 1, 1, 2, 1, 2, 4]
def baseStart_2381293 : Nat := 118140960795 + 2381293 * 2 ^ 59
def prefixEnd_2381293 : Nat := 4983230072969 + 3 ^ 40 * 2381293 * 2
def baseEnd_2381293 : Nat := 1222747888187056913886139

theorem tailTrace_2381293 : CollatzResearch.WordTrace tailWord_2381293 prefixEnd_2381293 1222747888187056913886139 := by
  unfold tailWord_2381293
  simp only [CollatzResearch.WordTrace]
  refine ⟨86852890961989628311068533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57901927307993085540712355 86852890961989628311068533)
  ·
    refine ⟨8142458527686527654162675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 86852890961989628311068533 8142458527686527654162675)
    ·
      refine ⟨12213687791529791481244013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8142458527686527654162675 12213687791529791481244013)
      ·
        refine ⟨4580132921823671805466505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12213687791529791481244013 4580132921823671805466505)
        ·
          refine ⟨3435099691367753854099879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4580132921823671805466505 3435099691367753854099879)
          ·
            refine ⟨5152649537051630781149819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3435099691367753854099879 5152649537051630781149819)
            ·
              refine ⟨7728974305577446171724729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5152649537051630781149819 7728974305577446171724729)
              ·
                refine ⟨5796730729183084628793547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7728974305577446171724729 5796730729183084628793547)
                ·
                  refine ⟨8695096093774626943190321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5796730729183084628793547 8695096093774626943190321)
                  ·
                    refine ⟨6521322070330970207392741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8695096093774626943190321 6521322070330970207392741)
                    ·
                      refine ⟨1222747888187056913886139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6521322070330970207392741 1222747888187056913886139)
                      ·
                        rfl

theorem cell23_2381293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_2381293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2381293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2381293 prefixEnd_2381293 := by exact prefixLift 2381293
  have htrace : WordTrace (prefixWord ++ tailWord_2381293) baseStart_2381293 baseEnd_2381293 := by
    simpa [prefixWord, tailWord_2381293, baseEnd_2381293] using wordTrace_append hprefix tailTrace_2381293
  have hstable : (prefixWord ++ tailWord_2381293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381293).length < 2 ^ (prefixWord ++ tailWord_2381293).sum := by decide
  have hdescent : baseEnd_2381293 < baseStart_2381293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381296 : List Nat := [2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 3]
def baseStart_2381296 : Nat := 118140960795 + 2381296 * 2 ^ 59
def prefixEnd_2381296 : Nat := 4983230072969 + 3 ^ 40 * 2381296 * 2
def baseEnd_2381296 : Nat := 1222749428629020402148625

theorem tailTrace_2381296 : CollatzResearch.WordTrace tailWord_2381296 prefixEnd_2381296 1222749428629020402148625 := by
  unfold tailWord_2381296
  simp only [CollatzResearch.WordTrace]
  refine ⟨43426500190489379911713871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57902000253985839882285161 43426500190489379911713871)
  ·
    refine ⟨65139750285734069867570807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43426500190489379911713871 65139750285734069867570807)
    ·
      refine ⟨97709625428601104801356211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65139750285734069867570807 97709625428601104801356211)
      ·
        refine ⟨146564438142901657202034317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97709625428601104801356211 146564438142901657202034317)
        ·
          refine ⟨54961664303588121450762869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146564438142901657202034317 54961664303588121450762869)
          ·
            refine ⟨5152656028461386386009019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54961664303588121450762869 5152656028461386386009019)
            ·
              refine ⟨7728984042692079579013529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5152656028461386386009019 7728984042692079579013529)
              ·
                refine ⟨5796738032019059684260147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7728984042692079579013529 5796738032019059684260147)
                ·
                  refine ⟨8695107048028589526390221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5796738032019059684260147 8695107048028589526390221)
                  ·
                    refine ⟨3260665143010721072396333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8695107048028589526390221 3260665143010721072396333)
                    ·
                      refine ⟨1222749428629020402148625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3260665143010721072396333 1222749428629020402148625)
                      ·
                        rfl

theorem cell23_2381296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 3].length) (baseStart_2381296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2381296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2381296 prefixEnd_2381296 := by exact prefixLift 2381296
  have htrace : WordTrace (prefixWord ++ tailWord_2381296) baseStart_2381296 baseEnd_2381296 := by
    simpa [prefixWord, tailWord_2381296, baseEnd_2381296] using wordTrace_append hprefix tailTrace_2381296
  have hstable : (prefixWord ++ tailWord_2381296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381296).length < 2 ^ (prefixWord ++ tailWord_2381296).sum := by decide
  have hdescent : baseEnd_2381296 < baseStart_2381296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381314 : List Nat := [3, 4, 1, 2, 1, 2, 1, 4, 1, 2, 2]
def baseStart_2381314 : Nat := 118140960795 + 2381314 * 2 ^ 59
def prefixEnd_2381314 : Nat := 4983230072969 + 3 ^ 40 * 2381314 * 2
def baseEnd_2381314 : Nat := 1222758671280801331723543

theorem tailTrace_2381314 : CollatzResearch.WordTrace tailWord_2381314 prefixEnd_2381314 1222758671280801331723543 := by
  unfold tailWord_2381314
  simp only [CollatzResearch.WordTrace]
  refine ⟨21713414223728387224395749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57902437929942365931721997 21713414223728387224395749)
  ·
    refine ⟨4071265166949072604574203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21713414223728387224395749 4071265166949072604574203)
    ·
      refine ⟨6106897750423608906861305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4071265166949072604574203 6106897750423608906861305)
      ·
        refine ⟨4580173312817706680145979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6106897750423608906861305 4580173312817706680145979)
        ·
          refine ⟨6870259969226560020218969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4580173312817706680145979 6870259969226560020218969)
          ·
            refine ⟨5152694976919920015164227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6870259969226560020218969 5152694976919920015164227)
            ·
              refine ⟨7729042465379880022746341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5152694976919920015164227 7729042465379880022746341)
              ·
                refine ⟨1449195462258727504264939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7729042465379880022746341 1449195462258727504264939)
                ·
                  refine ⟨2173793193388091256397409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1449195462258727504264939 2173793193388091256397409)
                  ·
                    refine ⟨1630344895041068442298057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2173793193388091256397409 1630344895041068442298057)
                    ·
                      refine ⟨1222758671280801331723543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1630344895041068442298057 1222758671280801331723543)
                      ·
                        rfl

theorem cell23_2381314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_2381314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2381314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2381314 prefixEnd_2381314 := by exact prefixLift 2381314
  have htrace : WordTrace (prefixWord ++ tailWord_2381314) baseStart_2381314 baseEnd_2381314 := by
    simpa [prefixWord, tailWord_2381314, baseEnd_2381314] using wordTrace_append hprefix tailTrace_2381314
  have hstable : (prefixWord ++ tailWord_2381314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381314).length < 2 ^ (prefixWord ++ tailWord_2381314).sum := by decide
  have hdescent : baseEnd_2381314 < baseStart_2381314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381329 : List Nat := [1, 2, 2, 1, 1, 2, 5, 1, 2, 6]
def baseStart_2381329 : Nat := 118140960795 + 2381329 * 2 ^ 59
def prefixEnd_2381329 : Nat := 4983230072969 + 3 ^ 40 * 2381329 * 2
def baseEnd_2381329 : Nat := 407588791163539591011991

theorem tailTrace_2381329 : CollatzResearch.WordTrace tailWord_2381329 prefixEnd_2381329 407588791163539591011991 := by
  unfold tailWord_2381329
  simp only [CollatzResearch.WordTrace]
  refine ⟨86854203989859206459379041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57902802659906137639586027 86854203989859206459379041)
  ·
    refine ⟨65140652992394404844534281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86854203989859206459379041 65140652992394404844534281)
    ·
      refine ⟨48855489744295803633400711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65140652992394404844534281 48855489744295803633400711)
      ·
        refine ⟨73283234616443705450101067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48855489744295803633400711 73283234616443705450101067)
        ·
          refine ⟨109924851924665558175151601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73283234616443705450101067 109924851924665558175151601)
          ·
            refine ⟨82443638943499168631363701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109924851924665558175151601 82443638943499168631363701)
            ·
              refine ⟨7729091150953047059190347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82443638943499168631363701 7729091150953047059190347)
              ·
                refine ⟨11593636726429570588785521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7729091150953047059190347 11593636726429570588785521)
                ·
                  refine ⟨8695227544822177941589141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11593636726429570588785521 8695227544822177941589141)
                  ·
                    refine ⟨407588791163539591011991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8695227544822177941589141 407588791163539591011991)
                    ·
                      rfl

theorem cell23_2381329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 6].length) (baseStart_2381329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2381329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2381329 prefixEnd_2381329 := by exact prefixLift 2381329
  have htrace : WordTrace (prefixWord ++ tailWord_2381329) baseStart_2381329 baseEnd_2381329 := by
    simpa [prefixWord, tailWord_2381329, baseEnd_2381329] using wordTrace_append hprefix tailTrace_2381329
  have hstable : (prefixWord ++ tailWord_2381329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381329).length < 2 ^ (prefixWord ++ tailWord_2381329).sum := by decide
  have hdescent : baseEnd_2381329 < baseStart_2381329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381349 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 3, 4, 4]
def baseStart_2381349 : Nat := 118140960795 + 2381349 * 2 ^ 59
def prefixEnd_2381349 : Nat := 4983230072969 + 3 ^ 40 * 2381349 * 2
def baseEnd_2381349 : Nat := 1222776643103708694785881

theorem tailTrace_2381349 : CollatzResearch.WordTrace tailWord_2381349 prefixEnd_2381349 1222776643103708694785881 := by
  unfold tailWord_2381349
  simp only [CollatzResearch.WordTrace]
  refine ⟨86854933449786749875107101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57903288966524499916738067 86854933449786749875107101)
  ·
    refine ⟨32570600043670031203165163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86854933449786749875107101 32570600043670031203165163)
    ·
      refine ⟨48855900065505046804747745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32570600043670031203165163 48855900065505046804747745)
      ·
        refine ⟨36641925049128785103560809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48855900065505046804747745 36641925049128785103560809)
        ·
          refine ⟨27481443786846588827670607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36641925049128785103560809 27481443786846588827670607)
          ·
            refine ⟨41222165680269883241505911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27481443786846588827670607 41222165680269883241505911)
            ·
              refine ⟨61833248520404824862258867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41222165680269883241505911 61833248520404824862258867)
              ·
                refine ⟨92749872780607237293388301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61833248520404824862258867 92749872780607237293388301)
                ·
                  refine ⟨34781202292727713985020613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92749872780607237293388301 34781202292727713985020613)
                  ·
                    refine ⟨6521475429886446372191365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34781202292727713985020613 6521475429886446372191365)
                    ·
                      refine ⟨1222776643103708694785881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6521475429886446372191365 1222776643103708694785881)
                      ·
                        rfl

theorem cell23_2381349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_2381349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2381349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2381349 prefixEnd_2381349 := by exact prefixLift 2381349
  have htrace : WordTrace (prefixWord ++ tailWord_2381349) baseStart_2381349 baseEnd_2381349 := by
    simpa [prefixWord, tailWord_2381349, baseEnd_2381349] using wordTrace_append hprefix tailTrace_2381349
  have hstable : (prefixWord ++ tailWord_2381349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381349).length < 2 ^ (prefixWord ++ tailWord_2381349).sum := by decide
  have hdescent : baseEnd_2381349 < baseStart_2381349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381386 : List Nat := [3, 1, 2, 1, 1, 3, 1, 3, 2, 3, 3]
def baseStart_2381386 : Nat := 118140960795 + 2381386 * 2 ^ 59
def prefixEnd_2381386 : Nat := 4983230072969 + 3 ^ 40 * 2381386 * 2
def baseEnd_2381386 : Nat := 1222795641887925050023211

theorem tailTrace_2381386 : CollatzResearch.WordTrace tailWord_2381386 prefixEnd_2381386 1222795641887925050023211 := by
  unfold tailWord_2381386
  simp only [CollatzResearch.WordTrace]
  refine ⟨21714070737663176298551003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57904188633768470129469341 21714070737663176298551003)
  ·
    refine ⟨32571106106494764447826505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21714070737663176298551003 32571106106494764447826505)
    ·
      refine ⟨24428329579871073335869879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32571106106494764447826505 24428329579871073335869879)
      ·
        refine ⟨36642494369806610003804819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24428329579871073335869879 36642494369806610003804819)
        ·
          refine ⟨54963741554709915005707229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36642494369806610003804819 54963741554709915005707229)
          ·
            refine ⟨20611403083016218127140211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54963741554709915005707229 20611403083016218127140211)
            ·
              refine ⟨30917104624524327190710317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20611403083016218127140211 30917104624524327190710317)
              ·
                refine ⟨11593914234196622696516369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30917104624524327190710317 11593914234196622696516369)
                ·
                  refine ⟨8695435675647467022387277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11593914234196622696516369 8695435675647467022387277)
                  ·
                    refine ⟨3260788378367800133395229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8695435675647467022387277 3260788378367800133395229)
                    ·
                      refine ⟨1222795641887925050023211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3260788378367800133395229 1222795641887925050023211)
                      ·
                        rfl

theorem cell23_2381386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 2, 3, 3].length) (baseStart_2381386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2381386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2381386 prefixEnd_2381386 := by exact prefixLift 2381386
  have htrace : WordTrace (prefixWord ++ tailWord_2381386) baseStart_2381386 baseEnd_2381386 := by
    simpa [prefixWord, tailWord_2381386, baseEnd_2381386] using wordTrace_append hprefix tailTrace_2381386
  have hstable : (prefixWord ++ tailWord_2381386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381386).length < 2 ^ (prefixWord ++ tailWord_2381386).sum := by decide
  have hdescent : baseEnd_2381386 < baseStart_2381386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381439 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 6]
def baseStart_2381439 : Nat := 118140960795 + 2381439 * 2 ^ 59
def prefixEnd_2381439 : Nat := 4983230072969 + 3 ^ 40 * 2381439 * 2
def baseEnd_2381439 : Nat := 1222822856362613342660467

theorem tailTrace_2381439 : CollatzResearch.WordTrace tailWord_2381439 prefixEnd_2381439 1222822856362613342660467 := by
  unfold tailWord_2381439
  simp only [CollatzResearch.WordTrace]
  refine ⟨86858216019460695245883371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57905477346307130163922247 86858216019460695245883371)
  ·
    refine ⟨130287324029191042868825057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86858216019460695245883371 130287324029191042868825057)
    ·
      refine ⟨97715493021893282151618793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130287324029191042868825057 97715493021893282151618793)
      ·
        refine ⟨73286619766419961613714095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97715493021893282151618793 73286619766419961613714095)
        ·
          refine ⟨109929929649629942420571143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73286619766419961613714095 109929929649629942420571143)
          ·
            refine ⟨164894894474444913630856715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109929929649629942420571143 164894894474444913630856715)
            ·
              refine ⟨247342341711667370446285073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164894894474444913630856715 247342341711667370446285073)
              ·
                refine ⟨185506756283750527834713805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 247342341711667370446285073 185506756283750527834713805)
                ·
                  refine ⟨69565033606406447938017677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 185506756283750527834713805 69565033606406447938017677)
                  ·
                    refine ⟨26086887602402417976756629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 69565033606406447938017677 26086887602402417976756629)
                    ·
                      refine ⟨1222822856362613342660467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26086887602402417976756629 1222822856362613342660467)
                      ·
                        rfl

theorem cell23_2381439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 6].length) (baseStart_2381439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2381439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2381439 prefixEnd_2381439 := by exact prefixLift 2381439
  have htrace : WordTrace (prefixWord ++ tailWord_2381439) baseStart_2381439 baseEnd_2381439 := by
    simpa [prefixWord, tailWord_2381439, baseEnd_2381439] using wordTrace_append hprefix tailTrace_2381439
  have hstable : (prefixWord ++ tailWord_2381439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381439).length < 2 ^ (prefixWord ++ tailWord_2381439).sum := by decide
  have hdescent : baseEnd_2381439 < baseStart_2381439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381459 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 9]
def baseStart_2381459 : Nat := 118140960795 + 2381459 * 2 ^ 59
def prefixEnd_2381459 : Nat := 4983230072969 + 3 ^ 40 * 2381459 * 2
def baseEnd_2381459 : Nat := 1222833125975703264410375

theorem tailTrace_2381459 : CollatzResearch.WordTrace tailWord_2381459 prefixEnd_2381459 1222833125975703264410375 := by
  unfold tailWord_2381459
  simp only [CollatzResearch.WordTrace]
  refine ⟨86858945479388238661611431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57905963652925492441074287 86858945479388238661611431)
  ·
    refine ⟨130288418219082357992417147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86858945479388238661611431 130288418219082357992417147)
    ·
      refine ⟨195432627328623536988625721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130288418219082357992417147 195432627328623536988625721)
      ·
        refine ⟨146574470496467652741469291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195432627328623536988625721 146574470496467652741469291)
        ·
          refine ⟨219861705744701479112203937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146574470496467652741469291 219861705744701479112203937)
          ·
            refine ⟨164896279308526109334152953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 219861705744701479112203937 164896279308526109334152953)
            ·
              refine ⟨123672209481394582000614715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164896279308526109334152953 123672209481394582000614715)
              ·
                refine ⟨185508314222091873000922073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123672209481394582000614715 185508314222091873000922073)
                ·
                  refine ⟨139131235666568904750691555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 185508314222091873000922073 139131235666568904750691555)
                  ·
                    refine ⟨208696853499853357126037333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 139131235666568904750691555 208696853499853357126037333)
                    ·
                      refine ⟨1222833125975703264410375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 208696853499853357126037333 1222833125975703264410375)
                      ·
                        rfl

theorem cell23_2381459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 9].length) (baseStart_2381459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2381459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2381459 prefixEnd_2381459 := by exact prefixLift 2381459
  have htrace : WordTrace (prefixWord ++ tailWord_2381459) baseStart_2381459 baseEnd_2381459 := by
    simpa [prefixWord, tailWord_2381459, baseEnd_2381459] using wordTrace_append hprefix tailTrace_2381459
  have hstable : (prefixWord ++ tailWord_2381459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381459).length < 2 ^ (prefixWord ++ tailWord_2381459).sum := by decide
  have hdescent : baseEnd_2381459 < baseStart_2381459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381463 : List Nat := [1, 1, 3, 3, 2, 2, 1, 3, 2, 2, 3]
def baseStart_2381463 : Nat := 118140960795 + 2381463 * 2 ^ 59
def prefixEnd_2381463 : Nat := 4983230072969 + 3 ^ 40 * 2381463 * 2
def baseEnd_2381463 : Nat := 1222835179898321248760357

theorem tailTrace_2381463 : CollatzResearch.WordTrace tailWord_2381463 prefixEnd_2381463 1222835179898321248760357 := by
  unfold tailWord_2381463
  simp only [CollatzResearch.WordTrace]
  refine ⟨86859091371373747344757043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57906060914249164896504695 86859091371373747344757043)
  ·
    refine ⟨130288637057060621017135565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86859091371373747344757043 130288637057060621017135565)
    ·
      refine ⟨48858238896397732881425837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130288637057060621017135565 48858238896397732881425837)
      ·
        refine ⟨18321839586149149830534689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48858238896397732881425837 18321839586149149830534689)
        ·
          refine ⟨13741379689611862372901017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18321839586149149830534689 13741379689611862372901017)
          ·
            refine ⟨10306034767208896779675763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13741379689611862372901017 10306034767208896779675763)
            ·
              refine ⟨15459052150813345169513645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10306034767208896779675763 15459052150813345169513645)
              ·
                refine ⟨5797144556555004438567617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15459052150813345169513645 5797144556555004438567617)
                ·
                  refine ⟨4347858417416253328925713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5797144556555004438567617 4347858417416253328925713)
                  ·
                    refine ⟨3260893813062189996694285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4347858417416253328925713 3260893813062189996694285)
                    ·
                      refine ⟨1222835179898321248760357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3260893813062189996694285 1222835179898321248760357)
                      ·
                        rfl

theorem cell23_2381463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_2381463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2381463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2381463 prefixEnd_2381463 := by exact prefixLift 2381463
  have htrace : WordTrace (prefixWord ++ tailWord_2381463) baseStart_2381463 baseEnd_2381463 := by
    simpa [prefixWord, tailWord_2381463, baseEnd_2381463] using wordTrace_append hprefix tailTrace_2381463
  have hstable : (prefixWord ++ tailWord_2381463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381463).length < 2 ^ (prefixWord ++ tailWord_2381463).sum := by decide
  have hdescent : baseEnd_2381463 < baseStart_2381463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381503 : List Nat := [1, 1, 2, 2, 2, 3, 2, 2, 1, 5, 2]
def baseStart_2381503 : Nat := 118140960795 + 2381503 * 2 ^ 59
def prefixEnd_2381503 : Nat := 4983230072969 + 3 ^ 40 * 2381503 * 2
def baseEnd_2381503 : Nat := 1222855719124501092260173

theorem tailTrace_2381503 : CollatzResearch.WordTrace tailWord_2381503 prefixEnd_2381503 1222855719124501092260173 := by
  unfold tailWord_2381503
  simp only [CollatzResearch.WordTrace]
  refine ⟨86860550291228834176213163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57907033527485889450808775 86860550291228834176213163)
  ·
    refine ⟨130290825436843251264319745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86860550291228834176213163 130290825436843251264319745)
    ·
      refine ⟨97718119077632438448239809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130290825436843251264319745 97718119077632438448239809)
      ·
        refine ⟨73288589308224328836179857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97718119077632438448239809 73288589308224328836179857)
        ·
          refine ⟨54966441981168246627134893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73288589308224328836179857 54966441981168246627134893)
          ·
            refine ⟨20612415742938092485175585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54966441981168246627134893 20612415742938092485175585)
            ·
              refine ⟨15459311807203569363881689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20612415742938092485175585 15459311807203569363881689)
              ·
                refine ⟨11594483855402677022911267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15459311807203569363881689 11594483855402677022911267)
                ·
                  refine ⟨17391725783104015534366901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11594483855402677022911267 17391725783104015534366901)
                  ·
                    refine ⟨1630474292166001456346897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17391725783104015534366901 1630474292166001456346897)
                    ·
                      refine ⟨1222855719124501092260173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1630474292166001456346897 1222855719124501092260173)
                      ·
                        rfl

theorem cell23_2381503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 5, 2].length) (baseStart_2381503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2381503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2381503 prefixEnd_2381503 := by exact prefixLift 2381503
  have htrace : WordTrace (prefixWord ++ tailWord_2381503) baseStart_2381503 baseEnd_2381503 := by
    simpa [prefixWord, tailWord_2381503, baseEnd_2381503] using wordTrace_append hprefix tailTrace_2381503
  have hstable : (prefixWord ++ tailWord_2381503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381503).length < 2 ^ (prefixWord ++ tailWord_2381503).sum := by decide
  have hdescent : baseEnd_2381503 < baseStart_2381503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381527 : List Nat := [1, 1, 3, 2, 1, 3, 4, 3, 1, 1, 3]
def baseStart_2381527 : Nat := 118140960795 + 2381527 * 2 ^ 59
def prefixEnd_2381527 : Nat := 4983230072969 + 3 ^ 40 * 2381527 * 2
def baseEnd_2381527 : Nat := 1222868042660208998360063

theorem tailTrace_2381527 : CollatzResearch.WordTrace tailWord_2381527 prefixEnd_2381527 1222868042660208998360063 := by
  unfold tailWord_2381527
  simp only [CollatzResearch.WordTrace]
  refine ⟨86861425643141886275086835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57907617095427924183391223 86861425643141886275086835)
  ·
    refine ⟨130292138464712829412630253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86861425643141886275086835 130292138464712829412630253)
    ·
      refine ⟨48859551924267311029736345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130292138464712829412630253 48859551924267311029736345)
      ·
        refine ⟨36644663943200483272302259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48859551924267311029736345 36644663943200483272302259)
        ·
          refine ⟨54966995914800724908453389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36644663943200483272302259 54966995914800724908453389)
          ·
            refine ⟨20612623468050271840670021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54966995914800724908453389 20612623468050271840670021)
            ·
              refine ⟨3864866900259425970125629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20612623468050271840670021 3864866900259425970125629)
              ·
                refine ⟨1449325087597284738797111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3864866900259425970125629 1449325087597284738797111)
                ·
                  refine ⟨2173987631395927108195667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1449325087597284738797111 2173987631395927108195667)
                  ·
                    refine ⟨3260981447093890662293501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2173987631395927108195667 3260981447093890662293501)
                    ·
                      refine ⟨1222868042660208998360063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3260981447093890662293501 1222868042660208998360063)
                      ·
                        rfl

theorem cell23_2381527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 3, 1, 1, 3].length) (baseStart_2381527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2381527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2381527 prefixEnd_2381527 := by exact prefixLift 2381527
  have htrace : WordTrace (prefixWord ++ tailWord_2381527) baseStart_2381527 baseEnd_2381527 := by
    simpa [prefixWord, tailWord_2381527, baseEnd_2381527] using wordTrace_append hprefix tailTrace_2381527
  have hstable : (prefixWord ++ tailWord_2381527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381527).length < 2 ^ (prefixWord ++ tailWord_2381527).sum := by decide
  have hdescent : baseEnd_2381527 < baseStart_2381527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381530 : List Nat := [3, 1, 1, 2, 2, 3, 4, 1, 1, 5]
def baseStart_2381530 : Nat := 118140960795 + 2381530 * 2 ^ 59
def prefixEnd_2381530 : Nat := 4983230072969 + 3 ^ 40 * 2381530 * 2
def baseEnd_2381530 : Nat := 407623194367390828874183

theorem tailTrace_2381530 : CollatzResearch.WordTrace tailWord_2381530 prefixEnd_2381530 407623194367390828874183 := by
  unfold tailWord_2381530
  simp only [CollatzResearch.WordTrace]
  refine ⟨21715383765532754446861511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57907690041420678524964029 21715383765532754446861511)
  ·
    refine ⟨32573075648299131670292267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21715383765532754446861511 32573075648299131670292267)
    ·
      refine ⟨48859613472448697505438401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32573075648299131670292267 48859613472448697505438401)
      ·
        refine ⟨36644710104336523129078801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48859613472448697505438401 36644710104336523129078801)
        ·
          refine ⟨27483532578252392346809101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36644710104336523129078801 27483532578252392346809101)
          ·
            refine ⟨10306324716844647130053413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27483532578252392346809101 10306324716844647130053413)
            ·
              refine ⟨1932435884408371336885015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10306324716844647130053413 1932435884408371336885015)
              ·
                refine ⟨2898653826612557005327523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1932435884408371336885015 2898653826612557005327523)
                ·
                  refine ⟨4347980739918835507991285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2898653826612557005327523 4347980739918835507991285)
                  ·
                    refine ⟨407623194367390828874183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4347980739918835507991285 407623194367390828874183)
                    ·
                      rfl

theorem cell23_2381530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 1, 1, 5].length) (baseStart_2381530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2381530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2381530 prefixEnd_2381530 := by exact prefixLift 2381530
  have htrace : WordTrace (prefixWord ++ tailWord_2381530) baseStart_2381530 baseEnd_2381530 := by
    simpa [prefixWord, tailWord_2381530, baseEnd_2381530] using wordTrace_append hprefix tailTrace_2381530
  have hstable : (prefixWord ++ tailWord_2381530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381530).length < 2 ^ (prefixWord ++ tailWord_2381530).sum := by decide
  have hdescent : baseEnd_2381530 < baseStart_2381530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381553 : List Nat := [1, 2, 2, 2, 2, 4, 1, 2, 1, 1, 5]
def baseStart_2381553 : Nat := 118140960795 + 2381553 * 2 ^ 59
def prefixEnd_2381553 : Nat := 4983230072969 + 3 ^ 40 * 2381553 * 2
def baseEnd_2381553 : Nat := 1222881393157225896634943

theorem tailTrace_2381553 : CollatzResearch.WordTrace tailWord_2381553 prefixEnd_2381553 1222881393157225896634943 := by
  unfold tailWord_2381553
  simp only [CollatzResearch.WordTrace]
  refine ⟨86862373941047692715533313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57908249294031795143688875 86862373941047692715533313)
  ·
    refine ⟨65146780455785769536649985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86862373941047692715533313 65146780455785769536649985)
    ·
      refine ⟨48860085341839327152487489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65146780455785769536649985 48860085341839327152487489)
      ·
        refine ⟨36645064006379495364365617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48860085341839327152487489 36645064006379495364365617)
        ·
          refine ⟨27483798004784621523274213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36645064006379495364365617 27483798004784621523274213)
          ·
            refine ⟨5153212125897116535613915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27483798004784621523274213 5153212125897116535613915)
            ·
              refine ⟨7729818188845674803420873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5153212125897116535613915 7729818188845674803420873)
              ·
                refine ⟨5797363641634256102565655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7729818188845674803420873 5797363641634256102565655)
                ·
                  refine ⟨8696045462451384153848483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5797363641634256102565655 8696045462451384153848483)
                  ·
                    refine ⟨13044068193677076230772725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8696045462451384153848483 13044068193677076230772725)
                    ·
                      refine ⟨1222881393157225896634943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13044068193677076230772725 1222881393157225896634943)
                      ·
                        rfl

theorem cell23_2381553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_2381553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2381553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2381553 prefixEnd_2381553 := by exact prefixLift 2381553
  have htrace : WordTrace (prefixWord ++ tailWord_2381553) baseStart_2381553 baseEnd_2381553 := by
    simpa [prefixWord, tailWord_2381553, baseEnd_2381553] using wordTrace_append hprefix tailTrace_2381553
  have hstable : (prefixWord ++ tailWord_2381553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381553).length < 2 ^ (prefixWord ++ tailWord_2381553).sum := by decide
  have hdescent : baseEnd_2381553 < baseStart_2381553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381593 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 1, 9, 2]
def baseStart_2381593 : Nat := 118140960795 + 2381593 * 2 ^ 59
def prefixEnd_2381593 : Nat := 4983230072969 + 3 ^ 40 * 2381593 * 2
def baseEnd_2381593 : Nat := 1222901932383405740134759

theorem tailTrace_2381593 : CollatzResearch.WordTrace tailWord_2381593 prefixEnd_2381593 1222901932383405740134759 := by
  unfold tailWord_2381593
  simp only [CollatzResearch.WordTrace]
  refine ⟨86863832860902779546989433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57909221907268519697992955 86863832860902779546989433)
  ·
    refine ⟨65147874645677084660242075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86863832860902779546989433 65147874645677084660242075)
    ·
      refine ⟨97721811968515626990363113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65147874645677084660242075 97721811968515626990363113)
      ·
        refine ⟨73291358976386720242772335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97721811968515626990363113 73291358976386720242772335)
        ·
          refine ⟨109937038464580080364158503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73291358976386720242772335 109937038464580080364158503)
          ·
            refine ⟨164905557696870120546237755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109937038464580080364158503 164905557696870120546237755)
            ·
              refine ⟨247358336545305180819356633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164905557696870120546237755 247358336545305180819356633)
              ·
                refine ⟨185518752408978885614517475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 247358336545305180819356633 185518752408978885614517475)
                ·
                  refine ⟨278278128613468328421776213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 185518752408978885614517475 278278128613468328421776213)
                  ·
                    refine ⟨1630535909844540986846345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 278278128613468328421776213 1630535909844540986846345)
                    ·
                      refine ⟨1222901932383405740134759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1630535909844540986846345 1222901932383405740134759)
                      ·
                        rfl

theorem cell23_2381593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 9, 2].length) (baseStart_2381593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2381593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2381593 prefixEnd_2381593 := by exact prefixLift 2381593
  have htrace : WordTrace (prefixWord ++ tailWord_2381593) baseStart_2381593 baseEnd_2381593 := by
    simpa [prefixWord, tailWord_2381593, baseEnd_2381593] using wordTrace_append hprefix tailTrace_2381593
  have hstable : (prefixWord ++ tailWord_2381593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381593).length < 2 ^ (prefixWord ++ tailWord_2381593).sum := by decide
  have hdescent : baseEnd_2381593 < baseStart_2381593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381600 : List Nat := [2, 1, 1, 5, 1, 1, 1, 3, 4, 1, 3]
def baseStart_2381600 : Nat := 118140960795 + 2381600 * 2 ^ 59
def prefixEnd_2381600 : Nat := 4983230072969 + 3 ^ 40 * 2381600 * 2
def baseEnd_2381600 : Nat := 1222905526747987212747227

theorem tailTrace_2381600 : CollatzResearch.WordTrace tailWord_2381600 prefixEnd_2381600 1222905526747987212747227 := by
  unfold tailWord_2381600
  simp only [CollatzResearch.WordTrace]
  refine ⟨43432044085938709871247127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57909392114584946494996169 43432044085938709871247127)
  ·
    refine ⟨65148066128908064806870691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43432044085938709871247127 65148066128908064806870691)
    ·
      refine ⟨97722099193362097210306037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65148066128908064806870691 97722099193362097210306037)
      ·
        refine ⟨9161446799377696613466191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 97722099193362097210306037 9161446799377696613466191)
        ·
          refine ⟨13742170199066544920199287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9161446799377696613466191 13742170199066544920199287)
          ·
            refine ⟨20613255298599817380298931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13742170199066544920199287 20613255298599817380298931)
            ·
              refine ⟨30919882947899726070448397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20613255298599817380298931 30919882947899726070448397)
              ·
                refine ⟨11594956105462397276418149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30919882947899726070448397 11594956105462397276418149)
                ·
                  refine ⟨2174054269774199489328403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11594956105462397276418149 2174054269774199489328403)
                  ·
                    refine ⟨3261081404661299233992605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2174054269774199489328403 3261081404661299233992605)
                    ·
                      refine ⟨1222905526747987212747227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3261081404661299233992605 1222905526747987212747227)
                      ·
                        rfl

theorem cell23_2381600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_2381600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2381600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2381600 prefixEnd_2381600 := by exact prefixLift 2381600
  have htrace : WordTrace (prefixWord ++ tailWord_2381600) baseStart_2381600 baseEnd_2381600 := by
    simpa [prefixWord, tailWord_2381600, baseEnd_2381600] using wordTrace_append hprefix tailTrace_2381600
  have hstable : (prefixWord ++ tailWord_2381600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381600).length < 2 ^ (prefixWord ++ tailWord_2381600).sum := by decide
  have hdescent : baseEnd_2381600 < baseStart_2381600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381601 : List Nat := [1, 2, 3, 2, 1, 4, 3, 2, 1, 2, 2]
def baseStart_2381601 : Nat := 118140960795 + 2381601 * 2 ^ 59
def prefixEnd_2381601 : Nat := 4983230072969 + 3 ^ 40 * 2381601 * 2
def baseEnd_2381601 : Nat := 1222906040228641708834723

theorem tailTrace_2381601 : CollatzResearch.WordTrace tailWord_2381601 prefixEnd_2381601 1222906040228641708834723 := by
  unfold tailWord_2381601
  simp only [CollatzResearch.WordTrace]
  refine ⟨86864124644873796913280657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57909416429915864608853771 86864124644873796913280657)
  ·
    refine ⟨65148093483655347684960493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86864124644873796913280657 65148093483655347684960493)
    ·
      refine ⟨24430535056370755381860185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65148093483655347684960493 24430535056370755381860185)
      ·
        refine ⟨18322901292278066536395139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24430535056370755381860185 18322901292278066536395139)
        ·
          refine ⟨27484351938417099804592709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18322901292278066536395139 27484351938417099804592709)
          ·
            refine ⟨5153315988453206213361133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27484351938417099804592709 5153315988453206213361133)
            ·
              refine ⟨1932493495669952330010425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5153315988453206213361133 1932493495669952330010425)
              ·
                refine ⟨1449370121752464247507819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1932493495669952330010425 1449370121752464247507819)
                ·
                  refine ⟨2174055182628696371261729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1449370121752464247507819 2174055182628696371261729)
                  ·
                    refine ⟨1630541386971522278446297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2174055182628696371261729 1630541386971522278446297)
                    ·
                      refine ⟨1222906040228641708834723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1630541386971522278446297 1222906040228641708834723)
                      ·
                        rfl

theorem cell23_2381601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 2, 1, 2, 2].length) (baseStart_2381601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2381601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2381601 prefixEnd_2381601 := by exact prefixLift 2381601
  have htrace : WordTrace (prefixWord ++ tailWord_2381601) baseStart_2381601 baseEnd_2381601 := by
    simpa [prefixWord, tailWord_2381601, baseEnd_2381601] using wordTrace_append hprefix tailTrace_2381601
  have hstable : (prefixWord ++ tailWord_2381601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381601).length < 2 ^ (prefixWord ++ tailWord_2381601).sum := by decide
  have hdescent : baseEnd_2381601 < baseStart_2381601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381617 : List Nat := [1, 2, 2, 3, 2, 3, 1, 3, 2, 1, 3]
def baseStart_2381617 : Nat := 118140960795 + 2381617 * 2 ^ 59
def prefixEnd_2381617 : Nat := 4983230072969 + 3 ^ 40 * 2381617 * 2
def baseEnd_2381617 : Nat := 1222914255919113646234649

theorem tailTrace_2381617 : CollatzResearch.WordTrace tailWord_2381617 prefixEnd_2381617 1222914255919113646234649 := by
  unfold tailWord_2381617
  simp only [CollatzResearch.WordTrace]
  refine ⟨86864708212815831645863105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57909805475210554430575403 86864708212815831645863105)
  ·
    refine ⟨65148531159611873734397329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86864708212815831645863105 65148531159611873734397329)
    ·
      refine ⟨48861398369708905300797997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65148531159611873734397329 48861398369708905300797997)
      ·
        refine ⟨18323024388640839487799249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48861398369708905300797997 18323024388640839487799249)
        ·
          refine ⟨13742268291480629615849437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18323024388640839487799249 13742268291480629615849437)
          ·
            refine ⟨5153350609305236105943539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13742268291480629615849437 5153350609305236105943539)
            ·
              refine ⟨7730025913957854158915309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5153350609305236105943539 7730025913957854158915309)
              ·
                refine ⟨2898759717734195309593241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7730025913957854158915309 2898759717734195309593241)
                ·
                  refine ⟨2174069788300646482194931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2898759717734195309593241 2174069788300646482194931)
                  ·
                    refine ⟨3261104682450969723292397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2174069788300646482194931 3261104682450969723292397)
                    ·
                      refine ⟨1222914255919113646234649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3261104682450969723292397 1222914255919113646234649)
                      ·
                        rfl

theorem cell23_2381617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_2381617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2381617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2381617 prefixEnd_2381617 := by exact prefixLift 2381617
  have htrace : WordTrace (prefixWord ++ tailWord_2381617) baseStart_2381617 baseEnd_2381617 := by
    simpa [prefixWord, tailWord_2381617, baseEnd_2381617] using wordTrace_append hprefix tailTrace_2381617
  have hstable : (prefixWord ++ tailWord_2381617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381617).length < 2 ^ (prefixWord ++ tailWord_2381617).sum := by decide
  have hdescent : baseEnd_2381617 < baseStart_2381617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381640 : List Nat := [2, 1, 3, 1, 1, 4, 1, 1, 3, 4, 2]
def baseStart_2381640 : Nat := 118140960795 + 2381640 * 2 ^ 59
def prefixEnd_2381640 : Nat := 4983230072969 + 3 ^ 40 * 2381640 * 2
def baseEnd_2381640 : Nat := 1222926065974167056247043

theorem tailTrace_2381640 : CollatzResearch.WordTrace tailWord_2381640 prefixEnd_2381640 1222926065974167056247043 := by
  unfold tailWord_2381640
  simp only [CollatzResearch.WordTrace]
  refine ⟨43432773545866253286975187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57910364727821671049300249 43432773545866253286975187)
  ·
    refine ⟨65149160318799379930462781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43432773545866253286975187 65149160318799379930462781)
    ·
      refine ⟨24430935119549767473923543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65149160318799379930462781 24430935119549767473923543)
      ·
        refine ⟨36646402679324651210885315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24430935119549767473923543 36646402679324651210885315)
        ·
          refine ⟨54969604018986976816327973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36646402679324651210885315 54969604018986976816327973)
          ·
            refine ⟨10306800753560058153061495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54969604018986976816327973 10306800753560058153061495)
            ·
              refine ⟨15460201130340087229592243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10306800753560058153061495 15460201130340087229592243)
              ·
                refine ⟨23190301695510130844388365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15460201130340087229592243 23190301695510130844388365)
                ·
                  refine ⟨8696363135816299066645637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23190301695510130844388365 8696363135816299066645637)
                  ·
                    refine ⟨1630568087965556074996057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8696363135816299066645637 1630568087965556074996057)
                    ·
                      refine ⟨1222926065974167056247043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1630568087965556074996057 1222926065974167056247043)
                      ·
                        rfl

theorem cell23_2381640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 3, 4, 2].length) (baseStart_2381640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2381640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2381640 prefixEnd_2381640 := by exact prefixLift 2381640
  have htrace : WordTrace (prefixWord ++ tailWord_2381640) baseStart_2381640 baseEnd_2381640 := by
    simpa [prefixWord, tailWord_2381640, baseEnd_2381640] using wordTrace_append hprefix tailTrace_2381640
  have hstable : (prefixWord ++ tailWord_2381640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381640).length < 2 ^ (prefixWord ++ tailWord_2381640).sum := by decide
  have hdescent : baseEnd_2381640 < baseStart_2381640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381743 : List Nat := [1, 1, 2, 1, 2, 2, 3, 1, 2, 4, 4]
def baseStart_2381743 : Nat := 118140960795 + 2381743 * 2 ^ 59
def prefixEnd_2381743 : Nat := 4983230072969 + 3 ^ 40 * 2381743 * 2
def baseEnd_2381743 : Nat := 1222978954481580153259069

theorem tailTrace_2381743 : CollatzResearch.WordTrace tailWord_2381743 prefixEnd_2381743 1222978954481580153259069 := by
  unfold tailWord_2381743
  simp only [CollatzResearch.WordTrace]
  refine ⟨86869303810359355164949883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57912869206906236776633255 86869303810359355164949883)
  ·
    refine ⟨130303955715539032747424825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86869303810359355164949883 130303955715539032747424825)
    ·
      refine ⟨97727966786654274560568619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130303955715539032747424825 97727966786654274560568619)
      ·
        refine ⟨146591950179981411840852929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97727966786654274560568619 146591950179981411840852929)
        ·
          refine ⟨109943962634986058880639697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146591950179981411840852929 109943962634986058880639697)
          ·
            refine ⟨82457971976239544160479773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109943962634986058880639697 82457971976239544160479773)
            ·
              refine ⟨30921739491089829060179915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82457971976239544160479773 30921739491089829060179915)
              ·
                refine ⟨46382609236634743590269873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30921739491089829060179915 46382609236634743590269873)
                ·
                  refine ⟨34786956927476057692702405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46382609236634743590269873 34786956927476057692702405)
                  ·
                    refine ⟨6522554423901760817381701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34786956927476057692702405 6522554423901760817381701)
                    ·
                      refine ⟨1222978954481580153259069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6522554423901760817381701 1222978954481580153259069)
                      ·
                        rfl

theorem cell23_2381743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 4, 4].length) (baseStart_2381743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2381743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2381743 prefixEnd_2381743 := by exact prefixLift 2381743
  have htrace : WordTrace (prefixWord ++ tailWord_2381743) baseStart_2381743 baseEnd_2381743 := by
    simpa [prefixWord, tailWord_2381743, baseEnd_2381743] using wordTrace_append hprefix tailTrace_2381743
  have hstable : (prefixWord ++ tailWord_2381743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381743).length < 2 ^ (prefixWord ++ tailWord_2381743).sum := by decide
  have hdescent : baseEnd_2381743 < baseStart_2381743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381748 : List Nat := [2, 5, 2, 1, 3, 1, 1, 3, 5]
def baseStart_2381748 : Nat := 118140960795 + 2381748 * 2 ^ 59
def prefixEnd_2381748 : Nat := 4983230072969 + 3 ^ 40 * 2381748 * 2
def baseEnd_2381748 : Nat := 135886835764983625966283

theorem tailTrace_2381748 : CollatzResearch.WordTrace tailWord_2381748 prefixEnd_2381748 135886835764983625966283 := by
  unfold tailWord_2381748
  simp only [CollatzResearch.WordTrace]
  refine ⟨43434743087670620509440949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57912990783560827345921265 43434743087670620509440949)
  ·
    refine ⟨4072007164469120672760089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43434743087670620509440949 4072007164469120672760089)
    ·
      refine ⟨3054005373351840504570067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4072007164469120672760089 3054005373351840504570067)
      ·
        refine ⟨4581008060027760756855101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3054005373351840504570067 4581008060027760756855101)
        ·
          refine ⟨1717878022510410283820663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4581008060027760756855101 1717878022510410283820663)
          ·
            refine ⟨2576817033765615425730995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1717878022510410283820663 2576817033765615425730995)
            ·
              refine ⟨3865225550648423138596493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2576817033765615425730995 3865225550648423138596493)
              ·
                refine ⟨1449459581493158676973685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3865225550648423138596493 1449459581493158676973685)
                ·
                  refine ⟨135886835764983625966283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1449459581493158676973685 135886835764983625966283)
                  ·
                    rfl

theorem cell23_2381748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_2381748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2381748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2381748 prefixEnd_2381748 := by exact prefixLift 2381748
  have htrace : WordTrace (prefixWord ++ tailWord_2381748) baseStart_2381748 baseEnd_2381748 := by
    simpa [prefixWord, tailWord_2381748, baseEnd_2381748] using wordTrace_append hprefix tailTrace_2381748
  have hstable : (prefixWord ++ tailWord_2381748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381748).length < 2 ^ (prefixWord ++ tailWord_2381748).sum := by decide
  have hdescent : baseEnd_2381748 < baseStart_2381748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381753 : List Nat := [1, 2, 1, 4, 2, 1, 1, 1, 10]
def baseStart_2381753 : Nat := 118140960795 + 2381753 * 2 ^ 59
def prefixEnd_2381753 : Nat := 4983230072969 + 3 ^ 40 * 2381753 * 2
def baseEnd_2381753 : Nat := 135887121032013901570447

theorem tailTrace_2381753 : CollatzResearch.WordTrace tailWord_2381753 prefixEnd_2381753 135887121032013901570447 := by
  unfold tailWord_2381753
  simp only [CollatzResearch.WordTrace]
  refine ⟨86869668540323126872813913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57913112360215417915209275 86869668540323126872813913)
  ·
    refine ⟨65152251405242345154610435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86869668540323126872813913 65152251405242345154610435)
    ·
      refine ⟨97728377107863517731915653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65152251405242345154610435 97728377107863517731915653)
      ·
        refine ⟨18324070707724409574734185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97728377107863517731915653 18324070707724409574734185)
        ·
          refine ⟨13743053030793307181050639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18324070707724409574734185 13743053030793307181050639)
          ·
            refine ⟨20614579546189960771575959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13743053030793307181050639 20614579546189960771575959)
            ·
              refine ⟨30921869319284941157363939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20614579546189960771575959 30921869319284941157363939)
              ·
                refine ⟨46382803978927411736045909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30921869319284941157363939 46382803978927411736045909)
                ·
                  refine ⟨135887121032013901570447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 46382803978927411736045909 135887121032013901570447)
                  ·
                    rfl

theorem cell23_2381753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 10].length) (baseStart_2381753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2381753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2381753 prefixEnd_2381753 := by exact prefixLift 2381753
  have htrace : WordTrace (prefixWord ++ tailWord_2381753) baseStart_2381753 baseEnd_2381753 := by
    simpa [prefixWord, tailWord_2381753, baseEnd_2381753] using wordTrace_append hprefix tailTrace_2381753
  have hstable : (prefixWord ++ tailWord_2381753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381753).length < 2 ^ (prefixWord ++ tailWord_2381753).sum := by decide
  have hdescent : baseEnd_2381753 < baseStart_2381753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381831 : List Nat := [1, 1, 4, 3, 1, 3, 1, 4, 1, 1, 3]
def baseStart_2381831 : Nat := 118140960795 + 2381831 * 2 ^ 59
def prefixEnd_2381831 : Nat := 4983230072969 + 3 ^ 40 * 2381831 * 2
def baseEnd_2381831 : Nat := 1223024140779175808958665

theorem tailTrace_2381831 : CollatzResearch.WordTrace tailWord_2381831 prefixEnd_2381831 1223024140779175808958665 := by
  unfold tailWord_2381831
  simp only [CollatzResearch.WordTrace]
  refine ⟨86872513434040546194153347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57915008956027030796102231 86872513434040546194153347)
  ·
    refine ⟨130308770151060819291230021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86872513434040546194153347 130308770151060819291230021)
    ·
      refine ⟨24432894403323903617105629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130308770151060819291230021 24432894403323903617105629)
      ·
        refine ⟨9162335401246463856414611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24432894403323903617105629 9162335401246463856414611)
        ·
          refine ⟨13743503101869695784621917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9162335401246463856414611 13743503101869695784621917)
          ·
            refine ⟨5153813663201135919233219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13743503101869695784621917 5153813663201135919233219)
            ·
              refine ⟨7730720494801703878849829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5153813663201135919233219 7730720494801703878849829)
              ·
                refine ⟨1449510092775319477284343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7730720494801703878849829 1449510092775319477284343)
                ·
                  refine ⟨2174265139162979215926515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1449510092775319477284343 2174265139162979215926515)
                  ·
                    refine ⟨3261397708744468823889773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2174265139162979215926515 3261397708744468823889773)
                    ·
                      refine ⟨1223024140779175808958665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3261397708744468823889773 1223024140779175808958665)
                      ·
                        rfl

theorem cell23_2381831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_2381831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2381831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2381831 prefixEnd_2381831 := by exact prefixLift 2381831
  have htrace : WordTrace (prefixWord ++ tailWord_2381831) baseStart_2381831 baseEnd_2381831 := by
    simpa [prefixWord, tailWord_2381831, baseEnd_2381831] using wordTrace_append hprefix tailTrace_2381831
  have hstable : (prefixWord ++ tailWord_2381831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381831).length < 2 ^ (prefixWord ++ tailWord_2381831).sum := by decide
  have hdescent : baseEnd_2381831 < baseStart_2381831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381874 : List Nat := [3, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3]
def baseStart_2381874 : Nat := 118140960795 + 2381874 * 2 ^ 59
def prefixEnd_2381874 : Nat := 4983230072969 + 3 ^ 40 * 2381874 * 2
def baseEnd_2381874 : Nat := 1223046220447319140720967

theorem tailTrace_2381874 : CollatzResearch.WordTrace tailWord_2381874 prefixEnd_2381874 1223046220447319140720967 := by
  unfold tailWord_2381874
  simp only [CollatzResearch.WordTrace]
  refine ⟨21718520443221191134492169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57916054515256509691979117 21718520443221191134492169)
  ·
    refine ⟨16288890332415893350869127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21718520443221191134492169 16288890332415893350869127)
    ·
      refine ⟨24433335498623840026303691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16288890332415893350869127 24433335498623840026303691)
      ·
        refine ⟨36650003247935760039455537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24433335498623840026303691 36650003247935760039455537)
        ·
          refine ⟨27487502435951820029591653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36650003247935760039455537 27487502435951820029591653)
          ·
            refine ⟨5153906706740966255548435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27487502435951820029591653 5153906706740966255548435)
            ·
              refine ⟨7730860060111449383322653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5153906706740966255548435 7730860060111449383322653)
              ·
                refine ⟨2899072522541793518745995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7730860060111449383322653 2899072522541793518745995)
                ·
                  refine ⟨4348608783812690278118993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2899072522541793518745995 4348608783812690278118993)
                  ·
                    refine ⟨3261456587859517708589245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4348608783812690278118993 3261456587859517708589245)
                    ·
                      refine ⟨1223046220447319140720967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3261456587859517708589245 1223046220447319140720967)
                      ·
                        rfl

theorem cell23_2381874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3].length) (baseStart_2381874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2381874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2381874 prefixEnd_2381874 := by exact prefixLift 2381874
  have htrace : WordTrace (prefixWord ++ tailWord_2381874) baseStart_2381874 baseEnd_2381874 := by
    simpa [prefixWord, tailWord_2381874, baseEnd_2381874] using wordTrace_append hprefix tailTrace_2381874
  have hstable : (prefixWord ++ tailWord_2381874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381874).length < 2 ^ (prefixWord ++ tailWord_2381874).sum := by decide
  have hdescent : baseEnd_2381874 < baseStart_2381874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381881 : List Nat := [1, 2, 1, 5, 3, 2, 1, 2, 2, 4]
def baseStart_2381881 : Nat := 118140960795 + 2381881 * 2 ^ 59
def prefixEnd_2381881 : Nat := 4983230072969 + 3 ^ 40 * 2381881 * 2
def baseEnd_2381881 : Nat := 407683271603966871111145

theorem tailTrace_2381881 : CollatzResearch.WordTrace tailWord_2381881 prefixEnd_2381881 407683271603966871111145 := by
  unfold tailWord_2381881
  simp only [CollatzResearch.WordTrace]
  refine ⟨86874337083859404733473497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57916224722572936488982331 86874337083859404733473497)
  ·
    refine ⟨65155752812894553550105123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86874337083859404733473497 65155752812894553550105123)
    ·
      refine ⟨97733629219341830325157685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65155752812894553550105123 97733629219341830325157685)
      ·
        refine ⟨9162527739313296592983533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 97733629219341830325157685 9162527739313296592983533)
        ·
          refine ⟨3435947902242486222368825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9162527739313296592983533 3435947902242486222368825)
          ·
            refine ⟨2576960926681864666776619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3435947902242486222368825 2576960926681864666776619)
            ·
              refine ⟨3865441390022797000164929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2576960926681864666776619 3865441390022797000164929)
              ·
                refine ⟨2899081042517097750123697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3865441390022797000164929 2899081042517097750123697)
                ·
                  refine ⟨2174310781887823312592773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2899081042517097750123697 2174310781887823312592773)
                  ·
                    refine ⟨407683271603966871111145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2174310781887823312592773 407683271603966871111145)
                    ·
                      rfl

theorem cell23_2381881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 2, 2, 4].length) (baseStart_2381881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2381881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2381881 prefixEnd_2381881 := by exact prefixLift 2381881
  have htrace : WordTrace (prefixWord ++ tailWord_2381881) baseStart_2381881 baseEnd_2381881 := by
    simpa [prefixWord, tailWord_2381881, baseEnd_2381881] using wordTrace_append hprefix tailTrace_2381881
  have hstable : (prefixWord ++ tailWord_2381881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381881).length < 2 ^ (prefixWord ++ tailWord_2381881).sum := by decide
  have hdescent : baseEnd_2381881 < baseStart_2381881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381922 : List Nat := [3, 3, 2, 2, 2, 2, 1, 3, 1, 2, 2]
def baseStart_2381922 : Nat := 118140960795 + 2381922 * 2 ^ 59
def prefixEnd_2381922 : Nat := 4983230072969 + 3 ^ 40 * 2381922 * 2
def baseEnd_2381922 : Nat := 1223070867518734952920747

theorem tailTrace_2381922 : CollatzResearch.WordTrace tailWord_2381922 prefixEnd_2381922 1223070867518734952920747 := by
  unfold tailWord_2381922
  simp only [CollatzResearch.WordTrace]
  refine ⟨21718958119177717183929005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57917221651140579157144013 21718958119177717183929005)
  ·
    refine ⟨8144609294691643943973377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21718958119177717183929005 8144609294691643943973377)
    ·
      refine ⟨6108456971018732957980033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8144609294691643943973377 6108456971018732957980033)
      ·
        refine ⟨4581342728264049718485025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6108456971018732957980033 4581342728264049718485025)
        ·
          refine ⟨3436007046198037288863769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4581342728264049718485025 3436007046198037288863769)
          ·
            refine ⟨2577005284648527966647827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3436007046198037288863769 2577005284648527966647827)
            ·
              refine ⟨3865507926972791949971741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2577005284648527966647827 3865507926972791949971741)
              ·
                refine ⟨1449565472614796981239403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3865507926972791949971741 1449565472614796981239403)
                ·
                  refine ⟨2174348208922195471859105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1449565472614796981239403 2174348208922195471859105)
                  ·
                    refine ⟨1630761156691646603894329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2174348208922195471859105 1630761156691646603894329)
                    ·
                      refine ⟨1223070867518734952920747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1630761156691646603894329 1223070867518734952920747)
                      ·
                        rfl

theorem cell23_2381922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_2381922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2381922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2381922 prefixEnd_2381922 := by exact prefixLift 2381922
  have htrace : WordTrace (prefixWord ++ tailWord_2381922) baseStart_2381922 baseEnd_2381922 := by
    simpa [prefixWord, tailWord_2381922, baseEnd_2381922] using wordTrace_append hprefix tailTrace_2381922
  have hstable : (prefixWord ++ tailWord_2381922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381922).length < 2 ^ (prefixWord ++ tailWord_2381922).sum := by decide
  have hdescent : baseEnd_2381922 < baseStart_2381922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381961 : List Nat := [1, 2, 1, 1, 4, 2, 3, 3, 2, 2, 2]
def baseStart_2381961 : Nat := 118140960795 + 2381961 * 2 ^ 59
def prefixEnd_2381961 : Nat := 4983230072969 + 3 ^ 40 * 2381961 * 2
def baseEnd_2381961 : Nat := 1223090893264260300333067

theorem tailTrace_2381961 : CollatzResearch.WordTrace tailWord_2381961 prefixEnd_2381961 1223090893264260300333067 := by
  unfold tailWord_2381961
  simp only [CollatzResearch.WordTrace]
  refine ⟨86877254923569578396385737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57918169949046385597590491 86877254923569578396385737)
  ·
    refine ⟨65157941192677183797289303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86877254923569578396385737 65157941192677183797289303)
    ·
      refine ⟨97736911789015775695933955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65157941192677183797289303 97736911789015775695933955)
      ·
        refine ⟨146605367683523663543900933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97736911789015775695933955 146605367683523663543900933)
        ·
          refine ⟨27488506440660686914481425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 146605367683523663543900933 27488506440660686914481425)
          ·
            refine ⟨20616379830495515185861069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27488506440660686914481425 20616379830495515185861069)
            ·
              refine ⟨7731142436435818194697901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20616379830495515185861069 7731142436435818194697901)
              ·
                refine ⟨2899178413663431823011713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7731142436435818194697901 2899178413663431823011713)
                ·
                  refine ⟨2174383810247573867258785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2899178413663431823011713 2174383810247573867258785)
                  ·
                    refine ⟨1630787857685680400444089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2174383810247573867258785 1630787857685680400444089)
                    ·
                      refine ⟨1223090893264260300333067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1630787857685680400444089 1223090893264260300333067)
                      ·
                        rfl

theorem cell23_2381961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 3, 2, 2, 2].length) (baseStart_2381961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2381961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2381961 prefixEnd_2381961 := by exact prefixLift 2381961
  have htrace : WordTrace (prefixWord ++ tailWord_2381961) baseStart_2381961 baseEnd_2381961 := by
    simpa [prefixWord, tailWord_2381961, baseEnd_2381961] using wordTrace_append hprefix tailTrace_2381961
  have hstable : (prefixWord ++ tailWord_2381961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381961).length < 2 ^ (prefixWord ++ tailWord_2381961).sum := by decide
  have hdescent : baseEnd_2381961 < baseStart_2381961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382000 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 8]
def baseStart_2382000 : Nat := 118140960795 + 2382000 * 2 ^ 59
def prefixEnd_2382000 : Nat := 4983230072969 + 3 ^ 40 * 2382000 * 2
def baseEnd_2382000 : Nat := 1223110919009785647745387

theorem tailTrace_2382000 : CollatzResearch.WordTrace tailWord_2382000 prefixEnd_2382000 1223110919009785647745387 := by
  unfold tailWord_2382000
  simp only [CollatzResearch.WordTrace]
  refine ⟨43439338685214144028527727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57919118246952192038036969 43439338685214144028527727)
  ·
    refine ⟨65159008027821216042791591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43439338685214144028527727 65159008027821216042791591)
    ·
      refine ⟨97738512041731824064187387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65159008027821216042791591 97738512041731824064187387)
      ·
        refine ⟨146607768062597736096281081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97738512041731824064187387 146607768062597736096281081)
        ·
          refine ⟨109955826046948302072210811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146607768062597736096281081 109955826046948302072210811)
          ·
            refine ⟨164933739070422453108316217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109955826046948302072210811 164933739070422453108316217)
            ·
              refine ⟨123700304302816839831237163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164933739070422453108316217 123700304302816839831237163)
              ·
                refine ⟨185550456454225259746855745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123700304302816839831237163 185550456454225259746855745)
                ·
                  refine ⟨139162842340668944810141809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 185550456454225259746855745 139162842340668944810141809)
                  ·
                    refine ⟨104372131755501708607606357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 139162842340668944810141809 104372131755501708607606357)
                    ·
                      refine ⟨1223110919009785647745387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 104372131755501708607606357 1223110919009785647745387)
                      ·
                        rfl

theorem cell23_2382000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 8].length) (baseStart_2382000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2382000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2382000 prefixEnd_2382000 := by exact prefixLift 2382000
  have htrace : WordTrace (prefixWord ++ tailWord_2382000) baseStart_2382000 baseEnd_2382000 := by
    simpa [prefixWord, tailWord_2382000, baseEnd_2382000] using wordTrace_append hprefix tailTrace_2382000
  have hstable : (prefixWord ++ tailWord_2382000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382000).length < 2 ^ (prefixWord ++ tailWord_2382000).sum := by decide
  have hdescent : baseEnd_2382000 < baseStart_2382000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382001 : List Nat := [1, 2, 2, 5, 2, 1, 1, 4, 5]
def baseStart_2382001 : Nat := 118140960795 + 2382001 * 2 ^ 59
def prefixEnd_2382001 : Nat := 4983230072969 + 3 ^ 40 * 2382001 * 2
def baseEnd_2382001 : Nat := 135901270276715571536987

theorem tailTrace_2382001 : CollatzResearch.WordTrace tailWord_2382001 prefixEnd_2382001 135901270276715571536987 := by
  unfold tailWord_2382001
  simp only [CollatzResearch.WordTrace]
  refine ⟨86878713843424665227841857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57919142562283110151894571 86878713843424665227841857)
  ·
    refine ⟨65159035382568498920881393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86878713843424665227841857 65159035382568498920881393)
    ·
      refine ⟨48869276536926374190661045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65159035382568498920881393 48869276536926374190661045)
      ·
        refine ⟨4581494675336847580374473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48869276536926374190661045 4581494675336847580374473)
        ·
          refine ⟨3436121006502635685280855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4581494675336847580374473 3436121006502635685280855)
          ·
            refine ⟨5154181509753953527921283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3436121006502635685280855 5154181509753953527921283)
            ·
              refine ⟨7731272264630930291881925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5154181509753953527921283 7731272264630930291881925)
              ·
                refine ⟨1449613549618299429727861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7731272264630930291881925 1449613549618299429727861)
                ·
                  refine ⟨135901270276715571536987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1449613549618299429727861 135901270276715571536987)
                  ·
                    rfl

theorem cell23_2382001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 4, 5].length) (baseStart_2382001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2382001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2382001 prefixEnd_2382001 := by exact prefixLift 2382001
  have htrace : WordTrace (prefixWord ++ tailWord_2382001) baseStart_2382001 baseEnd_2382001 := by
    simpa [prefixWord, tailWord_2382001, baseEnd_2382001] using wordTrace_append hprefix tailTrace_2382001
  have hstable : (prefixWord ++ tailWord_2382001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382001).length < 2 ^ (prefixWord ++ tailWord_2382001).sum := by decide
  have hdescent : baseEnd_2382001 < baseStart_2382001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382007 : List Nat := [1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 5]
def baseStart_2382007 : Nat := 118140960795 + 2382007 * 2 ^ 59
def prefixEnd_2382007 : Nat := 4983230072969 + 3 ^ 40 * 2382007 * 2
def baseEnd_2382007 : Nat := 1223114513374367120357855

theorem tailTrace_2382007 : CollatzResearch.WordTrace tailWord_2382007 prefixEnd_2382007 1223114513374367120357855 := by
  unfold tailWord_2382007
  simp only [CollatzResearch.WordTrace]
  refine ⟨86878932681402928252560275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57919288454268618835040183 86878932681402928252560275)
  ·
    refine ⟨130318399022104392378840413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86878932681402928252560275 130318399022104392378840413)
    ·
      refine ⟨48869399633289147142065155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130318399022104392378840413 48869399633289147142065155)
      ·
        refine ⟨73304099449933720713097733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48869399633289147142065155 73304099449933720713097733)
        ·
          refine ⟨13744518646862572633705825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73304099449933720713097733 13744518646862572633705825)
          ·
            refine ⟨10308388985146929475279369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13744518646862572633705825 10308388985146929475279369)
            ·
              refine ⟨7731291738860197106459527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10308388985146929475279369 7731291738860197106459527)
              ·
                refine ⟨11596937608290295659689291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7731291738860197106459527 11596937608290295659689291)
                ·
                  refine ⟨17395406412435443489533937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11596937608290295659689291 17395406412435443489533937)
                  ·
                    refine ⟨13046554809326582617150453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17395406412435443489533937 13046554809326582617150453)
                    ·
                      refine ⟨1223114513374367120357855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13046554809326582617150453 1223114513374367120357855)
                      ·
                        rfl

theorem cell23_2382007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 5].length) (baseStart_2382007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2382007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2382007 prefixEnd_2382007 := by exact prefixLift 2382007
  have htrace : WordTrace (prefixWord ++ tailWord_2382007) baseStart_2382007 baseEnd_2382007 := by
    simpa [prefixWord, tailWord_2382007, baseEnd_2382007] using wordTrace_append hprefix tailTrace_2382007
  have hstable : (prefixWord ++ tailWord_2382007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382007).length < 2 ^ (prefixWord ++ tailWord_2382007).sum := by decide
  have hdescent : baseEnd_2382007 < baseStart_2382007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382034 : List Nat := [3, 2, 2, 2, 1, 3, 1, 1, 1, 3, 4]
def baseStart_2382034 : Nat := 118140960795 + 2382034 * 2 ^ 59
def prefixEnd_2382034 : Nat := 4983230072969 + 3 ^ 40 * 2382034 * 2
def baseEnd_2382034 : Nat := 1223128377352038514720231

theorem tailTrace_2382034 : CollatzResearch.WordTrace tailWord_2382034 prefixEnd_2382034 1223128377352038514720231 := by
  unfold tailWord_2382034
  simp only [CollatzResearch.WordTrace]
  refine ⟨21719979363076277965948289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57919944968203407909195437 21719979363076277965948289)
  ·
    refine ⟨16289984522307208474461217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21719979363076277965948289 16289984522307208474461217)
    ·
      refine ⟨12217488391730406355845913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16289984522307208474461217 12217488391730406355845913)
      ·
        refine ⟨9163116293797804766884435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12217488391730406355845913 9163116293797804766884435)
        ·
          refine ⟨13744674440696707150326653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9163116293797804766884435 13744674440696707150326653)
          ·
            refine ⟨5154252915261265181372495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13744674440696707150326653 5154252915261265181372495)
            ·
              refine ⟨7731379372891897772058743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5154252915261265181372495 7731379372891897772058743)
              ·
                refine ⟨11597069059337846658088115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7731379372891897772058743 11597069059337846658088115)
                ·
                  refine ⟨17395603589006769987132173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11597069059337846658088115 17395603589006769987132173)
                  ·
                    refine ⟨6523351345877538745174565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17395603589006769987132173 6523351345877538745174565)
                    ·
                      refine ⟨1223128377352038514720231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6523351345877538745174565 1223128377352038514720231)
                      ·
                        rfl

theorem cell23_2382034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_2382034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2382034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2382034 prefixEnd_2382034 := by exact prefixLift 2382034
  have htrace : WordTrace (prefixWord ++ tailWord_2382034) baseStart_2382034 baseEnd_2382034 := by
    simpa [prefixWord, tailWord_2382034, baseEnd_2382034] using wordTrace_append hprefix tailTrace_2382034
  have hstable : (prefixWord ++ tailWord_2382034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382034).length < 2 ^ (prefixWord ++ tailWord_2382034).sum := by decide
  have hdescent : baseEnd_2382034 < baseStart_2382034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382104 : List Nat := [2, 1, 2, 3, 1, 2, 1, 5, 1, 5]
def baseStart_2382104 : Nat := 118140960795 + 2382104 * 2 ^ 59
def prefixEnd_2382104 : Nat := 4983230072969 + 3 ^ 40 * 2382104 * 2
def baseEnd_2382104 : Nat := 407721440332617746948303

theorem tailTrace_2382104 : CollatzResearch.WordTrace tailWord_2382104 prefixEnd_2382104 407721440332617746948303 := by
  unfold tailWord_2382104
  simp only [CollatzResearch.WordTrace]
  refine ⟨43441235281025756909420683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57921647041367675879227577 43441235281025756909420683)
  ·
    refine ⟨65161852921538635364131025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43441235281025756909420683 65161852921538635364131025)
    ·
      refine ⟨48871389691153976523098269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65161852921538635364131025 48871389691153976523098269)
      ·
        refine ⟨18326771134182741196161851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48871389691153976523098269 18326771134182741196161851)
        ·
          refine ⟨27490156701274111794242777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18326771134182741196161851 27490156701274111794242777)
          ·
            refine ⟨20617617525955583845682083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27490156701274111794242777 20617617525955583845682083)
            ·
              refine ⟨30926426288933375768523125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20617617525955583845682083 30926426288933375768523125)
              ·
                refine ⟨2899352464587503978299043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30926426288933375768523125 2899352464587503978299043)
                ·
                  refine ⟨4349028696881255967448565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2899352464587503978299043 4349028696881255967448565)
                  ·
                    refine ⟨407721440332617746948303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4349028696881255967448565 407721440332617746948303)
                    ·
                      rfl

theorem cell23_2382104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 5, 1, 5].length) (baseStart_2382104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2382104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2382104 prefixEnd_2382104 := by exact prefixLift 2382104
  have htrace : WordTrace (prefixWord ++ tailWord_2382104) baseStart_2382104 baseEnd_2382104 := by
    simpa [prefixWord, tailWord_2382104, baseEnd_2382104] using wordTrace_append hprefix tailTrace_2382104
  have hstable : (prefixWord ++ tailWord_2382104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382104).length < 2 ^ (prefixWord ++ tailWord_2382104).sum := by decide
  have hdescent : baseEnd_2382104 < baseStart_2382104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382111 : List Nat := [1, 1, 2, 4, 3, 1, 1, 1, 4, 3, 2]
def baseStart_2382111 : Nat := 118140960795 + 2382111 * 2 ^ 59
def prefixEnd_2382111 : Nat := 4983230072969 + 3 ^ 40 * 2382111 * 2
def baseEnd_2382111 : Nat := 1223167915362434713457377

theorem tailTrace_2382111 : CollatzResearch.WordTrace tailWord_2382111 prefixEnd_2382111 1223167915362434713457377 := by
  unfold tailWord_2382111
  simp only [CollatzResearch.WordTrace]
  refine ⟨86882725873026154014346187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57921817248684102676230791 86882725873026154014346187)
  ·
    refine ⟨130324088809539231021519281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86882725873026154014346187 130324088809539231021519281)
    ·
      refine ⟨97743066607154423266139461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130324088809539231021519281 97743066607154423266139461)
      ·
        refine ⟨18326824988841454362401149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97743066607154423266139461 18326824988841454362401149)
        ·
          refine ⟨6872559370815545385900431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18326824988841454362401149 6872559370815545385900431)
          ·
            refine ⟨10308839056223318078850647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6872559370815545385900431 10308839056223318078850647)
            ·
              refine ⟨15463258584334977118275971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10308839056223318078850647 15463258584334977118275971)
              ·
                refine ⟨23194887876502465677413957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15463258584334977118275971 23194887876502465677413957)
                ·
                  refine ⟨4349041476844212314515117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23194887876502465677413957 4349041476844212314515117)
                  ·
                    refine ⟨1630890553816579617943169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4349041476844212314515117 1630890553816579617943169)
                    ·
                      refine ⟨1223167915362434713457377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1630890553816579617943169 1223167915362434713457377)
                      ·
                        rfl

theorem cell23_2382111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 4, 3, 2].length) (baseStart_2382111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2382111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2382111 prefixEnd_2382111 := by exact prefixLift 2382111
  have htrace : WordTrace (prefixWord ++ tailWord_2382111) baseStart_2382111 baseEnd_2382111 := by
    simpa [prefixWord, tailWord_2382111, baseEnd_2382111] using wordTrace_append hprefix tailTrace_2382111
  have hstable : (prefixWord ++ tailWord_2382111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382111).length < 2 ^ (prefixWord ++ tailWord_2382111).sum := by decide
  have hdescent : baseEnd_2382111 < baseStart_2382111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382125 : List Nat := [1, 5, 3, 1, 2, 2, 2, 1, 6]
def baseStart_2382125 : Nat := 118140960795 + 2382125 * 2 ^ 59
def prefixEnd_2382125 : Nat := 4983230072969 + 3 ^ 40 * 2382125 * 2
def baseEnd_2382125 : Nat := 135908344899066406520257

theorem tailTrace_2382125 : CollatzResearch.WordTrace tailWord_2382125 prefixEnd_2382125 135908344899066406520257 := by
  unfold tailWord_2382125
  simp only [CollatzResearch.WordTrace]
  refine ⟨86883236494975434405355829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57922157663316956270237219 86883236494975434405355829)
  ·
    refine ⟨8145303421403946975502109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 86883236494975434405355829 8145303421403946975502109)
    ·
      refine ⟨3054488783026480115813291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8145303421403946975502109 3054488783026480115813291)
      ·
        refine ⟨4581733174539720173719937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3054488783026480115813291 4581733174539720173719937)
        ·
          refine ⟨3436299880904790130289953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4581733174539720173719937 3436299880904790130289953)
          ·
            refine ⟨2577224910678592597717465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3436299880904790130289953 2577224910678592597717465)
            ·
              refine ⟨1932918683008944448288099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2577224910678592597717465 1932918683008944448288099)
              ·
                refine ⟨2899378024513416672432149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1932918683008944448288099 2899378024513416672432149)
                ·
                  refine ⟨135908344899066406520257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2899378024513416672432149 135908344899066406520257)
                  ·
                    rfl

theorem cell23_2382125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 1, 6].length) (baseStart_2382125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2382125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2382125 prefixEnd_2382125 := by exact prefixLift 2382125
  have htrace : WordTrace (prefixWord ++ tailWord_2382125) baseStart_2382125 baseEnd_2382125 := by
    simpa [prefixWord, tailWord_2382125, baseEnd_2382125] using wordTrace_append hprefix tailTrace_2382125
  have hstable : (prefixWord ++ tailWord_2382125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382125).length < 2 ^ (prefixWord ++ tailWord_2382125).sum := by decide
  have hdescent : baseEnd_2382125 < baseStart_2382125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382145 : List Nat := [1, 2, 5, 2, 2, 1, 2, 1, 2, 3, 2]
def baseStart_2382145 : Nat := 118140960795 + 2382145 * 2 ^ 59
def prefixEnd_2382145 : Nat := 4983230072969 + 3 ^ 40 * 2382145 * 2
def baseEnd_2382145 : Nat := 1223185373704687580432221

theorem tailTrace_2382145 : CollatzResearch.WordTrace tailWord_2382145 prefixEnd_2382145 1223185373704687580432221 := by
  unfold tailWord_2382145
  simp only [CollatzResearch.WordTrace]
  refine ⟨86883965954902977821083889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57922643969935318547389259 86883965954902977821083889)
  ·
    refine ⟨65162974466177233365812917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86883965954902977821083889 65162974466177233365812917)
    ·
      refine ⟨6109028856204115628044961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65162974466177233365812917 6109028856204115628044961)
      ·
        refine ⟨4581771642153086721033721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6109028856204115628044961 4581771642153086721033721)
        ·
          refine ⟨3436328731614815040775291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4581771642153086721033721 3436328731614815040775291)
          ·
            refine ⟨5154493097422222561162937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3436328731614815040775291 5154493097422222561162937)
            ·
              refine ⟨3865869823066666920872203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5154493097422222561162937 3865869823066666920872203)
              ·
                refine ⟨5798804734600000381308305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3865869823066666920872203 5798804734600000381308305)
                ·
                  refine ⟨4349103550950000285981229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5798804734600000381308305 4349103550950000285981229)
                  ·
                    refine ⟨1630913831606250107242961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4349103550950000285981229 1630913831606250107242961)
                    ·
                      refine ⟨1223185373704687580432221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1630913831606250107242961 1223185373704687580432221)
                      ·
                        rfl

theorem cell23_2382145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_2382145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2382145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2382145 prefixEnd_2382145 := by exact prefixLift 2382145
  have htrace : WordTrace (prefixWord ++ tailWord_2382145) baseStart_2382145 baseEnd_2382145 := by
    simpa [prefixWord, tailWord_2382145, baseEnd_2382145] using wordTrace_append hprefix tailTrace_2382145
  have hstable : (prefixWord ++ tailWord_2382145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382145).length < 2 ^ (prefixWord ++ tailWord_2382145).sum := by decide
  have hdescent : baseEnd_2382145 < baseStart_2382145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382147 : List Nat := [1, 1, 1, 3, 1, 3, 4, 9]
def baseStart_2382147 : Nat := 118140960795 + 2382147 * 2 ^ 59
def prefixEnd_2382147 : Nat := 4983230072969 + 3 ^ 40 * 2382147 * 2
def baseEnd_2382147 : Nat := 45303200024666539726193

theorem tailTrace_2382147 : CollatzResearch.WordTrace tailWord_2382147 prefixEnd_2382147 45303200024666539726193 := by
  unfold tailWord_2382147
  simp only [CollatzResearch.WordTrace]
  refine ⟨86884038900895732162656695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57922692600597154775104463 86884038900895732162656695)
  ·
    refine ⟨130326058351343598243985043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86884038900895732162656695 130326058351343598243985043)
    ·
      refine ⟨195489087527015397365977565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130326058351343598243985043 195489087527015397365977565)
      ·
        refine ⟨73308407822630774012241587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 195489087527015397365977565 73308407822630774012241587)
        ·
          refine ⟨109962611733946161018362381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73308407822630774012241587 109962611733946161018362381)
          ·
            refine ⟨41235979400229810381885893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109962611733946161018362381 41235979400229810381885893)
            ·
              refine ⟨7731746137543089446603605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41235979400229810381885893 7731746137543089446603605)
              ·
                refine ⟨45303200024666539726193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7731746137543089446603605 45303200024666539726193)
                ·
                  rfl

theorem cell23_2382147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 9].length) (baseStart_2382147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2382147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2382147 prefixEnd_2382147 := by exact prefixLift 2382147
  have htrace : WordTrace (prefixWord ++ tailWord_2382147) baseStart_2382147 baseEnd_2382147 := by
    simpa [prefixWord, tailWord_2382147, baseEnd_2382147] using wordTrace_append hprefix tailTrace_2382147
  have hstable : (prefixWord ++ tailWord_2382147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382147).length < 2 ^ (prefixWord ++ tailWord_2382147).sum := by decide
  have hdescent : baseEnd_2382147 < baseStart_2382147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382161 : List Nat := [1, 2, 2, 1, 4, 4, 1, 1, 1, 1, 5]
def baseStart_2382161 : Nat := 118140960795 + 2382161 * 2 ^ 59
def prefixEnd_2382161 : Nat := 4983230072969 + 3 ^ 40 * 2382161 * 2
def baseEnd_2382161 : Nat := 1223193589395159517832147

theorem tailTrace_2382161 : CollatzResearch.WordTrace tailWord_2382161 prefixEnd_2382161 1223193589395159517832147 := by
  unfold tailWord_2382161
  simp only [CollatzResearch.WordTrace]
  refine ⟨86884549522845012553666337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57923033015230008369110891 86884549522845012553666337)
  ·
    refine ⟨65163412142133759415249753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86884549522845012553666337 65163412142133759415249753)
    ·
      refine ⟨48872559106600319561437315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65163412142133759415249753 48872559106600319561437315)
      ·
        refine ⟨73308838659900479342155973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48872559106600319561437315 73308838659900479342155973)
        ·
          refine ⟨13745407248731339876654245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73308838659900479342155973 13745407248731339876654245)
          ·
            refine ⟨2577263859137126226872671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13745407248731339876654245 2577263859137126226872671)
            ·
              refine ⟨3865895788705689340309007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2577263859137126226872671 3865895788705689340309007)
              ·
                refine ⟨5798843683058534010463511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3865895788705689340309007 5798843683058534010463511)
                ·
                  refine ⟨8698265524587801015695267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5798843683058534010463511 8698265524587801015695267)
                  ·
                    refine ⟨13047398286881701523542901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8698265524587801015695267 13047398286881701523542901)
                    ·
                      refine ⟨1223193589395159517832147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13047398286881701523542901 1223193589395159517832147)
                      ·
                        rfl

theorem cell23_2382161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 1, 5].length) (baseStart_2382161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2382161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2382161 prefixEnd_2382161 := by exact prefixLift 2382161
  have htrace : WordTrace (prefixWord ++ tailWord_2382161) baseStart_2382161 baseEnd_2382161 := by
    simpa [prefixWord, tailWord_2382161, baseEnd_2382161] using wordTrace_append hprefix tailTrace_2382161
  have hstable : (prefixWord ++ tailWord_2382161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382161).length < 2 ^ (prefixWord ++ tailWord_2382161).sum := by decide
  have hdescent : baseEnd_2382161 < baseStart_2382161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382231 : List Nat := [1, 1, 3, 3, 1, 1, 2, 2, 3, 4, 2]
def baseStart_2382231 : Nat := 118140960795 + 2382231 * 2 ^ 59
def prefixEnd_2382231 : Nat := 4983230072969 + 3 ^ 40 * 2382231 * 2
def baseEnd_2382231 : Nat := 1223229533040974243956825

theorem tailTrace_2382231 : CollatzResearch.WordTrace tailWord_2382231 prefixEnd_2382231 1223229533040974243956825 := by
  unfold tailWord_2382231
  simp only [CollatzResearch.WordTrace]
  refine ⟨86887102632591414508714547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57924735088394276339143031 86887102632591414508714547)
  ·
    refine ⟨130330653948887121763071821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86887102632591414508714547 130330653948887121763071821)
    ·
      refine ⟨48873995230832670661151933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130330653948887121763071821 48873995230832670661151933)
      ·
        refine ⟨18327748211562251497931975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48873995230832670661151933 18327748211562251497931975)
        ·
          refine ⟨27491622317343377246897963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18327748211562251497931975 27491622317343377246897963)
          ·
            refine ⟨41237433476015065870346945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27491622317343377246897963 41237433476015065870346945)
            ·
              refine ⟨30928075107011299402760209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41237433476015065870346945 30928075107011299402760209)
              ·
                refine ⟨23196056330258474552070157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30928075107011299402760209 23196056330258474552070157)
                ·
                  refine ⟨8698521123846927957026309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23196056330258474552070157 8698521123846927957026309)
                  ·
                    refine ⟨1630972710721298991942433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8698521123846927957026309 1630972710721298991942433)
                    ·
                      refine ⟨1223229533040974243956825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1630972710721298991942433 1223229533040974243956825)
                      ·
                        rfl

theorem cell23_2382231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 4, 2].length) (baseStart_2382231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2382231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2382231 prefixEnd_2382231 := by exact prefixLift 2382231
  have htrace : WordTrace (prefixWord ++ tailWord_2382231) baseStart_2382231 baseEnd_2382231 := by
    simpa [prefixWord, tailWord_2382231, baseEnd_2382231] using wordTrace_append hprefix tailTrace_2382231
  have hstable : (prefixWord ++ tailWord_2382231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382231).length < 2 ^ (prefixWord ++ tailWord_2382231).sum := by decide
  have hdescent : baseEnd_2382231 < baseStart_2382231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382301 : List Nat := [1, 4, 3, 1, 1, 1, 1, 2, 4, 5]
def baseStart_2382301 : Nat := 118140960795 + 2382301 * 2 ^ 59
def prefixEnd_2382301 : Nat := 4983230072969 + 3 ^ 40 * 2382301 * 2
def baseEnd_2382301 : Nat := 407755158895596323360501

theorem tailTrace_2382301 : CollatzResearch.WordTrace tailWord_2382301 prefixEnd_2382301 407755158895596323360501 := by
  unfold tailWord_2382301
  simp only [CollatzResearch.WordTrace]
  refine ⟨86889655742337816463762757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57926437161558544309175171 86889655742337816463762757)
  ·
    refine ⟨16291810451688340586955517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86889655742337816463762757 16291810451688340586955517)
    ·
      refine ⟨6109428919383127720108319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16291810451688340586955517 6109428919383127720108319)
      ·
        refine ⟨9164143379074691580162479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6109428919383127720108319 9164143379074691580162479)
        ·
          refine ⟨13746215068612037370243719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9164143379074691580162479 13746215068612037370243719)
          ·
            refine ⟨20619322602918056055365579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13746215068612037370243719 20619322602918056055365579)
            ·
              refine ⟨30928983904377084083048369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20619322602918056055365579 30928983904377084083048369)
              ·
                refine ⟨23196737928282813062286277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30928983904377084083048369 23196737928282813062286277)
                ·
                  refine ⟨4349388361553027449178677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23196737928282813062286277 4349388361553027449178677)
                  ·
                    refine ⟨407755158895596323360501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4349388361553027449178677 407755158895596323360501)
                    ·
                      rfl

theorem cell23_2382301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_2382301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2382301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2382301 prefixEnd_2382301 := by exact prefixLift 2382301
  have htrace : WordTrace (prefixWord ++ tailWord_2382301) baseStart_2382301 baseEnd_2382301 := by
    simpa [prefixWord, tailWord_2382301, baseEnd_2382301] using wordTrace_append hprefix tailTrace_2382301
  have hstable : (prefixWord ++ tailWord_2382301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382301).length < 2 ^ (prefixWord ++ tailWord_2382301).sum := by decide
  have hdescent : baseEnd_2382301 < baseStart_2382301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382318 : List Nat := [4, 1, 2, 1, 2, 3, 2, 1, 2, 5]
def baseStart_2382318 : Nat := 118140960795 + 2382318 * 2 ^ 59
def prefixEnd_2382318 : Nat := 4983230072969 + 3 ^ 40 * 2382318 * 2
def baseEnd_2382318 : Nat := 407758068619305134522975

theorem tailTrace_2382318 : CollatzResearch.WordTrace tailWord_2382318 prefixEnd_2382318 407758068619305134522975 := by
  unfold tailWord_2382318
  simp only [CollatzResearch.WordTrace]
  refine ⟨10861284472909528545891451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57926850522184152244754405 10861284472909528545891451)
  ·
    refine ⟨16291926709364292818837177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10861284472909528545891451 16291926709364292818837177)
    ·
      refine ⟨12218945032023219614127883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16291926709364292818837177 12218945032023219614127883)
      ·
        refine ⟨18328417548034829421191825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12218945032023219614127883 18328417548034829421191825)
        ·
          refine ⟨13746313161026122065893869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18328417548034829421191825 13746313161026122065893869)
          ·
            refine ⟨5154867435384795774710201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13746313161026122065893869 5154867435384795774710201)
            ·
              refine ⟨3866150576538596831032651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5154867435384795774710201 3866150576538596831032651)
              ·
                refine ⟨5799225864807895246548977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3866150576538596831032651 5799225864807895246548977)
                ·
                  refine ⟨4349419398605921434911733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5799225864807895246548977 4349419398605921434911733)
                  ·
                    refine ⟨407758068619305134522975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4349419398605921434911733 407758068619305134522975)
                    ·
                      rfl

theorem cell23_2382318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_2382318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2382318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2382318 prefixEnd_2382318 := by exact prefixLift 2382318
  have htrace : WordTrace (prefixWord ++ tailWord_2382318) baseStart_2382318 baseEnd_2382318 := by
    simpa [prefixWord, tailWord_2382318, baseEnd_2382318] using wordTrace_append hprefix tailTrace_2382318
  have hstable : (prefixWord ++ tailWord_2382318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382318).length < 2 ^ (prefixWord ++ tailWord_2382318).sum := by decide
  have hdescent : baseEnd_2382318 < baseStart_2382318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382372 : List Nat := [2, 3, 1, 5, 1, 2, 1, 1, 2, 1, 4]
def baseStart_2382372 : Nat := 118140960795 + 2382372 * 2 ^ 59
def prefixEnd_2382372 : Nat := 4983230072969 + 3 ^ 40 * 2382372 * 2
def baseEnd_2382372 : Nat := 1223301933813258192293677

theorem tailTrace_2382372 : CollatzResearch.WordTrace tailWord_2382372 prefixEnd_2382372 1223301933813258192293677 := by
  unfold tailWord_2382372
  simp only [CollatzResearch.WordTrace]
  refine ⟨43446122662540297794798685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57928163550053730393064913 43446122662540297794798685)
  ·
    refine ⟨16292295998452611673049507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43446122662540297794798685 16292295998452611673049507)
    ·
      refine ⟨24438443997678917509574261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16292295998452611673049507 24438443997678917509574261)
      ·
        refine ⟨2291104124782398516522587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24438443997678917509574261 2291104124782398516522587)
        ·
          refine ⟨3436656187173597774783881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2291104124782398516522587 3436656187173597774783881)
          ·
            refine ⟨2577492140380198331087911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3436656187173597774783881 2577492140380198331087911)
            ·
              refine ⟨3866238210570297496631867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2577492140380198331087911 3866238210570297496631867)
              ·
                refine ⟨5799357315855446244947801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3866238210570297496631867 5799357315855446244947801)
                ·
                  refine ⟨4349517986891584683710851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5799357315855446244947801 4349517986891584683710851)
                  ·
                    refine ⟨6524276980337377025566277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4349517986891584683710851 6524276980337377025566277)
                    ·
                      refine ⟨1223301933813258192293677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6524276980337377025566277 1223301933813258192293677)
                      ·
                        rfl

theorem cell23_2382372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_2382372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2382372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2382372 prefixEnd_2382372 := by exact prefixLift 2382372
  have htrace : WordTrace (prefixWord ++ tailWord_2382372) baseStart_2382372 baseEnd_2382372 := by
    simpa [prefixWord, tailWord_2382372, baseEnd_2382372] using wordTrace_append hprefix tailTrace_2382372
  have hstable : (prefixWord ++ tailWord_2382372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382372).length < 2 ^ (prefixWord ++ tailWord_2382372).sum := by decide
  have hdescent : baseEnd_2382372 < baseStart_2382372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382405 : List Nat := [1, 3, 1, 1, 1, 6, 2, 1, 3, 1, 3]
def baseStart_2382405 : Nat := 118140960795 + 2382405 * 2 ^ 59
def prefixEnd_2382405 : Nat := 4983230072969 + 3 ^ 40 * 2382405 * 2
def baseEnd_2382405 : Nat := 1223318878674856563181025

theorem tailTrace_2382405 : CollatzResearch.WordTrace tailWord_2382405 prefixEnd_2382405 1223318878674856563181025 := by
  unfold tailWord_2382405
  simp only [CollatzResearch.WordTrace]
  refine ⟨86893448933961042225548669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57928965955974028150365779 86893448933961042225548669)
  ·
    refine ⟨32585043350235390834580751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86893448933961042225548669 32585043350235390834580751)
    ·
      refine ⟨48877565025353086251871127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32585043350235390834580751 48877565025353086251871127)
      ·
        refine ⟨73316347538029629377806691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48877565025353086251871127 73316347538029629377806691)
        ·
          refine ⟨109974521307044444066710037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73316347538029629377806691 109974521307044444066710037)
          ·
            refine ⟨5155055686267708315627033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 109974521307044444066710037 5155055686267708315627033)
            ·
              refine ⟨3866291764700781236720275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5155055686267708315627033 3866291764700781236720275)
              ·
                refine ⟨5799437647051171855080413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3866291764700781236720275 5799437647051171855080413)
                ·
                  refine ⟨2174789117644189445655155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5799437647051171855080413 2174789117644189445655155)
                  ·
                    refine ⟨3262183676466284168482733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2174789117644189445655155 3262183676466284168482733)
                    ·
                      refine ⟨1223318878674856563181025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3262183676466284168482733 1223318878674856563181025)
                      ·
                        rfl

theorem cell23_2382405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 3, 1, 3].length) (baseStart_2382405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2382405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2382405 prefixEnd_2382405 := by exact prefixLift 2382405
  have htrace : WordTrace (prefixWord ++ tailWord_2382405) baseStart_2382405 baseEnd_2382405 := by
    simpa [prefixWord, tailWord_2382405, baseEnd_2382405] using wordTrace_append hprefix tailTrace_2382405
  have hstable : (prefixWord ++ tailWord_2382405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382405).length < 2 ^ (prefixWord ++ tailWord_2382405).sum := by decide
  have hdescent : baseEnd_2382405 < baseStart_2382405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382411 : List Nat := [1, 1, 1, 1, 3, 1, 4, 1, 5, 1, 4]
def baseStart_2382411 : Nat := 118140960795 + 2382411 * 2 ^ 59
def prefixEnd_2382411 : Nat := 4983230072969 + 3 ^ 40 * 2382411 * 2
def baseEnd_2382411 : Nat := 1223321959558783539705997

theorem tailTrace_2382411 : CollatzResearch.WordTrace tailWord_2382411 prefixEnd_2382411 1223321959558783539705997 := by
  unfold tailWord_2382411
  simp only [CollatzResearch.WordTrace]
  refine ⟨86893667771939305250267087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57929111847959536833511391 86893667771939305250267087)
  ·
    refine ⟨130340501657908957875400631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86893667771939305250267087 130340501657908957875400631)
    ·
      refine ⟨195510752486863436813100947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130340501657908957875400631 195510752486863436813100947)
      ·
        refine ⟨293266128730295155219651421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195510752486863436813100947 293266128730295155219651421)
        ·
          refine ⟨109974798273860683207369283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 293266128730295155219651421 109974798273860683207369283)
          ·
            refine ⟨164962197410791024811053925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109974798273860683207369283 164962197410791024811053925)
            ·
              refine ⟨30930412014523317152072611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 164962197410791024811053925 30930412014523317152072611)
              ·
                refine ⟨46395618021784975728108917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30930412014523317152072611 46395618021784975728108917)
                ·
                  refine ⟨4349589189542341474510211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46395618021784975728108917 4349589189542341474510211)
                  ·
                    refine ⟨6524383784313512211765317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4349589189542341474510211 6524383784313512211765317)
                    ·
                      refine ⟨1223321959558783539705997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6524383784313512211765317 1223321959558783539705997)
                      ·
                        rfl

theorem cell23_2382411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 5, 1, 4].length) (baseStart_2382411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2382411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2382411 prefixEnd_2382411 := by exact prefixLift 2382411
  have htrace : WordTrace (prefixWord ++ tailWord_2382411) baseStart_2382411 baseEnd_2382411 := by
    simpa [prefixWord, tailWord_2382411, baseEnd_2382411] using wordTrace_append hprefix tailTrace_2382411
  have hstable : (prefixWord ++ tailWord_2382411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382411).length < 2 ^ (prefixWord ++ tailWord_2382411).sum := by decide
  have hdescent : baseEnd_2382411 < baseStart_2382411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382431 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 2, 6, 3]
def baseStart_2382431 : Nat := 118140960795 + 2382431 * 2 ^ 59
def prefixEnd_2382431 : Nat := 4983230072969 + 3 ^ 40 * 2382431 * 2
def baseEnd_2382431 : Nat := 1223332229171873461455905

theorem tailTrace_2382431 : CollatzResearch.WordTrace tailWord_2382431 prefixEnd_2382431 1223332229171873461455905 := by
  unfold tailWord_2382431
  simp only [CollatzResearch.WordTrace]
  refine ⟨86894397231866848665995147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57929598154577899110663431 86894397231866848665995147)
  ·
    refine ⟨130341595847800272998992721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86894397231866848665995147 130341595847800272998992721)
    ·
      refine ⟨97756196885850204749244541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130341595847800272998992721 97756196885850204749244541)
      ·
        refine ⟨36658573832193826780966703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97756196885850204749244541 36658573832193826780966703)
        ·
          refine ⟨54987860748290740171450055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36658573832193826780966703 54987860748290740171450055)
          ·
            refine ⟨82481791122436110257175083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54987860748290740171450055 82481791122436110257175083)
            ·
              refine ⟨123722686683654165385762625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82481791122436110257175083 123722686683654165385762625)
              ·
                refine ⟨92792015012740624039321969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123722686683654165385762625 92792015012740624039321969)
                ·
                  refine ⟨69594011259555468029491477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92792015012740624039321969 69594011259555468029491477)
                  ·
                    refine ⟨3262219277791662563882413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 69594011259555468029491477 3262219277791662563882413)
                    ·
                      refine ⟨1223332229171873461455905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3262219277791662563882413 1223332229171873461455905)
                      ·
                        rfl

theorem cell23_2382431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 6, 3].length) (baseStart_2382431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2382431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2382431 prefixEnd_2382431 := by exact prefixLift 2382431
  have htrace : WordTrace (prefixWord ++ tailWord_2382431) baseStart_2382431 baseEnd_2382431 := by
    simpa [prefixWord, tailWord_2382431, baseEnd_2382431] using wordTrace_append hprefix tailTrace_2382431
  have hstable : (prefixWord ++ tailWord_2382431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382431).length < 2 ^ (prefixWord ++ tailWord_2382431).sum := by decide
  have hdescent : baseEnd_2382431 < baseStart_2382431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382441 : List Nat := [1, 2, 1, 1, 1, 4, 1, 3, 3, 2, 4]
def baseStart_2382441 : Nat := 118140960795 + 2382441 * 2 ^ 59
def prefixEnd_2382441 : Nat := 4983230072969 + 3 ^ 40 * 2382441 * 2
def baseEnd_2382441 : Nat := 1223337363978418422330859

theorem tailTrace_2382441 : CollatzResearch.WordTrace tailWord_2382441 prefixEnd_2382441 1223337363978418422330859 := by
  unfold tailWord_2382441
  simp only [CollatzResearch.WordTrace]
  refine ⟨86894761961830620373859177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57929841307887080249239451 86894761961830620373859177)
  ·
    refine ⟨65171071471372965280394383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86894761961830620373859177 65171071471372965280394383)
    ·
      refine ⟨97756607207059447920591575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65171071471372965280394383 97756607207059447920591575)
      ·
        refine ⟨146634910810589171880887363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97756607207059447920591575 146634910810589171880887363)
        ·
          refine ⟨219952366215883757821331045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146634910810589171880887363 219952366215883757821331045)
          ·
            refine ⟨41241068665478204591499571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 219952366215883757821331045 41241068665478204591499571)
            ·
              refine ⟨61861602998217306887249357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41241068665478204591499571 61861602998217306887249357)
              ·
                refine ⟨23198101124331490082718509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61861602998217306887249357 23198101124331490082718509)
                ·
                  refine ⟨8699287921624308781019441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23198101124331490082718509 8699287921624308781019441)
                  ·
                    refine ⟨6524465941218231585764581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8699287921624308781019441 6524465941218231585764581)
                    ·
                      refine ⟨1223337363978418422330859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6524465941218231585764581 1223337363978418422330859)
                      ·
                        rfl

theorem cell23_2382441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 2, 4].length) (baseStart_2382441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2382441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2382441 prefixEnd_2382441 := by exact prefixLift 2382441
  have htrace : WordTrace (prefixWord ++ tailWord_2382441) baseStart_2382441 baseEnd_2382441 := by
    simpa [prefixWord, tailWord_2382441, baseEnd_2382441] using wordTrace_append hprefix tailTrace_2382441
  have hstable : (prefixWord ++ tailWord_2382441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382441).length < 2 ^ (prefixWord ++ tailWord_2382441).sum := by decide
  have hdescent : baseEnd_2382441 < baseStart_2382441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382445 : List Nat := [1, 5, 1, 1, 3, 1, 2, 3, 1, 1, 4]
def baseStart_2382445 : Nat := 118140960795 + 2382445 * 2 ^ 59
def prefixEnd_2382445 : Nat := 4983230072969 + 3 ^ 40 * 2382445 * 2
def baseEnd_2382445 : Nat := 1223339417901036406680841

theorem tailTrace_2382445 : CollatzResearch.WordTrace tailWord_2382445 prefixEnd_2382445 1223339417901036406680841 := by
  unfold tailWord_2382445
  simp only [CollatzResearch.WordTrace]
  refine ⟨86894907853816129057004789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57929938569210752704669859 86894907853816129057004789)
  ·
    refine ⟨8146397611295262099094199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 86894907853816129057004789 8146397611295262099094199)
    ·
      refine ⟨12219596416942893148641299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8146397611295262099094199 12219596416942893148641299)
      ·
        refine ⟨18329394625414339722961949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12219596416942893148641299 18329394625414339722961949)
        ·
          refine ⟨6873522984530377396110731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18329394625414339722961949 6873522984530377396110731)
          ·
            refine ⟨10310284476795566094166097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6873522984530377396110731 10310284476795566094166097)
            ·
              refine ⟨7732713357596674570624573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10310284476795566094166097 7732713357596674570624573)
              ·
                refine ⟨2899767509098752963984215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7732713357596674570624573 2899767509098752963984215)
                ·
                  refine ⟨4349651263648129445976323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2899767509098752963984215 4349651263648129445976323)
                  ·
                    refine ⟨6524476895472194168964485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4349651263648129445976323 6524476895472194168964485)
                    ·
                      refine ⟨1223339417901036406680841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6524476895472194168964485 1223339417901036406680841)
                      ·
                        rfl

theorem cell23_2382445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_2382445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2382445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2382445 prefixEnd_2382445 := by exact prefixLift 2382445
  have htrace : WordTrace (prefixWord ++ tailWord_2382445) baseStart_2382445 baseEnd_2382445 := by
    simpa [prefixWord, tailWord_2382445, baseEnd_2382445] using wordTrace_append hprefix tailTrace_2382445
  have hstable : (prefixWord ++ tailWord_2382445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382445).length < 2 ^ (prefixWord ++ tailWord_2382445).sum := by decide
  have hdescent : baseEnd_2382445 < baseStart_2382445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382468 : List Nat := [2, 3, 2, 1, 3, 2, 2, 8]
def baseStart_2382468 : Nat := 118140960795 + 2382468 * 2 ^ 59
def prefixEnd_2382468 : Nat := 4983230072969 + 3 ^ 40 * 2382468 * 2
def baseEnd_2382468 : Nat := 45309304739114437655305

theorem tailTrace_2382468 : CollatzResearch.WordTrace tailWord_2382468 prefixEnd_2382468 45309304739114437655305 := by
  unfold tailWord_2382468
  simp only [CollatzResearch.WordTrace]
  refine ⟨43447873366366401992546029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57930497821821869323394705 43447873366366401992546029)
  ·
    refine ⟨16292952512387400747204761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43447873366366401992546029 16292952512387400747204761)
    ·
      refine ⟨12219714384290550560403571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16292952512387400747204761 12219714384290550560403571)
      ·
        refine ⟨18329571576435825840605357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12219714384290550560403571 18329571576435825840605357)
        ·
          refine ⟨6873589341163434690227009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18329571576435825840605357 6873589341163434690227009)
          ·
            refine ⟨5155192005872576017670257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6873589341163434690227009 5155192005872576017670257)
            ·
              refine ⟨3866394004404432013252693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5155192005872576017670257 3866394004404432013252693)
              ·
                refine ⟨45309304739114437655305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3866394004404432013252693 45309304739114437655305)
                ·
                  rfl

theorem cell23_2382468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 8].length) (baseStart_2382468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2382468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2382468 prefixEnd_2382468 := by exact prefixLift 2382468
  have htrace : WordTrace (prefixWord ++ tailWord_2382468) baseStart_2382468 baseEnd_2382468 := by
    simpa [prefixWord, tailWord_2382468, baseEnd_2382468] using wordTrace_append hprefix tailTrace_2382468
  have hstable : (prefixWord ++ tailWord_2382468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382468).length < 2 ^ (prefixWord ++ tailWord_2382468).sum := by decide
  have hdescent : baseEnd_2382468 < baseStart_2382468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382471 : List Nat := [1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 6]
def baseStart_2382471 : Nat := 118140960795 + 2382471 * 2 ^ 59
def prefixEnd_2382471 : Nat := 4983230072969 + 3 ^ 40 * 2382471 * 2
def baseEnd_2382471 : Nat := 1223352768398053304955721

theorem tailTrace_2382471 : CollatzResearch.WordTrace tailWord_2382471 prefixEnd_2382471 1223352768398053304955721 := by
  unfold tailWord_2382471
  simp only [CollatzResearch.WordTrace]
  refine ⟨86895856151721935497451267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57930570767814623664967511 86895856151721935497451267)
  ·
    refine ⟨130343784227582903246176901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86895856151721935497451267 130343784227582903246176901)
    ·
      refine ⟨24439459542671794358658169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130343784227582903246176901 24439459542671794358658169)
      ·
        refine ⟨18329594657003845768993627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24439459542671794358658169 18329594657003845768993627)
        ·
          refine ⟨27494391985505768653490441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18329594657003845768993627 27494391985505768653490441)
          ·
            refine ⟨20620793989129326490117831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27494391985505768653490441 20620793989129326490117831)
            ·
              refine ⟨30931190983693989735176747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20620793989129326490117831 30931190983693989735176747)
              ·
                refine ⟨46396786475540984602765121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30931190983693989735176747 46396786475540984602765121)
                ·
                  refine ⟨34797589856655738452073841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46396786475540984602765121 34797589856655738452073841)
                  ·
                    refine ⟨26098192392491803839055381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34797589856655738452073841 26098192392491803839055381)
                    ·
                      refine ⟨1223352768398053304955721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26098192392491803839055381 1223352768398053304955721)
                      ·
                        rfl

theorem cell23_2382471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_2382471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2382471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2382471 prefixEnd_2382471 := by exact prefixLift 2382471
  have htrace : WordTrace (prefixWord ++ tailWord_2382471) baseStart_2382471 baseEnd_2382471 := by
    simpa [prefixWord, tailWord_2382471, baseEnd_2382471] using wordTrace_append hprefix tailTrace_2382471
  have hstable : (prefixWord ++ tailWord_2382471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382471).length < 2 ^ (prefixWord ++ tailWord_2382471).sum := by decide
  have hdescent : baseEnd_2382471 < baseStart_2382471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382482 : List Nat := [3, 2, 3, 1, 2, 1, 3, 2, 1, 2, 3]
def baseStart_2382482 : Nat := 118140960795 + 2382482 * 2 ^ 59
def prefixEnd_2382482 : Nat := 4983230072969 + 3 ^ 40 * 2382482 * 2
def baseEnd_2382482 : Nat := 1223358416685252761918171

theorem tailTrace_2382482 : CollatzResearch.WordTrace tailWord_2382482 prefixEnd_2382482 1223358416685252761918171 := by
  unfold tailWord_2382482
  simp only [CollatzResearch.WordTrace]
  refine ⟨21724064338670521094025425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57930838236454722917401133 21724064338670521094025425)
  ·
    refine ⟨16293048254002890820519069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21724064338670521094025425 16293048254002890820519069)
    ·
      refine ⟨6109893095251084057694651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16293048254002890820519069 6109893095251084057694651)
      ·
        refine ⟨9164839642876626086541977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6109893095251084057694651 9164839642876626086541977)
        ·
          refine ⟨6873629732157469564906483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9164839642876626086541977 6873629732157469564906483)
          ·
            refine ⟨10310444598236204347359725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6873629732157469564906483 10310444598236204347359725)
            ·
              refine ⟨3866416724338576630259897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10310444598236204347359725 3866416724338576630259897)
              ·
                refine ⟨2899812543253932472694923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3866416724338576630259897 2899812543253932472694923)
                ·
                  refine ⟨4349718814880898709042385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2899812543253932472694923 4349718814880898709042385)
                  ·
                    refine ⟨3262289111160674031781789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4349718814880898709042385 3262289111160674031781789)
                    ·
                      refine ⟨1223358416685252761918171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3262289111160674031781789 1223358416685252761918171)
                      ·
                        rfl

theorem cell23_2382482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_2382482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2382482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2382482 prefixEnd_2382482 := by exact prefixLift 2382482
  have htrace : WordTrace (prefixWord ++ tailWord_2382482) baseStart_2382482 baseEnd_2382482 := by
    simpa [prefixWord, tailWord_2382482, baseEnd_2382482] using wordTrace_append hprefix tailTrace_2382482
  have hstable : (prefixWord ++ tailWord_2382482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382482).length < 2 ^ (prefixWord ++ tailWord_2382482).sum := by decide
  have hdescent : baseEnd_2382482 < baseStart_2382482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382528 : List Nat := [2, 1, 1, 2, 4, 3, 1, 1, 2, 6]
def baseStart_2382528 : Nat := 118140960795 + 2382528 * 2 ^ 59
def prefixEnd_2382528 : Nat := 4983230072969 + 3 ^ 40 * 2382528 * 2
def baseEnd_2382528 : Nat := 407794012265119860647653

theorem tailTrace_2382528 : CollatzResearch.WordTrace tailWord_2382528 prefixEnd_2382528 407794012265119860647653 := by
  unfold tailWord_2382528
  simp only [CollatzResearch.WordTrace]
  refine ⟨43448967556257717116138119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57931956741676956154850825 43448967556257717116138119)
  ·
    refine ⟨65173451334386575674207179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43448967556257717116138119 65173451334386575674207179)
    ·
      refine ⟨97760177001579863511310769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65173451334386575674207179 97760177001579863511310769)
      ·
        refine ⟨73320132751184897633483077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97760177001579863511310769 73320132751184897633483077)
        ·
          refine ⟨13747524890847168306278077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73320132751184897633483077 13747524890847168306278077)
          ·
            refine ⟨5155321834067688114854279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13747524890847168306278077 5155321834067688114854279)
            ·
              refine ⟨7732982751101532172281419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5155321834067688114854279 7732982751101532172281419)
              ·
                refine ⟨11599474126652298258422129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7732982751101532172281419 11599474126652298258422129)
                ·
                  refine ⟨8699605594989223693816597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11599474126652298258422129 8699605594989223693816597)
                  ·
                    refine ⟨407794012265119860647653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8699605594989223693816597 407794012265119860647653)
                    ·
                      rfl

theorem cell23_2382528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 2, 6].length) (baseStart_2382528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2382528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2382528 prefixEnd_2382528 := by exact prefixLift 2382528
  have htrace : WordTrace (prefixWord ++ tailWord_2382528) baseStart_2382528 baseEnd_2382528 := by
    simpa [prefixWord, tailWord_2382528, baseEnd_2382528] using wordTrace_append hprefix tailTrace_2382528
  have hstable : (prefixWord ++ tailWord_2382528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382528).length < 2 ^ (prefixWord ++ tailWord_2382528).sum := by decide
  have hdescent : baseEnd_2382528 < baseStart_2382528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382529 : List Nat := [1, 2, 6, 2, 1, 1, 2, 1, 1, 3, 3]
def baseStart_2382529 : Nat := 118140960795 + 2382529 * 2 ^ 59
def prefixEnd_2382529 : Nat := 4983230072969 + 3 ^ 40 * 2382529 * 2
def baseEnd_2382529 : Nat := 1223382550276014078030455

theorem tailTrace_2382529 : CollatzResearch.WordTrace tailWord_2382529 prefixEnd_2382529 1223382550276014078030455 := by
  unfold tailWord_2382529
  simp only [CollatzResearch.WordTrace]
  refine ⟨86897971585511811403062641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57931981057007874268708427 86897971585511811403062641)
  ·
    refine ⟨65173478689133858552296981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86897971585511811403062641 65173478689133858552296981)
    ·
      refine ⟨3055006813553149619638921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 65173478689133858552296981 3055006813553149619638921)
      ·
        refine ⟨2291255110164862214729191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3055006813553149619638921 2291255110164862214729191)
        ·
          refine ⟨3436882665247293322093787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2291255110164862214729191 3436882665247293322093787)
          ·
            refine ⟨5155323997870939983140681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3436882665247293322093787 5155323997870939983140681)
            ·
              refine ⟨3866492998403204987355511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5155323997870939983140681 3866492998403204987355511)
              ·
                refine ⟨5799739497604807481033267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3866492998403204987355511 5799739497604807481033267)
                ·
                  refine ⟨8699609246407211221549901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5799739497604807481033267 8699609246407211221549901)
                  ·
                    refine ⟨3262353467402704208081213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8699609246407211221549901 3262353467402704208081213)
                    ·
                      refine ⟨1223382550276014078030455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3262353467402704208081213 1223382550276014078030455)
                      ·
                        rfl

theorem cell23_2382529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_2382529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2382529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2382529 prefixEnd_2382529 := by exact prefixLift 2382529
  have htrace : WordTrace (prefixWord ++ tailWord_2382529) baseStart_2382529 baseEnd_2382529 := by
    simpa [prefixWord, tailWord_2382529, baseEnd_2382529] using wordTrace_append hprefix tailTrace_2382529
  have hstable : (prefixWord ++ tailWord_2382529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382529).length < 2 ^ (prefixWord ++ tailWord_2382529).sum := by decide
  have hdescent : baseEnd_2382529 < baseStart_2382529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382556 : List Nat := [2, 2, 5, 1, 1, 1, 4, 1, 1, 3, 2]
def baseStart_2382556 : Nat := 118140960795 + 2382556 * 2 ^ 59
def prefixEnd_2382556 : Nat := 4983230072969 + 3 ^ 40 * 2382556 * 2
def baseEnd_2382556 : Nat := 1223396414253685472392831

theorem tailTrace_2382556 : CollatzResearch.WordTrace tailWord_2382556 prefixEnd_2382556 1223396414253685472392831 := by
  unfold tailWord_2382556
  simp only [CollatzResearch.WordTrace]
  refine ⟨43449478178206997507147761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57932637570942663342863681 43449478178206997507147761)
  ·
    refine ⟨32587108633655248130360821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43449478178206997507147761 32587108633655248130360821)
    ·
      refine ⟨3055041434405179512221327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32587108633655248130360821 3055041434405179512221327)
      ·
        refine ⟨4582562151607769268331991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3055041434405179512221327 4582562151607769268331991)
        ·
          refine ⟨6873843227411653902497987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4582562151607769268331991 6873843227411653902497987)
          ·
            refine ⟨10310764841117480853746981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6873843227411653902497987 10310764841117480853746981)
            ·
              refine ⟨1933268407709527660077559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10310764841117480853746981 1933268407709527660077559)
              ·
                refine ⟨2899902611564291490116339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1933268407709527660077559 2899902611564291490116339)
                ·
                  refine ⟨4349853917346437235174509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2899902611564291490116339 4349853917346437235174509)
                  ·
                    refine ⟨1631195219004913963190441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4349853917346437235174509 1631195219004913963190441)
                    ·
                      refine ⟨1223396414253685472392831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1631195219004913963190441 1223396414253685472392831)
                      ·
                        rfl

theorem cell23_2382556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_2382556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2382556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2382556 prefixEnd_2382556 := by exact prefixLift 2382556
  have htrace : WordTrace (prefixWord ++ tailWord_2382556) baseStart_2382556 baseEnd_2382556 := by
    simpa [prefixWord, tailWord_2382556, baseEnd_2382556] using wordTrace_append hprefix tailTrace_2382556
  have hstable : (prefixWord ++ tailWord_2382556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382556).length < 2 ^ (prefixWord ++ tailWord_2382556).sum := by decide
  have hdescent : baseEnd_2382556 < baseStart_2382556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382575 : List Nat := [1, 1, 2, 1, 5, 2, 2, 4, 5]
def baseStart_2382575 : Nat := 118140960795 + 2382575 * 2 ^ 59
def prefixEnd_2382575 : Nat := 4983230072969 + 3 ^ 40 * 2382575 * 2
def baseEnd_2382575 : Nat := 135934018931791210895027

theorem tailTrace_2382575 : CollatzResearch.WordTrace tailWord_2382575 prefixEnd_2382575 135934018931791210895027 := by
  unfold tailWord_2382575
  simp only [CollatzResearch.WordTrace]
  refine ⟨86899649343345161259237179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57933099562230107506158119 86899649343345161259237179)
  ·
    refine ⟨130349474015017741888855769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86899649343345161259237179 130349474015017741888855769)
    ·
      refine ⟨97762105511263306416641827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130349474015017741888855769 97762105511263306416641827)
      ·
        refine ⟨146643158266894959624962741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97762105511263306416641827 146643158266894959624962741)
        ·
          refine ⟨13747796087521402464840257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 146643158266894959624962741 13747796087521402464840257)
          ·
            refine ⟨10310847065641051848630193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13747796087521402464840257 10310847065641051848630193)
            ·
              refine ⟨7733135299230788886472645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10310847065641051848630193 7733135299230788886472645)
              ·
                refine ⟨1449962868605772916213621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7733135299230788886472645 1449962868605772916213621)
                ·
                  refine ⟨135934018931791210895027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1449962868605772916213621 135934018931791210895027)
                  ·
                    rfl

theorem cell23_2382575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 4, 5].length) (baseStart_2382575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2382575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2382575 prefixEnd_2382575 := by exact prefixLift 2382575
  have htrace : WordTrace (prefixWord ++ tailWord_2382575) baseStart_2382575 baseEnd_2382575 := by
    simpa [prefixWord, tailWord_2382575, baseEnd_2382575] using wordTrace_append hprefix tailTrace_2382575
  have hstable : (prefixWord ++ tailWord_2382575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382575).length < 2 ^ (prefixWord ++ tailWord_2382575).sum := by decide
  have hdescent : baseEnd_2382575 < baseStart_2382575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382588 : List Nat := [2, 2, 2, 1, 3, 2, 1, 2, 1, 7]
def baseStart_2382588 : Nat := 118140960795 + 2382588 * 2 ^ 59
def prefixEnd_2382588 : Nat := 4983230072969 + 3 ^ 40 * 2382588 * 2
def baseEnd_2382588 : Nat := 407804281878209782397561

theorem tailTrace_2382588 : CollatzResearch.WordTrace tailWord_2382588 prefixEnd_2382588 407804281878209782397561 := by
  unfold tailWord_2382588
  simp only [CollatzResearch.WordTrace]
  refine ⟨43450061746149032239730209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57933415661532042986306945 43450061746149032239730209)
  ·
    refine ⟨32587546309611774179797657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43450061746149032239730209 32587546309611774179797657)
    ·
      refine ⟨24440659732208830634848243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32587546309611774179797657 24440659732208830634848243)
      ·
        refine ⟨36660989598313245952272365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24440659732208830634848243 36660989598313245952272365)
        ·
          refine ⟨13747871099367467232102137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36660989598313245952272365 13747871099367467232102137)
          ·
            refine ⟨10310903324525600424076603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13747871099367467232102137 10310903324525600424076603)
            ·
              refine ⟨15466354986788400636114905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10310903324525600424076603 15466354986788400636114905)
              ·
                refine ⟨11599766240091300477086179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15466354986788400636114905 11599766240091300477086179)
                ·
                  refine ⟨17399649360136950715629269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11599766240091300477086179 17399649360136950715629269)
                  ·
                    refine ⟨407804281878209782397561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17399649360136950715629269 407804281878209782397561)
                    ·
                      rfl

theorem cell23_2382588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 1, 7].length) (baseStart_2382588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2382588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2382588 prefixEnd_2382588 := by exact prefixLift 2382588
  have htrace : WordTrace (prefixWord ++ tailWord_2382588) baseStart_2382588 baseEnd_2382588 := by
    simpa [prefixWord, tailWord_2382588, baseEnd_2382588] using wordTrace_append hprefix tailTrace_2382588
  have hstable : (prefixWord ++ tailWord_2382588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382588).length < 2 ^ (prefixWord ++ tailWord_2382588).sum := by decide
  have hdescent : baseEnd_2382588 < baseStart_2382588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382625 : List Nat := [1, 2, 3, 2, 1, 2, 3, 2, 2, 1, 4]
def baseStart_2382625 : Nat := 118140960795 + 2382625 * 2 ^ 59
def prefixEnd_2382625 : Nat := 4983230072969 + 3 ^ 40 * 2382625 * 2
def baseEnd_2382625 : Nat := 1223431844418845702430013

theorem tailTrace_2382625 : CollatzResearch.WordTrace tailWord_2382625 prefixEnd_2382625 1223431844418845702430013 := by
  unfold tailWord_2382625
  simp only [CollatzResearch.WordTrace]
  refine ⟨86901472993164019798557329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57934315328776013199038219 86901472993164019798557329)
  ·
    refine ⟨65176104744873014848917997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86901472993164019798557329 65176104744873014848917997)
    ·
      refine ⟨24441039279327380568344249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65176104744873014848917997 24441039279327380568344249)
      ·
        refine ⟨18330779459495535426258187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24441039279327380568344249 18330779459495535426258187)
        ·
          refine ⟨27496169189243303139387281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18330779459495535426258187 27496169189243303139387281)
          ·
            refine ⟨20622126891932477354540461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27496169189243303139387281 20622126891932477354540461)
            ·
              refine ⟨7733297584474679007952673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20622126891932477354540461 7733297584474679007952673)
              ·
                refine ⟨5799973188356009255964505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7733297584474679007952673 5799973188356009255964505)
                ·
                  refine ⟨4349979891267006941973379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5799973188356009255964505 4349979891267006941973379)
                  ·
                    refine ⟨6524969836900510412960069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4349979891267006941973379 6524969836900510412960069)
                    ·
                      refine ⟨1223431844418845702430013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6524969836900510412960069 1223431844418845702430013)
                      ·
                        rfl

theorem cell23_2382625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_2382625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2382625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2382625 prefixEnd_2382625 := by exact prefixLift 2382625
  have htrace : WordTrace (prefixWord ++ tailWord_2382625) baseStart_2382625 baseEnd_2382625 := by
    simpa [prefixWord, tailWord_2382625, baseEnd_2382625] using wordTrace_append hprefix tailTrace_2382625
  have hstable : (prefixWord ++ tailWord_2382625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382625).length < 2 ^ (prefixWord ++ tailWord_2382625).sum := by decide
  have hdescent : baseEnd_2382625 < baseStart_2382625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382637 : List Nat := [1, 5, 3, 2, 2, 1, 2, 1, 2, 2, 2]
def baseStart_2382637 : Nat := 118140960795 + 2382637 * 2 ^ 59
def prefixEnd_2382637 : Nat := 4983230072969 + 3 ^ 40 * 2382637 * 2
def baseEnd_2382637 : Nat := 1223438006186699655479959

theorem tailTrace_2382637 : CollatzResearch.WordTrace tailWord_2382637 prefixEnd_2382637 1223438006186699655479959 := by
  unfold tailWord_2382637
  simp only [CollatzResearch.WordTrace]
  refine ⟨86901910669120545847994165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57934607112747030565329443 86901910669120545847994165)
  ·
    refine ⟨8147054125230051173249453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 86901910669120545847994165 8147054125230051173249453)
    ·
      refine ⟨3055145296961269189968545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8147054125230051173249453 3055145296961269189968545)
      ·
        refine ⟨2291358972720951892476409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3055145296961269189968545 2291358972720951892476409)
        ·
          refine ⟨1718519229540713919357307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2291358972720951892476409 1718519229540713919357307)
          ·
            refine ⟨2577778844311070879035961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1718519229540713919357307 2577778844311070879035961)
            ·
              refine ⟨1933334133233303159276971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2577778844311070879035961 1933334133233303159276971)
              ·
                refine ⟨2900001199849954738915457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1933334133233303159276971 2900001199849954738915457)
                ·
                  refine ⟨2175000899887466054186593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2900001199849954738915457 2175000899887466054186593)
                  ·
                    refine ⟨1631250674915599540639945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2175000899887466054186593 1631250674915599540639945)
                    ·
                      refine ⟨1223438006186699655479959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1631250674915599540639945 1223438006186699655479959)
                      ·
                        rfl

theorem cell23_2382637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_2382637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2382637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2382637 prefixEnd_2382637 := by exact prefixLift 2382637
  have htrace : WordTrace (prefixWord ++ tailWord_2382637) baseStart_2382637 baseEnd_2382637 := by
    simpa [prefixWord, tailWord_2382637, baseEnd_2382637] using wordTrace_append hprefix tailTrace_2382637
  have hstable : (prefixWord ++ tailWord_2382637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382637).length < 2 ^ (prefixWord ++ tailWord_2382637).sum := by decide
  have hdescent : baseEnd_2382637 < baseStart_2382637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382695 : List Nat := [1, 1, 5, 1, 2, 2, 1, 2, 3, 5]
def baseStart_2382695 : Nat := 118140960795 + 2382695 * 2 ^ 59
def prefixEnd_2382695 : Nat := 4983230072969 + 3 ^ 40 * 2382695 * 2
def baseEnd_2382695 : Nat := 407822596021553476184897

theorem tailTrace_2382695 : CollatzResearch.WordTrace tailWord_2382695 prefixEnd_2382695 407822596021553476184897 := by
  unfold tailWord_2382695
  simp only [CollatzResearch.WordTrace]
  refine ⟨86904026102910421753605539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57936017401940281169070359 86904026102910421753605539)
  ·
    refine ⟨130356039154365632630408309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86904026102910421753605539 130356039154365632630408309)
    ·
      refine ⟨12220878670721778059100779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 130356039154365632630408309 12220878670721778059100779)
      ·
        refine ⟨18331318006082667088651169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12220878670721778059100779 18331318006082667088651169)
        ·
          refine ⟨13748488504562000316488377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18331318006082667088651169 13748488504562000316488377)
          ·
            refine ⟨10311366378421500237366283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13748488504562000316488377 10311366378421500237366283)
            ·
              refine ⟨15467049567632250356049425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10311366378421500237366283 15467049567632250356049425)
              ·
                refine ⟨11600287175724187767037069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15467049567632250356049425 11600287175724187767037069)
                ·
                  refine ⟨4350107690896570412638901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11600287175724187767037069 4350107690896570412638901)
                  ·
                    refine ⟨407822596021553476184897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4350107690896570412638901 407822596021553476184897)
                    ·
                      rfl

theorem cell23_2382695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_2382695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2382695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2382695 prefixEnd_2382695 := by exact prefixLift 2382695
  have htrace : WordTrace (prefixWord ++ tailWord_2382695) baseStart_2382695 baseEnd_2382695 := by
    simpa [prefixWord, tailWord_2382695, baseEnd_2382695] using wordTrace_append hprefix tailTrace_2382695
  have hstable : (prefixWord ++ tailWord_2382695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382695).length < 2 ^ (prefixWord ++ tailWord_2382695).sum := by decide
  have hdescent : baseEnd_2382695 < baseStart_2382695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382709 : List Nat := [1, 3, 4, 1, 1, 3, 1, 2, 3, 1, 3]
def baseStart_2382709 : Nat := 118140960795 + 2382709 * 2 ^ 59
def prefixEnd_2382709 : Nat := 4983230072969 + 3 ^ 40 * 2382709 * 2
def baseEnd_2382709 : Nat := 1223474976793823373779627

theorem tailTrace_2382709 : CollatzResearch.WordTrace tailWord_2382709 prefixEnd_2382709 1223474976793823373779627 := by
  unfold tailWord_2382709
  simp only [CollatzResearch.WordTrace]
  refine ⟨86904536724859702144615181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57936357816573134763076787 86904536724859702144615181)
  ·
    refine ⟨32589201271822388304230693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86904536724859702144615181 32589201271822388304230693)
    ·
      refine ⟨6110475238466697807043255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32589201271822388304230693 6110475238466697807043255)
      ·
        refine ⟨9165712857700046710564883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6110475238466697807043255 9165712857700046710564883)
        ·
          refine ⟨13748569286550070065847325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9165712857700046710564883 13748569286550070065847325)
          ·
            refine ⟨5155713482456276274692747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13748569286550070065847325 5155713482456276274692747)
            ·
              refine ⟨7733570223684414412039121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5155713482456276274692747 7733570223684414412039121)
              ·
                refine ⟨5800177667763310809029341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7733570223684414412039121 5800177667763310809029341)
                ·
                  refine ⟨2175066625411241553386003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5800177667763310809029341 2175066625411241553386003)
                  ·
                    refine ⟨3262599938116862330079005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2175066625411241553386003 3262599938116862330079005)
                    ·
                      refine ⟨1223474976793823373779627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3262599938116862330079005 1223474976793823373779627)
                      ·
                        rfl

theorem cell23_2382709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_2382709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2382709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2382709 prefixEnd_2382709 := by exact prefixLift 2382709
  have htrace : WordTrace (prefixWord ++ tailWord_2382709) baseStart_2382709 baseEnd_2382709 := by
    simpa [prefixWord, tailWord_2382709, baseEnd_2382709] using wordTrace_append hprefix tailTrace_2382709
  have hstable : (prefixWord ++ tailWord_2382709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382709).length < 2 ^ (prefixWord ++ tailWord_2382709).sum := by decide
  have hdescent : baseEnd_2382709 < baseStart_2382709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382715 : List Nat := [1, 1, 1, 1, 1, 5, 4, 1, 3, 1, 4]
def baseStart_2382715 : Nat := 118140960795 + 2382715 * 2 ^ 59
def prefixEnd_2382715 : Nat := 4983230072969 + 3 ^ 40 * 2382715 * 2
def baseEnd_2382715 : Nat := 1223478057677750350304599

theorem tailTrace_2382715 : CollatzResearch.WordTrace tailWord_2382715 prefixEnd_2382715 1223478057677750350304599 := by
  unfold tailWord_2382715
  simp only [CollatzResearch.WordTrace]
  refine ⟨86904755562837965169333599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57936503708558643446222399 86904755562837965169333599)
  ·
    refine ⟨130357133344256947754000399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86904755562837965169333599 130357133344256947754000399)
    ·
      refine ⟨195535700016385421631000599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130357133344256947754000399 195535700016385421631000599)
      ·
        refine ⟨293303550024578132446500899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195535700016385421631000599 293303550024578132446500899)
        ·
          refine ⟨439955325036867198669751349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293303550024578132446500899 439955325036867198669751349)
          ·
            refine ⟨41245811722206299875289189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 439955325036867198669751349 41245811722206299875289189)
            ·
              refine ⟨7733589697913681226616723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41245811722206299875289189 7733589697913681226616723)
              ·
                refine ⟨11600384546870521839925085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7733589697913681226616723 11600384546870521839925085)
                ·
                  refine ⟨4350144205076445689971907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11600384546870521839925085 4350144205076445689971907)
                  ·
                    refine ⟨6525216307614668534957861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4350144205076445689971907 6525216307614668534957861)
                    ·
                      refine ⟨1223478057677750350304599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6525216307614668534957861 1223478057677750350304599)
                      ·
                        rfl

theorem cell23_2382715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 3, 1, 4].length) (baseStart_2382715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2382715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2382715 prefixEnd_2382715 := by exact prefixLift 2382715
  have htrace : WordTrace (prefixWord ++ tailWord_2382715) baseStart_2382715 baseEnd_2382715 := by
    simpa [prefixWord, tailWord_2382715, baseEnd_2382715] using wordTrace_append hprefix tailTrace_2382715
  have hstable : (prefixWord ++ tailWord_2382715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382715).length < 2 ^ (prefixWord ++ tailWord_2382715).sum := by decide
  have hdescent : baseEnd_2382715 < baseStart_2382715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382725 : List Nat := [1, 3, 1, 1, 3, 3, 2, 2, 1, 6]
def baseStart_2382725 : Nat := 118140960795 + 2382725 * 2 ^ 59
def prefixEnd_2382725 : Nat := 4983230072969 + 3 ^ 40 * 2382725 * 2
def baseEnd_2382725 : Nat := 407827730828098437059851

theorem tailTrace_2382725 : CollatzResearch.WordTrace tailWord_2382725 prefixEnd_2382725 407827730828098437059851 := by
  unfold tailWord_2382725
  simp only [CollatzResearch.WordTrace]
  refine ⟨86905120292801736877197629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57936746861867824584798419 86905120292801736877197629)
  ·
    refine ⟨32589420109800651328949111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86905120292801736877197629 32589420109800651328949111)
    ·
      refine ⟨48884130164700976993423667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32589420109800651328949111 48884130164700976993423667)
      ·
        refine ⟨73326195247051465490135501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48884130164700976993423667 73326195247051465490135501)
        ·
          refine ⟨27497323217644299558800813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73326195247051465490135501 27497323217644299558800813)
          ·
            refine ⟨10311496206616612334550305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27497323217644299558800813 10311496206616612334550305)
            ·
              refine ⟨7733622154962459250912729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10311496206616612334550305 7733622154962459250912729)
              ·
                refine ⟨5800216616221844438184547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7733622154962459250912729 5800216616221844438184547)
                ·
                  refine ⟨8700324924332766657276821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5800216616221844438184547 8700324924332766657276821)
                  ·
                    refine ⟨407827730828098437059851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8700324924332766657276821 407827730828098437059851)
                    ·
                      rfl

theorem cell23_2382725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 6].length) (baseStart_2382725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2382725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2382725 prefixEnd_2382725 := by exact prefixLift 2382725
  have htrace : WordTrace (prefixWord ++ tailWord_2382725) baseStart_2382725 baseEnd_2382725 := by
    simpa [prefixWord, tailWord_2382725, baseEnd_2382725] using wordTrace_append hprefix tailTrace_2382725
  have hstable : (prefixWord ++ tailWord_2382725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382725).length < 2 ^ (prefixWord ++ tailWord_2382725).sum := by decide
  have hdescent : baseEnd_2382725 < baseStart_2382725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382729 : List Nat := [1, 2, 1, 1, 5, 4, 2, 1, 1, 5]
def baseStart_2382729 : Nat := 118140960795 + 2382729 * 2 ^ 59
def prefixEnd_2382729 : Nat := 4983230072969 + 3 ^ 40 * 2382729 * 2
def baseEnd_2382729 : Nat := 407828415468971098509845

theorem tailTrace_2382729 : CollatzResearch.WordTrace tailWord_2382729 prefixEnd_2382729 407828415468971098509845 := by
  unfold tailWord_2382729
  simp only [CollatzResearch.WordTrace]
  refine ⟨86905266184787245560343241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57936844123191497040228827 86905266184787245560343241)
  ·
    refine ⟨65178949638590434170257431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86905266184787245560343241 65178949638590434170257431)
    ·
      refine ⟨97768424457885651255386147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65178949638590434170257431 97768424457885651255386147)
      ·
        refine ⟨146652636686828476883079221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97768424457885651255386147 146652636686828476883079221)
        ·
          refine ⟨13748684689390169707788677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 146652636686828476883079221 13748684689390169707788677)
          ·
            refine ⟨2577878379260656820210377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13748684689390169707788677 2577878379260656820210377)
            ·
              refine ⟨1933408784445492615157783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2577878379260656820210377 1933408784445492615157783)
              ·
                refine ⟨2900113176668238922736675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1933408784445492615157783 2900113176668238922736675)
                ·
                  refine ⟨4350169765002358384105013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2900113176668238922736675 4350169765002358384105013)
                  ·
                    refine ⟨407828415468971098509845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4350169765002358384105013 407828415468971098509845)
                    ·
                      rfl

theorem cell23_2382729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 1, 1, 5].length) (baseStart_2382729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2382729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2382729 prefixEnd_2382729 := by exact prefixLift 2382729
  have htrace : WordTrace (prefixWord ++ tailWord_2382729) baseStart_2382729 baseEnd_2382729 := by
    simpa [prefixWord, tailWord_2382729, baseEnd_2382729] using wordTrace_append hprefix tailTrace_2382729
  have hstable : (prefixWord ++ tailWord_2382729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382729).length < 2 ^ (prefixWord ++ tailWord_2382729).sum := by decide
  have hdescent : baseEnd_2382729 < baseStart_2382729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382759 : List Nat := [1, 1, 6, 1, 3, 2, 1, 1, 1, 6]
def baseStart_2382759 : Nat := 118140960795 + 2382759 * 2 ^ 59
def prefixEnd_2382759 : Nat := 4983230072969 + 3 ^ 40 * 2382759 * 2
def baseEnd_2382759 : Nat := 407833550275516059384799

theorem tailTrace_2382759 : CollatzResearch.WordTrace tailWord_2382759 prefixEnd_2382759 407833550275516059384799 := by
  unfold tailWord_2382759
  simp only [CollatzResearch.WordTrace]
  refine ⟨86906360374678560683935331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57937573583119040455956887 86906360374678560683935331)
  ·
    refine ⟨130359540562017841025902997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86906360374678560683935331 130359540562017841025902997)
    ·
      refine ⟨6110603463844586298089203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 130359540562017841025902997 6110603463844586298089203)
      ·
        refine ⟨9165905195766879447133805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6110603463844586298089203 9165905195766879447133805)
        ·
          refine ⟨3437214448412579792675177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9165905195766879447133805 3437214448412579792675177)
          ·
            refine ⟨2577910836309434844506383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3437214448412579792675177 2577910836309434844506383)
            ·
              refine ⟨3866866254464152266759575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2577910836309434844506383 3866866254464152266759575)
              ·
                refine ⟨5800299381696228400139363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3866866254464152266759575 5800299381696228400139363)
                ·
                  refine ⟨8700449072544342600209045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5800299381696228400139363 8700449072544342600209045)
                  ·
                    refine ⟨407833550275516059384799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8700449072544342600209045 407833550275516059384799)
                    ·
                      rfl

theorem cell23_2382759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_2382759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2382759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2382759 prefixEnd_2382759 := by exact prefixLift 2382759
  have htrace : WordTrace (prefixWord ++ tailWord_2382759) baseStart_2382759 baseEnd_2382759 := by
    simpa [prefixWord, tailWord_2382759, baseEnd_2382759] using wordTrace_append hprefix tailTrace_2382759
  have hstable : (prefixWord ++ tailWord_2382759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382759).length < 2 ^ (prefixWord ++ tailWord_2382759).sum := by decide
  have hdescent : baseEnd_2382759 < baseStart_2382759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382782 : List Nat := [4, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3]
def baseStart_2382782 : Nat := 118140960795 + 2382782 * 2 ^ 59
def prefixEnd_2382782 : Nat := 4983230072969 + 3 ^ 40 * 2382782 * 2
def baseEnd_2382782 : Nat := 1223512460881601588166791

theorem tailTrace_2382782 : CollatzResearch.WordTrace tailWord_2382782 prefixEnd_2382782 1223512460881601588166791 := by
  unfold tailWord_2382782
  simp only [CollatzResearch.WordTrace]
  refine ⟨10863399906699404451502825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57938132835730157074681733 10863399906699404451502825)
  ·
    refine ⟨8147549930024553338627119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10863399906699404451502825 8147549930024553338627119)
    ·
      refine ⟨12221324895036830007940679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8147549930024553338627119 12221324895036830007940679)
      ·
        refine ⟨18331987342555245011911019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12221324895036830007940679 18331987342555245011911019)
        ·
          refine ⟨27497981013832867517866529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18331987342555245011911019 27497981013832867517866529)
          ·
            refine ⟨20623485760374650638399897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27497981013832867517866529 20623485760374650638399897)
            ·
              refine ⟨15467614320280987978799923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20623485760374650638399897 15467614320280987978799923)
              ·
                refine ⟨23201421480421481968199885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15467614320280987978799923 23201421480421481968199885)
                ·
                  refine ⟨8700533055158055738074957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23201421480421481968199885 8700533055158055738074957)
                  ·
                    refine ⟨3262699895684270901778109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8700533055158055738074957 3262699895684270901778109)
                    ·
                      refine ⟨1223512460881601588166791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3262699895684270901778109 1223512460881601588166791)
                      ·
                        rfl

theorem cell23_2382782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_2382782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2382782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2382782 prefixEnd_2382782 := by exact prefixLift 2382782
  have htrace : WordTrace (prefixWord ++ tailWord_2382782) baseStart_2382782 baseEnd_2382782 := by
    simpa [prefixWord, tailWord_2382782, baseEnd_2382782] using wordTrace_append hprefix tailTrace_2382782
  have hstable : (prefixWord ++ tailWord_2382782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382782).length < 2 ^ (prefixWord ++ tailWord_2382782).sum := by decide
  have hdescent : baseEnd_2382782 < baseStart_2382782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382826 : List Nat := [3, 1, 3, 1, 2, 2, 3, 2, 1, 3, 2]
def baseStart_2382826 : Nat := 118140960795 + 2382826 * 2 ^ 59
def prefixEnd_2382826 : Nat := 4983230072969 + 3 ^ 40 * 2382826 * 2
def baseEnd_2382826 : Nat := 1223535054030399416016589

theorem tailTrace_2382826 : CollatzResearch.WordTrace tailWord_2382826 prefixEnd_2382826 1223535054030399416016589 := by
  unfold tailWord_2382826
  simp only [CollatzResearch.WordTrace]
  refine ⟨21727201016358957781656083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57939202710290554084416221 21727201016358957781656083)
  ·
    refine ⟨32590801524538436672484125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21727201016358957781656083 32590801524538436672484125)
    ·
      refine ⟨12221550571701913752181547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32590801524538436672484125 12221550571701913752181547)
      ·
        refine ⟨18332325857552870628272321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12221550571701913752181547 18332325857552870628272321)
        ·
          refine ⟨13749244393164652971204241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18332325857552870628272321 13749244393164652971204241)
          ·
            refine ⟨10311933294873489728403181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13749244393164652971204241 10311933294873489728403181)
            ·
              refine ⟨3866974985577558648151193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10311933294873489728403181 3866974985577558648151193)
              ·
                refine ⟨2900231239183168986113395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3866974985577558648151193 2900231239183168986113395)
                ·
                  refine ⟨4350346858774753479170093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2900231239183168986113395 4350346858774753479170093)
                  ·
                    refine ⟨1631380072040532554688785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4350346858774753479170093 1631380072040532554688785)
                    ·
                      refine ⟨1223535054030399416016589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1631380072040532554688785 1223535054030399416016589)
                      ·
                        rfl

theorem cell23_2382826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 2, 1, 3, 2].length) (baseStart_2382826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2382826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2382826 prefixEnd_2382826 := by exact prefixLift 2382826
  have htrace : WordTrace (prefixWord ++ tailWord_2382826) baseStart_2382826 baseEnd_2382826 := by
    simpa [prefixWord, tailWord_2382826, baseEnd_2382826] using wordTrace_append hprefix tailTrace_2382826
  have hstable : (prefixWord ++ tailWord_2382826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382826).length < 2 ^ (prefixWord ++ tailWord_2382826).sum := by decide
  have hdescent : baseEnd_2382826 < baseStart_2382826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382835 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 6, 2, 4]
def baseStart_2382835 : Nat := 118140960795 + 2382835 * 2 ^ 59
def prefixEnd_2382835 : Nat := 4983230072969 + 3 ^ 40 * 2382835 * 2
def baseEnd_2382835 : Nat := 1223539675356289880804047

theorem tailTrace_2382835 : CollatzResearch.WordTrace tailWord_2382835 prefixEnd_2382835 1223539675356289880804047 := by
  unfold tailWord_2382835
  simp only [CollatzResearch.WordTrace]
  refine ⟨86909132322403225663701959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57939421548268817109134639 86909132322403225663701959)
  ·
    refine ⟨130363698483604838495552939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86909132322403225663701959 130363698483604838495552939)
    ·
      refine ⟨195545547725407257743329409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130363698483604838495552939 195545547725407257743329409)
      ·
        refine ⟨146659160794055443307497057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195545547725407257743329409 146659160794055443307497057)
        ·
          refine ⟨109994370595541582480622793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146659160794055443307497057 109994370595541582480622793)
          ·
            refine ⟨82495777946656186860467095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109994370595541582480622793 82495777946656186860467095)
            ·
              refine ⟨123743666919984280290700643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82495777946656186860467095 123743666919984280290700643)
              ·
                refine ⟨185615500379976420436050965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123743666919984280290700643 185615500379976420436050965)
                ·
                  refine ⟨8700726580311394707939889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 185615500379976420436050965 8700726580311394707939889)
                  ·
                    refine ⟨6525544935233546030954917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8700726580311394707939889 6525544935233546030954917)
                    ·
                      refine ⟨1223539675356289880804047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6525544935233546030954917 1223539675356289880804047)
                      ·
                        rfl

theorem cell23_2382835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 2, 4].length) (baseStart_2382835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2382835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2382835 prefixEnd_2382835 := by exact prefixLift 2382835
  have htrace : WordTrace (prefixWord ++ tailWord_2382835) baseStart_2382835 baseEnd_2382835 := by
    simpa [prefixWord, tailWord_2382835, baseEnd_2382835] using wordTrace_append hprefix tailTrace_2382835
  have hstable : (prefixWord ++ tailWord_2382835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382835).length < 2 ^ (prefixWord ++ tailWord_2382835).sum := by decide
  have hdescent : baseEnd_2382835 < baseStart_2382835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382850 : List Nat := [3, 4, 1, 3, 1, 1, 2, 2, 2, 1, 3]
def baseStart_2382850 : Nat := 118140960795 + 2382850 * 2 ^ 59
def prefixEnd_2382850 : Nat := 4983230072969 + 3 ^ 40 * 2382850 * 2
def baseEnd_2382850 : Nat := 1223547377566107322116479

theorem tailTrace_2382850 : CollatzResearch.WordTrace tailWord_2382850 prefixEnd_2382850 1223547377566107322116479 := by
  unfold tailWord_2382850
  simp only [CollatzResearch.WordTrace]
  refine ⟨21727419854337220806374501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57939786278232588816998669 21727419854337220806374501)
  ·
    refine ⟨4073891222688228901195219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21727419854337220806374501 4073891222688228901195219)
    ·
      refine ⟨6110836834032343351792829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4073891222688228901195219 6110836834032343351792829)
      ·
        refine ⟨2291563812762128756922311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6110836834032343351792829 2291563812762128756922311)
        ·
          refine ⟨3437345719143193135383467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2291563812762128756922311 3437345719143193135383467)
          ·
            refine ⟨5156018578714789703075201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3437345719143193135383467 5156018578714789703075201)
            ·
              refine ⟨3867013934036092277306401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5156018578714789703075201 3867013934036092277306401)
              ·
                refine ⟨2900260450527069207979801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3867013934036092277306401 2900260450527069207979801)
                ·
                  refine ⟨2175195337895301905984851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2900260450527069207979801 2175195337895301905984851)
                  ·
                    refine ⟨3262793006842952858977277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2175195337895301905984851 3262793006842952858977277)
                    ·
                      refine ⟨1223547377566107322116479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3262793006842952858977277 1223547377566107322116479)
                      ·
                        rfl

theorem cell23_2382850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_2382850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2382850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2382850 prefixEnd_2382850 := by exact prefixLift 2382850
  have htrace : WordTrace (prefixWord ++ tailWord_2382850) baseStart_2382850 baseEnd_2382850 := by
    simpa [prefixWord, tailWord_2382850, baseEnd_2382850] using wordTrace_append hprefix tailTrace_2382850
  have hstable : (prefixWord ++ tailWord_2382850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382850).length < 2 ^ (prefixWord ++ tailWord_2382850).sum := by decide
  have hdescent : baseEnd_2382850 < baseStart_2382850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382856 : List Nat := [2, 1, 3, 2, 1, 3, 1, 4, 2, 2, 2]
def baseStart_2382856 : Nat := 118140960795 + 2382856 * 2 ^ 59
def prefixEnd_2382856 : Nat := 4983230072969 + 3 ^ 40 * 2382856 * 2
def baseEnd_2382856 : Nat := 1223550458450034298641451

theorem tailTrace_2382856 : CollatzResearch.WordTrace tailWord_2382856 prefixEnd_2382856 1223550458450034298641451 := by
  unfold tailWord_2382856
  simp only [CollatzResearch.WordTrace]
  refine ⟨43454949127663573125108211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57939932170218097500144281 43454949127663573125108211)
  ·
    refine ⟨65182423691495359687662317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43454949127663573125108211 65182423691495359687662317)
    ·
      refine ⟨24443408884310759882873369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65182423691495359687662317 24443408884310759882873369)
      ·
        refine ⟨18332556663233069912155027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24443408884310759882873369 18332556663233069912155027)
        ·
          refine ⟨27498834994849604868232541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18332556663233069912155027 27498834994849604868232541)
          ·
            refine ⟨10312063123068601825587203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27498834994849604868232541 10312063123068601825587203)
            ·
              refine ⟨15468094684602902738380805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10312063123068601825587203 15468094684602902738380805)
              ·
                refine ⟨2900267753363044263446401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15468094684602902738380805 2900267753363044263446401)
                ·
                  refine ⟨2175200815022283197584801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2900267753363044263446401 2175200815022283197584801)
                  ·
                    refine ⟨1631400611266712398188601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2175200815022283197584801 1631400611266712398188601)
                    ·
                      refine ⟨1223550458450034298641451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1631400611266712398188601 1223550458450034298641451)
                      ·
                        rfl

theorem cell23_2382856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 4, 2, 2, 2].length) (baseStart_2382856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2382856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2382856 prefixEnd_2382856 := by exact prefixLift 2382856
  have htrace : WordTrace (prefixWord ++ tailWord_2382856) baseStart_2382856 baseEnd_2382856 := by
    simpa [prefixWord, tailWord_2382856, baseEnd_2382856] using wordTrace_append hprefix tailTrace_2382856
  have hstable : (prefixWord ++ tailWord_2382856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382856).length < 2 ^ (prefixWord ++ tailWord_2382856).sum := by decide
  have hdescent : baseEnd_2382856 < baseStart_2382856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382872 : List Nat := [2, 1, 2, 3, 2, 2, 1, 1, 1, 5, 3]
def baseStart_2382872 : Nat := 118140960795 + 2382872 * 2 ^ 59
def prefixEnd_2382872 : Nat := 4983230072969 + 3 ^ 40 * 2382872 * 2
def baseEnd_2382872 : Nat := 1223558674140506236041377

theorem tailTrace_2382872 : CollatzResearch.WordTrace tailWord_2382872 prefixEnd_2382872 1223558674140506236041377 := by
  unfold tailWord_2382872
  simp only [CollatzResearch.WordTrace]
  refine ⟨43455240911634590491399435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57940321215512787321865913 43455240911634590491399435)
  ·
    refine ⟨65182861367451885737099153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43455240911634590491399435 65182861367451885737099153)
    ·
      refine ⟨48887146025588914302824365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65182861367451885737099153 48887146025588914302824365)
      ·
        refine ⟨18332679759595842863559137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48887146025588914302824365 18332679759595842863559137)
        ·
          refine ⟨13749509819696882147669353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18332679759595842863559137 13749509819696882147669353)
          ·
            refine ⟨10312132364772661610752015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13749509819696882147669353 10312132364772661610752015)
            ·
              refine ⟨15468198547158992416128023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10312132364772661610752015 15468198547158992416128023)
              ·
                refine ⟨23202297820738488624192035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15468198547158992416128023 23202297820738488624192035)
                ·
                  refine ⟨34803446731107732936288053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23202297820738488624192035 34803446731107732936288053)
                  ·
                    refine ⟨3262823131041349962777005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34803446731107732936288053 3262823131041349962777005)
                    ·
                      refine ⟨1223558674140506236041377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3262823131041349962777005 1223558674140506236041377)
                      ·
                        rfl

theorem cell23_2382872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_2382872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2382872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2382872 prefixEnd_2382872 := by exact prefixLift 2382872
  have htrace : WordTrace (prefixWord ++ tailWord_2382872) baseStart_2382872 baseEnd_2382872 := by
    simpa [prefixWord, tailWord_2382872, baseEnd_2382872] using wordTrace_append hprefix tailTrace_2382872
  have hstable : (prefixWord ++ tailWord_2382872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382872).length < 2 ^ (prefixWord ++ tailWord_2382872).sum := by decide
  have hdescent : baseEnd_2382872 < baseStart_2382872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382912 : List Nat := [2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 4]
def baseStart_2382912 : Nat := 118140960795 + 2382912 * 2 ^ 59
def prefixEnd_2382912 : Nat := 4983230072969 + 3 ^ 40 * 2382912 * 2
def baseEnd_2382912 : Nat := 1223579213366686079541193

theorem tailTrace_2382912 : CollatzResearch.WordTrace tailWord_2382912 prefixEnd_2382912 1223579213366686079541193 := by
  unfold tailWord_2382912
  simp only [CollatzResearch.WordTrace]
  refine ⟨43455970371562133907127495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57941293828749511876169993 43455970371562133907127495)
  ·
    refine ⟨65183955557343200860691243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43455970371562133907127495 65183955557343200860691243)
    ·
      refine ⟨97775933336014801291036865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65183955557343200860691243 97775933336014801291036865)
      ·
        refine ⟨73331950002011100968277649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97775933336014801291036865 73331950002011100968277649)
        ·
          refine ⟨54998962501508325726208237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73331950002011100968277649 54998962501508325726208237)
          ·
            refine ⟨20624610938065622147328089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54998962501508325726208237 20624610938065622147328089)
            ·
              refine ⟨15468458203549216610496067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20624610938065622147328089 15468458203549216610496067)
              ·
                refine ⟨23202687305323824915744101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15468458203549216610496067 23202687305323824915744101)
                ·
                  refine ⟨4350503869748217171702019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23202687305323824915744101 4350503869748217171702019)
                  ·
                    refine ⟨6525755804622325757553029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4350503869748217171702019 6525755804622325757553029)
                    ·
                      refine ⟨1223579213366686079541193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6525755804622325757553029 1223579213366686079541193)
                      ·
                        rfl

theorem cell23_2382912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 4].length) (baseStart_2382912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2382912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2382912 prefixEnd_2382912 := by exact prefixLift 2382912
  have htrace : WordTrace (prefixWord ++ tailWord_2382912) baseStart_2382912 baseEnd_2382912 := by
    simpa [prefixWord, tailWord_2382912, baseEnd_2382912] using wordTrace_append hprefix tailTrace_2382912
  have hstable : (prefixWord ++ tailWord_2382912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382912).length < 2 ^ (prefixWord ++ tailWord_2382912).sum := by decide
  have hdescent : baseEnd_2382912 < baseStart_2382912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382929 : List Nat := [1, 2, 2, 1, 3, 1, 4, 1, 2, 4, 2]
def baseStart_2382929 : Nat := 118140960795 + 2382929 * 2 ^ 59
def prefixEnd_2382929 : Nat := 4983230072969 + 3 ^ 40 * 2382929 * 2
def baseEnd_2382929 : Nat := 1223587942537812513028615

theorem tailTrace_2382929 : CollatzResearch.WordTrace tailWord_2382929 prefixEnd_2382929 1223587942537812513028615 := by
  unfold tailWord_2382929
  simp only [CollatzResearch.WordTrace]
  refine ⟨86912560784062679717623841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57941707189375119811749227 86912560784062679717623841)
  ·
    refine ⟨65184420588047009788217881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86912560784062679717623841 65184420588047009788217881)
    ·
      refine ⟨48888315441035257341163411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65184420588047009788217881 48888315441035257341163411)
      ·
        refine ⟨73332473161552886011745117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48888315441035257341163411 73332473161552886011745117)
        ·
          refine ⟨27499677435582332254404419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73332473161552886011745117 27499677435582332254404419)
          ·
            refine ⟨41249516153373498381606629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27499677435582332254404419 41249516153373498381606629)
            ·
              refine ⟨7734284278757530946551243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41249516153373498381606629 7734284278757530946551243)
              ·
                refine ⟨11601426418136296419826865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7734284278757530946551243 11601426418136296419826865)
                ·
                  refine ⟨8701069813602222314870149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11601426418136296419826865 8701069813602222314870149)
                  ·
                    refine ⟨1631450590050416684038153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8701069813602222314870149 1631450590050416684038153)
                    ·
                      refine ⟨1223587942537812513028615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1631450590050416684038153 1223587942537812513028615)
                      ·
                        rfl

theorem cell23_2382929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 4, 2].length) (baseStart_2382929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2382929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2382929 prefixEnd_2382929 := by exact prefixLift 2382929
  have htrace : WordTrace (prefixWord ++ tailWord_2382929) baseStart_2382929 baseEnd_2382929 := by
    simpa [prefixWord, tailWord_2382929, baseEnd_2382929] using wordTrace_append hprefix tailTrace_2382929
  have hstable : (prefixWord ++ tailWord_2382929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382929).length < 2 ^ (prefixWord ++ tailWord_2382929).sum := by decide
  have hdescent : baseEnd_2382929 < baseStart_2382929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382949 : List Nat := [1, 3, 1, 3, 2, 1, 2, 3, 2, 2, 3]
def baseStart_2382949 : Nat := 118140960795 + 2382949 * 2 ^ 59
def prefixEnd_2382949 : Nat := 4983230072969 + 3 ^ 40 * 2382949 * 2
def baseEnd_2382949 : Nat := 1223598212150902434778523

theorem tailTrace_2382949 : CollatzResearch.WordTrace tailWord_2382949 prefixEnd_2382949 1223598212150902434778523 := by
  unfold tailWord_2382949
  simp only [CollatzResearch.WordTrace]
  refine ⟨86913290243990223133351901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57942193495993482088901267 86913290243990223133351901)
  ·
    refine ⟨32592483841496333675006963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86913290243990223133351901 32592483841496333675006963)
    ·
      refine ⟨48888725762244500512510445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32592483841496333675006963 48888725762244500512510445)
      ·
        refine ⟨18333272160841687692191417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48888725762244500512510445 18333272160841687692191417)
        ·
          refine ⟨13749954120631265769143563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18333272160841687692191417 13749954120631265769143563)
          ·
            refine ⟨20624931180946898653715345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13749954120631265769143563 20624931180946898653715345)
            ·
              refine ⟨15468698385710173990286509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20624931180946898653715345 15468698385710173990286509)
              ·
                refine ⟨5800761894641315246357441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15468698385710173990286509 5800761894641315246357441)
                ·
                  refine ⟨4350571420980986434768081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5800761894641315246357441 4350571420980986434768081)
                  ·
                    refine ⟨3262928565735739826076061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4350571420980986434768081 3262928565735739826076061)
                    ·
                      refine ⟨1223598212150902434778523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3262928565735739826076061 1223598212150902434778523)
                      ·
                        rfl

theorem cell23_2382949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_2382949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2382949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2382949 prefixEnd_2382949 := by exact prefixLift 2382949
  have htrace : WordTrace (prefixWord ++ tailWord_2382949) baseStart_2382949 baseEnd_2382949 := by
    simpa [prefixWord, tailWord_2382949, baseEnd_2382949] using wordTrace_append hprefix tailTrace_2382949
  have hstable : (prefixWord ++ tailWord_2382949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382949).length < 2 ^ (prefixWord ++ tailWord_2382949).sum := by decide
  have hdescent : baseEnd_2382949 < baseStart_2382949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382966 : List Nat := [5, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3]
def baseStart_2382966 : Nat := 118140960795 + 2382966 * 2 ^ 59
def prefixEnd_2382966 : Nat := 4983230072969 + 3 ^ 40 * 2382966 * 2
def baseEnd_2382966 : Nat := 1223606941322028868265945

theorem tailTrace_2382966 : CollatzResearch.WordTrace tailWord_2382966 prefixEnd_2382966 1223606941322028868265945 := by
  unfold tailWord_2382966
  simp only [CollatzResearch.WordTrace]
  refine ⟨5432119392808039689795047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57942606856619090024480501 5432119392808039689795047)
  ·
    refine ⟨8148179089212059534692571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5432119392808039689795047 8148179089212059534692571)
    ·
      refine ⟨12222268633818089302038857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8148179089212059534692571 12222268633818089302038857)
      ·
        refine ⟨9166701475363566976529143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12222268633818089302038857 9166701475363566976529143)
        ·
          refine ⟨13750052213045350464793715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9166701475363566976529143 13750052213045350464793715)
          ·
            refine ⟨20625078319568025697190573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13750052213045350464793715 20625078319568025697190573)
            ·
              refine ⟨7734404369838009636446465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20625078319568025697190573 7734404369838009636446465)
              ·
                refine ⟨5800803277378507227334849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7734404369838009636446465 5800803277378507227334849)
                ·
                  refine ⟨4350602458033880420501137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5800803277378507227334849 4350602458033880420501137)
                  ·
                    refine ⟨3262951843525410315375853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4350602458033880420501137 3262951843525410315375853)
                    ·
                      refine ⟨1223606941322028868265945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3262951843525410315375853 1223606941322028868265945)
                      ·
                        rfl

theorem cell23_2382966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_2382966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2382966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2382966 prefixEnd_2382966 := by exact prefixLift 2382966
  have htrace : WordTrace (prefixWord ++ tailWord_2382966) baseStart_2382966 baseEnd_2382966 := by
    simpa [prefixWord, tailWord_2382966, baseEnd_2382966] using wordTrace_append hprefix tailTrace_2382966
  have hstable : (prefixWord ++ tailWord_2382966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382966).length < 2 ^ (prefixWord ++ tailWord_2382966).sum := by decide
  have hdescent : baseEnd_2382966 < baseStart_2382966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382973 : List Nat := [1, 4, 1, 1, 3, 1, 5, 2, 1, 4]
def baseStart_2382973 : Nat := 118140960795 + 2382973 * 2 ^ 59
def prefixEnd_2382973 : Nat := 4983230072969 + 3 ^ 40 * 2382973 * 2
def baseEnd_2382973 : Nat := 407870178562203446959471

theorem tailTrace_2382973 : CollatzResearch.WordTrace tailWord_2382973 prefixEnd_2382973 407870178562203446959471 := by
  unfold tailWord_2382973
  simp only [CollatzResearch.WordTrace]
  refine ⟨86914165595903275232225573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57942777063935516821483715 86914165595903275232225573)
  ·
    refine ⟨16296406049231864106042295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86914165595903275232225573 16296406049231864106042295)
    ·
      refine ⟨24444609073847796159063443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16296406049231864106042295 24444609073847796159063443)
      ·
        refine ⟨36666913610771694238595165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24444609073847796159063443 36666913610771694238595165)
        ·
          refine ⟨13750092604039385339473187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36666913610771694238595165 13750092604039385339473187)
          ·
            refine ⟨20625138906059078009209781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13750092604039385339473187 20625138906059078009209781)
            ·
              refine ⟨1933606772443038563363417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20625138906059078009209781 1933606772443038563363417)
              ·
                refine ⟨1450205079332278922522563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1933606772443038563363417 1450205079332278922522563)
                ·
                  refine ⟨2175307618998418383783845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1450205079332278922522563 2175307618998418383783845)
                  ·
                    refine ⟨407870178562203446959471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2175307618998418383783845 407870178562203446959471)
                    ·
                      rfl

theorem cell23_2382973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 2, 1, 4].length) (baseStart_2382973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2382973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2382973 prefixEnd_2382973 := by exact prefixLift 2382973
  have htrace : WordTrace (prefixWord ++ tailWord_2382973) baseStart_2382973 baseEnd_2382973 := by
    simpa [prefixWord, tailWord_2382973, baseEnd_2382973] using wordTrace_append hprefix tailTrace_2382973
  have hstable : (prefixWord ++ tailWord_2382973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382973).length < 2 ^ (prefixWord ++ tailWord_2382973).sum := by decide
  have hdescent : baseEnd_2382973 < baseStart_2382973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382999 : List Nat := [1, 1, 3, 3, 3, 2, 1, 1, 3, 5]
def baseStart_2382999 : Nat := 118140960795 + 2382999 * 2 ^ 59
def prefixEnd_2382999 : Nat := 4983230072969 + 3 ^ 40 * 2382999 * 2
def baseEnd_2382999 : Nat := 407874628727875746384431

theorem tailTrace_2382999 : CollatzResearch.WordTrace tailWord_2382999 prefixEnd_2382999 407874628727875746384431 := by
  unfold tailWord_2382999
  simp only [CollatzResearch.WordTrace]
  refine ⟨86915113893809081672672051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57943409262539387781781367 86915113893809081672672051)
  ·
    refine ⟨130372670840713622509008077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86915113893809081672672051 130372670840713622509008077)
    ·
      refine ⟨48889751565267608440878029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130372670840713622509008077 48889751565267608440878029)
      ·
        refine ⟨18333656836975353165329261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48889751565267608440878029 18333656836975353165329261)
        ·
          refine ⟨6875121313865757436998473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18333656836975353165329261 6875121313865757436998473)
          ·
            refine ⟨5156340985399318077748855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6875121313865757436998473 5156340985399318077748855)
            ·
              refine ⟨7734511478098977116623283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5156340985399318077748855 7734511478098977116623283)
              ·
                refine ⟨11601767217148465674934925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7734511478098977116623283 11601767217148465674934925)
                ·
                  refine ⟨4350662706430674628100597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11601767217148465674934925 4350662706430674628100597)
                  ·
                    refine ⟨407874628727875746384431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4350662706430674628100597 407874628727875746384431)
                    ·
                      rfl

theorem cell23_2382999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 3, 5].length) (baseStart_2382999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2382999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2382999 prefixEnd_2382999 := by exact prefixLift 2382999
  have htrace : WordTrace (prefixWord ++ tailWord_2382999) baseStart_2382999 baseEnd_2382999 := by
    simpa [prefixWord, tailWord_2382999, baseEnd_2382999] using wordTrace_append hprefix tailTrace_2382999
  have hstable : (prefixWord ++ tailWord_2382999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382999).length < 2 ^ (prefixWord ++ tailWord_2382999).sum := by decide
  have hdescent : baseEnd_2382999 < baseStart_2382999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383032 : List Nat := [2, 1, 2, 1, 2, 1, 2, 4, 1, 1, 6]
def baseStart_2383032 : Nat := 118140960795 + 2383032 * 2 ^ 59
def prefixEnd_2383032 : Nat := 4983230072969 + 3 ^ 40 * 2383032 * 2
def baseEnd_2383032 : Nat := 1223640831045225610040641

theorem tailTrace_2383032 : CollatzResearch.WordTrace tailWord_2383032 prefixEnd_2383032 1223640831045225610040641 := by
  unfold tailWord_2383032
  simp only [CollatzResearch.WordTrace]
  refine ⟨43458158751344764154311675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57944211668459685539082233 43458158751344764154311675)
  ·
    refine ⟨65187238127017146231467513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43458158751344764154311675 65187238127017146231467513)
    ·
      refine ⟨48890428595262859673600635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65187238127017146231467513 48890428595262859673600635)
      ·
        refine ⟨73335642892894289510400953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48890428595262859673600635 73335642892894289510400953)
        ·
          refine ⟨55001732169670717132800715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73335642892894289510400953 55001732169670717132800715)
          ·
            refine ⟨82502598254506075699201073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55001732169670717132800715 82502598254506075699201073)
            ·
              refine ⟨61876948690879556774400805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82502598254506075699201073 61876948690879556774400805)
              ·
                refine ⟨11601927879539916895200151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61876948690879556774400805 11601927879539916895200151)
                ·
                  refine ⟨17402891819309875342800227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11601927879539916895200151 17402891819309875342800227)
                  ·
                    refine ⟨26104337728964813014200341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17402891819309875342800227 26104337728964813014200341)
                    ·
                      refine ⟨1223640831045225610040641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26104337728964813014200341 1223640831045225610040641)
                      ·
                        rfl

theorem cell23_2383032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 1, 1, 6].length) (baseStart_2383032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2383032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2383032 prefixEnd_2383032 := by exact prefixLift 2383032
  have htrace : WordTrace (prefixWord ++ tailWord_2383032) baseStart_2383032 baseEnd_2383032 := by
    simpa [prefixWord, tailWord_2383032, baseEnd_2383032] using wordTrace_append hprefix tailTrace_2383032
  have hstable : (prefixWord ++ tailWord_2383032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383032).length < 2 ^ (prefixWord ++ tailWord_2383032).sum := by decide
  have hdescent : baseEnd_2383032 < baseStart_2383032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383039 : List Nat := [1, 1, 2, 2, 2, 2, 3, 2, 3, 2, 3]
def baseStart_2383039 : Nat := 118140960795 + 2383039 * 2 ^ 59
def prefixEnd_2383039 : Nat := 4983230072969 + 3 ^ 40 * 2383039 * 2
def baseEnd_2383039 : Nat := 1223644425409807082653109

theorem tailTrace_2383039 : CollatzResearch.WordTrace tailWord_2383039 prefixEnd_2383039 1223644425409807082653109 := by
  unfold tailWord_2383039
  simp only [CollatzResearch.WordTrace]
  refine ⟨86916572813664168504128171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57944381875776112336085447 86916572813664168504128171)
  ·
    refine ⟨130374859220496252756192257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86916572813664168504128171 130374859220496252756192257)
    ·
      refine ⟨97781144415372189567144193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130374859220496252756192257 97781144415372189567144193)
      ·
        refine ⟨73335858311529142175358145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97781144415372189567144193 73335858311529142175358145)
        ·
          refine ⟨55001893733646856631518609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73335858311529142175358145 55001893733646856631518609)
          ·
            refine ⟨41251420300235142473638957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55001893733646856631518609 41251420300235142473638957)
            ·
              refine ⟨15469282612588178427614609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41251420300235142473638957 15469282612588178427614609)
              ·
                refine ⟨11601961959441133820710957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15469282612588178427614609 11601961959441133820710957)
                ·
                  refine ⟨4350735734790425182766609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11601961959441133820710957 4350735734790425182766609)
                  ·
                    refine ⟨3263051801092818887074957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4350735734790425182766609 3263051801092818887074957)
                    ·
                      refine ⟨1223644425409807082653109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3263051801092818887074957 1223644425409807082653109)
                      ·
                        rfl

theorem cell23_2383039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 3, 2, 3].length) (baseStart_2383039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2383039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2383039 prefixEnd_2383039 := by exact prefixLift 2383039
  have htrace : WordTrace (prefixWord ++ tailWord_2383039) baseStart_2383039 baseEnd_2383039 := by
    simpa [prefixWord, tailWord_2383039, baseEnd_2383039] using wordTrace_append hprefix tailTrace_2383039
  have hstable : (prefixWord ++ tailWord_2383039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383039).length < 2 ^ (prefixWord ++ tailWord_2383039).sum := by decide
  have hdescent : baseEnd_2383039 < baseStart_2383039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383073 : List Nat := [1, 2, 3, 1, 3, 2, 4, 1, 1, 2, 3]
def baseStart_2383073 : Nat := 118140960795 + 2383073 * 2 ^ 59
def prefixEnd_2383073 : Nat := 4983230072969 + 3 ^ 40 * 2383073 * 2
def baseEnd_2383073 : Nat := 1223661883752059949627953

theorem tailTrace_2383073 : CollatzResearch.WordTrace tailWord_2383073 prefixEnd_2383073 1223661883752059949627953 := by
  unfold tailWord_2383073
  simp only [CollatzResearch.WordTrace]
  refine ⟨86917812895540992310865873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57945208597027328207243915 86917812895540992310865873)
  ·
    refine ⟨65188359671655744233149405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86917812895540992310865873 65188359671655744233149405)
    ·
      refine ⟨24445634876870904087431027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65188359671655744233149405 24445634876870904087431027)
      ·
        refine ⟨36668452315306356131146541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24445634876870904087431027 36668452315306356131146541)
        ·
          refine ⟨13750669618239883549179953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36668452315306356131146541 13750669618239883549179953)
          ·
            refine ⟨10313002213679912661884965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13750669618239883549179953 10313002213679912661884965)
            ·
              refine ⟨1933687915064983624103431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10313002213679912661884965 1933687915064983624103431)
              ·
                refine ⟨2900531872597475436155147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1933687915064983624103431 2900531872597475436155147)
                ·
                  refine ⟨4350797808896213154232721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2900531872597475436155147 4350797808896213154232721)
                  ·
                    refine ⟨3263098356672159865674541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4350797808896213154232721 3263098356672159865674541)
                    ·
                      refine ⟨1223661883752059949627953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3263098356672159865674541 1223661883752059949627953)
                      ·
                        rfl

theorem cell23_2383073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 1, 1, 2, 3].length) (baseStart_2383073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2383073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2383073 prefixEnd_2383073 := by exact prefixLift 2383073
  have htrace : WordTrace (prefixWord ++ tailWord_2383073) baseStart_2383073 baseEnd_2383073 := by
    simpa [prefixWord, tailWord_2383073, baseEnd_2383073] using wordTrace_append hprefix tailTrace_2383073
  have hstable : (prefixWord ++ tailWord_2383073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383073).length < 2 ^ (prefixWord ++ tailWord_2383073).sum := by decide
  have hdescent : baseEnd_2383073 < baseStart_2383073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383113 : List Nat := [1, 2, 1, 1, 3, 3, 4, 2, 1, 3, 2]
def baseStart_2383113 : Nat := 118140960795 + 2383113 * 2 ^ 59
def prefixEnd_2383113 : Nat := 4983230072969 + 3 ^ 40 * 2383113 * 2
def baseEnd_2383113 : Nat := 1223682422978239793127769

theorem tailTrace_2383113 : CollatzResearch.WordTrace tailWord_2383113 prefixEnd_2383113 1223682422978239793127769 := by
  unfold tailWord_2383113
  simp only [CollatzResearch.WordTrace]
  refine ⟨86919271815396079142321993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57946181210264052761547995 86919271815396079142321993)
  ·
    refine ⟨65189453861547059356741495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86919271815396079142321993 65189453861547059356741495)
    ·
      refine ⟨97784180792320589035112243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65189453861547059356741495 97784180792320589035112243)
      ·
        refine ⟨146676271188480883552668365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97784180792320589035112243 146676271188480883552668365)
        ·
          refine ⟨55003601695680331332250637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146676271188480883552668365 55003601695680331332250637)
          ·
            refine ⟨20626350635880124249593989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55003601695680331332250637 20626350635880124249593989)
            ·
              refine ⟨3867440744227523296798873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20626350635880124249593989 3867440744227523296798873)
              ·
                refine ⟨2900580558170642472599155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3867440744227523296798873 2900580558170642472599155)
                ·
                  refine ⟨4350870837255963708898733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2900580558170642472599155 4350870837255963708898733)
                  ·
                    refine ⟨1631576563970986390837025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4350870837255963708898733 1631576563970986390837025)
                    ·
                      refine ⟨1223682422978239793127769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1631576563970986390837025 1223682422978239793127769)
                      ·
                        rfl

theorem cell23_2383113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 2, 1, 3, 2].length) (baseStart_2383113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2383113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2383113 prefixEnd_2383113 := by exact prefixLift 2383113
  have htrace : WordTrace (prefixWord ++ tailWord_2383113) baseStart_2383113 baseEnd_2383113 := by
    simpa [prefixWord, tailWord_2383113, baseEnd_2383113] using wordTrace_append hprefix tailTrace_2383113
  have hstable : (prefixWord ++ tailWord_2383113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383113).length < 2 ^ (prefixWord ++ tailWord_2383113).sum := by decide
  have hdescent : baseEnd_2383113 < baseStart_2383113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383156 : List Nat := [2, 5, 1, 1, 1, 1, 2, 1, 1, 4, 4]
def baseStart_2383156 : Nat := 118140960795 + 2383156 * 2 ^ 59
def prefixEnd_2383156 : Nat := 4983230072969 + 3 ^ 40 * 2383156 * 2
def baseEnd_2383156 : Nat := 1223704502646383124890071

theorem tailTrace_2383156 : CollatzResearch.WordTrace tailWord_2383156 prefixEnd_2383156 1223704502646383124890071 := by
  unfold tailWord_2383156
  simp only [CollatzResearch.WordTrace]
  refine ⟨43460420077120148743068661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57947226769493531657424881 43460420077120148743068661)
  ·
    refine ⟨4074414382230013944662687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43460420077120148743068661 4074414382230013944662687)
    ·
      refine ⟨6111621573345020916994031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4074414382230013944662687 6111621573345020916994031)
      ·
        refine ⟨9167432360017531375491047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6111621573345020916994031 9167432360017531375491047)
        ·
          refine ⟨13751148540026297063236571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9167432360017531375491047 13751148540026297063236571)
          ·
            refine ⟨20626722810039445594854857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13751148540026297063236571 20626722810039445594854857)
            ·
              refine ⟨15470042107529584196141143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20626722810039445594854857 15470042107529584196141143)
              ·
                refine ⟨23205063161294376294211715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15470042107529584196141143 23205063161294376294211715)
                ·
                  refine ⟨34807594741941564441317573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23205063161294376294211715 34807594741941564441317573)
                  ·
                    refine ⟨6526424014114043332747045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34807594741941564441317573 6526424014114043332747045)
                    ·
                      refine ⟨1223704502646383124890071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6526424014114043332747045 1223704502646383124890071)
                      ·
                        rfl

theorem cell23_2383156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_2383156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2383156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2383156 prefixEnd_2383156 := by exact prefixLift 2383156
  have htrace : WordTrace (prefixWord ++ tailWord_2383156) baseStart_2383156 baseEnd_2383156 := by
    simpa [prefixWord, tailWord_2383156, baseEnd_2383156] using wordTrace_append hprefix tailTrace_2383156
  have hstable : (prefixWord ++ tailWord_2383156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383156).length < 2 ^ (prefixWord ++ tailWord_2383156).sum := by decide
  have hdescent : baseEnd_2383156 < baseStart_2383156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383199 : List Nat := [1, 1, 2, 3, 1, 2, 1, 2, 3, 3, 4]
def baseStart_2383199 : Nat := 118140960795 + 2383199 * 2 ^ 59
def prefixEnd_2383199 : Nat := 4983230072969 + 3 ^ 40 * 2383199 * 2
def baseEnd_2383199 : Nat := 1223726582314526456652373

theorem tailTrace_2383199 : CollatzResearch.WordTrace tailWord_2383199 prefixEnd_2383199 1223726582314526456652373 := by
  unfold tailWord_2383199
  simp only [CollatzResearch.WordTrace]
  refine ⟨86922408493084515829952651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57948272328723010553301767 86922408493084515829952651)
  ·
    refine ⟨130383612739626773744928977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86922408493084515829952651 130383612739626773744928977)
    ·
      refine ⟨97787709554720080308696733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130383612739626773744928977 97787709554720080308696733)
      ·
        refine ⟨36670391083020030115761275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97787709554720080308696733 36670391083020030115761275)
        ·
          refine ⟨55005586624530045173641913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36670391083020030115761275 55005586624530045173641913)
          ·
            refine ⟨41254189968397533880231435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55005586624530045173641913 41254189968397533880231435)
            ·
              refine ⟨61881284952596300820347153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41254189968397533880231435 61881284952596300820347153)
              ·
                refine ⟨46410963714447225615260365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61881284952596300820347153 46410963714447225615260365)
                ·
                  refine ⟨17404111392917709605722637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46410963714447225615260365 17404111392917709605722637)
                  ·
                    refine ⟨6526541772344141102145989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17404111392917709605722637 6526541772344141102145989)
                    ·
                      refine ⟨1223726582314526456652373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6526541772344141102145989 1223726582314526456652373)
                      ·
                        rfl

theorem cell23_2383199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_2383199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2383199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2383199 prefixEnd_2383199 := by exact prefixLift 2383199
  have htrace : WordTrace (prefixWord ++ tailWord_2383199) baseStart_2383199 baseEnd_2383199 := by
    simpa [prefixWord, tailWord_2383199, baseEnd_2383199] using wordTrace_append hprefix tailTrace_2383199
  have hstable : (prefixWord ++ tailWord_2383199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383199).length < 2 ^ (prefixWord ++ tailWord_2383199).sum := by decide
  have hdescent : baseEnd_2383199 < baseStart_2383199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383200 : List Nat := [2, 1, 1, 3, 4, 3, 2, 2, 5]
def baseStart_2383200 : Nat := 118140960795 + 2383200 * 2 ^ 59
def prefixEnd_2383200 : Nat := 4983230072969 + 3 ^ 40 * 2383200 * 2
def baseEnd_2383200 : Nat := 135969677310575661415541

theorem tailTrace_2383200 : CollatzResearch.WordTrace tailWord_2383200 prefixEnd_2383200 135969677310575661415541 := by
  unfold tailWord_2383200
  simp only [CollatzResearch.WordTrace]
  refine ⟨43461222483040446500369527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57948296644053928667159369 43461222483040446500369527)
  ·
    refine ⟨65191833724560669750554291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43461222483040446500369527 65191833724560669750554291)
    ·
      refine ⟨97787750586841004625831437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65191833724560669750554291 97787750586841004625831437)
      ·
        refine ⟨36670406470065376734686789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97787750586841004625831437 36670406470065376734686789)
        ·
          refine ⟨6875701213137258137753773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36670406470065376734686789 6875701213137258137753773)
          ·
            refine ⟨2578387954926471801657665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6875701213137258137753773 2578387954926471801657665)
            ·
              refine ⟨1933790966194853851243249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2578387954926471801657665 1933790966194853851243249)
              ·
                refine ⟨1450343224646140388432437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1933790966194853851243249 1450343224646140388432437)
                ·
                  refine ⟨135969677310575661415541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1450343224646140388432437 135969677310575661415541)
                  ·
                    rfl

theorem cell23_2383200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 2, 5].length) (baseStart_2383200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2383200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2383200 prefixEnd_2383200 := by exact prefixLift 2383200
  have htrace : WordTrace (prefixWord ++ tailWord_2383200) baseStart_2383200 baseEnd_2383200 := by
    simpa [prefixWord, tailWord_2383200, baseEnd_2383200] using wordTrace_append hprefix tailTrace_2383200
  have hstable : (prefixWord ++ tailWord_2383200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383200).length < 2 ^ (prefixWord ++ tailWord_2383200).sum := by decide
  have hdescent : baseEnd_2383200 < baseStart_2383200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383226 : List Nat := [3, 1, 1, 1, 1, 1, 2, 6, 3, 4]
def baseStart_2383226 : Nat := 118140960795 + 2383226 * 2 ^ 59
def prefixEnd_2383226 : Nat := 4983230072969 + 3 ^ 40 * 2383226 * 2
def baseEnd_2383226 : Nat := 407913482097399283671583

theorem tailTrace_2383226 : CollatzResearch.WordTrace tailWord_2383226 prefixEnd_2383226 407913482097399283671583 := by
  unfold tailWord_2383226
  simp only [CollatzResearch.WordTrace]
  refine ⟨21730848315996674860296383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57948928842657799627457021 21730848315996674860296383)
  ·
    refine ⟨32596272473995012290444575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21730848315996674860296383 32596272473995012290444575)
    ·
      refine ⟨48894408710992518435666863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32596272473995012290444575 48894408710992518435666863)
      ·
        refine ⟨73341613066488777653500295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48894408710992518435666863 73341613066488777653500295)
        ·
          refine ⟨110012419599733166480250443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73341613066488777653500295 110012419599733166480250443)
          ·
            refine ⟨165018629399599749720375665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110012419599733166480250443 165018629399599749720375665)
            ·
              refine ⟨123763972049699812290281749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165018629399599749720375665 123763972049699812290281749)
              ·
                refine ⟨5801436189829678701106957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 123763972049699812290281749 5801436189829678701106957)
                ·
                  refine ⟨2175538571186129512915109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5801436189829678701106957 2175538571186129512915109)
                  ·
                    refine ⟨407913482097399283671583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2175538571186129512915109 407913482097399283671583)
                    ·
                      rfl

theorem cell23_2383226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 3, 4].length) (baseStart_2383226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2383226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2383226 prefixEnd_2383226 := by exact prefixLift 2383226
  have htrace : WordTrace (prefixWord ++ tailWord_2383226) baseStart_2383226 baseEnd_2383226 := by
    simpa [prefixWord, tailWord_2383226, baseEnd_2383226] using wordTrace_append hprefix tailTrace_2383226
  have hstable : (prefixWord ++ tailWord_2383226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383226).length < 2 ^ (prefixWord ++ tailWord_2383226).sum := by decide
  have hdescent : baseEnd_2383226 < baseStart_2383226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383230 : List Nat := [4, 2, 3, 2, 1, 1, 1, 1, 1, 7]
def baseStart_2383230 : Nat := 118140960795 + 2383230 * 2 ^ 59
def prefixEnd_2383230 : Nat := 4983230072969 + 3 ^ 40 * 2383230 * 2
def baseEnd_2383230 : Nat := 407914166738271945121577

theorem tailTrace_2383230 : CollatzResearch.WordTrace tailWord_2383230 prefixEnd_2383230 407914166738271945121577 := by
  unfold tailWord_2383230
  simp only [CollatzResearch.WordTrace]
  refine ⟨10865442394496526015541393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57949026103981472082887429 10865442394496526015541393)
  ·
    refine ⟨8149081795872394511656045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10865442394496526015541393 8149081795872394511656045)
    ·
      refine ⟨3055905673452147941871017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8149081795872394511656045 3055905673452147941871017)
      ·
        refine ⟨2291929255089110956403263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3055905673452147941871017 2291929255089110956403263)
        ·
          refine ⟨3437893882633666434604895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2291929255089110956403263 3437893882633666434604895)
          ·
            refine ⟨5156840823950499651907343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3437893882633666434604895 5156840823950499651907343)
            ·
              refine ⟨7735261235925749477861015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5156840823950499651907343 7735261235925749477861015)
              ·
                refine ⟨11602891853888624216791523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7735261235925749477861015 11602891853888624216791523)
                ·
                  refine ⟨17404337780832936325187285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11602891853888624216791523 17404337780832936325187285)
                  ·
                    refine ⟨407914166738271945121577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17404337780832936325187285 407914166738271945121577)
                    ·
                      rfl

theorem cell23_2383230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_2383230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2383230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2383230 prefixEnd_2383230 := by exact prefixLift 2383230
  have htrace : WordTrace (prefixWord ++ tailWord_2383230) baseStart_2383230 baseEnd_2383230 := by
    simpa [prefixWord, tailWord_2383230, baseEnd_2383230] using wordTrace_append hprefix tailTrace_2383230
  have hstable : (prefixWord ++ tailWord_2383230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383230).length < 2 ^ (prefixWord ++ tailWord_2383230).sum := by decide
  have hdescent : baseEnd_2383230 < baseStart_2383230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383233 : List Nat := [1, 2, 4, 3, 2, 1, 1, 1, 1, 3, 4]
def baseStart_2383233 : Nat := 118140960795 + 2383233 * 2 ^ 59
def prefixEnd_2383233 : Nat := 4983230072969 + 3 ^ 40 * 2383233 * 2
def baseEnd_2383233 : Nat := 1223744040656779323627217

theorem tailTrace_2383233 : CollatzResearch.WordTrace tailWord_2383233 prefixEnd_2383233 1223744040656779323627217 := by
  unfold tailWord_2383233
  simp only [CollatzResearch.WordTrace]
  refine ⟨86923648574961339636690353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57949099049974226424460235 86923648574961339636690353)
  ·
    refine ⟨65192736431221004727517765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86923648574961339636690353 65192736431221004727517765)
    ·
      refine ⟨12223638080853938386409581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65192736431221004727517765 12223638080853938386409581)
      ·
        refine ⟨4583864280320226894903593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12223638080853938386409581 4583864280320226894903593)
        ·
          refine ⟨3437898210240170171177695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4583864280320226894903593 3437898210240170171177695)
          ·
            refine ⟨5156847315360255256766543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3437898210240170171177695 5156847315360255256766543)
            ·
              refine ⟨7735270973040382885149815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5156847315360255256766543 7735270973040382885149815)
              ·
                refine ⟨11602906459560574327724723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7735270973040382885149815 11602906459560574327724723)
                ·
                  refine ⟨17404359689340861491587085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11602906459560574327724723 17404359689340861491587085)
                  ·
                    refine ⟨6526634883502823059345157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17404359689340861491587085 6526634883502823059345157)
                    ·
                      refine ⟨1223744040656779323627217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6526634883502823059345157 1223744040656779323627217)
                      ·
                        rfl

theorem cell23_2383233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_2383233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2383233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2383233 prefixEnd_2383233 := by exact prefixLift 2383233
  have htrace : WordTrace (prefixWord ++ tailWord_2383233) baseStart_2383233 baseEnd_2383233 := by
    simpa [prefixWord, tailWord_2383233, baseEnd_2383233] using wordTrace_append hprefix tailTrace_2383233
  have hstable : (prefixWord ++ tailWord_2383233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383233).length < 2 ^ (prefixWord ++ tailWord_2383233).sum := by decide
  have hdescent : baseEnd_2383233 < baseStart_2383233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
