import V185TrunkScan23Chunk0922

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5462802 : List Nat := [3, 2, 4, 1, 2, 1, 1, 1, 8]
def baseStart_5462802 : Nat := 118140960795 + 5462802 * 2 ^ 59
def prefixEnd_5462802 : Nat := 4983230072969 + 3 ^ 40 * 5462802 * 2
def baseEnd_5462802 : Nat := 311671460704737888416893

theorem tailTrace_5462802 : CollatzResearch.WordTrace tailWord_5462802 prefixEnd_5462802 311671460704737888416893 := by
  unfold tailWord_5462802
  simp only [CollatzResearch.WordTrace]
  refine ⟨49811189388802200287247665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132829838370139200765993773 49811189388802200287247665)
  ·
    refine ⟨37358392041601650215435749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49811189388802200287247665 37358392041601650215435749)
    ·
      refine ⟨7004698507800309415394203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37358392041601650215435749 7004698507800309415394203)
      ·
        refine ⟨10507047761700464123091305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7004698507800309415394203 10507047761700464123091305)
        ·
          refine ⟨7880285821275348092318479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10507047761700464123091305 7880285821275348092318479)
          ·
            refine ⟨11820428731913022138477719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7880285821275348092318479 11820428731913022138477719)
            ·
              refine ⟨17730643097869533207716579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11820428731913022138477719 17730643097869533207716579)
              ·
                refine ⟨26595964646804299811574869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17730643097869533207716579 26595964646804299811574869)
                ·
                  refine ⟨311671460704737888416893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26595964646804299811574869 311671460704737888416893)
                  ·
                    rfl

theorem cell23_5462802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 8].length) (baseStart_5462802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5462802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5462802 prefixEnd_5462802 := by exact prefixLift 5462802
  have htrace : WordTrace (prefixWord ++ tailWord_5462802) baseStart_5462802 baseEnd_5462802 := by
    simpa [prefixWord, tailWord_5462802, baseEnd_5462802] using wordTrace_append hprefix tailTrace_5462802
  have hstable : (prefixWord ++ tailWord_5462802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5462802).length < 2 ^ (prefixWord ++ tailWord_5462802).sum := by decide
  have hdescent : baseEnd_5462802 < baseStart_5462802 := by decide
  rcases family_descends (prefixWord ++ tailWord_5462802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5462812 : List Nat := [2, 2, 3, 1, 1, 3, 1, 3, 3, 1, 3]
def baseStart_5462812 : Nat := 118140960795 + 5462812 * 2 ^ 59
def prefixEnd_5462812 : Nat := 4983230072969 + 3 ^ 40 * 5462812 * 2
def baseEnd_5462812 : Nat := 2805048281149185956626991

theorem tailTrace_5462812 : CollatzResearch.WordTrace tailWord_5462812 prefixEnd_5462812 2805048281149185956626991 := by
  unfold tailWord_5462812
  simp only [CollatzResearch.WordTrace]
  refine ⟨99622561142586286428427345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132830081523448381904569793 99622561142586286428427345)
  ·
    refine ⟨74716920856939714821320509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99622561142586286428427345 74716920856939714821320509)
    ·
      refine ⟨28018845321352393057995191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74716920856939714821320509 28018845321352393057995191)
      ·
        refine ⟨42028267982028589586992787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28018845321352393057995191 42028267982028589586992787)
        ·
          refine ⟨63042401973042884380489181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42028267982028589586992787 63042401973042884380489181)
          ·
            refine ⟨23640900739891081642683443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63042401973042884380489181 23640900739891081642683443)
            ·
              refine ⟨35461351109836622464025165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23640900739891081642683443 35461351109836622464025165)
              ·
                refine ⟨13298006666188733424009437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35461351109836622464025165 13298006666188733424009437)
                ·
                  refine ⟨4986752499820775034003539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13298006666188733424009437 4986752499820775034003539)
                  ·
                    refine ⟨7480128749731162551005309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4986752499820775034003539 7480128749731162551005309)
                    ·
                      refine ⟨2805048281149185956626991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7480128749731162551005309 2805048281149185956626991)
                      ·
                        rfl

theorem cell23_5462812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_5462812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5462812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5462812 prefixEnd_5462812 := by exact prefixLift 5462812
  have htrace : WordTrace (prefixWord ++ tailWord_5462812) baseStart_5462812 baseEnd_5462812 := by
    simpa [prefixWord, tailWord_5462812, baseEnd_5462812] using wordTrace_append hprefix tailTrace_5462812
  have hstable : (prefixWord ++ tailWord_5462812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5462812).length < 2 ^ (prefixWord ++ tailWord_5462812).sum := by decide
  have hdescent : baseEnd_5462812 < baseStart_5462812 := by decide
  rcases family_descends (prefixWord ++ tailWord_5462812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5462855 : List Nat := [1, 1, 4, 1, 2, 1, 1, 2, 5, 2, 3]
def baseStart_5462855 : Nat := 118140960795 + 5462855 * 2 ^ 59
def prefixEnd_5462855 : Nat := 4983230072969 + 3 ^ 40 * 5462855 * 2
def baseEnd_5462855 : Nat := 2805070360817329288389293

theorem tailTrace_5462855 : CollatzResearch.WordTrace tailWord_5462855 prefixEnd_5462855 2805070360817329288389293 := by
  unfold tailWord_5462855
  simp only [CollatzResearch.WordTrace]
  refine ⟨199246690624016791200670019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132831127082677860800446679 199246690624016791200670019)
  ·
    refine ⟨298870035936025186801005029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199246690624016791200670019 298870035936025186801005029)
    ·
      refine ⟨56038131738004722525188443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 298870035936025186801005029 56038131738004722525188443)
      ·
        refine ⟨84057197607007083787782665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56038131738004722525188443 84057197607007083787782665)
        ·
          refine ⟨63042898205255312840836999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84057197607007083787782665 63042898205255312840836999)
          ·
            refine ⟨94564347307882969261255499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63042898205255312840836999 94564347307882969261255499)
            ·
              refine ⟨141846520961824453891883249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94564347307882969261255499 141846520961824453891883249)
              ·
                refine ⟨106384890721368340418912437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141846520961824453891883249 106384890721368340418912437)
                ·
                  refine ⟨9973583505128281914273041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 106384890721368340418912437 9973583505128281914273041)
                  ·
                    refine ⟨7480187628846211435704781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9973583505128281914273041 7480187628846211435704781)
                    ·
                      refine ⟨2805070360817329288389293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7480187628846211435704781 2805070360817329288389293)
                      ·
                        rfl

theorem cell23_5462855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 5, 2, 3].length) (baseStart_5462855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5462855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5462855 prefixEnd_5462855 := by exact prefixLift 5462855
  have htrace : WordTrace (prefixWord ++ tailWord_5462855) baseStart_5462855 baseEnd_5462855 := by
    simpa [prefixWord, tailWord_5462855, baseEnd_5462855] using wordTrace_append hprefix tailTrace_5462855
  have hstable : (prefixWord ++ tailWord_5462855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5462855).length < 2 ^ (prefixWord ++ tailWord_5462855).sum := by decide
  have hdescent : baseEnd_5462855 < baseStart_5462855 := by decide
  rcases family_descends (prefixWord ++ tailWord_5462855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5462914 : List Nat := [3, 4, 2, 2, 2, 1, 2, 2, 1, 1, 3]
def baseStart_5462914 : Nat := 118140960795 + 5462914 * 2 ^ 59
def prefixEnd_5462914 : Nat := 4983230072969 + 3 ^ 40 * 5462914 * 2
def baseEnd_5462914 : Nat := 2805100656175944557551523

theorem tailTrace_5462914 : CollatzResearch.WordTrace tailWord_5462914 prefixEnd_5462914 2805100656175944557551523 := by
  unfold tailWord_5462914
  simp only [CollatzResearch.WordTrace]
  refine ⟨49812210632700761069266949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132832561687202029518045197 49812210632700761069266949)
  ·
    refine ⟨9339789493631392700487553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49812210632700761069266949 9339789493631392700487553)
    ·
      refine ⟨7004842120223544525365665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9339789493631392700487553 7004842120223544525365665)
      ·
        refine ⟨5253631590167658394024249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7004842120223544525365665 5253631590167658394024249)
        ·
          refine ⟨3940223692625743795518187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5253631590167658394024249 3940223692625743795518187)
          ·
            refine ⟨5910335538938615693277281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3940223692625743795518187 5910335538938615693277281)
            ·
              refine ⟨4432751654203961769957961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5910335538938615693277281 4432751654203961769957961)
              ·
                refine ⟨3324563740652971327468471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4432751654203961769957961 3324563740652971327468471)
                ·
                  refine ⟨4986845610979456991202707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3324563740652971327468471 4986845610979456991202707)
                  ·
                    refine ⟨7480268416469185486804061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4986845610979456991202707 7480268416469185486804061)
                    ·
                      refine ⟨2805100656175944557551523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7480268416469185486804061 2805100656175944557551523)
                      ·
                        rfl

theorem cell23_5462914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_5462914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5462914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5462914 prefixEnd_5462914 := by exact prefixLift 5462914
  have htrace : WordTrace (prefixWord ++ tailWord_5462914) baseStart_5462914 baseEnd_5462914 := by
    simpa [prefixWord, tailWord_5462914, baseEnd_5462914] using wordTrace_append hprefix tailTrace_5462914
  have hstable : (prefixWord ++ tailWord_5462914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5462914).length < 2 ^ (prefixWord ++ tailWord_5462914).sum := by decide
  have hdescent : baseEnd_5462914 < baseStart_5462914 := by decide
  rcases family_descends (prefixWord ++ tailWord_5462914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5462919 : List Nat := [1, 1, 4, 2, 3, 1, 1, 4, 2, 1, 3]
def baseStart_5462919 : Nat := 118140960795 + 5462919 * 2 ^ 59
def prefixEnd_5462919 : Nat := 4983230072969 + 3 ^ 40 * 5462919 * 2
def baseEnd_5462919 : Nat := 2805103223579217037988999

theorem tailTrace_5462919 : CollatzResearch.WordTrace tailWord_5462919 prefixEnd_5462919 2805103223579217037988999 := by
  unfold tailWord_5462919
  simp only [CollatzResearch.WordTrace]
  refine ⟨199249024895784930130999811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132832683263856620087333207 199249024895784930130999811)
  ·
    refine ⟨298873537343677395196499717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199249024895784930130999811 298873537343677395196499717)
    ·
      refine ⟨56038788251939511599343697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 298873537343677395196499717 56038788251939511599343697)
      ·
        refine ⟨42029091188954633699507773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56038788251939511599343697 42029091188954633699507773)
        ·
          refine ⟨15760909195857987637315415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42029091188954633699507773 15760909195857987637315415)
          ·
            refine ⟨23641363793786981455973123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15760909195857987637315415 23641363793786981455973123)
            ·
              refine ⟨35462045690680472183959685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23641363793786981455973123 35462045690680472183959685)
              ·
                refine ⟨6649133567002588534492441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35462045690680472183959685 6649133567002588534492441)
                ·
                  refine ⟨4986850175251941400869331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6649133567002588534492441 4986850175251941400869331)
                  ·
                    refine ⟨7480275262877912101303997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4986850175251941400869331 7480275262877912101303997)
                    ·
                      refine ⟨2805103223579217037988999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7480275262877912101303997 2805103223579217037988999)
                      ·
                        rfl

theorem cell23_5462919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_5462919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5462919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5462919 prefixEnd_5462919 := by exact prefixLift 5462919
  have htrace : WordTrace (prefixWord ++ tailWord_5462919) baseStart_5462919 baseEnd_5462919 := by
    simpa [prefixWord, tailWord_5462919, baseEnd_5462919] using wordTrace_append hprefix tailTrace_5462919
  have hstable : (prefixWord ++ tailWord_5462919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5462919).length < 2 ^ (prefixWord ++ tailWord_5462919).sum := by decide
  have hdescent : baseEnd_5462919 < baseStart_5462919 := by decide
  rcases family_descends (prefixWord ++ tailWord_5462919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5462920 : List Nat := [2, 1, 3, 3, 2, 3, 2, 2, 1, 2, 2]
def baseStart_5462920 : Nat := 118140960795 + 5462920 * 2 ^ 59
def prefixEnd_5462920 : Nat := 4983230072969 + 3 ^ 40 * 5462920 * 2
def baseEnd_5462920 : Nat := 2805103737059871534076495

theorem tailTrace_5462920 : CollatzResearch.WordTrace tailWord_5462920 prefixEnd_5462920 2805103737059871534076495 := by
  unfold tailWord_5462920
  simp only [CollatzResearch.WordTrace]
  refine ⟨99624530684390653650893107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132832707579187538201190809 99624530684390653650893107)
  ·
    refine ⟨149436796026585980476339661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99624530684390653650893107 149436796026585980476339661)
    ·
      refine ⟨56038798509969742678627373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149436796026585980476339661 56038798509969742678627373)
      ·
        refine ⟨21014549441238653504485265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56038798509969742678627373 21014549441238653504485265)
        ·
          refine ⟨15760912080928990128363949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21014549441238653504485265 15760912080928990128363949)
          ·
            refine ⟨5910342030348371298136481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15760912080928990128363949 5910342030348371298136481)
            ·
              refine ⟨4432756522761278473602361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5910342030348371298136481 4432756522761278473602361)
              ·
                refine ⟨3324567392070958855201771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4432756522761278473602361 3324567392070958855201771)
                ·
                  refine ⟨4986851088106438282802657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3324567392070958855201771 4986851088106438282802657)
                  ·
                    refine ⟨3740138316079828712101993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4986851088106438282802657 3740138316079828712101993)
                    ·
                      refine ⟨2805103737059871534076495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3740138316079828712101993 2805103737059871534076495)
                      ·
                        rfl

theorem cell23_5462920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_5462920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5462920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5462920 prefixEnd_5462920 := by exact prefixLift 5462920
  have htrace : WordTrace (prefixWord ++ tailWord_5462920) baseStart_5462920 baseEnd_5462920 := by
    simpa [prefixWord, tailWord_5462920, baseEnd_5462920] using wordTrace_append hprefix tailTrace_5462920
  have hstable : (prefixWord ++ tailWord_5462920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5462920).length < 2 ^ (prefixWord ++ tailWord_5462920).sum := by decide
  have hdescent : baseEnd_5462920 < baseStart_5462920 := by decide
  rcases family_descends (prefixWord ++ tailWord_5462920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5462935 : List Nat := [1, 1, 3, 3, 1, 2, 3, 1, 2, 6]
def baseStart_5462935 : Nat := 118140960795 + 5462935 * 2 ^ 59
def prefixEnd_5462935 : Nat := 4983230072969 + 3 ^ 40 * 5462935 * 2
def baseEnd_5462935 : Nat := 935037146423229658462975

theorem tailTrace_5462935 : CollatzResearch.WordTrace tailWord_5462935 prefixEnd_5462935 935037146423229658462975 := by
  unfold tailWord_5462935
  simp only [CollatzResearch.WordTrace]
  refine ⟨199249608463726964863582259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132833072309151309909054839 199249608463726964863582259)
  ·
    refine ⟨298874412695590447295373389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199249608463726964863582259 298874412695590447295373389)
    ·
      refine ⟨112077904760846417735765021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 298874412695590447295373389 112077904760846417735765021)
      ·
        refine ⟨42029214285317406650911883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112077904760846417735765021 42029214285317406650911883)
        ·
          refine ⟨63043821427976109976367825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42029214285317406650911883 63043821427976109976367825)
          ·
            refine ⟨47282866070982082482275869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63043821427976109976367825 47282866070982082482275869)
            ·
              refine ⟨17731074776618280930853451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47282866070982082482275869 17731074776618280930853451)
              ·
                refine ⟨26596612164927421396280177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17731074776618280930853451 26596612164927421396280177)
                ·
                  refine ⟨19947459123695566047210133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26596612164927421396280177 19947459123695566047210133)
                  ·
                    refine ⟨935037146423229658462975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19947459123695566047210133 935037146423229658462975)
                    ·
                      rfl

theorem cell23_5462935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 6].length) (baseStart_5462935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5462935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5462935 prefixEnd_5462935 := by exact prefixLift 5462935
  have htrace : WordTrace (prefixWord ++ tailWord_5462935) baseStart_5462935 baseEnd_5462935 := by
    simpa [prefixWord, tailWord_5462935, baseEnd_5462935] using wordTrace_append hprefix tailTrace_5462935
  have hstable : (prefixWord ++ tailWord_5462935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5462935).length < 2 ^ (prefixWord ++ tailWord_5462935).sum := by decide
  have hdescent : baseEnd_5462935 < baseStart_5462935 := by decide
  rcases family_descends (prefixWord ++ tailWord_5462935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5462965 : List Nat := [1, 3, 3, 2, 1, 1, 1, 2, 9]
def baseStart_5462965 : Nat := 118140960795 + 5462965 * 2 ^ 59
def prefixEnd_5462965 : Nat := 4983230072969 + 3 ^ 40 * 5462965 * 2
def baseEnd_5462965 : Nat := 311680760409924873112643

theorem tailTrace_5462965 : CollatzResearch.WordTrace tailWord_5462965 prefixEnd_5462965 311680760409924873112643 := by
  unfold tailWord_5462965
  simp only [CollatzResearch.WordTrace]
  refine ⟨199250702653618279987174349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132833801769078853324782899 199250702653618279987174349)
  ·
    refine ⟨74719013495106854995190381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199250702653618279987174349 74719013495106854995190381)
    ·
      refine ⟨28019630060665070623196393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74719013495106854995190381 28019630060665070623196393)
      ·
        refine ⟨21014722545498802967397295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28019630060665070623196393 21014722545498802967397295)
        ·
          refine ⟨31522083818248204451095943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21014722545498802967397295 31522083818248204451095943)
          ·
            refine ⟨47283125727372306676643915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31522083818248204451095943 47283125727372306676643915)
            ·
              refine ⟨70924688591058460014965873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47283125727372306676643915 70924688591058460014965873)
              ·
                refine ⟨53193516443293845011224405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70924688591058460014965873 53193516443293845011224405)
                ·
                  refine ⟨311680760409924873112643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 53193516443293845011224405 311680760409924873112643)
                  ·
                    rfl

theorem cell23_5462965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 9].length) (baseStart_5462965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5462965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5462965 prefixEnd_5462965 := by exact prefixLift 5462965
  have htrace : WordTrace (prefixWord ++ tailWord_5462965) baseStart_5462965 baseEnd_5462965 := by
    simpa [prefixWord, tailWord_5462965, baseEnd_5462965] using wordTrace_append hprefix tailTrace_5462965
  have hstable : (prefixWord ++ tailWord_5462965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5462965).length < 2 ^ (prefixWord ++ tailWord_5462965).sum := by decide
  have hdescent : baseEnd_5462965 < baseStart_5462965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5462965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5462976 : List Nat := [2, 1, 1, 2, 3, 3, 3, 2, 2, 2, 2]
def baseStart_5462976 : Nat := 118140960795 + 5462976 * 2 ^ 59
def prefixEnd_5462976 : Nat := 4983230072969 + 3 ^ 40 * 5462976 * 2
def baseEnd_5462976 : Nat := 2805132491976523314976237

theorem tailTrace_5462976 : CollatzResearch.WordTrace tailWord_5462976 prefixEnd_5462976 2805132491976523314976237 := by
  unfold tailWord_5462976
  simp only [CollatzResearch.WordTrace]
  refine ⟨99625551928289214432912391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132834069237718952577216521 99625551928289214432912391)
  ·
    refine ⟨149438327892433821649368587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99625551928289214432912391 149438327892433821649368587)
    ·
      refine ⟨224157491838650732474052881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149438327892433821649368587 224157491838650732474052881)
      ·
        refine ⟨168118118878988049355539661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224157491838650732474052881 168118118878988049355539661)
        ·
          refine ⟨63044294579620518508327373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168118118878988049355539661 63044294579620518508327373)
          ·
            refine ⟨23641610467357694440622765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63044294579620518508327373 23641610467357694440622765)
            ·
              refine ⟨8865603925259135415233537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23641610467357694440622765 8865603925259135415233537)
              ·
                refine ⟨6649202943944351561425153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8865603925259135415233537 6649202943944351561425153)
                ·
                  refine ⟨4986902207958263671068865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6649202943944351561425153 4986902207958263671068865)
                  ·
                    refine ⟨3740176655968697753301649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4986902207958263671068865 3740176655968697753301649)
                    ·
                      refine ⟨2805132491976523314976237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3740176655968697753301649 2805132491976523314976237)
                      ·
                        rfl

theorem cell23_5462976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 2, 2, 2, 2].length) (baseStart_5462976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5462976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5462976 prefixEnd_5462976 := by exact prefixLift 5462976
  have htrace : WordTrace (prefixWord ++ tailWord_5462976) baseStart_5462976 baseEnd_5462976 := by
    simpa [prefixWord, tailWord_5462976, baseEnd_5462976] using wordTrace_append hprefix tailTrace_5462976
  have hstable : (prefixWord ++ tailWord_5462976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5462976).length < 2 ^ (prefixWord ++ tailWord_5462976).sum := by decide
  have hdescent : baseEnd_5462976 < baseStart_5462976 := by decide
  rcases family_descends (prefixWord ++ tailWord_5462976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5463109 : List Nat := [1, 3, 1, 1, 1, 3, 2, 2, 4, 3, 2]
def baseStart_5463109 : Nat := 118140960795 + 5463109 * 2 ^ 59
def prefixEnd_5463109 : Nat := 4983230072969 + 3 ^ 40 * 5463109 * 2
def baseEnd_5463109 : Nat := 2805200784903571294613125

theorem tailTrace_5463109 : CollatzResearch.WordTrace tailWord_5463109 prefixEnd_5463109 2805200784903571294613125 := by
  unfold tailWord_5463109
  simp only [CollatzResearch.WordTrace]
  refine ⟨199255954765096592580416381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132837303176731061720277587 199255954765096592580416381)
  ·
    refine ⟨74720983036911222217656143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199255954765096592580416381 74720983036911222217656143)
    ·
      refine ⟨112081474555366833326484215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74720983036911222217656143 112081474555366833326484215)
      ·
        refine ⟨168122211833050249989726323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112081474555366833326484215 168122211833050249989726323)
        ·
          refine ⟨252183317749575374984589485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168122211833050249989726323 252183317749575374984589485)
          ·
            refine ⟨94568744156090765619221057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 252183317749575374984589485 94568744156090765619221057)
            ·
              refine ⟨70926558117068074214415793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94568744156090765619221057 70926558117068074214415793)
              ·
                refine ⟨53194918587801055660811845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70926558117068074214415793 53194918587801055660811845)
                ·
                  refine ⟨9974047235212697936402221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53194918587801055660811845 9974047235212697936402221)
                  ·
                    refine ⟨3740267713204761726150833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9974047235212697936402221 3740267713204761726150833)
                    ·
                      refine ⟨2805200784903571294613125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3740267713204761726150833 2805200784903571294613125)
                      ·
                        rfl

theorem cell23_5463109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 4, 3, 2].length) (baseStart_5463109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5463109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5463109 prefixEnd_5463109 := by exact prefixLift 5463109
  have htrace : WordTrace (prefixWord ++ tailWord_5463109) baseStart_5463109 baseEnd_5463109 := by
    simpa [prefixWord, tailWord_5463109, baseEnd_5463109] using wordTrace_append hprefix tailTrace_5463109
  have hstable : (prefixWord ++ tailWord_5463109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5463109).length < 2 ^ (prefixWord ++ tailWord_5463109).sum := by decide
  have hdescent : baseEnd_5463109 < baseStart_5463109 := by decide
  rcases family_descends (prefixWord ++ tailWord_5463109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5463152 : List Nat := [2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 6]
def baseStart_5463152 : Nat := 118140960795 + 5463152 * 2 ^ 59
def prefixEnd_5463152 : Nat := 4983230072969 + 3 ^ 40 * 5463152 * 2
def baseEnd_5463152 : Nat := 2805222864571714626375427

theorem tailTrace_5463152 : CollatzResearch.WordTrace tailWord_5463152 prefixEnd_5463152 2805222864571714626375427 := by
  unfold tailWord_5463152
  simp only [CollatzResearch.WordTrace]
  refine ⟨99628761551970405462115855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132838348735960540616154473 99628761551970405462115855)
  ·
    refine ⟨149443142327955608193173783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99628761551970405462115855 149443142327955608193173783)
    ·
      refine ⟨224164713491933412289760675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149443142327955608193173783 224164713491933412289760675)
      ·
        refine ⟨336247070237900118434641013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224164713491933412289760675 336247070237900118434641013)
        ·
          refine ⟨31523162834803136103247595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 336247070237900118434641013 31523162834803136103247595)
          ·
            refine ⟨47284744252204704154871393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31523162834803136103247595 47284744252204704154871393)
            ·
              refine ⟨35463558189153528116153545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47284744252204704154871393 35463558189153528116153545)
              ·
                refine ⟨26597668641865146087115159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35463558189153528116153545 26597668641865146087115159)
                ·
                  refine ⟨39896502962797719130672739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26597668641865146087115159 39896502962797719130672739)
                  ·
                    refine ⟨59844754444196578696009109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39896502962797719130672739 59844754444196578696009109)
                    ·
                      refine ⟨2805222864571714626375427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59844754444196578696009109 2805222864571714626375427)
                      ·
                        rfl

theorem cell23_5463152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 6].length) (baseStart_5463152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5463152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5463152 prefixEnd_5463152 := by exact prefixLift 5463152
  have htrace : WordTrace (prefixWord ++ tailWord_5463152) baseStart_5463152 baseEnd_5463152 := by
    simpa [prefixWord, tailWord_5463152, baseEnd_5463152] using wordTrace_append hprefix tailTrace_5463152
  have hstable : (prefixWord ++ tailWord_5463152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5463152).length < 2 ^ (prefixWord ++ tailWord_5463152).sum := by decide
  have hdescent : baseEnd_5463152 < baseStart_5463152 := by decide
  rcases family_descends (prefixWord ++ tailWord_5463152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5463169 : List Nat := [1, 2, 4, 2, 2, 2, 1, 1, 1, 1, 6]
def baseStart_5463169 : Nat := 118140960795 + 5463169 * 2 ^ 59
def prefixEnd_5463169 : Nat := 4983230072969 + 3 ^ 40 * 5463169 * 2
def baseEnd_5463169 : Nat := 2805231593742841059862849

theorem tailTrace_5463169 : CollatzResearch.WordTrace tailWord_5463169 prefixEnd_5463169 2805231593742841059862849 := by
  unfold tailWord_5463169
  simp only [CollatzResearch.WordTrace]
  refine ⟨199258143144879222827600561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132838762096586148551733707 199258143144879222827600561)
  ·
    refine ⟨149443607358659417120700421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199258143144879222827600561 149443607358659417120700421)
    ·
      refine ⟨28020676379748640710131329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149443607358659417120700421 28020676379748640710131329)
      ·
        refine ⟨21015507284811480532598497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28020676379748640710131329 21015507284811480532598497)
        ·
          refine ⟨15761630463608610399448873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21015507284811480532598497 15761630463608610399448873)
          ·
            refine ⟨11821222847706457799586655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15761630463608610399448873 11821222847706457799586655)
            ·
              refine ⟨17731834271559686699379983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11821222847706457799586655 17731834271559686699379983)
              ·
                refine ⟨26597751407339530049069975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17731834271559686699379983 26597751407339530049069975)
                ·
                  refine ⟨39896627111009295073604963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26597751407339530049069975 39896627111009295073604963)
                  ·
                    refine ⟨59844940666513942610407445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39896627111009295073604963 59844940666513942610407445)
                    ·
                      refine ⟨2805231593742841059862849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59844940666513942610407445 2805231593742841059862849)
                      ·
                        rfl

theorem cell23_5463169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_5463169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5463169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5463169 prefixEnd_5463169 := by exact prefixLift 5463169
  have htrace : WordTrace (prefixWord ++ tailWord_5463169) baseStart_5463169 baseEnd_5463169 := by
    simpa [prefixWord, tailWord_5463169, baseEnd_5463169] using wordTrace_append hprefix tailTrace_5463169
  have hstable : (prefixWord ++ tailWord_5463169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5463169).length < 2 ^ (prefixWord ++ tailWord_5463169).sum := by decide
  have hdescent : baseEnd_5463169 < baseStart_5463169 := by decide
  rcases family_descends (prefixWord ++ tailWord_5463169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5463250 : List Nat := [3, 2, 2, 2, 1, 1, 5, 1, 1, 3, 2]
def baseStart_5463250 : Nat := 118140960795 + 5463250 * 2 ^ 59
def prefixEnd_5463250 : Nat := 4983230072969 + 3 ^ 40 * 5463250 * 2
def baseEnd_5463250 : Nat := 2805273185675855242949977

theorem tailTrace_5463250 : CollatzResearch.WordTrace tailWord_5463250 prefixEnd_5463250 2805273185675855242949977 := by
  unfold tailWord_5463250
  simp only [CollatzResearch.WordTrace]
  refine ⟨49815274364396443415324801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132840731638390515774199469 49815274364396443415324801)
  ·
    refine ⟨37361455773297332561493601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49815274364396443415324801 37361455773297332561493601)
    ·
      refine ⟨28021091829972999421120201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37361455773297332561493601 28021091829972999421120201)
      ·
        refine ⟨21015818872479749565840151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28021091829972999421120201 21015818872479749565840151)
        ·
          refine ⟨31523728308719624348760227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21015818872479749565840151 31523728308719624348760227)
          ·
            refine ⟨47285592463079436523140341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31523728308719624348760227 47285592463079436523140341)
            ·
              refine ⟨4433024293413697174044407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47285592463079436523140341 4433024293413697174044407)
              ·
                refine ⟨6649536440120545761066611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4433024293413697174044407 6649536440120545761066611)
                ·
                  refine ⟨9974304660180818641599917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6649536440120545761066611 9974304660180818641599917)
                  ·
                    refine ⟨3740364247567806990599969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9974304660180818641599917 3740364247567806990599969)
                    ·
                      refine ⟨2805273185675855242949977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3740364247567806990599969 2805273185675855242949977)
                      ·
                        rfl

theorem cell23_5463250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_5463250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5463250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5463250 prefixEnd_5463250 := by exact prefixLift 5463250
  have htrace : WordTrace (prefixWord ++ tailWord_5463250) baseStart_5463250 baseEnd_5463250 := by
    simpa [prefixWord, tailWord_5463250, baseEnd_5463250] using wordTrace_append hprefix tailTrace_5463250
  have hstable : (prefixWord ++ tailWord_5463250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5463250).length < 2 ^ (prefixWord ++ tailWord_5463250).sum := by decide
  have hdescent : baseEnd_5463250 < baseStart_5463250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5463250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5463263 : List Nat := [1, 1, 2, 3, 2, 1, 3, 4, 2, 2, 2]
def baseStart_5463263 : Nat := 118140960795 + 5463263 * 2 ^ 59
def prefixEnd_5463263 : Nat := 4983230072969 + 3 ^ 40 * 5463263 * 2
def baseEnd_5463263 : Nat := 2805279860924363692087417

theorem tailTrace_5463263 : CollatzResearch.WordTrace tailWord_5463263 prefixEnd_5463263 2805279860924363692087417 := by
  unfold tailWord_5463263
  simp only [CollatzResearch.WordTrace]
  refine ⟨199261571606538676881522443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132841047737692451254348295 199261571606538676881522443)
  ·
    refine ⟨298892357409808015322283665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199261571606538676881522443 298892357409808015322283665)
    ·
      refine ⟨224169268057356011491712749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 298892357409808015322283665 224169268057356011491712749)
      ·
        refine ⟨84063475521508504309392281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 224169268057356011491712749 84063475521508504309392281)
        ·
          refine ⟨63047606641131378232044211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84063475521508504309392281 63047606641131378232044211)
          ·
            refine ⟨94571409961697067348066317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63047606641131378232044211 94571409961697067348066317)
            ·
              refine ⟨35464278735636400255524869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94571409961697067348066317 35464278735636400255524869)
              ·
                refine ⟨6649552262931825047910913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35464278735636400255524869 6649552262931825047910913)
                ·
                  refine ⟨4987164197198868785933185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6649552262931825047910913 4987164197198868785933185)
                  ·
                    refine ⟨3740373147899151589449889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4987164197198868785933185 3740373147899151589449889)
                    ·
                      refine ⟨2805279860924363692087417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3740373147899151589449889 2805279860924363692087417)
                      ·
                        rfl

theorem cell23_5463263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 4, 2, 2, 2].length) (baseStart_5463263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5463263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5463263 prefixEnd_5463263 := by exact prefixLift 5463263
  have htrace : WordTrace (prefixWord ++ tailWord_5463263) baseStart_5463263 baseEnd_5463263 := by
    simpa [prefixWord, tailWord_5463263, baseEnd_5463263] using wordTrace_append hprefix tailTrace_5463263
  have hstable : (prefixWord ++ tailWord_5463263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5463263).length < 2 ^ (prefixWord ++ tailWord_5463263).sum := by decide
  have hdescent : baseEnd_5463263 < baseStart_5463263 := by decide
  rcases family_descends (prefixWord ++ tailWord_5463263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5463299 : List Nat := [1, 1, 1, 3, 2, 5, 1, 1, 1, 7]
def baseStart_5463299 : Nat := 118140960795 + 5463299 * 2 ^ 59
def prefixEnd_5463299 : Nat := 4983230072969 + 3 ^ 40 * 5463299 * 2
def baseEnd_5463299 : Nat := 935099448742641850412417

theorem tailTrace_5463299 : CollatzResearch.WordTrace tailWord_5463299 prefixEnd_5463299 935099448742641850412417 := by
  unfold tailWord_5463299
  simp only [CollatzResearch.WordTrace]
  refine ⟨199262884634408255029832951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132841923089605503353221967 199262884634408255029832951)
  ·
    refine ⟨298894326951612382544749427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199262884634408255029832951 298894326951612382544749427)
    ·
      refine ⟨448341490427418573817124141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298894326951612382544749427 448341490427418573817124141)
      ·
        refine ⟨168128058910281965181421553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 448341490427418573817124141 168128058910281965181421553)
        ·
          refine ⟨126096044182711473886066165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168128058910281965181421553 126096044182711473886066165)
          ·
            refine ⟨11821504142129200676818703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 126096044182711473886066165 11821504142129200676818703)
            ·
              refine ⟨17732256213193801015228055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11821504142129200676818703 17732256213193801015228055)
              ·
                refine ⟨26598384319790701522842083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17732256213193801015228055 26598384319790701522842083)
                ·
                  refine ⟨39897576479686052284263125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26598384319790701522842083 39897576479686052284263125)
                  ·
                    refine ⟨935099448742641850412417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39897576479686052284263125 935099448742641850412417)
                    ·
                      rfl

theorem cell23_5463299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 7].length) (baseStart_5463299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5463299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5463299 prefixEnd_5463299 := by exact prefixLift 5463299
  have htrace : WordTrace (prefixWord ++ tailWord_5463299) baseStart_5463299 baseEnd_5463299 := by
    simpa [prefixWord, tailWord_5463299, baseEnd_5463299] using wordTrace_append hprefix tailTrace_5463299
  have hstable : (prefixWord ++ tailWord_5463299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5463299).length < 2 ^ (prefixWord ++ tailWord_5463299).sum := by decide
  have hdescent : baseEnd_5463299 < baseStart_5463299 := by decide
  rcases family_descends (prefixWord ++ tailWord_5463299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5463336 : List Nat := [2, 1, 5, 1, 2, 1, 1, 2, 1, 3, 4]
def baseStart_5463336 : Nat := 118140960795 + 5463336 * 2 ^ 59
def prefixEnd_5463336 : Nat := 4983230072969 + 3 ^ 40 * 5463336 * 2
def baseEnd_5463336 : Nat := 2805317345012141906474581

theorem tailTrace_5463336 : CollatzResearch.WordTrace tailWord_5463336 prefixEnd_5463336 2805317345012141906474581 := by
  unfold tailWord_5463336
  simp only [CollatzResearch.WordTrace]
  refine ⟨99632117067637105174464931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132842822756849473565953241 99632117067637105174464931)
  ·
    refine ⟨149448175601455657761697397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99632117067637105174464931 149448175601455657761697397)
    ·
      refine ⟨14010766462636467915159131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 149448175601455657761697397 14010766462636467915159131)
      ·
        refine ⟨21016149693954701872738697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14010766462636467915159131 21016149693954701872738697)
        ·
          refine ⟨15762112270466026404554023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21016149693954701872738697 15762112270466026404554023)
          ·
            refine ⟨23643168405699039606831035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15762112270466026404554023 23643168405699039606831035)
            ·
              refine ⟨35464752608548559410246553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23643168405699039606831035 35464752608548559410246553)
              ·
                refine ⟨26598564456411419557684915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35464752608548559410246553 26598564456411419557684915)
                ·
                  refine ⟨39897846684617129336527373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26598564456411419557684915 39897846684617129336527373)
                  ·
                    refine ⟨14961692506731423501197765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39897846684617129336527373 14961692506731423501197765)
                    ·
                      refine ⟨2805317345012141906474581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14961692506731423501197765 2805317345012141906474581)
                      ·
                        rfl

theorem cell23_5463336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_5463336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5463336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5463336 prefixEnd_5463336 := by exact prefixLift 5463336
  have htrace : WordTrace (prefixWord ++ tailWord_5463336) baseStart_5463336 baseEnd_5463336 := by
    simpa [prefixWord, tailWord_5463336, baseEnd_5463336] using wordTrace_append hprefix tailTrace_5463336
  have hstable : (prefixWord ++ tailWord_5463336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5463336).length < 2 ^ (prefixWord ++ tailWord_5463336).sum := by decide
  have hdescent : baseEnd_5463336 < baseStart_5463336 := by decide
  rcases family_descends (prefixWord ++ tailWord_5463336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5463356 : List Nat := [2, 2, 2, 2, 1, 3, 2, 1, 1, 4, 3]
def baseStart_5463356 : Nat := 118140960795 + 5463356 * 2 ^ 59
def prefixEnd_5463356 : Nat := 4983230072969 + 3 ^ 40 * 5463356 * 2
def baseEnd_5463356 : Nat := 2805327614625231828224489

theorem tailTrace_5463356 : CollatzResearch.WordTrace tailWord_5463356 prefixEnd_5463356 2805327614625231828224489 := by
  unfold tailWord_5463356
  simp only [CollatzResearch.WordTrace]
  refine ⟨99632481797600876882328961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132843309063467835843105281 99632481797600876882328961)
  ·
    refine ⟨74724361348200657661746721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99632481797600876882328961 74724361348200657661746721)
    ·
      refine ⟨56043271011150493246310041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74724361348200657661746721 56043271011150493246310041)
      ·
        refine ⟨42032453258362869934732531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56043271011150493246310041 42032453258362869934732531)
        ·
          refine ⟨63048679887544304902098797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42032453258362869934732531 63048679887544304902098797)
          ·
            refine ⟨23643254957829114338287049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63048679887544304902098797 23643254957829114338287049)
            ·
              refine ⟨17732441218371835753715287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23643254957829114338287049 17732441218371835753715287)
              ·
                refine ⟨26598661827557753630572931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17732441218371835753715287 26598661827557753630572931)
                ·
                  refine ⟨39897992741336630445859397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26598661827557753630572931 39897992741336630445859397)
                  ·
                    refine ⟨7480873639000618208598637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39897992741336630445859397 7480873639000618208598637)
                    ·
                      refine ⟨2805327614625231828224489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7480873639000618208598637 2805327614625231828224489)
                      ·
                        rfl

theorem cell23_5463356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_5463356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5463356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5463356 prefixEnd_5463356 := by exact prefixLift 5463356
  have htrace : WordTrace (prefixWord ++ tailWord_5463356) baseStart_5463356 baseEnd_5463356 := by
    simpa [prefixWord, tailWord_5463356, baseEnd_5463356] using wordTrace_append hprefix tailTrace_5463356
  have hstable : (prefixWord ++ tailWord_5463356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5463356).length < 2 ^ (prefixWord ++ tailWord_5463356).sum := by decide
  have hdescent : baseEnd_5463356 < baseStart_5463356 := by decide
  rcases family_descends (prefixWord ++ tailWord_5463356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5463359 : List Nat := [1, 1, 2, 2, 4, 2, 1, 2, 8]
def baseStart_5463359 : Nat := 118140960795 + 5463359 * 2 ^ 59
def prefixEnd_5463359 : Nat := 4983230072969 + 3 ^ 40 * 5463359 * 2
def baseEnd_5463359 : Nat := 311703239451910590720775

theorem tailTrace_5463359 : CollatzResearch.WordTrace tailWord_5463359 prefixEnd_5463359 311703239451910590720775 := by
  unfold tailWord_5463359
  simp only [CollatzResearch.WordTrace]
  refine ⟨199265073014190885277017131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132843382009460590184678087 199265073014190885277017131)
  ·
    refine ⟨298897609521286327915525697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199265073014190885277017131 298897609521286327915525697)
    ·
      refine ⟨224173207140964745936644273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 298897609521286327915525697 224173207140964745936644273)
      ·
        refine ⟨168129905355723559452483205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224173207140964745936644273 168129905355723559452483205)
        ·
          refine ⟨31524357254198167397340601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 168129905355723559452483205 31524357254198167397340601)
          ·
            refine ⟨23643267940648625548005451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31524357254198167397340601 23643267940648625548005451)
            ·
              refine ⟨35464901910972938322008177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23643267940648625548005451 35464901910972938322008177)
              ·
                refine ⟨26598676433229703741506133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35464901910972938322008177 26598676433229703741506133)
                ·
                  refine ⟨311703239451910590720775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26598676433229703741506133 311703239451910590720775)
                  ·
                    rfl

theorem cell23_5463359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 8].length) (baseStart_5463359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5463359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5463359 prefixEnd_5463359 := by exact prefixLift 5463359
  have htrace : WordTrace (prefixWord ++ tailWord_5463359) baseStart_5463359 baseEnd_5463359 := by
    simpa [prefixWord, tailWord_5463359, baseEnd_5463359] using wordTrace_append hprefix tailTrace_5463359
  have hstable : (prefixWord ++ tailWord_5463359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5463359).length < 2 ^ (prefixWord ++ tailWord_5463359).sum := by decide
  have hdescent : baseEnd_5463359 < baseStart_5463359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5463359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5463420 : List Nat := [2, 2, 2, 1, 1, 1, 4, 5, 1, 1, 3]
def baseStart_5463420 : Nat := 118140960795 + 5463420 * 2 ^ 59
def prefixEnd_5463420 : Nat := 4983230072969 + 3 ^ 40 * 5463420 * 2
def baseEnd_5463420 : Nat := 2805360477387119577824195

theorem tailTrace_5463420 : CollatzResearch.WordTrace tailWord_5463420 prefixEnd_5463420 2805360477387119577824195 := by
  unfold tailWord_5463420
  simp only [CollatzResearch.WordTrace]
  refine ⟨99633648933484946347493857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132844865244646595129991809 99633648933484946347493857)
  ·
    refine ⟨74725236700113709760620393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99633648933484946347493857 74725236700113709760620393)
    ·
      refine ⟨56043927525085282320465295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74725236700113709760620393 56043927525085282320465295)
      ·
        refine ⟨84065891287627923480697943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56043927525085282320465295 84065891287627923480697943)
        ·
          refine ⟨126098836931441885221046915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84065891287627923480697943 126098836931441885221046915)
          ·
            refine ⟨189148255397162827831570373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126098836931441885221046915 189148255397162827831570373)
            ·
              refine ⟨35465297886968030218419445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 189148255397162827831570373 35465297886968030218419445)
              ·
                refine ⟨3324871676903252832976823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35465297886968030218419445 3324871676903252832976823)
                ·
                  refine ⟨4987307515354879249465235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3324871676903252832976823 4987307515354879249465235)
                  ·
                    refine ⟨7480961273032318874197853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4987307515354879249465235 7480961273032318874197853)
                    ·
                      refine ⟨2805360477387119577824195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7480961273032318874197853 2805360477387119577824195)
                      ·
                        rfl

theorem cell23_5463420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 5, 1, 1, 3].length) (baseStart_5463420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5463420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5463420 prefixEnd_5463420 := by exact prefixLift 5463420
  have htrace : WordTrace (prefixWord ++ tailWord_5463420) baseStart_5463420 baseEnd_5463420 := by
    simpa [prefixWord, tailWord_5463420, baseEnd_5463420] using wordTrace_append hprefix tailTrace_5463420
  have hstable : (prefixWord ++ tailWord_5463420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5463420).length < 2 ^ (prefixWord ++ tailWord_5463420).sum := by decide
  have hdescent : baseEnd_5463420 < baseStart_5463420 := by decide
  rcases family_descends (prefixWord ++ tailWord_5463420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5463443 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 9, 2, 2]
def baseStart_5463443 : Nat := 118140960795 + 5463443 * 2 ^ 59
def prefixEnd_5463443 : Nat := 4983230072969 + 3 ^ 40 * 5463443 * 2
def baseEnd_5463443 : Nat := 2805372287442172987836589

theorem tailTrace_5463443 : CollatzResearch.WordTrace tailWord_5463443 prefixEnd_5463443 2805372287442172987836589 := by
  unfold tailWord_5463443
  simp only [CollatzResearch.WordTrace]
  refine ⟨199268136745886567623074983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132845424497257711748716655 199268136745886567623074983)
  ·
    refine ⟨298902205118829851434612475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199268136745886567623074983 298902205118829851434612475)
    ·
      refine ⟨448353307678244777151918713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298902205118829851434612475 448353307678244777151918713)
      ·
        refine ⟨336264980758683582863939035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 448353307678244777151918713 336264980758683582863939035)
        ·
          refine ⟨504397471138025374295908553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 336264980758683582863939035 504397471138025374295908553)
          ·
            refine ⟨378298103353519030721931415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 504397471138025374295908553 378298103353519030721931415)
            ·
              refine ⟨567447155030278546082897123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 378298103353519030721931415 567447155030278546082897123)
              ·
                refine ⟨851170732545417819124345685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 567447155030278546082897123 851170732545417819124345685)
                ·
                  refine ⟨4987328511008307533931713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 851170732545417819124345685 4987328511008307533931713)
                  ·
                    refine ⟨3740496383256230650448785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4987328511008307533931713 3740496383256230650448785)
                    ·
                      refine ⟨2805372287442172987836589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3740496383256230650448785 2805372287442172987836589)
                      ·
                        rfl

theorem cell23_5463443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 9, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 9, 2, 2].length) (baseStart_5463443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5463443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5463443 prefixEnd_5463443 := by exact prefixLift 5463443
  have htrace : WordTrace (prefixWord ++ tailWord_5463443) baseStart_5463443 baseEnd_5463443 := by
    simpa [prefixWord, tailWord_5463443, baseEnd_5463443] using wordTrace_append hprefix tailTrace_5463443
  have hstable : (prefixWord ++ tailWord_5463443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5463443).length < 2 ^ (prefixWord ++ tailWord_5463443).sum := by decide
  have hdescent : baseEnd_5463443 < baseStart_5463443 := by decide
  rcases family_descends (prefixWord ++ tailWord_5463443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5463453 : List Nat := [1, 4, 2, 1, 3, 2, 2, 1, 1, 6]
def baseStart_5463453 : Nat := 118140960795 + 5463453 * 2 ^ 59
def prefixEnd_5463453 : Nat := 4983230072969 + 3 ^ 40 * 5463453 * 2
def baseEnd_5463453 : Nat := 935125807416239316237181

theorem tailTrace_5463453 : CollatzResearch.WordTrace tailWord_5463453 prefixEnd_5463453 935125807416239316237181 := by
  unfold tailWord_5463453
  simp only [CollatzResearch.WordTrace]
  refine ⟨199268501475850339330939013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132845667650566892887292675 199268501475850339330939013)
  ·
    refine ⟨37362844026721938624551065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 199268501475850339330939013 37362844026721938624551065)
    ·
      refine ⟨28022133020041453968413299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37362844026721938624551065 28022133020041453968413299)
      ·
        refine ⟨42033199530062180952619949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28022133020041453968413299 42033199530062180952619949)
        ·
          refine ⟨15762449823773317857232481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42033199530062180952619949 15762449823773317857232481)
          ·
            refine ⟨11821837367829988392924361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15762449823773317857232481 11821837367829988392924361)
            ·
              refine ⟨8866378025872491294693271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11821837367829988392924361 8866378025872491294693271)
              ·
                refine ⟨13299567038808736942039907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8866378025872491294693271 13299567038808736942039907)
                ·
                  refine ⟨19949350558213105413059861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13299567038808736942039907 19949350558213105413059861)
                  ·
                    refine ⟨935125807416239316237181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19949350558213105413059861 935125807416239316237181)
                    ·
                      rfl

theorem cell23_5463453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_5463453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5463453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5463453 prefixEnd_5463453 := by exact prefixLift 5463453
  have htrace : WordTrace (prefixWord ++ tailWord_5463453) baseStart_5463453 baseEnd_5463453 := by
    simpa [prefixWord, tailWord_5463453, baseEnd_5463453] using wordTrace_append hprefix tailTrace_5463453
  have hstable : (prefixWord ++ tailWord_5463453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5463453).length < 2 ^ (prefixWord ++ tailWord_5463453).sum := by decide
  have hdescent : baseEnd_5463453 < baseStart_5463453 := by decide
  rcases family_descends (prefixWord ++ tailWord_5463453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5463463 : List Nat := [1, 1, 6, 1, 1, 1, 1, 3, 3, 2, 3]
def baseStart_5463463 : Nat := 118140960795 + 5463463 * 2 ^ 59
def prefixEnd_5463463 : Nat := 4983230072969 + 3 ^ 40 * 5463463 * 2
def baseEnd_5463463 : Nat := 2805382557055262909586497

theorem tailTrace_5463463 : CollatzResearch.WordTrace tailWord_5463463 prefixEnd_5463463 2805382557055262909586497 := by
  unfold tailWord_5463463
  simp only [CollatzResearch.WordTrace]
  refine ⟨199268866205814111038803043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132845910803876074025868695 199268866205814111038803043)
  ·
    refine ⟨298903299308721166558204565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199268866205814111038803043 298903299308721166558204565)
    ·
      refine ⟨14011092155096304682415839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 298903299308721166558204565 14011092155096304682415839)
      ·
        refine ⟨21016638232644457023623759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14011092155096304682415839 21016638232644457023623759)
        ·
          refine ⟨31524957348966685535435639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21016638232644457023623759 31524957348966685535435639)
          ·
            refine ⟨47287436023450028303153459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31524957348966685535435639 47287436023450028303153459)
            ·
              refine ⟨70931154035175042454730189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47287436023450028303153459 70931154035175042454730189)
              ·
                refine ⟨26599182763190640920523821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70931154035175042454730189 26599182763190640920523821)
                ·
                  refine ⟨9974693536196490345196433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26599182763190640920523821 9974693536196490345196433)
                  ·
                    refine ⟨7481020152147367758897325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9974693536196490345196433 7481020152147367758897325)
                    ·
                      refine ⟨2805382557055262909586497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7481020152147367758897325 2805382557055262909586497)
                      ·
                        rfl

theorem cell23_5463463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_5463463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5463463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5463463 prefixEnd_5463463 := by exact prefixLift 5463463
  have htrace : WordTrace (prefixWord ++ tailWord_5463463) baseStart_5463463 baseEnd_5463463 := by
    simpa [prefixWord, tailWord_5463463, baseEnd_5463463] using wordTrace_append hprefix tailTrace_5463463
  have hstable : (prefixWord ++ tailWord_5463463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5463463).length < 2 ^ (prefixWord ++ tailWord_5463463).sum := by decide
  have hdescent : baseEnd_5463463 < baseStart_5463463 := by decide
  rcases family_descends (prefixWord ++ tailWord_5463463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5463464 : List Nat := [2, 1, 6, 1, 2, 2, 1, 1, 2, 3, 2]
def baseStart_5463464 : Nat := 118140960795 + 5463464 * 2 ^ 59
def prefixEnd_5463464 : Nat := 4983230072969 + 3 ^ 40 * 5463464 * 2
def baseEnd_5463464 : Nat := 2805383070535917405673993

theorem tailTrace_5463464 : CollatzResearch.WordTrace tailWord_5463464 prefixEnd_5463464 2805383070535917405673993 := by
  unfold tailWord_5463464
  simp only [CollatzResearch.WordTrace]
  refine ⟨99634451339405244104794723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132845935119206992139726297 99634451339405244104794723)
  ·
    refine ⟨149451677009107866157192085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99634451339405244104794723 149451677009107866157192085)
    ·
      refine ⟨7005547359801931226118379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 149451677009107866157192085 7005547359801931226118379)
      ·
        refine ⟨10508321039702896839177569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7005547359801931226118379 10508321039702896839177569)
        ·
          refine ⟨7881240779777172629383177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10508321039702896839177569 7881240779777172629383177)
          ·
            refine ⟨5910930584832879472037383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7881240779777172629383177 5910930584832879472037383)
            ·
              refine ⟨8866395877249319208056075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5910930584832879472037383 8866395877249319208056075)
              ·
                refine ⟨13299593815873978812084113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8866395877249319208056075 13299593815873978812084113)
                ·
                  refine ⟨9974695361905484109063085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13299593815873978812084113 9974695361905484109063085)
                  ·
                    refine ⟨3740510760714556540898657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9974695361905484109063085 3740510760714556540898657)
                    ·
                      refine ⟨2805383070535917405673993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3740510760714556540898657 2805383070535917405673993)
                      ·
                        rfl

theorem cell23_5463464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_5463464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5463464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5463464 prefixEnd_5463464 := by exact prefixLift 5463464
  have htrace : WordTrace (prefixWord ++ tailWord_5463464) baseStart_5463464 baseEnd_5463464 := by
    simpa [prefixWord, tailWord_5463464, baseEnd_5463464] using wordTrace_append hprefix tailTrace_5463464
  have hstable : (prefixWord ++ tailWord_5463464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5463464).length < 2 ^ (prefixWord ++ tailWord_5463464).sum := by decide
  have hdescent : baseEnd_5463464 < baseStart_5463464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5463464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5463477 : List Nat := [1, 3, 3, 2, 2, 3, 2, 1, 1, 1, 4]
def baseStart_5463477 : Nat := 118140960795 + 5463477 * 2 ^ 59
def prefixEnd_5463477 : Nat := 4983230072969 + 3 ^ 40 * 5463477 * 2
def baseEnd_5463477 : Nat := 2805389745784425854811433

theorem tailTrace_5463477 : CollatzResearch.WordTrace tailWord_5463477 prefixEnd_5463477 2805389745784425854811433 := by
  unfold tailWord_5463477
  simp only [CollatzResearch.WordTrace]
  refine ⟨199269376827763391429812685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132846251218508927619875123 199269376827763391429812685)
  ·
    refine ⟨74726016310411271786179757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199269376827763391429812685 74726016310411271786179757)
    ·
      refine ⟨28022256116404226919817409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74726016310411271786179757 28022256116404226919817409)
      ·
        refine ⟨21016692087303170189863057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28022256116404226919817409 21016692087303170189863057)
        ·
          refine ⟨15762519065477377642397293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21016692087303170189863057 15762519065477377642397293)
          ·
            refine ⟨5910944649554016615898985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15762519065477377642397293 5910944649554016615898985)
            ·
              refine ⟨4433208487165512461924239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5910944649554016615898985 4433208487165512461924239)
              ·
                refine ⟨6649812730748268692886359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4433208487165512461924239 6649812730748268692886359)
                ·
                  refine ⟨9974719096122403039329539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6649812730748268692886359 9974719096122403039329539)
                  ·
                    refine ⟨14962078644183604558994309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9974719096122403039329539 14962078644183604558994309)
                    ·
                      refine ⟨2805389745784425854811433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14962078644183604558994309 2805389745784425854811433)
                      ·
                        rfl

theorem cell23_5463477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_5463477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5463477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5463477 prefixEnd_5463477 := by exact prefixLift 5463477
  have htrace : WordTrace (prefixWord ++ tailWord_5463477) baseStart_5463477 baseEnd_5463477 := by
    simpa [prefixWord, tailWord_5463477, baseEnd_5463477] using wordTrace_append hprefix tailTrace_5463477
  have hstable : (prefixWord ++ tailWord_5463477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5463477).length < 2 ^ (prefixWord ++ tailWord_5463477).sum := by decide
  have hdescent : baseEnd_5463477 < baseStart_5463477 := by decide
  rcases family_descends (prefixWord ++ tailWord_5463477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5463480 : List Nat := [2, 1, 2, 1, 2, 2, 6, 1, 1, 2, 3]
def baseStart_5463480 : Nat := 118140960795 + 5463480 * 2 ^ 59
def prefixEnd_5463480 : Nat := 4983230072969 + 3 ^ 40 * 5463480 * 2
def baseEnd_5463480 : Nat := 2805391286226389343073919

theorem tailTrace_5463480 : CollatzResearch.WordTrace tailWord_5463480 prefixEnd_5463480 2805391286226389343073919 := by
  unfold tailWord_5463480
  simp only [CollatzResearch.WordTrace]
  refine ⟨99634743123376261471085947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132846324164501681961447929 99634743123376261471085947)
  ·
    refine ⟨149452114685064392206628921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99634743123376261471085947 149452114685064392206628921)
    ·
      refine ⟨112089086013798294154971691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149452114685064392206628921 112089086013798294154971691)
      ·
        refine ⟨168133629020697441232457537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112089086013798294154971691 168133629020697441232457537)
        ·
          refine ⟨126100221765523080924343153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168133629020697441232457537 126100221765523080924343153)
          ·
            refine ⟨94575166324142310693257365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126100221765523080924343153 94575166324142310693257365)
            ·
              refine ⟨4433210921444170813746439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 94575166324142310693257365 4433210921444170813746439)
              ·
                refine ⟨6649816382166256220619659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4433210921444170813746439 6649816382166256220619659)
                ·
                  refine ⟨9974724573249384330929489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6649816382166256220619659 9974724573249384330929489)
                  ·
                    refine ⟨7481043429937038248197117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9974724573249384330929489 7481043429937038248197117)
                    ·
                      refine ⟨2805391286226389343073919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7481043429937038248197117 2805391286226389343073919)
                      ·
                        rfl

theorem cell23_5463480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 1, 1, 2, 3].length) (baseStart_5463480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5463480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5463480 prefixEnd_5463480 := by exact prefixLift 5463480
  have htrace : WordTrace (prefixWord ++ tailWord_5463480) baseStart_5463480 baseEnd_5463480 := by
    simpa [prefixWord, tailWord_5463480, baseEnd_5463480] using wordTrace_append hprefix tailTrace_5463480
  have hstable : (prefixWord ++ tailWord_5463480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5463480).length < 2 ^ (prefixWord ++ tailWord_5463480).sum := by decide
  have hdescent : baseEnd_5463480 < baseStart_5463480 := by decide
  rcases family_descends (prefixWord ++ tailWord_5463480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5463486 : List Nat := [4, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6]
def baseStart_5463486 : Nat := 118140960795 + 5463486 * 2 ^ 59
def prefixEnd_5463486 : Nat := 4983230072969 + 3 ^ 40 * 5463486 * 2
def baseEnd_5463486 : Nat := 2805394367110316319598891

theorem tailTrace_5463486 : CollatzResearch.WordTrace tailWord_5463486 prefixEnd_5463486 2805394367110316319598891 := by
  unfold tailWord_5463486
  simp only [CollatzResearch.WordTrace]
  refine ⟨24908713135591348245861289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132846470056487190644593541 24908713135591348245861289)
  ·
    refine ⟨18681534851693511184395967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24908713135591348245861289 18681534851693511184395967)
    ·
      refine ⟨28022302277540266776593951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18681534851693511184395967 28022302277540266776593951)
      ·
        refine ⟨42033453416310400164890927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28022302277540266776593951 42033453416310400164890927)
        ·
          refine ⟨63050180124465600247336391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42033453416310400164890927 63050180124465600247336391)
          ·
            refine ⟨94575270186698400371004587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63050180124465600247336391 94575270186698400371004587)
            ·
              refine ⟨141862905280047600556506881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94575270186698400371004587 141862905280047600556506881)
              ·
                refine ⟨106397178960035700417380161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141862905280047600556506881 106397178960035700417380161)
                ·
                  refine ⟨79797884220026775313035121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106397178960035700417380161 79797884220026775313035121)
                  ·
                    refine ⟨59848413165020081484776341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 79797884220026775313035121 59848413165020081484776341)
                    ·
                      refine ⟨2805394367110316319598891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59848413165020081484776341 2805394367110316319598891)
                      ·
                        rfl

theorem cell23_5463486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_5463486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5463486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5463486 prefixEnd_5463486 := by exact prefixLift 5463486
  have htrace : WordTrace (prefixWord ++ tailWord_5463486) baseStart_5463486 baseEnd_5463486 := by
    simpa [prefixWord, tailWord_5463486, baseEnd_5463486] using wordTrace_append hprefix tailTrace_5463486
  have hstable : (prefixWord ++ tailWord_5463486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5463486).length < 2 ^ (prefixWord ++ tailWord_5463486).sum := by decide
  have hdescent : baseEnd_5463486 < baseStart_5463486 := by decide
  rcases family_descends (prefixWord ++ tailWord_5463486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5463503 : List Nat := [1, 1, 2, 1, 1, 4, 2, 1, 5, 3, 2]
def baseStart_5463503 : Nat := 118140960795 + 5463503 * 2 ^ 59
def prefixEnd_5463503 : Nat := 4983230072969 + 3 ^ 40 * 5463503 * 2
def baseEnd_5463503 : Nat := 2805403096281442753086313

theorem tailTrace_5463503 : CollatzResearch.WordTrace tailWord_5463503 prefixEnd_5463503 2805403096281442753086313 := by
  unfold tailWord_5463503
  simp only [CollatzResearch.WordTrace]
  refine ⟨199270325125669197870259163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132846883417112798580172775 199270325125669197870259163)
  ·
    refine ⟨298905487688503796805388745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199270325125669197870259163 298905487688503796805388745)
    ·
      refine ⟨224179115766377847604041559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 298905487688503796805388745 224179115766377847604041559)
      ·
        refine ⟨336268673649566771406062339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224179115766377847604041559 336268673649566771406062339)
        ·
          refine ⟨504403010474350157109093509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 336268673649566771406062339 504403010474350157109093509)
          ·
            refine ⟨94575564463940654457955033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 504403010474350157109093509 94575564463940654457955033)
            ·
              refine ⟨70931673347955490843466275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94575564463940654457955033 70931673347955490843466275)
              ·
                refine ⟨106397510021933236265199413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70931673347955490843466275 106397510021933236265199413)
                ·
                  refine ⟨9974766564556240899862445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 106397510021933236265199413 9974766564556240899862445)
                  ·
                    refine ⟨3740537461708590337448417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9974766564556240899862445 3740537461708590337448417)
                    ·
                      refine ⟨2805403096281442753086313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3740537461708590337448417 2805403096281442753086313)
                      ·
                        rfl

theorem cell23_5463503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 5, 3, 2].length) (baseStart_5463503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5463503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5463503 prefixEnd_5463503 := by exact prefixLift 5463503
  have htrace : WordTrace (prefixWord ++ tailWord_5463503) baseStart_5463503 baseEnd_5463503 := by
    simpa [prefixWord, tailWord_5463503, baseEnd_5463503] using wordTrace_append hprefix tailTrace_5463503
  have hstable : (prefixWord ++ tailWord_5463503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5463503).length < 2 ^ (prefixWord ++ tailWord_5463503).sum := by decide
  have hdescent : baseEnd_5463503 < baseStart_5463503 := by decide
  rcases family_descends (prefixWord ++ tailWord_5463503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5463536 : List Nat := [2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 5]
def baseStart_5463536 : Nat := 118140960795 + 5463536 * 2 ^ 59
def prefixEnd_5463536 : Nat := 4983230072969 + 3 ^ 40 * 5463536 * 2
def baseEnd_5463536 : Nat := 2805420041143041123973661

theorem tailTrace_5463536 : CollatzResearch.WordTrace tailWord_5463536 prefixEnd_5463536 2805420041143041123973661 := by
  unfold tailWord_5463536
  simp only [CollatzResearch.WordTrace]
  refine ⟨99635764367274822253105231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132847685823033096337473641 99635764367274822253105231)
  ·
    refine ⟨149453646550912233379657847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99635764367274822253105231 149453646550912233379657847)
    ·
      refine ⟨224180469826368350069486771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149453646550912233379657847 224180469826368350069486771)
      ·
        refine ⟨336270704739552525104230157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224180469826368350069486771 336270704739552525104230157)
        ·
          refine ⟨126101514277332196914086309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 336270704739552525104230157 126101514277332196914086309)
          ·
            refine ⟨23644033926999786921391183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126101514277332196914086309 23644033926999786921391183)
            ·
              refine ⟨35466050890499680382086775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23644033926999786921391183 35466050890499680382086775)
              ·
                refine ⟨53199076335749520573130163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35466050890499680382086775 53199076335749520573130163)
                ·
                  refine ⟨79798614503624280859695245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53199076335749520573130163 79798614503624280859695245)
                  ·
                    refine ⟨29924480438859105322385717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 79798614503624280859695245 29924480438859105322385717)
                    ·
                      refine ⟨2805420041143041123973661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29924480438859105322385717 2805420041143041123973661)
                      ·
                        rfl

theorem cell23_5463536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 5].length) (baseStart_5463536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5463536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5463536 prefixEnd_5463536 := by exact prefixLift 5463536
  have htrace : WordTrace (prefixWord ++ tailWord_5463536) baseStart_5463536 baseEnd_5463536 := by
    simpa [prefixWord, tailWord_5463536, baseEnd_5463536] using wordTrace_append hprefix tailTrace_5463536
  have hstable : (prefixWord ++ tailWord_5463536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5463536).length < 2 ^ (prefixWord ++ tailWord_5463536).sum := by decide
  have hdescent : baseEnd_5463536 < baseStart_5463536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5463536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5463603 : List Nat := [1, 1, 1, 2, 4, 3, 2, 2, 2, 5]
def baseStart_5463603 : Nat := 118140960795 + 5463603 * 2 ^ 59
def prefixEnd_5463603 : Nat := 4983230072969 + 3 ^ 40 * 5463603 * 2
def baseEnd_5463603 : Nat := 935151481448964120611951

theorem tailTrace_5463603 : CollatzResearch.WordTrace tailWord_5463603 prefixEnd_5463603 935151481448964120611951 := by
  unfold tailWord_5463603
  simp only [CollatzResearch.WordTrace]
  refine ⟨199273972425306914948899463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132849314950204609965932975 199273972425306914948899463)
  ·
    refine ⟨298910958637960372423349195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199273972425306914948899463 298910958637960372423349195)
    ·
      refine ⟨448366437956940558635023793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298910958637960372423349195 448366437956940558635023793)
      ·
        refine ⟨336274828467705418976267845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 448366437956940558635023793 336274828467705418976267845)
        ·
          refine ⟨63051530337694766058050221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 336274828467705418976267845 63051530337694766058050221)
          ·
            refine ⟨23644323876635537271768833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63051530337694766058050221 23644323876635537271768833)
            ·
              refine ⟨17733242907476652953826625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23644323876635537271768833 17733242907476652953826625)
              ·
                refine ⟨13299932180607489715369969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17733242907476652953826625 13299932180607489715369969)
                ·
                  refine ⟨9974949135455617286527477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13299932180607489715369969 9974949135455617286527477)
                  ·
                    refine ⟨935151481448964120611951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9974949135455617286527477 935151481448964120611951)
                    ·
                      rfl

theorem cell23_5463603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 2, 5].length) (baseStart_5463603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5463603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5463603 prefixEnd_5463603 := by exact prefixLift 5463603
  have htrace : WordTrace (prefixWord ++ tailWord_5463603) baseStart_5463603 baseEnd_5463603 := by
    simpa [prefixWord, tailWord_5463603, baseEnd_5463603] using wordTrace_append hprefix tailTrace_5463603
  have hstable : (prefixWord ++ tailWord_5463603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5463603).length < 2 ^ (prefixWord ++ tailWord_5463603).sum := by decide
  have hdescent : baseEnd_5463603 < baseStart_5463603 := by decide
  rcases family_descends (prefixWord ++ tailWord_5463603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5463607 : List Nat := [1, 1, 3, 1, 2, 6, 2, 2, 5]
def baseStart_5463607 : Nat := 118140960795 + 5463607 * 2 ^ 59
def prefixEnd_5463607 : Nat := 4983230072969 + 3 ^ 40 * 5463607 * 2
def baseEnd_5463607 : Nat := 311717388696612260687315

theorem tailTrace_5463607 : CollatzResearch.WordTrace tailWord_5463607 prefixEnd_5463607 311717388696612260687315 := by
  unfold tailWord_5463607
  simp only [CollatzResearch.WordTrace]
  refine ⟨199274118317292423632045075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132849412211528282421363383 199274118317292423632045075)
  ·
    refine ⟨298911177475938635448067613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199274118317292423632045075 298911177475938635448067613)
    ·
      refine ⟨112091691553476988293025355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 298911177475938635448067613 112091691553476988293025355)
      ·
        refine ⟨168137537330215482439538033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112091691553476988293025355 168137537330215482439538033)
        ·
          refine ⟨126103152997661611829653525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168137537330215482439538033 126103152997661611829653525)
          ·
            refine ⟨5911085296765388054515009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 126103152997661611829653525 5911085296765388054515009)
            ·
              refine ⟨4433313972574041040886257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5911085296765388054515009 4433313972574041040886257)
              ·
                refine ⟨3324985479430530780664693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4433313972574041040886257 3324985479430530780664693)
                ·
                  refine ⟨311717388696612260687315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3324985479430530780664693 311717388696612260687315)
                  ·
                    rfl

theorem cell23_5463607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 2, 5].length) (baseStart_5463607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5463607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5463607 prefixEnd_5463607 := by exact prefixLift 5463607
  have htrace : WordTrace (prefixWord ++ tailWord_5463607) baseStart_5463607 baseEnd_5463607 := by
    simpa [prefixWord, tailWord_5463607, baseEnd_5463607] using wordTrace_append hprefix tailTrace_5463607
  have hstable : (prefixWord ++ tailWord_5463607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5463607).length < 2 ^ (prefixWord ++ tailWord_5463607).sum := by decide
  have hdescent : baseEnd_5463607 < baseStart_5463607 := by decide
  rcases family_descends (prefixWord ++ tailWord_5463607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5463616 : List Nat := [2, 1, 1, 2, 2, 2, 1, 2, 2, 8]
def baseStart_5463616 : Nat := 118140960795 + 5463616 * 2 ^ 59
def prefixEnd_5463616 : Nat := 4983230072969 + 3 ^ 40 * 5463616 * 2
def baseEnd_5463616 : Nat := 935153706531800270324431

theorem tailTrace_5463616 : CollatzResearch.WordTrace tailWord_5463616 prefixEnd_5463616 935153706531800270324431 := by
  unfold tailWord_5463616
  simp only [CollatzResearch.WordTrace]
  refine ⟨99637223287129909084561351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132849631049506545446081801 99637223287129909084561351)
  ·
    refine ⟨149455834930694863626842027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99637223287129909084561351 149455834930694863626842027)
    ·
      refine ⟨224183752396042295440263041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149455834930694863626842027 224183752396042295440263041)
      ·
        refine ⟨168137814297031721580197281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224183752396042295440263041 168137814297031721580197281)
        ·
          refine ⟨126103360722773791185147961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168137814297031721580197281 126103360722773791185147961)
          ·
            refine ⟨94577520542080343388860971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126103360722773791185147961 94577520542080343388860971)
            ·
              refine ⟨141866280813120515083291457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94577520542080343388860971 141866280813120515083291457)
              ·
                refine ⟨106399710609840386312468593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141866280813120515083291457 106399710609840386312468593)
                ·
                  refine ⟨79799782957380289734351445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106399710609840386312468593 79799782957380289734351445)
                  ·
                    refine ⟨935153706531800270324431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 79799782957380289734351445 935153706531800270324431)
                    ·
                      rfl

theorem cell23_5463616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 2, 8].length) (baseStart_5463616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5463616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5463616 prefixEnd_5463616 := by exact prefixLift 5463616
  have htrace : WordTrace (prefixWord ++ tailWord_5463616) baseStart_5463616 baseEnd_5463616 := by
    simpa [prefixWord, tailWord_5463616, baseEnd_5463616] using wordTrace_append hprefix tailTrace_5463616
  have hstable : (prefixWord ++ tailWord_5463616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5463616).length < 2 ^ (prefixWord ++ tailWord_5463616).sum := by decide
  have hdescent : baseEnd_5463616 < baseStart_5463616 := by decide
  rcases family_descends (prefixWord ++ tailWord_5463616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5463653 : List Nat := [1, 3, 1, 3, 3, 1, 1, 1, 2, 1, 6]
def baseStart_5463653 : Nat := 118140960795 + 5463653 * 2 ^ 59
def prefixEnd_5463653 : Nat := 4983230072969 + 3 ^ 40 * 5463653 * 2
def baseEnd_5463653 : Nat := 2805480118379617166210623

theorem tailTrace_5463653 : CollatzResearch.WordTrace tailWord_5463653 prefixEnd_5463653 2805480118379617166210623 := by
  unfold tailWord_5463653
  simp only [CollatzResearch.WordTrace]
  refine ⟨199275796075125773488219613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132850530716750515658813075 199275796075125773488219613)
  ·
    refine ⟨74728423528172165058082355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199275796075125773488219613 74728423528172165058082355)
    ·
      refine ⟨112092635292258247587123533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74728423528172165058082355 112092635292258247587123533)
      ·
        refine ⟨42034738234596842845171325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112092635292258247587123533 42034738234596842845171325)
        ·
          refine ⟨15763026837973816066939247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42034738234596842845171325 15763026837973816066939247)
          ·
            refine ⟨23644540256960724100408871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15763026837973816066939247 23644540256960724100408871)
            ·
              refine ⟨35466810385441086150613307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23644540256960724100408871 35466810385441086150613307)
              ·
                refine ⟨53200215578161629225919961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35466810385441086150613307 53200215578161629225919961)
                ·
                  refine ⟨39900161683621221919439971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53200215578161629225919961 39900161683621221919439971)
                  ·
                    refine ⟨59850242525431832879159957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39900161683621221919439971 59850242525431832879159957)
                    ·
                      refine ⟨2805480118379617166210623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59850242525431832879159957 2805480118379617166210623)
                      ·
                        rfl

theorem cell23_5463653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_5463653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5463653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5463653 prefixEnd_5463653 := by exact prefixLift 5463653
  have htrace : WordTrace (prefixWord ++ tailWord_5463653) baseStart_5463653 baseEnd_5463653 := by
    simpa [prefixWord, tailWord_5463653, baseEnd_5463653] using wordTrace_append hprefix tailTrace_5463653
  have hstable : (prefixWord ++ tailWord_5463653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5463653).length < 2 ^ (prefixWord ++ tailWord_5463653).sum := by decide
  have hdescent : baseEnd_5463653 < baseStart_5463653 := by decide
  rcases family_descends (prefixWord ++ tailWord_5463653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5463680 : List Nat := [2, 1, 1, 2, 1, 4, 5, 1, 6]
def baseStart_5463680 : Nat := 118140960795 + 5463680 * 2 ^ 59
def prefixEnd_5463680 : Nat := 4983230072969 + 3 ^ 40 * 5463680 * 2
def baseEnd_5463680 : Nat := 311721553595254284508111

theorem tailTrace_5463680 : CollatzResearch.WordTrace tailWord_5463680 prefixEnd_5463680 311721553595254284508111 := by
  unfold tailWord_5463680
  simp only [CollatzResearch.WordTrace]
  refine ⟨99638390423013978549726247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132851187230685304732968329 99638390423013978549726247)
  ·
    refine ⟨149457585634520967824589371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99638390423013978549726247 149457585634520967824589371)
    ·
      refine ⟨224186378451781451736884057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149457585634520967824589371 224186378451781451736884057)
      ·
        refine ⟨168139783838836088802663043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224186378451781451736884057 168139783838836088802663043)
        ·
          refine ⟨252209675758254133203994565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168139783838836088802663043 252209675758254133203994565)
          ·
            refine ⟨47289314204672649975748981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 252209675758254133203994565 47289314204672649975748981)
            ·
              refine ⟨4433373206688060935226467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47289314204672649975748981 4433373206688060935226467)
              ·
                refine ⟨6650059810032091402839701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4433373206688060935226467 6650059810032091402839701)
                ·
                  refine ⟨311721553595254284508111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6650059810032091402839701 311721553595254284508111)
                  ·
                    rfl

theorem cell23_5463680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 1, 6].length) (baseStart_5463680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5463680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5463680 prefixEnd_5463680 := by exact prefixLift 5463680
  have htrace : WordTrace (prefixWord ++ tailWord_5463680) baseStart_5463680 baseEnd_5463680 := by
    simpa [prefixWord, tailWord_5463680, baseEnd_5463680] using wordTrace_append hprefix tailTrace_5463680
  have hstable : (prefixWord ++ tailWord_5463680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5463680).length < 2 ^ (prefixWord ++ tailWord_5463680).sum := by decide
  have hdescent : baseEnd_5463680 < baseStart_5463680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5463680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5463743 : List Nat := [1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 6]
def baseStart_5463743 : Nat := 118140960795 + 5463743 * 2 ^ 59
def prefixEnd_5463743 : Nat := 4983230072969 + 3 ^ 40 * 5463743 * 2
def baseEnd_5463743 : Nat := 2805526331638521814085209

theorem tailTrace_5463743 : CollatzResearch.WordTrace tailWord_5463743 prefixEnd_5463743 2805526331638521814085209 := by
  unfold tailWord_5463743
  simp only [CollatzResearch.WordTrace]
  refine ⟨199279078644799718858995883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132852719096533145905997255 199279078644799718858995883)
  ·
    refine ⟨298918617967199578288493825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199279078644799718858995883 298918617967199578288493825)
    ·
      refine ⟨224188963475399683716370369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 298918617967199578288493825 224188963475399683716370369)
      ·
        refine ⟨168141722606549762787277777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224188963475399683716370369 168141722606549762787277777)
        ·
          refine ⟨126106291954912322090458333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168141722606549762787277777 126106291954912322090458333)
          ·
            refine ⟨47289859483092120783921875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126106291954912322090458333 47289859483092120783921875)
            ·
              refine ⟨70934789224638181175882813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47289859483092120783921875 70934789224638181175882813)
              ·
                refine ⟨26600545959239317940956055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70934789224638181175882813 26600545959239317940956055)
                ·
                  refine ⟨39900818938858976911434083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26600545959239317940956055 39900818938858976911434083)
                  ·
                    refine ⟨59851228408288465367151125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39900818938858976911434083 59851228408288465367151125)
                    ·
                      refine ⟨2805526331638521814085209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59851228408288465367151125 2805526331638521814085209)
                      ·
                        rfl

theorem cell23_5463743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 6].length) (baseStart_5463743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5463743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5463743 prefixEnd_5463743 := by exact prefixLift 5463743
  have htrace : WordTrace (prefixWord ++ tailWord_5463743) baseStart_5463743 baseEnd_5463743 := by
    simpa [prefixWord, tailWord_5463743, baseEnd_5463743] using wordTrace_append hprefix tailTrace_5463743
  have hstable : (prefixWord ++ tailWord_5463743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5463743).length < 2 ^ (prefixWord ++ tailWord_5463743).sum := by decide
  have hdescent : baseEnd_5463743 < baseStart_5463743 := by decide
  rcases family_descends (prefixWord ++ tailWord_5463743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5463757 : List Nat := [1, 6, 2, 1, 1, 1, 1, 1, 3, 6]
def baseStart_5463757 : Nat := 118140960795 + 5463757 * 2 ^ 59
def prefixEnd_5463757 : Nat := 4983230072969 + 3 ^ 40 * 5463757 * 2
def baseEnd_5463757 : Nat := 935177840122561586436715

theorem tailTrace_5463757 : CollatzResearch.WordTrace tailWord_5463757 prefixEnd_5463757 935177840122561586436715 := by
  unfold tailWord_5463757
  simp only [CollatzResearch.WordTrace]
  refine ⟨199279589266748999250005525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132853059511165999500003683 199279589266748999250005525)
  ·
    refine ⟨9341230746878859339844009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 199279589266748999250005525 9341230746878859339844009)
    ·
      refine ⟨7005923060159144504883007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9341230746878859339844009 7005923060159144504883007)
      ·
        refine ⟨10508884590238716757324511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7005923060159144504883007 10508884590238716757324511)
        ·
          refine ⟨15763326885358075135986767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10508884590238716757324511 15763326885358075135986767)
          ·
            refine ⟨23644990328037112703980151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15763326885358075135986767 23644990328037112703980151)
            ·
              refine ⟨35467485492055669055970227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23644990328037112703980151 35467485492055669055970227)
              ·
                refine ⟨53201228238083503583955341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35467485492055669055970227 53201228238083503583955341)
                ·
                  refine ⟨19950460589281313843983253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53201228238083503583955341 19950460589281313843983253)
                  ·
                    refine ⟨935177840122561586436715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19950460589281313843983253 935177840122561586436715)
                    ·
                      rfl

theorem cell23_5463757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_5463757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5463757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5463757 prefixEnd_5463757 := by exact prefixLift 5463757
  have htrace : WordTrace (prefixWord ++ tailWord_5463757) baseStart_5463757 baseEnd_5463757 := by
    simpa [prefixWord, tailWord_5463757, baseEnd_5463757] using wordTrace_append hprefix tailTrace_5463757
  have hstable : (prefixWord ++ tailWord_5463757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5463757).length < 2 ^ (prefixWord ++ tailWord_5463757).sum := by decide
  have hdescent : baseEnd_5463757 < baseStart_5463757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5463757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5463780 : List Nat := [2, 3, 1, 1, 1, 3, 1, 2, 3, 3, 3]
def baseStart_5463780 : Nat := 118140960795 + 5463780 * 2 ^ 59
def prefixEnd_5463780 : Nat := 4983230072969 + 3 ^ 40 * 5463780 * 2
def baseEnd_5463780 : Nat := 2805545330422738169322539

theorem tailTrace_5463780 : CollatzResearch.WordTrace tailWord_5463780 prefixEnd_5463780 2805545330422738169322539 := by
  unfold tailWord_5463780
  simp only [CollatzResearch.WordTrace]
  refine ⟨99640214072832837089046397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132853618763777116118728529 99640214072832837089046397)
  ·
    refine ⟨37365080277312313908392399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99640214072832837089046397 37365080277312313908392399)
    ·
      refine ⟨56047620415968470862588599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37365080277312313908392399 56047620415968470862588599)
      ·
        refine ⟨84071430623952706293882899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56047620415968470862588599 84071430623952706293882899)
        ·
          refine ⟨126107145935929059440824349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84071430623952706293882899 126107145935929059440824349)
          ·
            refine ⟨47290179725973397290309131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126107145935929059440824349 47290179725973397290309131)
            ·
              refine ⟨70935269588960095935463697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47290179725973397290309131 70935269588960095935463697)
              ·
                refine ⟨53201452191720071951597773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70935269588960095935463697 53201452191720071951597773)
                ·
                  refine ⟨19950544571895026981849165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53201452191720071951597773 19950544571895026981849165)
                  ·
                    refine ⟨7481454214460635118193437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19950544571895026981849165 7481454214460635118193437)
                    ·
                      refine ⟨2805545330422738169322539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7481454214460635118193437 2805545330422738169322539)
                      ·
                        rfl

theorem cell23_5463780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 3, 3, 3].length) (baseStart_5463780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5463780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5463780 prefixEnd_5463780 := by exact prefixLift 5463780
  have htrace : WordTrace (prefixWord ++ tailWord_5463780) baseStart_5463780 baseEnd_5463780 := by
    simpa [prefixWord, tailWord_5463780, baseEnd_5463780] using wordTrace_append hprefix tailTrace_5463780
  have hstable : (prefixWord ++ tailWord_5463780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5463780).length < 2 ^ (prefixWord ++ tailWord_5463780).sum := by decide
  have hdescent : baseEnd_5463780 < baseStart_5463780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5463780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5463781 : List Nat := [1, 3, 1, 4, 1, 1, 3, 4, 1, 2, 2]
def baseStart_5463781 : Nat := 118140960795 + 5463781 * 2 ^ 59
def prefixEnd_5463781 : Nat := 4983230072969 + 3 ^ 40 * 5463781 * 2
def baseEnd_5463781 : Nat := 2805545843903392665410035

theorem tailTrace_5463781 : CollatzResearch.WordTrace tailWord_5463781 prefixEnd_5463781 2805545843903392665410035 := by
  unfold tailWord_5463781
  simp only [CollatzResearch.WordTrace]
  refine ⟨199280464618662051348879197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132853643079108034232586131 199280464618662051348879197)
  ·
    refine ⟨74730174231998269255829699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199280464618662051348879197 74730174231998269255829699)
    ·
      refine ⟨112095261347997403883744549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74730174231998269255829699 112095261347997403883744549)
      ·
        refine ⟨21017861502749513228202103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112095261347997403883744549 21017861502749513228202103)
        ·
          refine ⟨31526792254124269842303155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21017861502749513228202103 31526792254124269842303155)
          ·
            refine ⟨47290188381186404763454733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31526792254124269842303155 47290188381186404763454733)
            ·
              refine ⟨17733820642944901786295525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47290188381186404763454733 17733820642944901786295525)
              ·
                refine ⟨3325091370552169084930411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17733820642944901786295525 3325091370552169084930411)
                ·
                  refine ⟨4987637055828253627395617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3325091370552169084930411 4987637055828253627395617)
                  ·
                    refine ⟨3740727791871190220546713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4987637055828253627395617 3740727791871190220546713)
                    ·
                      refine ⟨2805545843903392665410035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3740727791871190220546713 2805545843903392665410035)
                      ·
                        rfl

theorem cell23_5463781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_5463781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5463781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5463781 prefixEnd_5463781 := by exact prefixLift 5463781
  have htrace : WordTrace (prefixWord ++ tailWord_5463781) baseStart_5463781 baseEnd_5463781 := by
    simpa [prefixWord, tailWord_5463781, baseEnd_5463781] using wordTrace_append hprefix tailTrace_5463781
  have hstable : (prefixWord ++ tailWord_5463781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5463781).length < 2 ^ (prefixWord ++ tailWord_5463781).sum := by decide
  have hdescent : baseEnd_5463781 < baseStart_5463781 := by decide
  rcases family_descends (prefixWord ++ tailWord_5463781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5463807 : List Nat := [1, 1, 2, 2, 1, 3, 4, 1, 3, 3, 2]
def baseStart_5463807 : Nat := 118140960795 + 5463807 * 2 ^ 59
def prefixEnd_5463807 : Nat := 4983230072969 + 3 ^ 40 * 5463807 * 2
def baseEnd_5463807 : Nat := 2805559194400409563684915

theorem tailTrace_5463807 : CollatzResearch.WordTrace tailWord_5463807 prefixEnd_5463807 2805559194400409563684915 := by
  unfold tailWord_5463807
  simp only [CollatzResearch.WordTrace]
  refine ⟨199281412916567857789325675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132854275277711905192883783 199281412916567857789325675)
  ·
    refine ⟨298922119374851786683988513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199281412916567857789325675 298922119374851786683988513)
    ·
      refine ⟨224191589531138840012991385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 298922119374851786683988513 224191589531138840012991385)
      ·
        refine ⟨168143692148354130009743539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224191589531138840012991385 168143692148354130009743539)
        ·
          refine ⟨252215538222531195014615309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168143692148354130009743539 252215538222531195014615309)
          ·
            refine ⟨94580826833449198130480741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 252215538222531195014615309 94580826833449198130480741)
            ·
              refine ⟨17733905031271724649465139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94580826833449198130480741 17733905031271724649465139)
              ·
                refine ⟨26600857546907586974197709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17733905031271724649465139 26600857546907586974197709)
                ·
                  refine ⟨9975321580090345115324141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26600857546907586974197709 9975321580090345115324141)
                  ·
                    refine ⟨3740745592533879418246553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9975321580090345115324141 3740745592533879418246553)
                    ·
                      refine ⟨2805559194400409563684915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3740745592533879418246553 2805559194400409563684915)
                      ·
                        rfl

theorem cell23_5463807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 3, 3, 2].length) (baseStart_5463807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5463807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5463807 prefixEnd_5463807 := by exact prefixLift 5463807
  have htrace : WordTrace (prefixWord ++ tailWord_5463807) baseStart_5463807 baseEnd_5463807 := by
    simpa [prefixWord, tailWord_5463807, baseEnd_5463807] using wordTrace_append hprefix tailTrace_5463807
  have hstable : (prefixWord ++ tailWord_5463807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5463807).length < 2 ^ (prefixWord ++ tailWord_5463807).sum := by decide
  have hdescent : baseEnd_5463807 < baseStart_5463807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5463807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5463821 : List Nat := [1, 7, 2, 1, 1, 1, 10]
def baseStart_5463821 : Nat := 118140960795 + 5463821 * 2 ^ 59
def prefixEnd_5463821 : Nat := 4983230072969 + 3 ^ 40 * 5463821 * 2
def baseEnd_5463821 : Nat := 34636622013945339616171

theorem tailTrace_5463821 : CollatzResearch.WordTrace tailWord_5463821 prefixEnd_5463821 34636622013945339616171 := by
  unfold tailWord_5463821
  simp only [CollatzResearch.WordTrace]
  refine ⟨199281923538517138180335317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132854615692344758786890211 199281923538517138180335317)
  ·
    refine ⟨4670670082933995426101609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 199281923538517138180335317 4670670082933995426101609)
    ·
      refine ⟨3503002562200496569576207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4670670082933995426101609 3503002562200496569576207)
      ·
        refine ⟨5254503843300744854364311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3503002562200496569576207 5254503843300744854364311)
        ·
          refine ⟨7881755764951117281546467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5254503843300744854364311 7881755764951117281546467)
          ·
            refine ⟨11822633647426675922319701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7881755764951117281546467 11822633647426675922319701)
            ·
              refine ⟨34636622013945339616171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11822633647426675922319701 34636622013945339616171)
              ·
                rfl

theorem cell23_5463821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 10].length) (baseStart_5463821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5463821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5463821 prefixEnd_5463821 := by exact prefixLift 5463821
  have htrace : WordTrace (prefixWord ++ tailWord_5463821) baseStart_5463821 baseEnd_5463821 := by
    simpa [prefixWord, tailWord_5463821, baseEnd_5463821] using wordTrace_append hprefix tailTrace_5463821
  have hstable : (prefixWord ++ tailWord_5463821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5463821).length < 2 ^ (prefixWord ++ tailWord_5463821).sum := by decide
  have hdescent : baseEnd_5463821 < baseStart_5463821 := by decide
  rcases family_descends (prefixWord ++ tailWord_5463821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5463831 : List Nat := [1, 1, 3, 4, 2, 3, 1, 2, 2, 1, 3]
def baseStart_5463831 : Nat := 118140960795 + 5463831 * 2 ^ 59
def prefixEnd_5463831 : Nat := 4983230072969 + 3 ^ 40 * 5463831 * 2
def baseEnd_5463831 : Nat := 2805571517936117469784805

theorem tailTrace_5463831 : CollatzResearch.WordTrace tailWord_5463831 prefixEnd_5463831 2805571517936117469784805 := by
  unfold tailWord_5463831
  simp only [CollatzResearch.WordTrace]
  refine ⟨199282288268480909888199347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132854858845653939925466231 199282288268480909888199347)
  ·
    refine ⟨298923432402721364832299021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199282288268480909888199347 298923432402721364832299021)
    ·
      refine ⟨112096287151020511812112133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 298923432402721364832299021 112096287151020511812112133)
      ·
        refine ⟨21018053840816345964771025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112096287151020511812112133 21018053840816345964771025)
        ·
          refine ⟨15763540380612259473578269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21018053840816345964771025 15763540380612259473578269)
          ·
            refine ⟨5911327642729597302591851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15763540380612259473578269 5911327642729597302591851)
            ·
              refine ⟨8866991464094395953887777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5911327642729597302591851 8866991464094395953887777)
              ·
                refine ⟨6650243598070796965415833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8866991464094395953887777 6650243598070796965415833)
                ·
                  refine ⟨4987682698553097724061875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6650243598070796965415833 4987682698553097724061875)
                  ·
                    refine ⟨7481524047829646586092813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4987682698553097724061875 7481524047829646586092813)
                    ·
                      refine ⟨2805571517936117469784805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7481524047829646586092813 2805571517936117469784805)
                      ·
                        rfl

theorem cell23_5463831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_5463831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5463831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5463831 prefixEnd_5463831 := by exact prefixLift 5463831
  have htrace : WordTrace (prefixWord ++ tailWord_5463831) baseStart_5463831 baseEnd_5463831 := by
    simpa [prefixWord, tailWord_5463831, baseEnd_5463831] using wordTrace_append hprefix tailTrace_5463831
  have hstable : (prefixWord ++ tailWord_5463831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5463831).length < 2 ^ (prefixWord ++ tailWord_5463831).sum := by decide
  have hdescent : baseEnd_5463831 < baseStart_5463831 := by decide
  rcases family_descends (prefixWord ++ tailWord_5463831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5463897 : List Nat := [1, 2, 1, 2, 2, 3, 2, 1, 2, 5, 2]
def baseStart_5463897 : Nat := 118140960795 + 5463897 * 2 ^ 59
def prefixEnd_5463897 : Nat := 4983230072969 + 3 ^ 40 * 5463897 * 2
def baseEnd_5463897 : Nat := 2805605407659314211559501

theorem tailTrace_5463897 : CollatzResearch.WordTrace tailWord_5463897 prefixEnd_5463897 2805605407659314211559501 := by
  unfold tailWord_5463897
  simp only [CollatzResearch.WordTrace]
  refine ⟨199284695486241803160101945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132856463657494535440067963 199284695486241803160101945)
  ·
    refine ⟨149463521614681352370076459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199284695486241803160101945 149463521614681352370076459)
    ·
      refine ⟨224195282422022028555114689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149463521614681352370076459 224195282422022028555114689)
      ·
        refine ⟨168146461816516521416336017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224195282422022028555114689 168146461816516521416336017)
        ·
          refine ⟨126109846362387391062252013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168146461816516521416336017 126109846362387391062252013)
          ·
            refine ⟨47291192385895271648344505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126109846362387391062252013 47291192385895271648344505)
            ·
              refine ⟨35468394289421453736258379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47291192385895271648344505 35468394289421453736258379)
              ·
                refine ⟨53202591434132180604387569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35468394289421453736258379 53202591434132180604387569)
                ·
                  refine ⟨39901943575599135453290677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53202591434132180604387569 39901943575599135453290677)
                  ·
                    refine ⟨3740807210212418948746001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39901943575599135453290677 3740807210212418948746001)
                    ·
                      refine ⟨2805605407659314211559501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3740807210212418948746001 2805605407659314211559501)
                      ·
                        rfl

theorem cell23_5463897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 5, 2].length) (baseStart_5463897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5463897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5463897 prefixEnd_5463897 := by exact prefixLift 5463897
  have htrace : WordTrace (prefixWord ++ tailWord_5463897) baseStart_5463897 baseEnd_5463897 := by
    simpa [prefixWord, tailWord_5463897, baseEnd_5463897] using wordTrace_append hprefix tailTrace_5463897
  have hstable : (prefixWord ++ tailWord_5463897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5463897).length < 2 ^ (prefixWord ++ tailWord_5463897).sum := by decide
  have hdescent : baseEnd_5463897 < baseStart_5463897 := by decide
  rcases family_descends (prefixWord ++ tailWord_5463897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5463927 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 6, 4, 2]
def baseStart_5463927 : Nat := 118140960795 + 5463927 * 2 ^ 59
def prefixEnd_5463927 : Nat := 4983230072969 + 3 ^ 40 * 5463927 * 2
def baseEnd_5463927 : Nat := 2805620812078949094184363

theorem tailTrace_5463927 : CollatzResearch.WordTrace tailWord_5463927 prefixEnd_5463927 2805620812078949094184363 := by
  unfold tailWord_5463927
  simp only [CollatzResearch.WordTrace]
  refine ⟨199285789676133118283694035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132857193117422078855796023 199285789676133118283694035)
  ·
    refine ⟨298928684514199677425541053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199285789676133118283694035 298928684514199677425541053)
    ·
      refine ⟨112098256692824879034577895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 298928684514199677425541053 112098256692824879034577895)
      ·
        refine ⟨168147385039237318551866843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112098256692824879034577895 168147385039237318551866843)
        ·
          refine ⟨252221077558855977827800265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168147385039237318551866843 252221077558855977827800265)
          ·
            refine ⟨189165808169141983370850199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 252221077558855977827800265 189165808169141983370850199)
            ·
              refine ⟨283748712253712975056275299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189165808169141983370850199 283748712253712975056275299)
              ·
                refine ⟨425623068380569462584412949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 283748712253712975056275299 425623068380569462584412949)
                ·
                  refine ⟨19951081330339193558644357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 425623068380569462584412949 19951081330339193558644357)
                  ·
                    refine ⟨3740827749438598792245817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19951081330339193558644357 3740827749438598792245817)
                    ·
                      refine ⟨2805620812078949094184363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3740827749438598792245817 2805620812078949094184363)
                      ·
                        rfl

theorem cell23_5463927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 4, 2].length) (baseStart_5463927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5463927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5463927 prefixEnd_5463927 := by exact prefixLift 5463927
  have htrace : WordTrace (prefixWord ++ tailWord_5463927) baseStart_5463927 baseEnd_5463927 := by
    simpa [prefixWord, tailWord_5463927, baseEnd_5463927] using wordTrace_append hprefix tailTrace_5463927
  have hstable : (prefixWord ++ tailWord_5463927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5463927).length < 2 ^ (prefixWord ++ tailWord_5463927).sum := by decide
  have hdescent : baseEnd_5463927 < baseStart_5463927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5463927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5463934 : List Nat := [4, 2, 3, 1, 1, 1, 1, 2, 1, 2, 5]
def baseStart_5463934 : Nat := 118140960795 + 5463934 * 2 ^ 59
def prefixEnd_5463934 : Nat := 4983230072969 + 3 ^ 40 * 5463934 * 2
def baseEnd_5463934 : Nat := 2805624406443530566796831

theorem tailTrace_5463934 : CollatzResearch.WordTrace tailWord_5463934 prefixEnd_5463934 2805624406443530566796831 := by
  unfold tailWord_5463934
  simp only [CollatzResearch.WordTrace]
  refine ⟨24910755623388469809899857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132857363324738505652799237 24910755623388469809899857)
  ·
    refine ⟨18683066717541352357424893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24910755623388469809899857 18683066717541352357424893)
    ·
      refine ⟨7006150019078007134034335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18683066717541352357424893 7006150019078007134034335)
      ·
        refine ⟨10509225028617010701051503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7006150019078007134034335 10509225028617010701051503)
        ·
          refine ⟨15763837542925516051577255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10509225028617010701051503 15763837542925516051577255)
          ·
            refine ⟨23645756314388274077365883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15763837542925516051577255 23645756314388274077365883)
            ·
              refine ⟨35468634471582411116048825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23645756314388274077365883 35468634471582411116048825)
              ·
                refine ⟨26601475853686808337036619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35468634471582411116048825 26601475853686808337036619)
                ·
                  refine ⟨39902213780530212505554929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26601475853686808337036619 39902213780530212505554929)
                  ·
                    refine ⟨29926660335397659379166197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39902213780530212505554929 29926660335397659379166197)
                    ·
                      refine ⟨2805624406443530566796831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29926660335397659379166197 2805624406443530566796831)
                      ·
                        rfl

theorem cell23_5463934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_5463934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5463934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5463934 prefixEnd_5463934 := by exact prefixLift 5463934
  have htrace : WordTrace (prefixWord ++ tailWord_5463934) baseStart_5463934 baseEnd_5463934 := by
    simpa [prefixWord, tailWord_5463934, baseEnd_5463934] using wordTrace_append hprefix tailTrace_5463934
  have hstable : (prefixWord ++ tailWord_5463934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5463934).length < 2 ^ (prefixWord ++ tailWord_5463934).sum := by decide
  have hdescent : baseEnd_5463934 < baseStart_5463934 := by decide
  rcases family_descends (prefixWord ++ tailWord_5463934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5464011 : List Nat := [1, 1, 1, 1, 3, 4, 1, 6, 1, 1, 3]
def baseStart_5464011 : Nat := 118140960795 + 5464011 * 2 ^ 59
def prefixEnd_5464011 : Nat := 4983230072969 + 3 ^ 40 * 5464011 * 2
def baseEnd_5464011 : Nat := 2805663944453926765533977

theorem tailTrace_5464011 : CollatzResearch.WordTrace tailWord_5464011 prefixEnd_5464011 2805663944453926765533977 := by
  unfold tailWord_5464011
  simp only [CollatzResearch.WordTrace]
  refine ⟨199288853407828800629751887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132859235605219200419834591 199288853407828800629751887)
  ·
    refine ⟨298933280111743200944627831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199288853407828800629751887 298933280111743200944627831)
    ·
      refine ⟨448399920167614801416941747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298933280111743200944627831 448399920167614801416941747)
      ·
        refine ⟨672599880251422202125412621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 448399920167614801416941747 672599880251422202125412621)
        ·
          refine ⟨252224955094283325797029733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 672599880251422202125412621 252224955094283325797029733)
          ·
            refine ⟨47292179080178123586943075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 252224955094283325797029733 47292179080178123586943075)
            ·
              refine ⟨70938268620267185380414613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47292179080178123586943075 70938268620267185380414613)
              ·
                refine ⟨3325231341575024314706935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 70938268620267185380414613 3325231341575024314706935)
                ·
                  refine ⟨4987847012362536472060403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3325231341575024314706935 4987847012362536472060403)
                  ·
                    refine ⟨7481770518543804708090605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4987847012362536472060403 7481770518543804708090605)
                    ·
                      refine ⟨2805663944453926765533977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7481770518543804708090605 2805663944453926765533977)
                      ·
                        rfl

theorem cell23_5464011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 6, 1, 1, 3].length) (baseStart_5464011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5464011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5464011 prefixEnd_5464011 := by exact prefixLift 5464011
  have htrace : WordTrace (prefixWord ++ tailWord_5464011) baseStart_5464011 baseEnd_5464011 := by
    simpa [prefixWord, tailWord_5464011, baseEnd_5464011] using wordTrace_append hprefix tailTrace_5464011
  have hstable : (prefixWord ++ tailWord_5464011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5464011).length < 2 ^ (prefixWord ++ tailWord_5464011).sum := by decide
  have hdescent : baseEnd_5464011 < baseStart_5464011 := by decide
  rcases family_descends (prefixWord ++ tailWord_5464011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5464017 : List Nat := [1, 2, 2, 1, 2, 1, 2, 4, 3, 1, 4]
def baseStart_5464017 : Nat := 118140960795 + 5464017 * 2 ^ 59
def prefixEnd_5464017 : Nat := 4983230072969 + 3 ^ 40 * 5464017 * 2
def baseEnd_5464017 : Nat := 2805667025337853742058949

theorem tailTrace_5464017 : CollatzResearch.WordTrace tailWord_5464017 prefixEnd_5464017 2805667025337853742058949 := by
  unfold tailWord_5464017
  simp only [CollatzResearch.WordTrace]
  refine ⟨199289072245807063654470305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132859381497204709102980203 199289072245807063654470305)
  ·
    refine ⟨149466804184355297740852729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199289072245807063654470305 149466804184355297740852729)
    ·
      refine ⟨112100103138266473305639547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149466804184355297740852729 112100103138266473305639547)
      ·
        refine ⟨168150154707399709958459321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112100103138266473305639547 168150154707399709958459321)
        ·
          refine ⟨126112616030549782468844491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168150154707399709958459321 126112616030549782468844491)
          ·
            refine ⟨189168924045824673703266737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126112616030549782468844491 189168924045824673703266737)
            ·
              refine ⟨141876693034368505277450053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189168924045824673703266737 141876693034368505277450053)
              ·
                refine ⟨26601879943944094739521885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 141876693034368505277450053 26601879943944094739521885)
                ·
                  refine ⟨9975704978979035527320707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26601879943944094739521885 9975704978979035527320707)
                  ·
                    refine ⟨14963557468468553290981061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9975704978979035527320707 14963557468468553290981061)
                    ·
                      refine ⟨2805667025337853742058949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14963557468468553290981061 2805667025337853742058949)
                      ·
                        rfl

theorem cell23_5464017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 3, 1, 4].length) (baseStart_5464017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5464017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5464017 prefixEnd_5464017 := by exact prefixLift 5464017
  have htrace : WordTrace (prefixWord ++ tailWord_5464017) baseStart_5464017 baseEnd_5464017 := by
    simpa [prefixWord, tailWord_5464017, baseEnd_5464017] using wordTrace_append hprefix tailTrace_5464017
  have hstable : (prefixWord ++ tailWord_5464017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5464017).length < 2 ^ (prefixWord ++ tailWord_5464017).sum := by decide
  have hdescent : baseEnd_5464017 < baseStart_5464017 := by decide
  rcases family_descends (prefixWord ++ tailWord_5464017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5464047 : List Nat := [1, 1, 2, 1, 4, 2, 2, 1, 3, 2, 4]
def baseStart_5464047 : Nat := 118140960795 + 5464047 * 2 ^ 59
def prefixEnd_5464047 : Nat := 4983230072969 + 3 ^ 40 * 5464047 * 2
def baseEnd_5464047 : Nat := 2805682429757488624683811

theorem tailTrace_5464047 : CollatzResearch.WordTrace tailWord_5464047 prefixEnd_5464047 2805682429757488624683811 := by
  unfold tailWord_5464047
  simp only [CollatzResearch.WordTrace]
  refine ⟨199290166435698378778062395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132860110957132252518708263 199290166435698378778062395)
  ·
    refine ⟨298935249653547568167093593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199290166435698378778062395 298935249653547568167093593)
    ·
      refine ⟨224201437240160676125320195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 298935249653547568167093593 224201437240160676125320195)
      ·
        refine ⟨336302155860241014187980293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224201437240160676125320195 336302155860241014187980293)
        ·
          refine ⟨63056654223795190160246305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 336302155860241014187980293 63056654223795190160246305)
          ·
            refine ⟨47292490667846392620184729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63056654223795190160246305 47292490667846392620184729)
            ·
              refine ⟨35469368000884794465138547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47292490667846392620184729 35469368000884794465138547)
              ·
                refine ⟨53204052001327191697707821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35469368000884794465138547 53204052001327191697707821)
                ·
                  refine ⟨19951519500497696886640433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53204052001327191697707821 19951519500497696886640433)
                  ·
                    refine ⟨14963639625373272664980325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19951519500497696886640433 14963639625373272664980325)
                    ·
                      refine ⟨2805682429757488624683811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14963639625373272664980325 2805682429757488624683811)
                      ·
                        rfl

theorem cell23_5464047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 2, 4].length) (baseStart_5464047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5464047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5464047 prefixEnd_5464047 := by exact prefixLift 5464047
  have htrace : WordTrace (prefixWord ++ tailWord_5464047) baseStart_5464047 baseEnd_5464047 := by
    simpa [prefixWord, tailWord_5464047, baseEnd_5464047] using wordTrace_append hprefix tailTrace_5464047
  have hstable : (prefixWord ++ tailWord_5464047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5464047).length < 2 ^ (prefixWord ++ tailWord_5464047).sum := by decide
  have hdescent : baseEnd_5464047 < baseStart_5464047 := by decide
  rcases family_descends (prefixWord ++ tailWord_5464047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5464057 : List Nat := [1, 2, 1, 3, 1, 6, 9]
def baseStart_5464057 : Nat := 118140960795 + 5464057 * 2 ^ 59
def prefixEnd_5464057 : Nat := 4983230072969 + 3 ^ 40 * 5464057 * 2
def baseEnd_5464057 : Nat := 34638118081037451673565

theorem tailTrace_5464057 : CollatzResearch.WordTrace tailWord_5464057 prefixEnd_5464057 34638118081037451673565 := by
  unfold tailWord_5464057
  simp only [CollatzResearch.WordTrace]
  refine ⟨199290531165662150485926425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132860354110441433657284283 199290531165662150485926425)
  ·
    refine ⟨149467898374246612864444819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199290531165662150485926425 149467898374246612864444819)
    ·
      refine ⟨224201847561369919296667229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149467898374246612864444819 224201847561369919296667229)
      ·
        refine ⟨84075692835513719736250211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 224201847561369919296667229 84075692835513719736250211)
        ·
          refine ⟨126113539253270579604375317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84075692835513719736250211 126113539253270579604375317)
          ·
            refine ⟨5911572152497058418955093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 126113539253270579604375317 5911572152497058418955093)
            ·
              refine ⟨34638118081037451673565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5911572152497058418955093 34638118081037451673565)
              ·
                rfl

theorem cell23_5464057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 9].length) (baseStart_5464057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5464057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5464057 prefixEnd_5464057 := by exact prefixLift 5464057
  have htrace : WordTrace (prefixWord ++ tailWord_5464057) baseStart_5464057 baseEnd_5464057 := by
    simpa [prefixWord, tailWord_5464057, baseEnd_5464057] using wordTrace_append hprefix tailTrace_5464057
  have hstable : (prefixWord ++ tailWord_5464057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5464057).length < 2 ^ (prefixWord ++ tailWord_5464057).sum := by decide
  have hdescent : baseEnd_5464057 < baseStart_5464057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5464057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5464062 : List Nat := [4, 2, 2, 2, 1, 2, 3, 2, 1, 1, 3]
def baseStart_5464062 : Nat := 118140960795 + 5464062 * 2 ^ 59
def prefixEnd_5464062 : Nat := 4983230072969 + 3 ^ 40 * 5464062 * 2
def baseEnd_5464062 : Nat := 2805690131967306065996243

theorem tailTrace_5464062 : CollatzResearch.WordTrace tailWord_5464062 prefixEnd_5464062 2805690131967306065996243 := by
  unfold tailWord_5464062
  simp only [CollatzResearch.WordTrace]
  refine ⟨24911339191330504542482305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132860475687096024226572293 24911339191330504542482305)
  ·
    refine ⟨18683504393497878406861729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24911339191330504542482305 18683504393497878406861729)
    ·
      refine ⟨14012628295123408805146297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18683504393497878406861729 14012628295123408805146297)
      ·
        refine ⟨10509471221342556603859723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14012628295123408805146297 10509471221342556603859723)
        ·
          refine ⟨15764206832013834905789585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10509471221342556603859723 15764206832013834905789585)
          ·
            refine ⟨11823155124010376179342189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15764206832013834905789585 11823155124010376179342189)
            ·
              refine ⟨4433683171503891067253321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11823155124010376179342189 4433683171503891067253321)
              ·
                refine ⟨3325262378627918300439991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4433683171503891067253321 3325262378627918300439991)
                ·
                  refine ⟨4987893567941877450659987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3325262378627918300439991 4987893567941877450659987)
                  ·
                    refine ⟨7481840351912816175989981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4987893567941877450659987 7481840351912816175989981)
                    ·
                      refine ⟨2805690131967306065996243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7481840351912816175989981 2805690131967306065996243)
                      ·
                        rfl

theorem cell23_5464062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_5464062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5464062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5464062 prefixEnd_5464062 := by exact prefixLift 5464062
  have htrace : WordTrace (prefixWord ++ tailWord_5464062) baseStart_5464062 baseEnd_5464062 := by
    simpa [prefixWord, tailWord_5464062, baseEnd_5464062] using wordTrace_append hprefix tailTrace_5464062
  have hstable : (prefixWord ++ tailWord_5464062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5464062).length < 2 ^ (prefixWord ++ tailWord_5464062).sum := by decide
  have hdescent : baseEnd_5464062 < baseStart_5464062 := by decide
  rcases family_descends (prefixWord ++ tailWord_5464062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5464074 : List Nat := [3, 1, 2, 2, 4, 1, 2, 8]
def baseStart_5464074 : Nat := 118140960795 + 5464074 * 2 ^ 59
def prefixEnd_5464074 : Nat := 4983230072969 + 3 ^ 40 * 5464074 * 2
def baseEnd_5464074 : Nat := 103914677545746667372081

theorem tailTrace_5464074 : CollatzResearch.WordTrace tailWord_5464074 prefixEnd_5464074 103914677545746667372081 := by
  unfold tailWord_5464074
  simp only [CollatzResearch.WordTrace]
  refine ⟨49822787801650140597323819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132860767471067041592863517 49822787801650140597323819)
  ·
    refine ⟨74734181702475210895985729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49822787801650140597323819 74734181702475210895985729)
    ·
      refine ⟨56050636276856408171989297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74734181702475210895985729 56050636276856408171989297)
      ·
        refine ⟨42037977207642306128991973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56050636276856408171989297 42037977207642306128991973)
        ·
          refine ⟨7882120726432932399185995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42037977207642306128991973 7882120726432932399185995)
          ·
            refine ⟨11823181089649398598778993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7882120726432932399185995 11823181089649398598778993)
            ·
              refine ⟨8867385817237048949084245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11823181089649398598778993 8867385817237048949084245)
              ·
                refine ⟨103914677545746667372081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8867385817237048949084245 103914677545746667372081)
                ·
                  rfl

theorem cell23_5464074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 8].length) (baseStart_5464074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5464074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5464074 prefixEnd_5464074 := by exact prefixLift 5464074
  have htrace : WordTrace (prefixWord ++ tailWord_5464074) baseStart_5464074 baseEnd_5464074 := by
    simpa [prefixWord, tailWord_5464074, baseEnd_5464074] using wordTrace_append hprefix tailTrace_5464074
  have hstable : (prefixWord ++ tailWord_5464074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5464074).length < 2 ^ (prefixWord ++ tailWord_5464074).sum := by decide
  have hdescent : baseEnd_5464074 < baseStart_5464074 := by decide
  rcases family_descends (prefixWord ++ tailWord_5464074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5464127 : List Nat := [1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 5]
def baseStart_5464127 : Nat := 118140960795 + 5464127 * 2 ^ 59
def prefixEnd_5464127 : Nat := 4983230072969 + 3 ^ 40 * 5464127 * 2
def baseEnd_5464127 : Nat := 2805723508209848311683443

theorem tailTrace_5464127 : CollatzResearch.WordTrace tailWord_5464127 prefixEnd_5464127 2805723508209848311683443 := by
  unfold tailWord_5464127
  simp only [CollatzResearch.WordTrace]
  refine ⟨199293084275408552440974635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132862056183605701627316423 199293084275408552440974635)
  ·
    refine ⟨298939626413112828661461953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199293084275408552440974635 298939626413112828661461953)
    ·
      refine ⟨224204719809834621496096465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 298939626413112828661461953 224204719809834621496096465)
      ·
        refine ⟨168153539857375966122072349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224204719809834621496096465 168153539857375966122072349)
        ·
          refine ⟨63057577446515987295777131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168153539857375966122072349 63057577446515987295777131)
          ·
            refine ⟨94586366169773980943665697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63057577446515987295777131 94586366169773980943665697)
            ·
              refine ⟨70939774627330485707749273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94586366169773980943665697 70939774627330485707749273)
              ·
                refine ⟨53204830970497864280811955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70939774627330485707749273 53204830970497864280811955)
                ·
                  refine ⟨79807246455746796421217933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53204830970497864280811955 79807246455746796421217933)
                  ·
                    refine ⟨29927717420905048657956725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 79807246455746796421217933 29927717420905048657956725)
                    ·
                      refine ⟨2805723508209848311683443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29927717420905048657956725 2805723508209848311683443)
                      ·
                        rfl

theorem cell23_5464127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 5].length) (baseStart_5464127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5464127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5464127 prefixEnd_5464127 := by exact prefixLift 5464127
  have htrace : WordTrace (prefixWord ++ tailWord_5464127) baseStart_5464127 baseEnd_5464127 := by
    simpa [prefixWord, tailWord_5464127, baseEnd_5464127] using wordTrace_append hprefix tailTrace_5464127
  have hstable : (prefixWord ++ tailWord_5464127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5464127).length < 2 ^ (prefixWord ++ tailWord_5464127).sum := by decide
  have hdescent : baseEnd_5464127 < baseStart_5464127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5464127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5464175 : List Nat := [1, 1, 2, 1, 3, 6, 1, 2, 2, 2, 2]
def baseStart_5464175 : Nat := 118140960795 + 5464175 * 2 ^ 59
def prefixEnd_5464175 : Nat := 4983230072969 + 3 ^ 40 * 5464175 * 2
def baseEnd_5464175 : Nat := 2805748155281264123883223

theorem tailTrace_5464175 : CollatzResearch.WordTrace tailWord_5464175 prefixEnd_5464175 2805748155281264123883223 := by
  unfold tailWord_5464175
  simp only [CollatzResearch.WordTrace]
  refine ⟨199294834979234656638721979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132863223319489771092481319 199294834979234656638721979)
  ·
    refine ⟨298942252468851984958082969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199294834979234656638721979 298942252468851984958082969)
    ·
      refine ⟨224206689351638988718562227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 298942252468851984958082969 224206689351638988718562227)
      ·
        refine ⟨336310034027458483077843341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224206689351638988718562227 336310034027458483077843341)
        ·
          refine ⟨126116262760296931154191253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 336310034027458483077843341 126116262760296931154191253)
          ·
            refine ⟨5911699816888918647852715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 126116262760296931154191253 5911699816888918647852715)
            ·
              refine ⟨8867549725333377971779073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5911699816888918647852715 8867549725333377971779073)
              ·
                refine ⟨6650662294000033478834305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8867549725333377971779073 6650662294000033478834305)
                ·
                  refine ⟨4987996720500025109125729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6650662294000033478834305 4987996720500025109125729)
                  ·
                    refine ⟨3740997540375018831844297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4987996720500025109125729 3740997540375018831844297)
                    ·
                      refine ⟨2805748155281264123883223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3740997540375018831844297 2805748155281264123883223)
                      ·
                        rfl

theorem cell23_5464175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 2, 2, 2, 2].length) (baseStart_5464175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5464175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5464175 prefixEnd_5464175 := by exact prefixLift 5464175
  have htrace : WordTrace (prefixWord ++ tailWord_5464175) baseStart_5464175 baseEnd_5464175 := by
    simpa [prefixWord, tailWord_5464175, baseEnd_5464175] using wordTrace_append hprefix tailTrace_5464175
  have hstable : (prefixWord ++ tailWord_5464175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5464175).length < 2 ^ (prefixWord ++ tailWord_5464175).sum := by decide
  have hdescent : baseEnd_5464175 < baseStart_5464175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5464175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5464215 : List Nat := [1, 1, 3, 3, 5, 1, 1, 3, 5]
def baseStart_5464215 : Nat := 118140960795 + 5464215 * 2 ^ 59
def prefixEnd_5464215 : Nat := 4983230072969 + 3 ^ 40 * 5464215 * 2
def baseEnd_5464215 : Nat := 311752077167493774153671

theorem tailTrace_5464215 : CollatzResearch.WordTrace tailWord_5464215 prefixEnd_5464215 311752077167493774153671 := by
  unfold tailWord_5464215
  simp only [CollatzResearch.WordTrace]
  refine ⟨199296293899089743470178099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132864195932726495646785399 199296293899089743470178099)
  ·
    refine ⟨298944440848634615205267149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199296293899089743470178099 298944440848634615205267149)
    ·
      refine ⟨112104165318237980701975181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 298944440848634615205267149 112104165318237980701975181)
      ·
        refine ⟨42039061994339242763240693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112104165318237980701975181 42039061994339242763240693)
        ·
          refine ⟨3941162061969304009053815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42039061994339242763240693 3941162061969304009053815)
          ·
            refine ⟨5911743092953956013580723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3941162061969304009053815 5911743092953956013580723)
            ·
              refine ⟨8867614639430934020371085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5911743092953956013580723 8867614639430934020371085)
              ·
                refine ⟨3325355489786600257639157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8867614639430934020371085 3325355489786600257639157)
                ·
                  refine ⟨311752077167493774153671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3325355489786600257639157 311752077167493774153671)
                  ·
                    rfl

theorem cell23_5464215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 3, 5].length) (baseStart_5464215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5464215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5464215 prefixEnd_5464215 := by exact prefixLift 5464215
  have htrace : WordTrace (prefixWord ++ tailWord_5464215) baseStart_5464215 baseEnd_5464215 := by
    simpa [prefixWord, tailWord_5464215, baseEnd_5464215] using wordTrace_append hprefix tailTrace_5464215
  have hstable : (prefixWord ++ tailWord_5464215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5464215).length < 2 ^ (prefixWord ++ tailWord_5464215).sum := by decide
  have hdescent : baseEnd_5464215 < baseStart_5464215 := by decide
  rcases family_descends (prefixWord ++ tailWord_5464215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5464298 : List Nat := [3, 1, 3, 1, 1, 2, 2, 3, 3, 1, 3]
def baseStart_5464298 : Nat := 118140960795 + 5464298 * 2 ^ 59
def prefixEnd_5464298 : Nat := 4983230072969 + 3 ^ 40 * 5464298 * 2
def baseEnd_5464298 : Nat := 2805811313401767142645157

theorem tailTrace_5464298 : CollatzResearch.WordTrace tailWord_5464298 prefixEnd_5464298 2805811313401767142645157 := by
  unfold tailWord_5464298
  simp only [CollatzResearch.WordTrace]
  refine ⟨49824830289447262161362387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132866214105192699096966365 49824830289447262161362387)
  ·
    refine ⟨74737245434170893242043581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49824830289447262161362387 74737245434170893242043581)
    ·
      refine ⟨28026467037814084965766343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74737245434170893242043581 28026467037814084965766343)
      ·
        refine ⟨42039700556721127448649515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28026467037814084965766343 42039700556721127448649515)
        ·
          refine ⟨63059550835081691172974273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42039700556721127448649515 63059550835081691172974273)
          ·
            refine ⟨47294663126311268379730705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63059550835081691172974273 47294663126311268379730705)
            ·
              refine ⟨35470997344733451284798029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47294663126311268379730705 35470997344733451284798029)
              ·
                refine ⟨13301624004275044231799261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35470997344733451284798029 13301624004275044231799261)
                ·
                  refine ⟨4988109001603141586924723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13301624004275044231799261 4988109001603141586924723)
                  ·
                    refine ⟨7482163502404712380387085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4988109001603141586924723 7482163502404712380387085)
                    ·
                      refine ⟨2805811313401767142645157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7482163502404712380387085 2805811313401767142645157)
                      ·
                        rfl

theorem cell23_5464298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_5464298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5464298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5464298 prefixEnd_5464298 := by exact prefixLift 5464298
  have htrace : WordTrace (prefixWord ++ tailWord_5464298) baseStart_5464298 baseEnd_5464298 := by
    simpa [prefixWord, tailWord_5464298, baseEnd_5464298] using wordTrace_append hprefix tailTrace_5464298
  have hstable : (prefixWord ++ tailWord_5464298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5464298).length < 2 ^ (prefixWord ++ tailWord_5464298).sum := by decide
  have hdescent : baseEnd_5464298 < baseStart_5464298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5464298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5464318 : List Nat := [4, 2, 2, 1, 1, 1, 2, 4, 1, 5]
def baseStart_5464318 : Nat := 118140960795 + 5464318 * 2 ^ 59
def prefixEnd_5464318 : Nat := 4983230072969 + 3 ^ 40 * 5464318 * 2
def baseEnd_5464318 : Nat := 935273861004952354798355

theorem tailTrace_5464318 : CollatzResearch.WordTrace tailWord_5464318 prefixEnd_5464318 935273861004952354798355 := by
  unfold tailWord_5464318
  simp only [CollatzResearch.WordTrace]
  refine ⟨24912506327214574007647201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132866700411811061374118405 24912506327214574007647201)
  ·
    refine ⟨18684379745410930505735401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24912506327214574007647201 18684379745410930505735401)
    ·
      refine ⟨14013284809058197879301551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18684379745410930505735401 14013284809058197879301551)
      ·
        refine ⟨21019927213587296818952327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14013284809058197879301551 21019927213587296818952327)
        ·
          refine ⟨31529890820380945228428491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21019927213587296818952327 31529890820380945228428491)
          ·
            refine ⟨47294836230571417842642737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31529890820380945228428491 47294836230571417842642737)
            ·
              refine ⟨35471127172928563381982053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47294836230571417842642737 35471127172928563381982053)
              ·
                refine ⟨6650836344924105634121635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35471127172928563381982053 6650836344924105634121635)
                ·
                  refine ⟨9976254517386158451182453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6650836344924105634121635 9976254517386158451182453)
                  ·
                    refine ⟨935273861004952354798355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9976254517386158451182453 935273861004952354798355)
                    ·
                      rfl

theorem cell23_5464318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_5464318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5464318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5464318 prefixEnd_5464318 := by exact prefixLift 5464318
  have htrace : WordTrace (prefixWord ++ tailWord_5464318) baseStart_5464318 baseEnd_5464318 := by
    simpa [prefixWord, tailWord_5464318, baseEnd_5464318] using wordTrace_append hprefix tailTrace_5464318
  have hstable : (prefixWord ++ tailWord_5464318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5464318).length < 2 ^ (prefixWord ++ tailWord_5464318).sum := by decide
  have hdescent : baseEnd_5464318 < baseStart_5464318 := by decide
  rcases family_descends (prefixWord ++ tailWord_5464318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5464321 : List Nat := [1, 2, 4, 1, 1, 2, 1, 3, 3, 1, 4]
def baseStart_5464321 : Nat := 118140960795 + 5464321 * 2 ^ 59
def prefixEnd_5464321 : Nat := 4983230072969 + 3 ^ 40 * 5464321 * 2
def baseEnd_5464321 : Nat := 2805823123456820552657551

theorem tailTrace_5464321 : CollatzResearch.WordTrace tailWord_5464321 prefixEnd_5464321 2805823123456820552657551 := by
  unfold tailWord_5464321
  simp only [CollatzResearch.WordTrace]
  refine ⟨199300160036705723573536817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132866773357803815715691211 199300160036705723573536817)
  ·
    refine ⟨149475120027529292680152613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199300160036705723573536817 149475120027529292680152613)
    ·
      refine ⟨28026585005161742377528615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149475120027529292680152613 28026585005161742377528615)
      ·
        refine ⟨42039877507742613566292923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28026585005161742377528615 42039877507742613566292923)
        ·
          refine ⟨63059816261613920349439385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42039877507742613566292923 63059816261613920349439385)
          ·
            refine ⟨47294862196210440262079539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63059816261613920349439385 47294862196210440262079539)
            ·
              refine ⟨70942293294315660393119309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47294862196210440262079539 70942293294315660393119309)
              ·
                refine ⟨26603359985368372647419741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70942293294315660393119309 26603359985368372647419741)
                ·
                  refine ⟨9976259994513139742782403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26603359985368372647419741 9976259994513139742782403)
                  ·
                    refine ⟨14964389991769709614173605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9976259994513139742782403 14964389991769709614173605)
                    ·
                      refine ⟨2805823123456820552657551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14964389991769709614173605 2805823123456820552657551)
                      ·
                        rfl

theorem cell23_5464321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_5464321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5464321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5464321 prefixEnd_5464321 := by exact prefixLift 5464321
  have htrace : WordTrace (prefixWord ++ tailWord_5464321) baseStart_5464321 baseEnd_5464321 := by
    simpa [prefixWord, tailWord_5464321, baseEnd_5464321] using wordTrace_append hprefix tailTrace_5464321
  have hstable : (prefixWord ++ tailWord_5464321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5464321).length < 2 ^ (prefixWord ++ tailWord_5464321).sum := by decide
  have hdescent : baseEnd_5464321 < baseStart_5464321 := by decide
  rcases family_descends (prefixWord ++ tailWord_5464321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5464331 : List Nat := [1, 1, 1, 1, 5, 2, 2, 2, 4, 4]
def baseStart_5464331 : Nat := 118140960795 + 5464331 * 2 ^ 59
def prefixEnd_5464331 : Nat := 4983230072969 + 3 ^ 40 * 5464331 * 2
def baseEnd_5464331 : Nat := 935276086087788504510835

theorem tailTrace_5464331 : CollatzResearch.WordTrace tailWord_5464331 prefixEnd_5464331 935276086087788504510835 := by
  unfold tailWord_5464331
  simp only [CollatzResearch.WordTrace]
  refine ⟨199300524766669495281400847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132867016511112996854267231 199300524766669495281400847)
  ·
    refine ⟨298950787150004242922101271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199300524766669495281400847 298950787150004242922101271)
    ·
      refine ⟨448426180725006364383151907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298950787150004242922101271 448426180725006364383151907)
      ·
        refine ⟨672639271087509546574727861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 448426180725006364383151907 672639271087509546574727861)
        ·
          refine ⟨63059931664454019991380737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 672639271087509546574727861 63059931664454019991380737)
          ·
            refine ⟨47294948748340514993535553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63059931664454019991380737 47294948748340514993535553)
            ·
              refine ⟨35471211561255386245151665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47294948748340514993535553 35471211561255386245151665)
              ·
                refine ⟨26603408670941539683863749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35471211561255386245151665 26603408670941539683863749)
                ·
                  refine ⟨4988139125801538690724453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26603408670941539683863749 4988139125801538690724453)
                  ·
                    refine ⟨935276086087788504510835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4988139125801538690724453 935276086087788504510835)
                    ·
                      rfl

theorem cell23_5464331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 4, 4].length) (baseStart_5464331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5464331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5464331 prefixEnd_5464331 := by exact prefixLift 5464331
  have htrace : WordTrace (prefixWord ++ tailWord_5464331) baseStart_5464331 baseEnd_5464331 := by
    simpa [prefixWord, tailWord_5464331, baseEnd_5464331] using wordTrace_append hprefix tailTrace_5464331
  have hstable : (prefixWord ++ tailWord_5464331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5464331).length < 2 ^ (prefixWord ++ tailWord_5464331).sum := by decide
  have hdescent : baseEnd_5464331 < baseStart_5464331 := by decide
  rcases family_descends (prefixWord ++ tailWord_5464331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5464344 : List Nat := [2, 1, 2, 3, 1, 2, 12]
def baseStart_5464344 : Nat := 118140960795 + 5464344 * 2 ^ 59
def prefixEnd_5464344 : Nat := 4983230072969 + 3 ^ 40 * 5464344 * 2
def baseEnd_5464344 : Nat := 34639937450763876082345

theorem tailTrace_5464344 : CollatzResearch.WordTrace tailWord_5464344 prefixEnd_5464344 34639937450763876082345 := by
  unfold tailWord_5464344
  simp only [CollatzResearch.WordTrace]
  refine ⟨99650499457811199250812043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132867332610414932334416057 99650499457811199250812043)
  ·
    refine ⟨149475749186716798876218065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99650499457811199250812043 149475749186716798876218065)
    ·
      refine ⟨112106811890037599157163549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149475749186716798876218065 112106811890037599157163549)
      ·
        refine ⟨42040054458764099683936331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112106811890037599157163549 42040054458764099683936331)
        ·
          refine ⟨63060081688146149525904497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42040054458764099683936331 63060081688146149525904497)
          ·
            refine ⟨47295061266109612144428373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63060081688146149525904497 47295061266109612144428373)
            ·
              refine ⟨34639937450763876082345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 47295061266109612144428373 34639937450763876082345)
              ·
                rfl

theorem cell23_5464344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 12].length) (baseStart_5464344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5464344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5464344 prefixEnd_5464344 := by exact prefixLift 5464344
  have htrace : WordTrace (prefixWord ++ tailWord_5464344) baseStart_5464344 baseEnd_5464344 := by
    simpa [prefixWord, tailWord_5464344, baseEnd_5464344] using wordTrace_append hprefix tailTrace_5464344
  have hstable : (prefixWord ++ tailWord_5464344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5464344).length < 2 ^ (prefixWord ++ tailWord_5464344).sum := by decide
  have hdescent : baseEnd_5464344 < baseStart_5464344 := by decide
  rcases family_descends (prefixWord ++ tailWord_5464344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5464355 : List Nat := [1, 1, 1, 4, 2, 2, 4, 1, 3, 2, 2]
def baseStart_5464355 : Nat := 118140960795 + 5464355 * 2 ^ 59
def prefixEnd_5464355 : Nat := 4983230072969 + 3 ^ 40 * 5464355 * 2
def baseEnd_5464355 : Nat := 2805840581799073419632395

theorem tailTrace_5464355 : CollatzResearch.WordTrace tailWord_5464355 prefixEnd_5464355 2805840581799073419632395 := by
  unfold tailWord_5464355
  simp only [CollatzResearch.WordTrace]
  refine ⟨199301400118582547380274519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132867600079055031586849679 199301400118582547380274519)
  ·
    refine ⟨298952100177873821070411779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199301400118582547380274519 298952100177873821070411779)
    ·
      refine ⟨448428150266810731605617669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298952100177873821070411779 448428150266810731605617669)
      ·
        refine ⟨84080278175027012176053313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 448428150266810731605617669 84080278175027012176053313)
        ·
          refine ⟨63060208631270259132039985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84080278175027012176053313 63060208631270259132039985)
          ·
            refine ⟨47295156473452694349029989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63060208631270259132039985 47295156473452694349029989)
            ·
              refine ⟨8867841838772380190443123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47295156473452694349029989 8867841838772380190443123)
              ·
                refine ⟨13301762758158570285664685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8867841838772380190443123 13301762758158570285664685)
                ·
                  refine ⟨4988161034309463857124257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13301762758158570285664685 4988161034309463857124257)
                  ·
                    refine ⟨3741120775732097892843193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4988161034309463857124257 3741120775732097892843193)
                    ·
                      refine ⟨2805840581799073419632395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3741120775732097892843193 2805840581799073419632395)
                      ·
                        rfl

theorem cell23_5464355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 3, 2, 2].length) (baseStart_5464355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5464355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5464355 prefixEnd_5464355 := by exact prefixLift 5464355
  have htrace : WordTrace (prefixWord ++ tailWord_5464355) baseStart_5464355 baseEnd_5464355 := by
    simpa [prefixWord, tailWord_5464355, baseEnd_5464355] using wordTrace_append hprefix tailTrace_5464355
  have hstable : (prefixWord ++ tailWord_5464355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5464355).length < 2 ^ (prefixWord ++ tailWord_5464355).sum := by decide
  have hdescent : baseEnd_5464355 < baseStart_5464355 := by decide
  rcases family_descends (prefixWord ++ tailWord_5464355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5464372 : List Nat := [2, 5, 1, 1, 1, 2, 2, 2, 3, 2, 2]
def baseStart_5464372 : Nat := 118140960795 + 5464372 * 2 ^ 59
def prefixEnd_5464372 : Nat := 4983230072969 + 3 ^ 40 * 5464372 * 2
def baseEnd_5464372 : Nat := 2805849310970199853119817

theorem tailTrace_5464372 : CollatzResearch.WordTrace tailWord_5464372 prefixEnd_5464372 2805849310970199853119817 := by
  unfold tailWord_5464372
  simp only [CollatzResearch.WordTrace]
  refine ⟨99651010079760479641821685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132868013439680639522428913 99651010079760479641821685)
  ·
    refine ⟨9342282194977544966420783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 99651010079760479641821685 9342282194977544966420783)
    ·
      refine ⟨14013423292466317449631175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9342282194977544966420783 14013423292466317449631175)
      ·
        refine ⟨21020134938699476174446763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14013423292466317449631175 21020134938699476174446763)
        ·
          refine ⟨31530202408049214261670145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21020134938699476174446763 31530202408049214261670145)
          ·
            refine ⟨23647651806036910696252609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31530202408049214261670145 23647651806036910696252609)
            ·
              refine ⟨17735738854527683022189457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23647651806036910696252609 17735738854527683022189457)
              ·
                refine ⟨13301804140895762266642093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17735738854527683022189457 13301804140895762266642093)
                ·
                  refine ⟨4988176552835910849990785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13301804140895762266642093 4988176552835910849990785)
                  ·
                    refine ⟨3741132414626933137493089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4988176552835910849990785 3741132414626933137493089)
                    ·
                      refine ⟨2805849310970199853119817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3741132414626933137493089 2805849310970199853119817)
                      ·
                        rfl

theorem cell23_5464372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_5464372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5464372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5464372 prefixEnd_5464372 := by exact prefixLift 5464372
  have htrace : WordTrace (prefixWord ++ tailWord_5464372) baseStart_5464372 baseEnd_5464372 := by
    simpa [prefixWord, tailWord_5464372, baseEnd_5464372] using wordTrace_append hprefix tailTrace_5464372
  have hstable : (prefixWord ++ tailWord_5464372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5464372).length < 2 ^ (prefixWord ++ tailWord_5464372).sum := by decide
  have hdescent : baseEnd_5464372 < baseStart_5464372 := by decide
  rcases family_descends (prefixWord ++ tailWord_5464372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5464378 : List Nat := [3, 1, 1, 1, 4, 4, 2, 7]
def baseStart_5464378 : Nat := 118140960795 + 5464378 * 2 ^ 59
def prefixEnd_5464378 : Nat := 4983230072969 + 3 ^ 40 * 5464378 * 2
def baseEnd_5464378 : Nat := 103920458957560252949807

theorem tailTrace_5464378 : CollatzResearch.WordTrace tailWord_5464378 prefixEnd_5464378 103920458957560252949807 := by
  unfold tailWord_5464378
  simp only [CollatzResearch.WordTrace]
  refine ⟨49825559749374805577090447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132868159331666148205574525 49825559749374805577090447)
  ·
    refine ⟨74738339624062208365635671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49825559749374805577090447 74738339624062208365635671)
    ·
      refine ⟨112107509436093312548453507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74738339624062208365635671 112107509436093312548453507)
      ·
        refine ⟨168161264154139968822680261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112107509436093312548453507 168161264154139968822680261)
        ·
          refine ⟨31530237028901244154252549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 168161264154139968822680261 31530237028901244154252549)
          ·
            refine ⟨5911919442918983278922353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31530237028901244154252549 5911919442918983278922353)
            ·
              refine ⟨4433939582189237459191765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5911919442918983278922353 4433939582189237459191765)
              ·
                refine ⟨103920458957560252949807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4433939582189237459191765 103920458957560252949807)
                ·
                  rfl

theorem cell23_5464378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 7].length) (baseStart_5464378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5464378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5464378 prefixEnd_5464378 := by exact prefixLift 5464378
  have htrace : WordTrace (prefixWord ++ tailWord_5464378) baseStart_5464378 baseEnd_5464378 := by
    simpa [prefixWord, tailWord_5464378, baseEnd_5464378] using wordTrace_append hprefix tailTrace_5464378
  have hstable : (prefixWord ++ tailWord_5464378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5464378).length < 2 ^ (prefixWord ++ tailWord_5464378).sum := by decide
  have hdescent : baseEnd_5464378 < baseStart_5464378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5464378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5464431 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 4, 4, 3]
def baseStart_5464431 : Nat := 118140960795 + 5464431 * 2 ^ 59
def prefixEnd_5464431 : Nat := 4983230072969 + 3 ^ 40 * 5464431 * 2
def baseEnd_5464431 : Nat := 2805879606328815122282045

theorem tailTrace_5464431 : CollatzResearch.WordTrace tailWord_5464431 prefixEnd_5464431 2805879606328815122282045 := by
  unfold tailWord_5464431
  simp only [CollatzResearch.WordTrace]
  refine ⟨199304172066307212360041147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132869448044204808240027431 199304172066307212360041147)
  ·
    refine ⟨298956258099460818540061721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199304172066307212360041147 298956258099460818540061721)
    ·
      refine ⟨224217193574595613905046291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 298956258099460818540061721 224217193574595613905046291)
      ·
        refine ⟨336325790361893420857569437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224217193574595613905046291 336325790361893420857569437)
        ·
          refine ⟨126122171385710032821588539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 336325790361893420857569437 126122171385710032821588539)
          ·
            refine ⟨189183257078565049232382809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126122171385710032821588539 189183257078565049232382809)
            ·
              refine ⟨141887442808923786924287107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189183257078565049232382809 141887442808923786924287107)
              ·
                refine ⟨212831164213385680386430661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141887442808923786924287107 212831164213385680386430661)
                ·
                  refine ⟨39905843290009815072455749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 212831164213385680386430661 39905843290009815072455749)
                  ·
                    refine ⟨7482345616876840326085453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39905843290009815072455749 7482345616876840326085453)
                    ·
                      refine ⟨2805879606328815122282045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7482345616876840326085453 2805879606328815122282045)
                      ·
                        rfl

theorem cell23_5464431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 4, 3].length) (baseStart_5464431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5464431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5464431 prefixEnd_5464431 := by exact prefixLift 5464431
  have htrace : WordTrace (prefixWord ++ tailWord_5464431) baseStart_5464431 baseEnd_5464431 := by
    simpa [prefixWord, tailWord_5464431, baseEnd_5464431] using wordTrace_append hprefix tailTrace_5464431
  have hstable : (prefixWord ++ tailWord_5464431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5464431).length < 2 ^ (prefixWord ++ tailWord_5464431).sum := by decide
  have hdescent : baseEnd_5464431 < baseStart_5464431 := by decide
  rcases family_descends (prefixWord ++ tailWord_5464431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5464432 : List Nat := [2, 1, 1, 1, 4, 5, 1, 2, 1, 3, 2]
def baseStart_5464432 : Nat := 118140960795 + 5464432 * 2 ^ 59
def prefixEnd_5464432 : Nat := 4983230072969 + 3 ^ 40 * 5464432 * 2
def baseEnd_5464432 : Nat := 2805880119809469618369541

theorem tailTrace_5464432 : CollatzResearch.WordTrace tailWord_5464432 prefixEnd_5464432 2805880119809469618369541 := by
  unfold tailWord_5464432
  simp only [CollatzResearch.WordTrace]
  refine ⟨99652104269651794765413775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132869472359535726353885033 99652104269651794765413775)
  ·
    refine ⟨149478156404477692148120663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99652104269651794765413775 149478156404477692148120663)
    ·
      refine ⟨224217234606716538222180995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149478156404477692148120663 224217234606716538222180995)
      ·
        refine ⟨336325851910074807333271493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224217234606716538222180995 336325851910074807333271493)
        ·
          refine ⟨63061097233139026374988405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 336325851910074807333271493 63061097233139026374988405)
          ·
            refine ⟨5911977865606783722655163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63061097233139026374988405 5911977865606783722655163)
            ·
              refine ⟨8867966798410175583982745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5911977865606783722655163 8867966798410175583982745)
              ·
                refine ⟨6650975098807631687987059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8867966798410175583982745 6650975098807631687987059)
                ·
                  refine ⟨9976462648211447531980589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6650975098807631687987059 9976462648211447531980589)
                  ·
                    refine ⟨3741173493079292824492721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9976462648211447531980589 3741173493079292824492721)
                    ·
                      refine ⟨2805880119809469618369541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3741173493079292824492721 2805880119809469618369541)
                      ·
                        rfl

theorem cell23_5464432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 2, 1, 3, 2].length) (baseStart_5464432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5464432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5464432 prefixEnd_5464432 := by exact prefixLift 5464432
  have htrace : WordTrace (prefixWord ++ tailWord_5464432) baseStart_5464432 baseEnd_5464432 := by
    simpa [prefixWord, tailWord_5464432, baseEnd_5464432] using wordTrace_append hprefix tailTrace_5464432
  have hstable : (prefixWord ++ tailWord_5464432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5464432).length < 2 ^ (prefixWord ++ tailWord_5464432).sum := by decide
  have hdescent : baseEnd_5464432 < baseStart_5464432 := by decide
  rcases family_descends (prefixWord ++ tailWord_5464432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5464441 : List Nat := [1, 2, 1, 3, 2, 1, 1, 2, 4, 2, 4]
def baseStart_5464441 : Nat := 118140960795 + 5464441 * 2 ^ 59
def prefixEnd_5464441 : Nat := 4983230072969 + 3 ^ 40 * 5464441 * 2
def baseEnd_5464441 : Nat := 2805884741135360083156999

theorem tailTrace_5464441 : CollatzResearch.WordTrace tailWord_5464441 prefixEnd_5464441 2805884741135360083156999 := by
  unfold tailWord_5464441
  simp only [CollatzResearch.WordTrace]
  refine ⟨199304536796270984067905177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132869691197513989378603451 199304536796270984067905177)
  ·
    refine ⟨149478402597203238050928883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199304536796270984067905177 149478402597203238050928883)
    ·
      refine ⟨224217603895804857076393325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149478402597203238050928883 224217603895804857076393325)
      ·
        refine ⟨84081601460926821403647497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 224217603895804857076393325 84081601460926821403647497)
        ·
          refine ⟨63061201095695116052735623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84081601460926821403647497 63061201095695116052735623)
          ·
            refine ⟨94591801643542674079103435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63061201095695116052735623 94591801643542674079103435)
            ·
              refine ⟨141887702465314011118655153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94591801643542674079103435 141887702465314011118655153)
              ·
                refine ⟨106415776848985508338991365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141887702465314011118655153 106415776848985508338991365)
                ·
                  refine ⟨19952958159184782813560881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 106415776848985508338991365 19952958159184782813560881)
                  ·
                    refine ⟨14964718619388587110170661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19952958159184782813560881 14964718619388587110170661)
                    ·
                      refine ⟨2805884741135360083156999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14964718619388587110170661 2805884741135360083156999)
                      ·
                        rfl

theorem cell23_5464441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_5464441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5464441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5464441 prefixEnd_5464441 := by exact prefixLift 5464441
  have htrace : WordTrace (prefixWord ++ tailWord_5464441) baseStart_5464441 baseEnd_5464441 := by
    simpa [prefixWord, tailWord_5464441, baseEnd_5464441] using wordTrace_append hprefix tailTrace_5464441
  have hstable : (prefixWord ++ tailWord_5464441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5464441).length < 2 ^ (prefixWord ++ tailWord_5464441).sum := by decide
  have hdescent : baseEnd_5464441 < baseStart_5464441 := by decide
  rcases family_descends (prefixWord ++ tailWord_5464441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5464445 : List Nat := [1, 4, 1, 1, 2, 4, 1, 2, 1, 4, 2]
def baseStart_5464445 : Nat := 118140960795 + 5464445 * 2 ^ 59
def prefixEnd_5464445 : Nat := 4983230072969 + 3 ^ 40 * 5464445 * 2
def baseEnd_5464445 : Nat := 2805886795057978067506981

theorem tailTrace_5464445 : CollatzResearch.WordTrace tailWord_5464445 prefixEnd_5464445 2805886795057978067506981 := by
  unfold tailWord_5464445
  simp only [CollatzResearch.WordTrace]
  refine ⟨199304682688256492751050789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132869788458837661834033859 199304682688256492751050789)
  ·
    refine ⟨37369628004048092390822023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 199304682688256492751050789 37369628004048092390822023)
    ·
      refine ⟨56054442006072138586233035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37369628004048092390822023 56054442006072138586233035)
      ·
        refine ⟨84081663009108207879349553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56054442006072138586233035 84081663009108207879349553)
        ·
          refine ⟨63061247256831155909512165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84081663009108207879349553 63061247256831155909512165)
          ·
            refine ⟨11823983860655841733033531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63061247256831155909512165 11823983860655841733033531)
            ·
              refine ⟨17735975790983762599550297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11823983860655841733033531 17735975790983762599550297)
              ·
                refine ⟨13301981843237821949662723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17735975790983762599550297 13301981843237821949662723)
                ·
                  refine ⟨19952972764856732924494085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13301981843237821949662723 19952972764856732924494085)
                  ·
                    refine ⟨3741182393410637423342641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19952972764856732924494085 3741182393410637423342641)
                    ·
                      refine ⟨2805886795057978067506981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3741182393410637423342641 2805886795057978067506981)
                      ·
                        rfl

theorem cell23_5464445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 4, 2].length) (baseStart_5464445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5464445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5464445 prefixEnd_5464445 := by exact prefixLift 5464445
  have htrace : WordTrace (prefixWord ++ tailWord_5464445) baseStart_5464445 baseEnd_5464445 := by
    simpa [prefixWord, tailWord_5464445, baseEnd_5464445] using wordTrace_append hprefix tailTrace_5464445
  have hstable : (prefixWord ++ tailWord_5464445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5464445).length < 2 ^ (prefixWord ++ tailWord_5464445).sum := by decide
  have hdescent : baseEnd_5464445 < baseStart_5464445 := by decide
  rcases family_descends (prefixWord ++ tailWord_5464445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5464449 : List Nat := [1, 2, 4, 3, 1, 2, 3, 1, 1, 3, 2]
def baseStart_5464449 : Nat := 118140960795 + 5464449 * 2 ^ 59
def prefixEnd_5464449 : Nat := 4983230072969 + 3 ^ 40 * 5464449 * 2
def baseEnd_5464449 : Nat := 2805888848980596051856963

theorem tailTrace_5464449 : CollatzResearch.WordTrace tailWord_5464449 prefixEnd_5464449 2805888848980596051856963 := by
  unfold tailWord_5464449
  simp only [CollatzResearch.WordTrace]
  refine ⟨199304828580242001434196401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132869885720161334289464267 199304828580242001434196401)
  ·
    refine ⟨149478621435181501075647301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199304828580242001434196401 149478621435181501075647301)
    ·
      refine ⟨28027241519096531451683869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149478621435181501075647301 28027241519096531451683869)
      ·
        refine ⟨10510215569661199294381451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28027241519096531451683869 10510215569661199294381451)
        ·
          refine ⟨15765323354491798941572177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10510215569661199294381451 15765323354491798941572177)
          ·
            refine ⟨11823992515868849206179133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15765323354491798941572177 11823992515868849206179133)
            ·
              refine ⟨4433997193450818452317175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11823992515868849206179133 4433997193450818452317175)
              ·
                refine ⟨6650995790176227678475763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4433997193450818452317175 6650995790176227678475763)
                ·
                  refine ⟨9976493685264341517713645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6650995790176227678475763 9976493685264341517713645)
                  ·
                    refine ⟨3741185131974128069142617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9976493685264341517713645 3741185131974128069142617)
                    ·
                      refine ⟨2805888848980596051856963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3741185131974128069142617 2805888848980596051856963)
                      ·
                        rfl

theorem cell23_5464449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_5464449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5464449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5464449 prefixEnd_5464449 := by exact prefixLift 5464449
  have htrace : WordTrace (prefixWord ++ tailWord_5464449) baseStart_5464449 baseEnd_5464449 := by
    simpa [prefixWord, tailWord_5464449, baseEnd_5464449] using wordTrace_append hprefix tailTrace_5464449
  have hstable : (prefixWord ++ tailWord_5464449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5464449).length < 2 ^ (prefixWord ++ tailWord_5464449).sum := by decide
  have hdescent : baseEnd_5464449 < baseStart_5464449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5464449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5464500 : List Nat := [2, 5, 2, 2, 2, 1, 2, 1, 1, 3, 2]
def baseStart_5464500 : Nat := 118140960795 + 5464500 * 2 ^ 59
def prefixEnd_5464500 : Nat := 4983230072969 + 3 ^ 40 * 5464500 * 2
def baseEnd_5464500 : Nat := 2805915036493975352319229

theorem tailTrace_5464500 : CollatzResearch.WordTrace tailWord_5464500 prefixEnd_5464500 2805915036493975352319229 := by
  unfold tailWord_5464500
  simp only [CollatzResearch.WordTrace]
  refine ⟨99653344351528618572151477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132871125802038158096201969 99653344351528618572151477)
  ·
    refine ⟨9342501032955807991139201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 99653344351528618572151477 9342501032955807991139201)
    ·
      refine ⟨7006875774716855993354401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9342501032955807991139201 7006875774716855993354401)
      ·
        refine ⟨5255156831037641995015801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7006875774716855993354401 5255156831037641995015801)
        ·
          refine ⟨3941367623278231496261851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5255156831037641995015801 3941367623278231496261851)
          ·
            refine ⟨5912051434917347244392777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3941367623278231496261851 5912051434917347244392777)
            ·
              refine ⟨4434038576188010433294583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5912051434917347244392777 4434038576188010433294583)
              ·
                refine ⟨6651057864282015649941875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4434038576188010433294583 6651057864282015649941875)
                ·
                  refine ⟨9976586796423023474912813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6651057864282015649941875 9976586796423023474912813)
                  ·
                    refine ⟨3741220048658633803092305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9976586796423023474912813 3741220048658633803092305)
                    ·
                      refine ⟨2805915036493975352319229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3741220048658633803092305 2805915036493975352319229)
                      ·
                        rfl

theorem cell23_5464500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_5464500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5464500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5464500 prefixEnd_5464500 := by exact prefixLift 5464500
  have htrace : WordTrace (prefixWord ++ tailWord_5464500) baseStart_5464500 baseEnd_5464500 := by
    simpa [prefixWord, tailWord_5464500, baseEnd_5464500] using wordTrace_append hprefix tailTrace_5464500
  have hstable : (prefixWord ++ tailWord_5464500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5464500).length < 2 ^ (prefixWord ++ tailWord_5464500).sum := by decide
  have hdescent : baseEnd_5464500 < baseStart_5464500 := by decide
  rcases family_descends (prefixWord ++ tailWord_5464500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5464521 : List Nat := [1, 2, 1, 1, 2, 1, 4, 1, 2, 3, 5]
def baseStart_5464521 : Nat := 118140960795 + 5464521 * 2 ^ 59
def prefixEnd_5464521 : Nat := 4983230072969 + 3 ^ 40 * 5464521 * 2
def baseEnd_5464521 : Nat := 2805925819587719770156631

theorem tailTrace_5464521 : CollatzResearch.WordTrace tailWord_5464521 prefixEnd_5464521 2805925819587719770156631 := by
  unfold tailWord_5464521
  simp only [CollatzResearch.WordTrace]
  refine ⟨199307454635981157730817417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132871636423987438487211611 199307454635981157730817417)
  ·
    refine ⟨149480590976985868298113063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199307454635981157730817417 149480590976985868298113063)
    ·
      refine ⟨224220886465478802447169595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149480590976985868298113063 224220886465478802447169595)
      ·
        refine ⟨336331329698218203670754393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224220886465478802447169595 336331329698218203670754393)
        ·
          refine ⟨252248497273663652753065795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 336331329698218203670754393 252248497273663652753065795)
          ·
            refine ⟨378372745910495479129598693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252248497273663652753065795 378372745910495479129598693)
            ·
              refine ⟨70944889858217902336799755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 378372745910495479129598693 70944889858217902336799755)
              ·
                refine ⟨106417334787326853505199633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70944889858217902336799755 106417334787326853505199633)
                ·
                  refine ⟨79813001090495140128899725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106417334787326853505199633 79813001090495140128899725)
                  ·
                    refine ⟨29929875408935677548337397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 79813001090495140128899725 29929875408935677548337397)
                    ·
                      refine ⟨2805925819587719770156631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29929875408935677548337397 2805925819587719770156631)
                      ·
                        rfl

theorem cell23_5464521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 3, 5].length) (baseStart_5464521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5464521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5464521 prefixEnd_5464521 := by exact prefixLift 5464521
  have htrace : WordTrace (prefixWord ++ tailWord_5464521) baseStart_5464521 baseEnd_5464521 := by
    simpa [prefixWord, tailWord_5464521, baseEnd_5464521] using wordTrace_append hprefix tailTrace_5464521
  have hstable : (prefixWord ++ tailWord_5464521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5464521).length < 2 ^ (prefixWord ++ tailWord_5464521).sum := by decide
  have hdescent : baseEnd_5464521 < baseStart_5464521 := by decide
  rcases family_descends (prefixWord ++ tailWord_5464521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5464538 : List Nat := [3, 1, 1, 2, 3, 1, 1, 1, 3, 4, 3]
def baseStart_5464538 : Nat := 118140960795 + 5464538 * 2 ^ 59
def prefixEnd_5464538 : Nat := 4983230072969 + 3 ^ 40 * 5464538 * 2
def baseEnd_5464538 : Nat := 2805934548758846203644053

theorem tailTrace_5464538 : CollatzResearch.WordTrace tailWord_5464538 prefixEnd_5464538 2805934548758846203644053 := by
  unfold tailWord_5464538
  simp only [CollatzResearch.WordTrace]
  refine ⟨49827018669229892408546567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132872049784613046422790845 49827018669229892408546567)
  ·
    refine ⟨74740528003844838612819851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49827018669229892408546567 74740528003844838612819851)
    ·
      refine ⟨112110792005767257919229777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74740528003844838612819851 112110792005767257919229777)
      ·
        refine ⟨84083094004325443439422333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112110792005767257919229777 84083094004325443439422333)
        ·
          refine ⟨31531160251622041289783375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84083094004325443439422333 31531160251622041289783375)
          ·
            refine ⟨47296740377433061934675063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31531160251622041289783375 47296740377433061934675063)
            ·
              refine ⟨70945110566149592902012595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47296740377433061934675063 70945110566149592902012595)
              ·
                refine ⟨106417665849224389353018893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70945110566149592902012595 106417665849224389353018893)
                ·
                  refine ⟨39906624693459146007382085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106417665849224389353018893 39906624693459146007382085)
                  ·
                    refine ⟨7482492130023589876384141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39906624693459146007382085 7482492130023589876384141)
                    ·
                      refine ⟨2805934548758846203644053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7482492130023589876384141 2805934548758846203644053)
                      ·
                        rfl

theorem cell23_5464538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 3, 4, 3].length) (baseStart_5464538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5464538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5464538 prefixEnd_5464538 := by exact prefixLift 5464538
  have htrace : WordTrace (prefixWord ++ tailWord_5464538) baseStart_5464538 baseEnd_5464538 := by
    simpa [prefixWord, tailWord_5464538, baseEnd_5464538] using wordTrace_append hprefix tailTrace_5464538
  have hstable : (prefixWord ++ tailWord_5464538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5464538).length < 2 ^ (prefixWord ++ tailWord_5464538).sum := by decide
  have hdescent : baseEnd_5464538 < baseStart_5464538 := by decide
  rcases family_descends (prefixWord ++ tailWord_5464538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5464558 : List Nat := [4, 1, 2, 1, 2, 2, 1, 2, 8]
def baseStart_5464558 : Nat := 118140960795 + 5464558 * 2 ^ 59
def prefixEnd_5464558 : Nat := 4983230072969 + 3 ^ 40 * 5464558 * 2
def baseEnd_5464558 : Nat := 311771646485770680599329

theorem tailTrace_5464558 : CollatzResearch.WordTrace tailWord_5464558 prefixEnd_5464558 311771646485770680599329 := by
  unfold tailWord_5464558
  simp only [CollatzResearch.WordTrace]
  refine ⟨24913600517105889131239291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132872536091231408699942885 24913600517105889131239291)
  ·
    refine ⟨37370400775658833696858937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24913600517105889131239291 37370400775658833696858937)
    ·
      refine ⟨28027800581744125272644203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37370400775658833696858937 28027800581744125272644203)
      ·
        refine ⟨42041700872616187908966305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28027800581744125272644203 42041700872616187908966305)
        ·
          refine ⟨31531275654462140931724729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42041700872616187908966305 31531275654462140931724729)
          ·
            refine ⟨23648456740846605698793547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31531275654462140931724729 23648456740846605698793547)
            ·
              refine ⟨35472685111269908548190321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23648456740846605698793547 35472685111269908548190321)
              ·
                refine ⟨26604513833452431411142741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35472685111269908548190321 26604513833452431411142741)
                ·
                  refine ⟨311771646485770680599329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26604513833452431411142741 311771646485770680599329)
                  ·
                    rfl

theorem cell23_5464558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 8].length) (baseStart_5464558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5464558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5464558 prefixEnd_5464558 := by exact prefixLift 5464558
  have htrace : WordTrace (prefixWord ++ tailWord_5464558) baseStart_5464558 baseEnd_5464558 := by
    simpa [prefixWord, tailWord_5464558, baseEnd_5464558] using wordTrace_append hprefix tailTrace_5464558
  have hstable : (prefixWord ++ tailWord_5464558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5464558).length < 2 ^ (prefixWord ++ tailWord_5464558).sum := by decide
  have hdescent : baseEnd_5464558 < baseStart_5464558 := by decide
  rcases family_descends (prefixWord ++ tailWord_5464558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5464585 : List Nat := [1, 2, 1, 1, 3, 1, 2, 5, 3, 1, 3]
def baseStart_5464585 : Nat := 118140960795 + 5464585 * 2 ^ 59
def prefixEnd_5464585 : Nat := 4983230072969 + 3 ^ 40 * 5464585 * 2
def baseEnd_5464585 : Nat := 2805958682349607519756337

theorem tailTrace_5464585 : CollatzResearch.WordTrace tailWord_5464585 prefixEnd_5464585 2805958682349607519756337 := by
  unfold tailWord_5464585
  simp only [CollatzResearch.WordTrace]
  refine ⟨199309788907749296661147209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132873192605166197774098139 199309788907749296661147209)
  ·
    refine ⟨149482341680811972495860407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199309788907749296661147209 149482341680811972495860407)
    ·
      refine ⟨224223512521217958743790611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149482341680811972495860407 224223512521217958743790611)
      ·
        refine ⟨336335268781826938115685917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224223512521217958743790611 336335268781826938115685917)
        ·
          refine ⟨126125725793185101793382219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 336335268781826938115685917 126125725793185101793382219)
          ·
            refine ⟨189188588689777652690073329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126125725793185101793382219 189188588689777652690073329)
            ·
              refine ⟨141891441517333239517554997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189188588689777652690073329 141891441517333239517554997)
              ·
                refine ⟨13302322642249991204770781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 141891441517333239517554997 13302322642249991204770781)
                ·
                  refine ⟨4988370990843746701789043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13302322642249991204770781 4988370990843746701789043)
                  ·
                    refine ⟨7482556486265620052683565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4988370990843746701789043 7482556486265620052683565)
                    ·
                      refine ⟨2805958682349607519756337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7482556486265620052683565 2805958682349607519756337)
                      ·
                        rfl

theorem cell23_5464585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 3, 1, 3].length) (baseStart_5464585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5464585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5464585 prefixEnd_5464585 := by exact prefixLift 5464585
  have htrace : WordTrace (prefixWord ++ tailWord_5464585) baseStart_5464585 baseEnd_5464585 := by
    simpa [prefixWord, tailWord_5464585, baseEnd_5464585] using wordTrace_append hprefix tailTrace_5464585
  have hstable : (prefixWord ++ tailWord_5464585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5464585).length < 2 ^ (prefixWord ++ tailWord_5464585).sum := by decide
  have hdescent : baseEnd_5464585 < baseStart_5464585 := by decide
  rcases family_descends (prefixWord ++ tailWord_5464585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5464595 : List Nat := [1, 1, 1, 2, 1, 5, 1, 2, 4, 3, 2]
def baseStart_5464595 : Nat := 118140960795 + 5464595 * 2 ^ 59
def prefixEnd_5464595 : Nat := 4983230072969 + 3 ^ 40 * 5464595 * 2
def baseEnd_5464595 : Nat := 2805963817156152480631291

theorem tailTrace_5464595 : CollatzResearch.WordTrace tailWord_5464595 prefixEnd_5464595 2805963817156152480631291 := by
  unfold tailWord_5464595
  simp only [CollatzResearch.WordTrace]
  refine ⟨199310153637713068369011239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132873435758475378912674159 199310153637713068369011239)
  ·
    refine ⟨298965230456569602553516859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199310153637713068369011239 298965230456569602553516859)
    ·
      refine ⟨448447845684854403830275289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298965230456569602553516859 448447845684854403830275289)
      ·
        refine ⟨336335884263640802872706467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 448447845684854403830275289 336335884263640802872706467)
        ·
          refine ⟨504503826395461204309059701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 336335884263640802872706467 504503826395461204309059701)
          ·
            refine ⟨47297233724574487903974347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 504503826395461204309059701 47297233724574487903974347)
            ·
              refine ⟨70945850586861731855961521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47297233724574487903974347 70945850586861731855961521)
              ·
                refine ⟨53209387940146298891971141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70945850586861731855961521 53209387940146298891971141)
                ·
                  refine ⟨9976760238777431042244589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53209387940146298891971141 9976760238777431042244589)
                  ·
                    refine ⟨3741285089541536640841721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9976760238777431042244589 3741285089541536640841721)
                    ·
                      refine ⟨2805963817156152480631291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3741285089541536640841721 2805963817156152480631291)
                      ·
                        rfl

theorem cell23_5464595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 4, 3, 2].length) (baseStart_5464595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5464595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5464595 prefixEnd_5464595 := by exact prefixLift 5464595
  have htrace : WordTrace (prefixWord ++ tailWord_5464595) baseStart_5464595 baseEnd_5464595 := by
    simpa [prefixWord, tailWord_5464595, baseEnd_5464595] using wordTrace_append hprefix tailTrace_5464595
  have hstable : (prefixWord ++ tailWord_5464595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5464595).length < 2 ^ (prefixWord ++ tailWord_5464595).sum := by decide
  have hdescent : baseEnd_5464595 < baseStart_5464595 := by decide
  rcases family_descends (prefixWord ++ tailWord_5464595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5464605 : List Nat := [1, 4, 2, 2, 1, 3, 1, 1, 3, 5]
def baseStart_5464605 : Nat := 118140960795 + 5464605 * 2 ^ 59
def prefixEnd_5464605 : Nat := 4983230072969 + 3 ^ 40 * 5464605 * 2
def baseEnd_5464605 : Nat := 935322983987565813835415

theorem tailTrace_5464605 : CollatzResearch.WordTrace tailWord_5464605 prefixEnd_5464605 935322983987565813835415 := by
  unfold tailWord_5464605
  simp only [CollatzResearch.WordTrace]
  refine ⟨199310518367676840076875269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132873678911784560051250179 199310518367676840076875269)
  ·
    refine ⟨37370722193939407514414113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 199310518367676840076875269 37370722193939407514414113)
    ·
      refine ⟨28028041645454555635810585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37370722193939407514414113 28028041645454555635810585)
      ·
        refine ⟨21021031234090916726857939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28028041645454555635810585 21021031234090916726857939)
        ·
          refine ⟨31531546851136375090286909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21021031234090916726857939 31531546851136375090286909)
          ·
            refine ⟨11824330069176140658857591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31531546851136375090286909 11824330069176140658857591)
            ·
              refine ⟨17736495103764210988286387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11824330069176140658857591 17736495103764210988286387)
              ·
                refine ⟨26604742655646316482429581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17736495103764210988286387 26604742655646316482429581)
                ·
                  refine ⟨9976778495867368680911093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26604742655646316482429581 9976778495867368680911093)
                  ·
                    refine ⟨935322983987565813835415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9976778495867368680911093 935322983987565813835415)
                    ·
                      rfl

theorem cell23_5464605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_5464605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5464605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5464605 prefixEnd_5464605 := by exact prefixLift 5464605
  have htrace : WordTrace (prefixWord ++ tailWord_5464605) baseStart_5464605 baseEnd_5464605 := by
    simpa [prefixWord, tailWord_5464605, baseEnd_5464605] using wordTrace_append hprefix tailTrace_5464605
  have hstable : (prefixWord ++ tailWord_5464605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5464605).length < 2 ^ (prefixWord ++ tailWord_5464605).sum := by decide
  have hdescent : baseEnd_5464605 < baseStart_5464605 := by decide
  rcases family_descends (prefixWord ++ tailWord_5464605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5464625 : List Nat := [1, 2, 2, 3, 1, 1, 2, 5, 1, 1, 4]
def baseStart_5464625 : Nat := 118140960795 + 5464625 * 2 ^ 59
def prefixEnd_5464625 : Nat := 4983230072969 + 3 ^ 40 * 5464625 * 2
def baseEnd_5464625 : Nat := 2805979221575787363256153

theorem tailTrace_5464625 : CollatzResearch.WordTrace tailWord_5464625 prefixEnd_5464625 2805979221575787363256153 := by
  unfold tailWord_5464625
  simp only [CollatzResearch.WordTrace]
  refine ⟨199311247827604383492603329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132874165218402922328402219 199311247827604383492603329)
  ·
    refine ⟨149483435870703287619452497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199311247827604383492603329 149483435870703287619452497)
    ·
      refine ⟨112112576903027465714589373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149483435870703287619452497 112112576903027465714589373)
      ·
        refine ⟨42042216338635299642971015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112112576903027465714589373 42042216338635299642971015)
        ·
          refine ⟨63063324507952949464456523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42042216338635299642971015 63063324507952949464456523)
          ·
            refine ⟨94594986761929424196684785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63063324507952949464456523 94594986761929424196684785)
            ·
              refine ⟨70946240071447068147513589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94594986761929424196684785 70946240071447068147513589)
              ·
                refine ⟨6651210006698162638829399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70946240071447068147513589 6651210006698162638829399)
                ·
                  refine ⟨9976815010047243958244099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6651210006698162638829399 9976815010047243958244099)
                  ·
                    refine ⟨14965222515070865937366149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9976815010047243958244099 14965222515070865937366149)
                    ·
                      refine ⟨2805979221575787363256153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14965222515070865937366149 2805979221575787363256153)
                      ·
                        rfl

theorem cell23_5464625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_5464625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5464625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5464625 prefixEnd_5464625 := by exact prefixLift 5464625
  have htrace : WordTrace (prefixWord ++ tailWord_5464625) baseStart_5464625 baseEnd_5464625 := by
    simpa [prefixWord, tailWord_5464625, baseEnd_5464625] using wordTrace_append hprefix tailTrace_5464625
  have hstable : (prefixWord ++ tailWord_5464625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5464625).length < 2 ^ (prefixWord ++ tailWord_5464625).sum := by decide
  have hdescent : baseEnd_5464625 < baseStart_5464625 := by decide
  rcases family_descends (prefixWord ++ tailWord_5464625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5464636 : List Nat := [2, 2, 2, 2, 3, 1, 4, 2, 1, 1, 3]
def baseStart_5464636 : Nat := 118140960795 + 5464636 * 2 ^ 59
def prefixEnd_5464636 : Nat := 4983230072969 + 3 ^ 40 * 5464636 * 2
def baseEnd_5464636 : Nat := 2805984869862986820218603

theorem tailTrace_5464636 : CollatzResearch.WordTrace tailWord_5464636 prefixEnd_5464636 2805984869862986820218603 := by
  unfold tailWord_5464636
  simp only [CollatzResearch.WordTrace]
  refine ⟨99655824515282266185626881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132874432687043021580835841 99655824515282266185626881)
  ·
    refine ⟨74741868386461699639220161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99655824515282266185626881 74741868386461699639220161)
    ·
      refine ⟨56056401289846274729415121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74741868386461699639220161 56056401289846274729415121)
      ·
        refine ⟨42042300967384706047061341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56056401289846274729415121 42042300967384706047061341)
        ·
          refine ⟨15765862862769264767648003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42042300967384706047061341 15765862862769264767648003)
          ·
            refine ⟨23648794294153897151472005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15765862862769264767648003 23648794294153897151472005)
            ·
              refine ⟨4434148930153855715901001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23648794294153897151472005 4434148930153855715901001)
              ·
                refine ⟨3325611697615391786925751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4434148930153855715901001 3325611697615391786925751)
                ·
                  refine ⟨4988417546423087680388627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3325611697615391786925751 4988417546423087680388627)
                  ·
                    refine ⟨7482626319634631520582941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4988417546423087680388627 7482626319634631520582941)
                    ·
                      refine ⟨2805984869862986820218603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7482626319634631520582941 2805984869862986820218603)
                      ·
                        rfl

theorem cell23_5464636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 2, 1, 1, 3].length) (baseStart_5464636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5464636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5464636 prefixEnd_5464636 := by exact prefixLift 5464636
  have htrace : WordTrace (prefixWord ++ tailWord_5464636) baseStart_5464636 baseEnd_5464636 := by
    simpa [prefixWord, tailWord_5464636, baseEnd_5464636] using wordTrace_append hprefix tailTrace_5464636
  have hstable : (prefixWord ++ tailWord_5464636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5464636).length < 2 ^ (prefixWord ++ tailWord_5464636).sum := by decide
  have hdescent : baseEnd_5464636 < baseStart_5464636 := by decide
  rcases family_descends (prefixWord ++ tailWord_5464636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5464645 : List Nat := [1, 3, 1, 1, 1, 5, 1, 2, 3, 2, 3]
def baseStart_5464645 : Nat := 118140960795 + 5464645 * 2 ^ 59
def prefixEnd_5464645 : Nat := 4983230072969 + 3 ^ 40 * 5464645 * 2
def baseEnd_5464645 : Nat := 2805989491188877285006061

theorem tailTrace_5464645 : CollatzResearch.WordTrace tailWord_5464645 prefixEnd_5464645 2805989491188877285006061 := by
  unfold tailWord_5464645
  simp only [CollatzResearch.WordTrace]
  refine ⟨199311977287531926908331389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132874651525021284605554259 199311977287531926908331389)
  ·
    refine ⟨74741991482824472590624271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199311977287531926908331389 74741991482824472590624271)
    ·
      refine ⟨112112987224236708885936407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74741991482824472590624271 112112987224236708885936407)
      ·
        refine ⟨168169480836355063328904611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112112987224236708885936407 168169480836355063328904611)
        ·
          refine ⟨252254221254532594993356917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168169480836355063328904611 252254221254532594993356917)
          ·
            refine ⟨23648833242612430780627211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 252254221254532594993356917 23648833242612430780627211)
            ·
              refine ⟨35473249863918646170940817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23648833242612430780627211 35473249863918646170940817)
              ·
                refine ⟨26604937397938984628205613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35473249863918646170940817 26604937397938984628205613)
                ·
                  refine ⟨9976851524227119235577105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26604937397938984628205613 9976851524227119235577105)
                  ·
                    refine ⟨7482638643170339426682829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9976851524227119235577105 7482638643170339426682829)
                    ·
                      refine ⟨2805989491188877285006061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7482638643170339426682829 2805989491188877285006061)
                      ·
                        rfl

theorem cell23_5464645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 3, 2, 3].length) (baseStart_5464645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5464645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5464645 prefixEnd_5464645 := by exact prefixLift 5464645
  have htrace : WordTrace (prefixWord ++ tailWord_5464645) baseStart_5464645 baseEnd_5464645 := by
    simpa [prefixWord, tailWord_5464645, baseEnd_5464645] using wordTrace_append hprefix tailTrace_5464645
  have hstable : (prefixWord ++ tailWord_5464645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5464645).length < 2 ^ (prefixWord ++ tailWord_5464645).sum := by decide
  have hdescent : baseEnd_5464645 < baseStart_5464645 := by decide
  rcases family_descends (prefixWord ++ tailWord_5464645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5464675 : List Nat := [1, 1, 1, 5, 1, 2, 1, 4, 1, 3, 3]
def baseStart_5464675 : Nat := 118140960795 + 5464675 * 2 ^ 59
def prefixEnd_5464675 : Nat := 4983230072969 + 3 ^ 40 * 5464675 * 2
def baseEnd_5464675 : Nat := 2806004895608512167630923

theorem tailTrace_5464675 : CollatzResearch.WordTrace tailWord_5464675 prefixEnd_5464675 2806004895608512167630923 := by
  unfold tailWord_5464675
  simp only [CollatzResearch.WordTrace]
  refine ⟨199313071477423242031923479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132875380984948828021282319 199313071477423242031923479)
  ·
    refine ⟨298969607216134863047885219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199313071477423242031923479 298969607216134863047885219)
    ·
      refine ⟨448454410824202294571827829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298969607216134863047885219 448454410824202294571827829)
      ·
        refine ⟨42042601014768965116108859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 448454410824202294571827829 42042601014768965116108859)
        ·
          refine ⟨63063901522153447674163289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42042601014768965116108859 63063901522153447674163289)
          ·
            refine ⟨47297926141615085755622467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63063901522153447674163289 47297926141615085755622467)
            ·
              refine ⟨70946889212422628633433701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47297926141615085755622467 70946889212422628633433701)
              ·
                refine ⟨13302541727329242868768819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70946889212422628633433701 13302541727329242868768819)
                ·
                  refine ⟨19953812590993864303153229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13302541727329242868768819 19953812590993864303153229)
                  ·
                    refine ⟨7482679721622699113682461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19953812590993864303153229 7482679721622699113682461)
                    ·
                      refine ⟨2806004895608512167630923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7482679721622699113682461 2806004895608512167630923)
                      ·
                        rfl

theorem cell23_5464675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_5464675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5464675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5464675 prefixEnd_5464675 := by exact prefixLift 5464675
  have htrace : WordTrace (prefixWord ++ tailWord_5464675) baseStart_5464675 baseEnd_5464675 := by
    simpa [prefixWord, tailWord_5464675, baseEnd_5464675] using wordTrace_append hprefix tailTrace_5464675
  have hstable : (prefixWord ++ tailWord_5464675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5464675).length < 2 ^ (prefixWord ++ tailWord_5464675).sum := by decide
  have hdescent : baseEnd_5464675 < baseStart_5464675 := by decide
  rcases family_descends (prefixWord ++ tailWord_5464675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5464676 : List Nat := [2, 3, 1, 1, 2, 2, 4, 3, 1, 2, 2]
def baseStart_5464676 : Nat := 118140960795 + 5464676 * 2 ^ 59
def prefixEnd_5464676 : Nat := 4983230072969 + 3 ^ 40 * 5464676 * 2
def baseEnd_5464676 : Nat := 2806005409089166663718419

theorem tailTrace_5464676 : CollatzResearch.WordTrace tailWord_5464676 prefixEnd_5464676 2806005409089166663718419 := by
  unfold tailWord_5464676
  simp only [CollatzResearch.WordTrace]
  refine ⟨99656553975209809601354941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132875405300279746135139921 99656553975209809601354941)
  ·
    refine ⟨37371207740703678600508103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99656553975209809601354941 37371207740703678600508103)
    ·
      refine ⟨56056811611055517900762155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37371207740703678600508103 56056811611055517900762155)
      ·
        refine ⟨84085217416583276851143233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56056811611055517900762155 84085217416583276851143233)
        ·
          refine ⟨63063913062437457638357425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84085217416583276851143233 63063913062437457638357425)
          ·
            refine ⟨47297934796828093228768069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63063913062437457638357425 47297934796828093228768069)
            ·
              refine ⟨8868362774405267480394013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47297934796828093228768069 8868362774405267480394013)
              ·
                refine ⟨3325636040401975305147755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8868362774405267480394013 3325636040401975305147755)
                ·
                  refine ⟨4988454060602962957721633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3325636040401975305147755 4988454060602962957721633)
                  ·
                    refine ⟨3741340545452222218291225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4988454060602962957721633 3741340545452222218291225)
                    ·
                      refine ⟨2806005409089166663718419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3741340545452222218291225 2806005409089166663718419)
                      ·
                        rfl

theorem cell23_5464676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 3, 1, 2, 2].length) (baseStart_5464676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5464676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5464676 prefixEnd_5464676 := by exact prefixLift 5464676
  have htrace : WordTrace (prefixWord ++ tailWord_5464676) baseStart_5464676 baseEnd_5464676 := by
    simpa [prefixWord, tailWord_5464676, baseEnd_5464676] using wordTrace_append hprefix tailTrace_5464676
  have hstable : (prefixWord ++ tailWord_5464676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5464676).length < 2 ^ (prefixWord ++ tailWord_5464676).sum := by decide
  have hdescent : baseEnd_5464676 < baseStart_5464676 := by decide
  rcases family_descends (prefixWord ++ tailWord_5464676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5464706 : List Nat := [3, 4, 3, 1, 1, 1, 1, 1, 1, 1, 6]
def baseStart_5464706 : Nat := 118140960795 + 5464706 * 2 ^ 59
def prefixEnd_5464706 : Nat := 4983230072969 + 3 ^ 40 * 5464706 * 2
def baseEnd_5464706 : Nat := 2806020813508801546343281

theorem tailTrace_5464706 : CollatzResearch.WordTrace tailWord_5464706 prefixEnd_5464706 2806020813508801546343281 := by
  unfold tailWord_5464706
  simp only [CollatzResearch.WordTrace]
  refine ⟨49828550535077733581575493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132876134760207289550867981 49828550535077733581575493)
  ·
    refine ⟨9342853225327075046545405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49828550535077733581575493 9342853225327075046545405)
    ·
      refine ⟨3503569959497653142454527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9342853225327075046545405 3503569959497653142454527)
      ·
        refine ⟨5255354939246479713681791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3503569959497653142454527 5255354939246479713681791)
        ·
          refine ⟨7883032408869719570522687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5255354939246479713681791 7883032408869719570522687)
          ·
            refine ⟨11824548613304579355784031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7883032408869719570522687 11824548613304579355784031)
            ·
              refine ⟨17736822919956869033676047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11824548613304579355784031 17736822919956869033676047)
              ·
                refine ⟨26605234379935303550514071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17736822919956869033676047 26605234379935303550514071)
                ·
                  refine ⟨39907851569902955325771107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26605234379935303550514071 39907851569902955325771107)
                  ·
                    refine ⟨59861777354854432988656661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39907851569902955325771107 59861777354854432988656661)
                    ·
                      refine ⟨2806020813508801546343281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59861777354854432988656661 2806020813508801546343281)
                      ·
                        rfl

theorem cell23_5464706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_5464706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5464706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5464706 prefixEnd_5464706 := by exact prefixLift 5464706
  have htrace : WordTrace (prefixWord ++ tailWord_5464706) baseStart_5464706 baseEnd_5464706 := by
    simpa [prefixWord, tailWord_5464706, baseEnd_5464706] using wordTrace_append hprefix tailTrace_5464706
  have hstable : (prefixWord ++ tailWord_5464706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5464706).length < 2 ^ (prefixWord ++ tailWord_5464706).sum := by decide
  have hdescent : baseEnd_5464706 < baseStart_5464706 := by decide
  rcases family_descends (prefixWord ++ tailWord_5464706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5464755 : List Nat := [1, 1, 1, 2, 3, 4, 3, 1, 7]
def baseStart_5464755 : Nat := 118140960795 + 5464755 * 2 ^ 59
def prefixEnd_5464755 : Nat := 4983230072969 + 3 ^ 40 * 5464755 * 2
def baseEnd_5464755 : Nat := 311782886006763539403395

theorem tailTrace_5464755 : CollatzResearch.WordTrace tailWord_5464755 prefixEnd_5464755 311782886006763539403395 := by
  unfold tailWord_5464755
  simp only [CollatzResearch.WordTrace]
  refine ⟨199315989317133415694835719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132877326211422277129890479 199315989317133415694835719)
  ·
    refine ⟨298973983975700123542253579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199315989317133415694835719 298973983975700123542253579)
    ·
      refine ⟨448460975963550185313380369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298973983975700123542253579 448460975963550185313380369)
      ·
        refine ⟨336345731972662638985035277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 448460975963550185313380369 336345731972662638985035277)
        ·
          refine ⟨126129649489748489619388229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 336345731972662638985035277 126129649489748489619388229)
          ·
            refine ⟨23649309279327841803635293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126129649489748489619388229 23649309279327841803635293)
            ·
              refine ⟨8868490979747940676363235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23649309279327841803635293 8868490979747940676363235)
              ·
                refine ⟨13302736469621911014544853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8868490979747940676363235 13302736469621911014544853)
                ·
                  refine ⟨311782886006763539403395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13302736469621911014544853 311782886006763539403395)
                  ·
                    rfl

theorem cell23_5464755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 7].length) (baseStart_5464755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5464755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5464755 prefixEnd_5464755 := by exact prefixLift 5464755
  have htrace : WordTrace (prefixWord ++ tailWord_5464755) baseStart_5464755 baseEnd_5464755 := by
    simpa [prefixWord, tailWord_5464755, baseEnd_5464755] using wordTrace_append hprefix tailTrace_5464755
  have hstable : (prefixWord ++ tailWord_5464755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5464755).length < 2 ^ (prefixWord ++ tailWord_5464755).sum := by decide
  have hdescent : baseEnd_5464755 < baseStart_5464755 := by decide
  rcases family_descends (prefixWord ++ tailWord_5464755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5464766 : List Nat := [4, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2]
def baseStart_5464766 : Nat := 118140960795 + 5464766 * 2 ^ 59
def prefixEnd_5464766 : Nat := 4983230072969 + 3 ^ 40 * 5464766 * 2
def baseEnd_5464766 : Nat := 2806051622348071311593005

theorem tailTrace_5464766 : CollatzResearch.WordTrace tailWord_5464766 prefixEnd_5464766 2806051622348071311593005 := by
  unfold tailWord_5464766
  simp only [CollatzResearch.WordTrace]
  refine ⟨24914548815011695571685769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132877593680062376382324101 24914548815011695571685769)
  ·
    refine ⟨18685911611258771678764327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24914548815011695571685769 18685911611258771678764327)
    ·
      refine ⟨28028867416888157518146491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18685911611258771678764327 28028867416888157518146491)
      ·
        refine ⟨42043301125332236277219737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28028867416888157518146491 42043301125332236277219737)
        ·
          refine ⟨31532475843999177207914803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42043301125332236277219737 31532475843999177207914803)
          ·
            refine ⟨47298713765998765811872205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31532475843999177207914803 47298713765998765811872205)
            ·
              refine ⟨17737017662249537179452077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47298713765998765811872205 17737017662249537179452077)
              ·
                refine ⟨6651381623343576442294529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17737017662249537179452077 6651381623343576442294529)
                ·
                  refine ⟨4988536217507682331720897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6651381623343576442294529 4988536217507682331720897)
                  ·
                    refine ⟨3741402163130761748790673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4988536217507682331720897 3741402163130761748790673)
                    ·
                      refine ⟨2806051622348071311593005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3741402163130761748790673 2806051622348071311593005)
                      ·
                        rfl

theorem cell23_5464766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2].length) (baseStart_5464766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5464766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5464766 prefixEnd_5464766 := by exact prefixLift 5464766
  have htrace : WordTrace (prefixWord ++ tailWord_5464766) baseStart_5464766 baseEnd_5464766 := by
    simpa [prefixWord, tailWord_5464766, baseEnd_5464766] using wordTrace_append hprefix tailTrace_5464766
  have hstable : (prefixWord ++ tailWord_5464766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5464766).length < 2 ^ (prefixWord ++ tailWord_5464766).sum := by decide
  have hdescent : baseEnd_5464766 < baseStart_5464766 := by decide
  rcases family_descends (prefixWord ++ tailWord_5464766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5464822 : List Nat := [5, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4]
def baseStart_5464822 : Nat := 118140960795 + 5464822 * 2 ^ 59
def prefixEnd_5464822 : Nat := 4983230072969 + 3 ^ 40 * 5464822 * 2
def baseEnd_5464822 : Nat := 2806080377264723092492747

theorem tailTrace_5464822 : CollatzResearch.WordTrace tailWord_5464822 prefixEnd_5464822 2806080377264723092492747 := by
  unfold tailWord_5464822
  simp only [CollatzResearch.WordTrace]
  refine ⟨12457402062993167883595295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 132878955338593790758349813 12457402062993167883595295)
  ·
    refine ⟨18686103094489751825392943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12457402062993167883595295 18686103094489751825392943)
    ·
      refine ⟨28029154641734627738089415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18686103094489751825392943 28029154641734627738089415)
      ·
        refine ⟨42043731962601941607134123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28029154641734627738089415 42043731962601941607134123)
        ·
          refine ⟨63065597943902912410701185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42043731962601941607134123 63065597943902912410701185)
          ·
            refine ⟨47299198457927184308025889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63065597943902912410701185 47299198457927184308025889)
            ·
              refine ⟨35474398843445388231019417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47299198457927184308025889 35474398843445388231019417)
              ·
                refine ⟨26605799132584041173264563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35474398843445388231019417 26605799132584041173264563)
                ·
                  refine ⟨39908698698876061759896845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26605799132584041173264563 39908698698876061759896845)
                  ·
                    refine ⟨14965762012078523159961317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39908698698876061759896845 14965762012078523159961317)
                    ·
                      refine ⟨2806080377264723092492747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14965762012078523159961317 2806080377264723092492747)
                      ·
                        rfl

theorem cell23_5464822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_5464822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5464822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5464822 prefixEnd_5464822 := by exact prefixLift 5464822
  have htrace : WordTrace (prefixWord ++ tailWord_5464822) baseStart_5464822 baseEnd_5464822 := by
    simpa [prefixWord, tailWord_5464822, baseEnd_5464822] using wordTrace_append hprefix tailTrace_5464822
  have hstable : (prefixWord ++ tailWord_5464822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5464822).length < 2 ^ (prefixWord ++ tailWord_5464822).sum := by decide
  have hdescent : baseEnd_5464822 < baseStart_5464822 := by decide
  rcases family_descends (prefixWord ++ tailWord_5464822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5464839 : List Nat := [1, 1, 4, 4, 1, 1, 3, 1, 2, 1, 4]
def baseStart_5464839 : Nat := 118140960795 + 5464839 * 2 ^ 59
def prefixEnd_5464839 : Nat := 4983230072969 + 3 ^ 40 * 5464839 * 2
def baseEnd_5464839 : Nat := 2806089106435849525980169

theorem tailTrace_5464839 : CollatzResearch.WordTrace tailWord_5464839 prefixEnd_5464839 2806089106435849525980169 := by
  unfold tailWord_5464839
  simp only [CollatzResearch.WordTrace]
  refine ⟨199319053048829098040893571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132879368699219398693929047 199319053048829098040893571)
  ·
    refine ⟨298978579573243647061340357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199319053048829098040893571 298978579573243647061340357)
    ·
      refine ⟨56058483669983183824001317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 298978579573243647061340357 56058483669983183824001317)
      ·
        refine ⟨10510965688121846967000247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56058483669983183824001317 10510965688121846967000247)
        ·
          refine ⟨15766448532182770450500371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10510965688121846967000247 15766448532182770450500371)
          ·
            refine ⟨23649672798274155675750557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15766448532182770450500371 23649672798274155675750557)
            ·
              refine ⟨8868627299352808378406459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23649672798274155675750557 8868627299352808378406459)
              ·
                refine ⟨13302940949029212567609689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8868627299352808378406459 13302940949029212567609689)
                ·
                  refine ⟨9977205711771909425707267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13302940949029212567609689 9977205711771909425707267)
                  ·
                    refine ⟨14965808567657864138560901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9977205711771909425707267 14965808567657864138560901)
                    ·
                      refine ⟨2806089106435849525980169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14965808567657864138560901 2806089106435849525980169)
                      ·
                        rfl

theorem cell23_5464839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_5464839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5464839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5464839 prefixEnd_5464839 := by exact prefixLift 5464839
  have htrace : WordTrace (prefixWord ++ tailWord_5464839) baseStart_5464839 baseEnd_5464839 := by
    simpa [prefixWord, tailWord_5464839, baseEnd_5464839] using wordTrace_append hprefix tailTrace_5464839
  have hstable : (prefixWord ++ tailWord_5464839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5464839).length < 2 ^ (prefixWord ++ tailWord_5464839).sum := by decide
  have hdescent : baseEnd_5464839 < baseStart_5464839 := by decide
  rcases family_descends (prefixWord ++ tailWord_5464839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5464842 : List Nat := [3, 1, 2, 2, 1, 2, 3, 1, 1, 4, 3]
def baseStart_5464842 : Nat := 118140960795 + 5464842 * 2 ^ 59
def prefixEnd_5464842 : Nat := 4983230072969 + 3 ^ 40 * 5464842 * 2
def baseEnd_5464842 : Nat := 2806090646877813014242655

theorem tailTrace_5464842 : CollatzResearch.WordTrace tailWord_5464842 prefixEnd_5464842 2806090646877813014242655 := by
  unfold tailWord_5464842
  simp only [CollatzResearch.WordTrace]
  refine ⟨49829790616954557388313195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132879441645212153035501853 49829790616954557388313195)
  ·
    refine ⟨74744685925431836082469793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49829790616954557388313195 74744685925431836082469793)
    ·
      refine ⟨56058514444073877061852345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74744685925431836082469793 56058514444073877061852345)
      ·
        refine ⟨42043885833055407796389259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56058514444073877061852345 42043885833055407796389259)
        ·
          refine ⟨63065828749583111694583889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42043885833055407796389259 63065828749583111694583889)
          ·
            refine ⟨47299371562187333770937917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63065828749583111694583889 47299371562187333770937917)
            ·
              refine ⟨17737264335820250164101719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47299371562187333770937917 17737264335820250164101719)
              ·
                refine ⟨26605896503730375246152579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17737264335820250164101719 26605896503730375246152579)
                ·
                  refine ⟨39908844755595562869228869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26605896503730375246152579 39908844755595562869228869)
                  ·
                    refine ⟨7482908391674168037980413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39908844755595562869228869 7482908391674168037980413)
                    ·
                      refine ⟨2806090646877813014242655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7482908391674168037980413 2806090646877813014242655)
                      ·
                        rfl

theorem cell23_5464842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_5464842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5464842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5464842 prefixEnd_5464842 := by exact prefixLift 5464842
  have htrace : WordTrace (prefixWord ++ tailWord_5464842) baseStart_5464842 baseEnd_5464842 := by
    simpa [prefixWord, tailWord_5464842, baseEnd_5464842] using wordTrace_append hprefix tailTrace_5464842
  have hstable : (prefixWord ++ tailWord_5464842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5464842).length < 2 ^ (prefixWord ++ tailWord_5464842).sum := by decide
  have hdescent : baseEnd_5464842 < baseStart_5464842 := by decide
  rcases family_descends (prefixWord ++ tailWord_5464842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5464849 : List Nat := [1, 2, 2, 1, 1, 3, 3, 5, 1, 4]
def baseStart_5464849 : Nat := 118140960795 + 5464849 * 2 ^ 59
def prefixEnd_5464849 : Nat := 4983230072969 + 3 ^ 40 * 5464849 * 2
def baseEnd_5464849 : Nat := 935364747080798162285041

theorem tailTrace_5464849 : CollatzResearch.WordTrace tailWord_5464849 prefixEnd_5464849 935364747080798162285041 := by
  unfold tailWord_5464849
  simp only [CollatzResearch.WordTrace]
  refine ⟨199319417778792869748757601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132879611852528579832505067 199319417778792869748757601)
  ·
    refine ⟨149489563334094652311568201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199319417778792869748757601 149489563334094652311568201)
    ·
      refine ⟨112117172500570989233676151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149489563334094652311568201 112117172500570989233676151)
      ·
        refine ⟨168175758750856483850514227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112117172500570989233676151 168175758750856483850514227)
        ·
          refine ⟨252263638126284725775771341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168175758750856483850514227 252263638126284725775771341)
          ·
            refine ⟨94598864297356772165914253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 252263638126284725775771341 94598864297356772165914253)
            ·
              refine ⟨35474574111508789562217845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94598864297356772165914253 35474574111508789562217845)
              ·
                refine ⟨3325741322953949021457923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35474574111508789562217845 3325741322953949021457923)
                ·
                  refine ⟨4988611984430923532186885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3325741322953949021457923 4988611984430923532186885)
                  ·
                    refine ⟨935364747080798162285041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4988611984430923532186885 935364747080798162285041)
                    ·
                      rfl

theorem cell23_5464849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 5, 1, 4].length) (baseStart_5464849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5464849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5464849 prefixEnd_5464849 := by exact prefixLift 5464849
  have htrace : WordTrace (prefixWord ++ tailWord_5464849) baseStart_5464849 baseEnd_5464849 := by
    simpa [prefixWord, tailWord_5464849, baseEnd_5464849] using wordTrace_append hprefix tailTrace_5464849
  have hstable : (prefixWord ++ tailWord_5464849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5464849).length < 2 ^ (prefixWord ++ tailWord_5464849).sum := by decide
  have hdescent : baseEnd_5464849 < baseStart_5464849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5464849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5464865 : List Nat := [1, 2, 3, 2, 1, 2, 1, 1, 1, 1, 8]
def baseStart_5464865 : Nat := 118140960795 + 5464865 * 2 ^ 59
def prefixEnd_5464865 : Nat := 4983230072969 + 3 ^ 40 * 5464865 * 2
def baseEnd_5464865 : Nat := 2806102456932866424255049

theorem tailTrace_5464865 : CollatzResearch.WordTrace tailWord_5464865 prefixEnd_5464865 2806102456932866424255049 := by
  unfold tailWord_5464865
  simp only [CollatzResearch.WordTrace]
  refine ⟨199320001346734904481340049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132880000897823269654226699 199320001346734904481340049)
  ·
    refine ⟨149490001010051178361005037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199320001346734904481340049 149490001010051178361005037)
    ·
      refine ⟨56058750378769191885376889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149490001010051178361005037 56058750378769191885376889)
      ·
        refine ⟨42044062784076893914032667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56058750378769191885376889 42044062784076893914032667)
        ·
          refine ⟨63066094176115340871049001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42044062784076893914032667 63066094176115340871049001)
          ·
            refine ⟨47299570632086505653286751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63066094176115340871049001 47299570632086505653286751)
            ·
              refine ⟨70949355948129758479930127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47299570632086505653286751 70949355948129758479930127)
              ·
                refine ⟨106424033922194637719895191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70949355948129758479930127 106424033922194637719895191)
                ·
                  refine ⟨159636050883291956579842787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106424033922194637719895191 159636050883291956579842787)
                  ·
                    refine ⟨239454076324937934869764181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 159636050883291956579842787 239454076324937934869764181)
                    ·
                      refine ⟨2806102456932866424255049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 239454076324937934869764181 2806102456932866424255049)
                      ·
                        rfl

theorem cell23_5464865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_5464865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5464865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5464865 prefixEnd_5464865 := by exact prefixLift 5464865
  have htrace : WordTrace (prefixWord ++ tailWord_5464865) baseStart_5464865 baseEnd_5464865 := by
    simpa [prefixWord, tailWord_5464865, baseEnd_5464865] using wordTrace_append hprefix tailTrace_5464865
  have hstable : (prefixWord ++ tailWord_5464865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5464865).length < 2 ^ (prefixWord ++ tailWord_5464865).sum := by decide
  have hdescent : baseEnd_5464865 < baseStart_5464865 := by decide
  rcases family_descends (prefixWord ++ tailWord_5464865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5464866 : List Nat := [3, 3, 1, 1, 2, 2, 2, 4, 1, 4]
def baseStart_5464866 : Nat := 118140960795 + 5464866 * 2 ^ 59
def prefixEnd_5464866 : Nat := 4983230072969 + 3 ^ 40 * 5464866 * 2
def baseEnd_5464866 : Nat := 935367656804506973447515

theorem tailTrace_5464866 : CollatzResearch.WordTrace tailWord_5464866 prefixEnd_5464866 935367656804506973447515 := by
  unfold tailWord_5464866
  simp only [CollatzResearch.WordTrace]
  refine ⟨49830009454932820413031613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132880025213154187768084301 49830009454932820413031613)
  ·
    refine ⟨18686253545599807654886855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49830009454932820413031613 18686253545599807654886855)
    ·
      refine ⟨28029380318399711482330283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18686253545599807654886855 28029380318399711482330283)
      ·
        refine ⟨42044070477599567223495425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28029380318399711482330283 42044070477599567223495425)
        ·
          refine ⟨31533052858199675417621569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42044070477599567223495425 31533052858199675417621569)
          ·
            refine ⟨23649789643649756563216177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31533052858199675417621569 23649789643649756563216177)
            ·
              refine ⟨17737342232737317422412133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23649789643649756563216177 17737342232737317422412133)
              ·
                refine ⟨3325751668638247016702275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17737342232737317422412133 3325751668638247016702275)
                ·
                  refine ⟨4988627502957370525053413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3325751668638247016702275 4988627502957370525053413)
                  ·
                    refine ⟨935367656804506973447515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4988627502957370525053413 935367656804506973447515)
                    ·
                      rfl

theorem cell23_5464866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_5464866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5464866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5464866 prefixEnd_5464866 := by exact prefixLift 5464866
  have htrace : WordTrace (prefixWord ++ tailWord_5464866) baseStart_5464866 baseEnd_5464866 := by
    simpa [prefixWord, tailWord_5464866, baseEnd_5464866] using wordTrace_append hprefix tailTrace_5464866
  have hstable : (prefixWord ++ tailWord_5464866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5464866).length < 2 ^ (prefixWord ++ tailWord_5464866).sum := by decide
  have hdescent : baseEnd_5464866 < baseStart_5464866 := by decide
  rcases family_descends (prefixWord ++ tailWord_5464866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5464899 : List Nat := [1, 1, 1, 3, 1, 4, 2, 3, 2, 3, 2]
def baseStart_5464899 : Nat := 118140960795 + 5464899 * 2 ^ 59
def prefixEnd_5464899 : Nat := 4983230072969 + 3 ^ 40 * 5464899 * 2
def baseEnd_5464899 : Nat := 2806119915275119291229893

theorem tailTrace_5464899 : CollatzResearch.WordTrace tailWord_5464899 prefixEnd_5464899 2806119915275119291229893 := by
  unfold tailWord_5464899
  simp only [CollatzResearch.WordTrace]
  refine ⟨199321241428611728288077751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132880827619074485525385167 199321241428611728288077751)
  ·
    refine ⟨298981862142917592432116627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199321241428611728288077751 298981862142917592432116627)
    ·
      refine ⟨448472793214376388648174941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298981862142917592432116627 448472793214376388648174941)
      ·
        refine ⟨168177297455391145743065603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 448472793214376388648174941 168177297455391145743065603)
        ·
          refine ⟨252265946183086718614598405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168177297455391145743065603 252265946183086718614598405)
          ·
            refine ⟨47299864909328759740237201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 252265946183086718614598405 47299864909328759740237201)
            ·
              refine ⟨35474898681996569805177901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47299864909328759740237201 35474898681996569805177901)
              ·
                refine ⟨13303087005748713676941713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35474898681996569805177901 13303087005748713676941713)
                ·
                  refine ⟨9977315254311535257706285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13303087005748713676941713 9977315254311535257706285)
                  ·
                    refine ⟨3741493220366825721639857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9977315254311535257706285 3741493220366825721639857)
                    ·
                      refine ⟨2806119915275119291229893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3741493220366825721639857 2806119915275119291229893)
                      ·
                        rfl

theorem cell23_5464899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 2, 3, 2].length) (baseStart_5464899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5464899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5464899 prefixEnd_5464899 := by exact prefixLift 5464899
  have htrace : WordTrace (prefixWord ++ tailWord_5464899) baseStart_5464899 baseEnd_5464899 := by
    simpa [prefixWord, tailWord_5464899, baseEnd_5464899] using wordTrace_append hprefix tailTrace_5464899
  have hstable : (prefixWord ++ tailWord_5464899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5464899).length < 2 ^ (prefixWord ++ tailWord_5464899).sum := by decide
  have hdescent : baseEnd_5464899 < baseStart_5464899 := by decide
  rcases family_descends (prefixWord ++ tailWord_5464899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5464906 : List Nat := [3, 1, 2, 1, 1, 1, 2, 7, 1, 1, 3]
def baseStart_5464906 : Nat := 118140960795 + 5464906 * 2 ^ 59
def prefixEnd_5464906 : Nat := 4983230072969 + 3 ^ 40 * 5464906 * 2
def baseEnd_5464906 : Nat := 2806123509639700763842361

theorem tailTrace_5464906 : CollatzResearch.WordTrace tailWord_5464906 prefixEnd_5464906 2806123509639700763842361 := by
  unfold tailWord_5464906
  simp only [CollatzResearch.WordTrace]
  refine ⟨49830374184896592120895643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132880997826390912322388381 49830374184896592120895643)
  ·
    refine ⟨74745561277344888181343465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49830374184896592120895643 74745561277344888181343465)
    ·
      refine ⟨56059170958008666136007599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74745561277344888181343465 56059170958008666136007599)
      ·
        refine ⟨84088756437012999204011399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56059170958008666136007599 84088756437012999204011399)
        ·
          refine ⟨126133134655519498806017099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84088756437012999204011399 126133134655519498806017099)
          ·
            refine ⟨189199701983279248209025649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126133134655519498806017099 189199701983279248209025649)
            ·
              refine ⟨141899776487459436156769237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189199701983279248209025649 141899776487459436156769237)
              ·
                refine ⟨3325776011424830534924279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 141899776487459436156769237 3325776011424830534924279)
                ·
                  refine ⟨4988664017137245802386419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3325776011424830534924279 4988664017137245802386419)
                  ·
                    refine ⟨7482996025705868703579629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4988664017137245802386419 7482996025705868703579629)
                    ·
                      refine ⟨2806123509639700763842361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7482996025705868703579629 2806123509639700763842361)
                      ·
                        rfl

theorem cell23_5464906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 7, 1, 1, 3].length) (baseStart_5464906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5464906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5464906 prefixEnd_5464906 := by exact prefixLift 5464906
  have htrace : WordTrace (prefixWord ++ tailWord_5464906) baseStart_5464906 baseEnd_5464906 := by
    simpa [prefixWord, tailWord_5464906, baseEnd_5464906] using wordTrace_append hprefix tailTrace_5464906
  have hstable : (prefixWord ++ tailWord_5464906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5464906).length < 2 ^ (prefixWord ++ tailWord_5464906).sum := by decide
  have hdescent : baseEnd_5464906 < baseStart_5464906 := by decide
  rcases family_descends (prefixWord ++ tailWord_5464906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5464946 : List Nat := [3, 2, 1, 2, 1, 1, 2, 4, 3, 2, 2]
def baseStart_5464946 : Nat := 118140960795 + 5464946 * 2 ^ 59
def prefixEnd_5464946 : Nat := 4983230072969 + 3 ^ 40 * 5464946 * 2
def baseEnd_5464946 : Nat := 2806144048865880607342177

theorem tailTrace_5464946 : CollatzResearch.WordTrace tailWord_5464946 prefixEnd_5464946 2806144048865880607342177 := by
  unfold tailWord_5464946
  simp only [CollatzResearch.WordTrace]
  refine ⟨49830738914860363828759673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132881970439627636876692461 49830738914860363828759673)
  ·
    refine ⟨37373054186145272871569755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49830738914860363828759673 37373054186145272871569755)
    ·
      refine ⟨56059581279217909307354633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37373054186145272871569755 56059581279217909307354633)
      ·
        refine ⟨42044685959413431980515975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56059581279217909307354633 42044685959413431980515975)
        ·
          refine ⟨63067028939120147970773963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42044685959413431980515975 63067028939120147970773963)
          ·
            refine ⟨94600543408680221956160945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63067028939120147970773963 94600543408680221956160945)
            ·
              refine ⟨70950407556510166467120709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94600543408680221956160945 70950407556510166467120709)
              ·
                refine ⟨13303201416845656212585133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70950407556510166467120709 13303201416845656212585133)
                ·
                  refine ⟨4988700531317121079719425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13303201416845656212585133 4988700531317121079719425)
                  ·
                    refine ⟨3741525398487840809789569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4988700531317121079719425 3741525398487840809789569)
                    ·
                      refine ⟨2806144048865880607342177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3741525398487840809789569 2806144048865880607342177)
                      ·
                        rfl

theorem cell23_5464946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 3, 2, 2].length) (baseStart_5464946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5464946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5464946 prefixEnd_5464946 := by exact prefixLift 5464946
  have htrace : WordTrace (prefixWord ++ tailWord_5464946) baseStart_5464946 baseEnd_5464946 := by
    simpa [prefixWord, tailWord_5464946, baseEnd_5464946] using wordTrace_append hprefix tailTrace_5464946
  have hstable : (prefixWord ++ tailWord_5464946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5464946).length < 2 ^ (prefixWord ++ tailWord_5464946).sum := by decide
  have hdescent : baseEnd_5464946 < baseStart_5464946 := by decide
  rcases family_descends (prefixWord ++ tailWord_5464946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5464963 : List Nat := [1, 1, 1, 3, 4, 1, 2, 5, 1, 2, 2]
def baseStart_5464963 : Nat := 118140960795 + 5464963 * 2 ^ 59
def prefixEnd_5464963 : Nat := 4983230072969 + 3 ^ 40 * 5464963 * 2
def baseEnd_5464963 : Nat := 2806152778037007040829599

theorem tailTrace_5464963 : CollatzResearch.WordTrace tailWord_5464963 prefixEnd_5464963 2806152778037007040829599 := by
  unfold tailWord_5464963
  simp only [CollatzResearch.WordTrace]
  refine ⟨199323575700379867218407543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132882383800253244812271695 199323575700379867218407543)
  ·
    refine ⟨298985363550569800827611315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199323575700379867218407543 298985363550569800827611315)
    ·
      refine ⟨448478045325854701241416973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298985363550569800827611315 448478045325854701241416973)
      ·
        refine ⟨168179266997195512965531365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 448478045325854701241416973 168179266997195512965531365)
        ·
          refine ⟨31533612561974158681037131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 168179266997195512965531365 31533612561974158681037131)
          ·
            refine ⟨47300418842961238021555697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31533612561974158681037131 47300418842961238021555697)
            ·
              refine ⟨35475314132220928516166773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47300418842961238021555697 35475314132220928516166773)
              ·
                refine ⟨3325810699895712048390635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35475314132220928516166773 3325810699895712048390635)
                ·
                  refine ⟨4988716049843568072585953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3325810699895712048390635 4988716049843568072585953)
                  ·
                    refine ⟨3741537037382676054439465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4988716049843568072585953 3741537037382676054439465)
                    ·
                      refine ⟨2806152778037007040829599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3741537037382676054439465 2806152778037007040829599)
                      ·
                        rfl

theorem cell23_5464963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 5, 1, 2, 2].length) (baseStart_5464963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5464963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5464963 prefixEnd_5464963 := by exact prefixLift 5464963
  have htrace : WordTrace (prefixWord ++ tailWord_5464963) baseStart_5464963 baseEnd_5464963 := by
    simpa [prefixWord, tailWord_5464963, baseEnd_5464963] using wordTrace_append hprefix tailTrace_5464963
  have hstable : (prefixWord ++ tailWord_5464963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5464963).length < 2 ^ (prefixWord ++ tailWord_5464963).sum := by decide
  have hdescent : baseEnd_5464963 < baseStart_5464963 := by decide
  rcases family_descends (prefixWord ++ tailWord_5464963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5464980 : List Nat := [2, 4, 2, 1, 1, 1, 3, 4, 1, 2, 2]
def baseStart_5464980 : Nat := 118140960795 + 5464980 * 2 ^ 59
def prefixEnd_5464980 : Nat := 4983230072969 + 3 ^ 40 * 5464980 * 2
def baseEnd_5464980 : Nat := 2806161507208133474317021

theorem tailTrace_5464980 : CollatzResearch.WordTrace tailWord_5464980 prefixEnd_5464980 2806161507208133474317021 := by
  unfold tailWord_5464980
  simp only [CollatzResearch.WordTrace]
  refine ⟨99662097870659139560888197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132882797160878852747850929 99662097870659139560888197)
  ·
    refine ⟨18686643350748588667666537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99662097870659139560888197 18686643350748588667666537)
    ·
      refine ⟨14014982513061441500749903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18686643350748588667666537 14014982513061441500749903)
      ·
        refine ⟨21022473769592162251124855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14014982513061441500749903 21022473769592162251124855)
        ·
          refine ⟨31533710654388243376687283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21022473769592162251124855 31533710654388243376687283)
          ·
            refine ⟨47300565981582365065030925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31533710654388243376687283 47300565981582365065030925)
            ·
              refine ⟨17737712243093386899386597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47300565981582365065030925 17737712243093386899386597)
              ·
                refine ⟨3325821045580010043634987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17737712243093386899386597 3325821045580010043634987)
                ·
                  refine ⟨4988731568370015065452481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3325821045580010043634987 4988731568370015065452481)
                  ·
                    refine ⟨3741548676277511299089361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4988731568370015065452481 3741548676277511299089361)
                    ·
                      refine ⟨2806161507208133474317021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3741548676277511299089361 2806161507208133474317021)
                      ·
                        rfl

theorem cell23_5464980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_5464980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5464980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5464980 prefixEnd_5464980 := by exact prefixLift 5464980
  have htrace : WordTrace (prefixWord ++ tailWord_5464980) baseStart_5464980 baseEnd_5464980 := by
    simpa [prefixWord, tailWord_5464980, baseEnd_5464980] using wordTrace_append hprefix tailTrace_5464980
  have hstable : (prefixWord ++ tailWord_5464980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5464980).length < 2 ^ (prefixWord ++ tailWord_5464980).sum := by decide
  have hdescent : baseEnd_5464980 < baseStart_5464980 := by decide
  rcases family_descends (prefixWord ++ tailWord_5464980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5464986 : List Nat := [3, 1, 1, 4, 4, 1, 1, 8]
def baseStart_5464986 : Nat := 118140960795 + 5464986 * 2 ^ 59
def prefixEnd_5464986 : Nat := 4983230072969 + 3 ^ 40 * 5464986 * 2
def baseEnd_5464986 : Nat := 103932021781187424105259

theorem tailTrace_5464986 : CollatzResearch.WordTrace tailWord_5464986 prefixEnd_5464986 103932021781187424105259 := by
  unfold tailWord_5464986
  simp only [CollatzResearch.WordTrace]
  refine ⟨49831103644824135536623703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132882943052864361430996541 49831103644824135536623703)
  ·
    refine ⟨74746655467236203304935555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49831103644824135536623703 74746655467236203304935555)
    ·
      refine ⟨112119983200854304957403333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74746655467236203304935555 112119983200854304957403333)
      ·
        refine ⟨21022496850160182179513125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112119983200854304957403333 21022496850160182179513125)
        ·
          refine ⟨3941718159405034158658711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21022496850160182179513125 3941718159405034158658711)
          ·
            refine ⟨5912577239107551237988067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3941718159405034158658711 5912577239107551237988067)
            ·
              refine ⟨8868865858661326856982101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5912577239107551237988067 8868865858661326856982101)
              ·
                refine ⟨103932021781187424105259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8868865858661326856982101 103932021781187424105259)
                ·
                  rfl

theorem cell23_5464986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 8].length) (baseStart_5464986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5464986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5464986 prefixEnd_5464986 := by exact prefixLift 5464986
  have htrace : WordTrace (prefixWord ++ tailWord_5464986) baseStart_5464986 baseEnd_5464986 := by
    simpa [prefixWord, tailWord_5464986, baseEnd_5464986] using wordTrace_append hprefix tailTrace_5464986
  have hstable : (prefixWord ++ tailWord_5464986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5464986).length < 2 ^ (prefixWord ++ tailWord_5464986).sum := by decide
  have hdescent : baseEnd_5464986 < baseStart_5464986 := by decide
  rcases family_descends (prefixWord ++ tailWord_5464986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5464996 : List Nat := [2, 3, 1, 2, 1, 2, 1, 5, 2, 1, 3]
def baseStart_5464996 : Nat := 118140960795 + 5464996 * 2 ^ 59
def prefixEnd_5464996 : Nat := 4983230072969 + 3 ^ 40 * 5464996 * 2
def baseEnd_5464996 : Nat := 2806169722898605411716947

theorem tailTrace_5464996 : CollatzResearch.WordTrace tailWord_5464996 prefixEnd_5464996 2806169722898605411716947 := by
  unfold tailWord_5464996
  simp only [CollatzResearch.WordTrace]
  refine ⟨99662389654630156927179421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132883186206173542569572561 99662389654630156927179421)
  ·
    refine ⟨37373396120486308847692283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99662389654630156927179421 37373396120486308847692283)
    ·
      refine ⟨56060094180729463271538425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37373396120486308847692283 56060094180729463271538425)
      ·
        refine ⟨42045070635547097453653819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56060094180729463271538425 42045070635547097453653819)
        ·
          refine ⟨63067605953320646180480729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42045070635547097453653819 63067605953320646180480729)
          ·
            refine ⟨47300704464990484635360547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63067605953320646180480729 47300704464990484635360547)
            ·
              refine ⟨70951056697485726953040821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47300704464990484635360547 70951056697485726953040821)
              ·
                refine ⟨6651661565389286901847577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70951056697485726953040821 6651661565389286901847577)
                ·
                  refine ⟨4988746174041965176385683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6651661565389286901847577 4988746174041965176385683)
                  ·
                    refine ⟨7483119261062947764578525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4988746174041965176385683 7483119261062947764578525)
                    ·
                      refine ⟨2806169722898605411716947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7483119261062947764578525 2806169722898605411716947)
                      ·
                        rfl

theorem cell23_5464996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_5464996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5464996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5464996 prefixEnd_5464996 := by exact prefixLift 5464996
  have htrace : WordTrace (prefixWord ++ tailWord_5464996) baseStart_5464996 baseEnd_5464996 := by
    simpa [prefixWord, tailWord_5464996, baseEnd_5464996] using wordTrace_append hprefix tailTrace_5464996
  have hstable : (prefixWord ++ tailWord_5464996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5464996).length < 2 ^ (prefixWord ++ tailWord_5464996).sum := by decide
  have hdescent : baseEnd_5464996 < baseStart_5464996 := by decide
  rcases family_descends (prefixWord ++ tailWord_5464996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5465014 : List Nat := [5, 1, 4, 1, 1, 2, 2, 1, 1, 1, 4]
def baseStart_5465014 : Nat := 118140960795 + 5465014 * 2 ^ 59
def prefixEnd_5465014 : Nat := 4983230072969 + 3 ^ 40 * 5465014 * 2
def baseEnd_5465014 : Nat := 2806178965550386341291865

theorem tailTrace_5465014 : CollatzResearch.WordTrace tailWord_5465014 prefixEnd_5465014 2806178965550386341291865 := by
  unfold tailWord_5465014
  simp only [CollatzResearch.WordTrace]
  refine ⟨12457839738949693933032131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 132883623882130068619009397 12457839738949693933032131)
  ·
    refine ⟨18686759608424540899548197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12457839738949693933032131 18686759608424540899548197)
    ·
      refine ⟨3503767426579601418665287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18686759608424540899548197 3503767426579601418665287)
      ·
        refine ⟨5255651139869402127997931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3503767426579601418665287 5255651139869402127997931)
        ·
          refine ⟨7883476709804103191996897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5255651139869402127997931 7883476709804103191996897)
          ·
            refine ⟨5912607532353077393997673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7883476709804103191996897 5912607532353077393997673)
            ·
              refine ⟨4434455649264808045498255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5912607532353077393997673 4434455649264808045498255)
              ·
                refine ⟨6651683473897212068247383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4434455649264808045498255 6651683473897212068247383)
                ·
                  refine ⟨9977525210845818102371075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6651683473897212068247383 9977525210845818102371075)
                  ·
                    refine ⟨14966287816268727153556613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9977525210845818102371075 14966287816268727153556613)
                    ·
                      refine ⟨2806178965550386341291865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14966287816268727153556613 2806178965550386341291865)
                      ·
                        rfl

theorem cell23_5465014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_5465014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5465014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5465014 prefixEnd_5465014 := by exact prefixLift 5465014
  have htrace : WordTrace (prefixWord ++ tailWord_5465014) baseStart_5465014 baseEnd_5465014 := by
    simpa [prefixWord, tailWord_5465014, baseEnd_5465014] using wordTrace_append hprefix tailTrace_5465014
  have hstable : (prefixWord ++ tailWord_5465014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5465014).length < 2 ^ (prefixWord ++ tailWord_5465014).sum := by decide
  have hdescent : baseEnd_5465014 < baseStart_5465014 := by decide
  rcases family_descends (prefixWord ++ tailWord_5465014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5465046 : List Nat := [5, 2, 1, 1, 2, 1, 2, 1, 2, 6]
def baseStart_5465046 : Nat := 118140960795 + 5465046 * 2 ^ 59
def prefixEnd_5465046 : Nat := 4983230072969 + 3 ^ 40 * 5465046 * 2
def baseEnd_5465046 : Nat := 935398465643776738697239

theorem tailTrace_5465046 : CollatzResearch.WordTrace tailWord_5465046 prefixEnd_5465046 935398465643776738697239 := by
  unfold tailWord_5465046
  simp only [CollatzResearch.WordTrace]
  refine ⟨12457912684942448274604937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 132884401972719448262452661 12457912684942448274604937)
  ·
    refine ⟨9343434513706836205953703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12457912684942448274604937 9343434513706836205953703)
    ·
      refine ⟨14015151770560254308930555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9343434513706836205953703 14015151770560254308930555)
      ·
        refine ⟨21022727655840381463395833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14015151770560254308930555 21022727655840381463395833)
        ·
          refine ⟨15767045741880286097546875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21022727655840381463395833 15767045741880286097546875)
          ·
            refine ⟨23650568612820429146320313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15767045741880286097546875 23650568612820429146320313)
            ·
              refine ⟨17737926459615321859740235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23650568612820429146320313 17737926459615321859740235)
              ·
                refine ⟨26606889689422982789610353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17737926459615321859740235 26606889689422982789610353)
                ·
                  refine ⟨19955167267067237092207765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26606889689422982789610353 19955167267067237092207765)
                  ·
                    refine ⟨935398465643776738697239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19955167267067237092207765 935398465643776738697239)
                    ·
                      rfl

theorem cell23_5465046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_5465046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5465046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5465046 prefixEnd_5465046 := by exact prefixLift 5465046
  have htrace : WordTrace (prefixWord ++ tailWord_5465046) baseStart_5465046 baseEnd_5465046 := by
    simpa [prefixWord, tailWord_5465046, baseEnd_5465046] using wordTrace_append hprefix tailTrace_5465046
  have hstable : (prefixWord ++ tailWord_5465046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5465046).length < 2 ^ (prefixWord ++ tailWord_5465046).sum := by decide
  have hdescent : baseEnd_5465046 < baseStart_5465046 := by decide
  rcases family_descends (prefixWord ++ tailWord_5465046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5465049 : List Nat := [1, 2, 1, 2, 5, 1, 2, 1, 2, 2, 4]
def baseStart_5465049 : Nat := 118140960795 + 5465049 * 2 ^ 59
def prefixEnd_5465049 : Nat := 4983230072969 + 3 ^ 40 * 5465049 * 2
def baseEnd_5465049 : Nat := 2806196937373293704354203

theorem tailTrace_5465049 : CollatzResearch.WordTrace tailWord_5465049 prefixEnd_5465049 2806196937373293704354203 := by
  unfold tailWord_5465049
  simp only [CollatzResearch.WordTrace]
  refine ⟨199326712378068303906038201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132884474918712202604025467 199326712378068303906038201)
  ·
    refine ⟨149495034283551227929528651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199326712378068303906038201 149495034283551227929528651)
    ·
      refine ⟨224242551425326841894292977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149495034283551227929528651 224242551425326841894292977)
      ·
        refine ⟨168181913568995131420719733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224242551425326841894292977 168181913568995131420719733)
        ·
          refine ⟨15767054397093293570692475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 168181913568995131420719733 15767054397093293570692475)
          ·
            refine ⟨23650581595639940356038713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15767054397093293570692475 23650581595639940356038713)
            ·
              refine ⟨17737936196729955267029035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23650581595639940356038713 17737936196729955267029035)
              ·
                refine ⟨26606904295094932900543553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17737936196729955267029035 26606904295094932900543553)
                ·
                  refine ⟨19955178221321199675407665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26606904295094932900543553 19955178221321199675407665)
                  ·
                    refine ⟨14966383665990899756555749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19955178221321199675407665 14966383665990899756555749)
                    ·
                      refine ⟨2806196937373293704354203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14966383665990899756555749 2806196937373293704354203)
                      ·
                        rfl

theorem cell23_5465049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 2, 4].length) (baseStart_5465049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5465049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5465049 prefixEnd_5465049 := by exact prefixLift 5465049
  have htrace : WordTrace (prefixWord ++ tailWord_5465049) baseStart_5465049 baseEnd_5465049 := by
    simpa [prefixWord, tailWord_5465049, baseEnd_5465049] using wordTrace_append hprefix tailTrace_5465049
  have hstable : (prefixWord ++ tailWord_5465049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5465049).length < 2 ^ (prefixWord ++ tailWord_5465049).sum := by decide
  have hdescent : baseEnd_5465049 < baseStart_5465049 := by decide
  rcases family_descends (prefixWord ++ tailWord_5465049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5465053 : List Nat := [1, 4, 3, 1, 2, 1, 3, 1, 1, 4, 2]
def baseStart_5465053 : Nat := 118140960795 + 5465053 * 2 ^ 59
def prefixEnd_5465053 : Nat := 4983230072969 + 3 ^ 40 * 5465053 * 2
def baseEnd_5465053 : Nat := 2806198991295911688704185

theorem tailTrace_5465053 : CollatzResearch.WordTrace tailWord_5465053 prefixEnd_5465053 2806198991295911688704185 := by
  unfold tailWord_5465053
  simp only [CollatzResearch.WordTrace]
  refine ⟨199326858270053812589183813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132884572180035875059455875 199326858270053812589183813)
  ·
    refine ⟨37373785925635089860471965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 199326858270053812589183813 37373785925635089860471965)
    ·
      refine ⟨14015169722113158697676987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37373785925635089860471965 14015169722113158697676987)
      ·
        refine ⟨21022754583169738046515481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14015169722113158697676987 21022754583169738046515481)
        ·
          refine ⟨15767065937377303534886611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21022754583169738046515481 15767065937377303534886611)
          ·
            refine ⟨23650598906065955302329917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15767065937377303534886611 23650598906065955302329917)
            ·
              refine ⟨8868974589774733238373719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23650598906065955302329917 8868974589774733238373719)
              ·
                refine ⟨13303461884662099857560579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8868974589774733238373719 13303461884662099857560579)
                ·
                  refine ⟨19955192826993149786340869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13303461884662099857560579 19955192826993149786340869)
                  ·
                    refine ⟨3741598655061215584938913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19955192826993149786340869 3741598655061215584938913)
                    ·
                      refine ⟨2806198991295911688704185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3741598655061215584938913 2806198991295911688704185)
                      ·
                        rfl

theorem cell23_5465053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_5465053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5465053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5465053 prefixEnd_5465053 := by exact prefixLift 5465053
  have htrace : WordTrace (prefixWord ++ tailWord_5465053) baseStart_5465053 baseEnd_5465053 := by
    simpa [prefixWord, tailWord_5465053, baseEnd_5465053] using wordTrace_append hprefix tailTrace_5465053
  have hstable : (prefixWord ++ tailWord_5465053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5465053).length < 2 ^ (prefixWord ++ tailWord_5465053).sum := by decide
  have hdescent : baseEnd_5465053 < baseStart_5465053 := by decide
  rcases family_descends (prefixWord ++ tailWord_5465053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5465082 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 3, 1, 7]
def baseStart_5465082 : Nat := 118140960795 + 5465082 * 2 ^ 59
def prefixEnd_5465082 : Nat := 4983230072969 + 3 ^ 40 * 5465082 * 2
def baseEnd_5465082 : Nat := 2806213882234892075241551

theorem tailTrace_5465082 : CollatzResearch.WordTrace tailWord_5465082 prefixEnd_5465082 2806213882234892075241551 := by
  unfold tailWord_5465082
  simp only [CollatzResearch.WordTrace]
  refine ⟨49831978996737187635497375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132885277324632500361326333 49831978996737187635497375)
  ·
    refine ⟨74747968495105781453246063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49831978996737187635497375 74747968495105781453246063)
    ·
      refine ⟨112121952742658672179869095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74747968495105781453246063 112121952742658672179869095)
      ·
        refine ⟨168182929113988008269803643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112121952742658672179869095 168182929113988008269803643)
        ·
          refine ⟨252274393670982012404705465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168182929113988008269803643 252274393670982012404705465)
          ·
            refine ⟨189205795253236509303529099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 252274393670982012404705465 189205795253236509303529099)
            ·
              refine ⟨283808692879854763955293649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189205795253236509303529099 283808692879854763955293649)
              ·
                refine ⟨212856519659891072966470237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 283808692879854763955293649 212856519659891072966470237)
                ·
                  refine ⟨79821194872459152362426339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 212856519659891072966470237 79821194872459152362426339)
                  ·
                    refine ⟨119731792308688728543639509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 79821194872459152362426339 119731792308688728543639509)
                    ·
                      refine ⟨2806213882234892075241551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 119731792308688728543639509 2806213882234892075241551)
                      ·
                        rfl

theorem cell23_5465082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 3, 1, 7].length) (baseStart_5465082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5465082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5465082 prefixEnd_5465082 := by exact prefixLift 5465082
  have htrace : WordTrace (prefixWord ++ tailWord_5465082) baseStart_5465082 baseEnd_5465082 := by
    simpa [prefixWord, tailWord_5465082, baseEnd_5465082] using wordTrace_append hprefix tailTrace_5465082
  have hstable : (prefixWord ++ tailWord_5465082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5465082).length < 2 ^ (prefixWord ++ tailWord_5465082).sum := by decide
  have hdescent : baseEnd_5465082 < baseStart_5465082 := by decide
  rcases family_descends (prefixWord ++ tailWord_5465082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5465089 : List Nat := [1, 2, 4, 1, 2, 2, 1, 1, 4, 5]
def baseStart_5465089 : Nat := 118140960795 + 5465089 * 2 ^ 59
def prefixEnd_5465089 : Nat := 4983230072969 + 3 ^ 40 * 5465089 * 2
def baseEnd_5465089 : Nat := 935405825533157849284673

theorem tailTrace_5465089 : CollatzResearch.WordTrace tailWord_5465089 prefixEnd_5465089 935405825533157849284673 := by
  unfold tailWord_5465089
  simp only [CollatzResearch.WordTrace]
  refine ⟨199328171297923390737494321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132885447531948927158329547 199328171297923390737494321)
  ·
    refine ⟨149496128473442543053120741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199328171297923390737494321 149496128473442543053120741)
    ·
      refine ⟨28030524088770476822460139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149496128473442543053120741 28030524088770476822460139)
      ·
        refine ⟨42045786133155715233690209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28030524088770476822460139 42045786133155715233690209)
        ·
          refine ⟨31534339599866786425267657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42045786133155715233690209 31534339599866786425267657)
          ·
            refine ⟨23650754699900089818950743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31534339599866786425267657 23650754699900089818950743)
            ·
              refine ⟨35476132049850134728426115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23650754699900089818950743 35476132049850134728426115)
              ·
                refine ⟨53214198074775202092639173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35476132049850134728426115 53214198074775202092639173)
                ·
                  refine ⟨9977662139020350392369845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53214198074775202092639173 9977662139020350392369845)
                  ·
                    refine ⟨935405825533157849284673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9977662139020350392369845 935405825533157849284673)
                    ·
                      rfl

theorem cell23_5465089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_5465089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5465089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5465089 prefixEnd_5465089 := by exact prefixLift 5465089
  have htrace : WordTrace (prefixWord ++ tailWord_5465089) baseStart_5465089 baseEnd_5465089 := by
    simpa [prefixWord, tailWord_5465089, baseEnd_5465089] using wordTrace_append hprefix tailTrace_5465089
  have hstable : (prefixWord ++ tailWord_5465089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5465089).length < 2 ^ (prefixWord ++ tailWord_5465089).sum := by decide
  have hdescent : baseEnd_5465089 < baseStart_5465089 := by decide
  rcases family_descends (prefixWord ++ tailWord_5465089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5465099 : List Nat := [1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 5]
def baseStart_5465099 : Nat := 118140960795 + 5465099 * 2 ^ 59
def prefixEnd_5465099 : Nat := 4983230072969 + 3 ^ 40 * 5465099 * 2
def baseEnd_5465099 : Nat := 2806222611406018508728973

theorem tailTrace_5465099 : CollatzResearch.WordTrace tailWord_5465099 prefixEnd_5465099 2806222611406018508728973 := by
  unfold tailWord_5465099
  simp only [CollatzResearch.WordTrace]
  refine ⟨199328536027887162445358351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132885690685258108296905567 199328536027887162445358351)
  ·
    refine ⟨298992804041830743668037527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199328536027887162445358351 298992804041830743668037527)
    ·
      refine ⟨448489206062746115502056291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298992804041830743668037527 448489206062746115502056291)
      ·
        refine ⟨672733809094119173253084437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 448489206062746115502056291 672733809094119173253084437)
        ·
          refine ⟨31534397301286836246238333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 672733809094119173253084437 31534397301286836246238333)
          ·
            refine ⟨11825398987982563592339375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31534397301286836246238333 11825398987982563592339375)
            ·
              refine ⟨17738098481973845388509063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11825398987982563592339375 17738098481973845388509063)
              ·
                refine ⟨26607147722960768082763595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17738098481973845388509063 26607147722960768082763595)
                ·
                  refine ⟨39910721584441152124145393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26607147722960768082763595 39910721584441152124145393)
                  ·
                    refine ⟨29933041188330864093109045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39910721584441152124145393 29933041188330864093109045)
                    ·
                      refine ⟨2806222611406018508728973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29933041188330864093109045 2806222611406018508728973)
                      ·
                        rfl

theorem cell23_5465099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 5].length) (baseStart_5465099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5465099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5465099 prefixEnd_5465099 := by exact prefixLift 5465099
  have htrace : WordTrace (prefixWord ++ tailWord_5465099) baseStart_5465099 baseEnd_5465099 := by
    simpa [prefixWord, tailWord_5465099, baseEnd_5465099] using wordTrace_append hprefix tailTrace_5465099
  have hstable : (prefixWord ++ tailWord_5465099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5465099).length < 2 ^ (prefixWord ++ tailWord_5465099).sum := by decide
  have hdescent : baseEnd_5465099 < baseStart_5465099 := by decide
  rcases family_descends (prefixWord ++ tailWord_5465099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5465146 : List Nat := [3, 1, 1, 1, 3, 1, 4, 2, 2, 2, 3]
def baseStart_5465146 : Nat := 118140960795 + 5465146 * 2 ^ 59
def prefixEnd_5465146 : Nat := 4983230072969 + 3 ^ 40 * 5465146 * 2
def baseEnd_5465146 : Nat := 2806246744996779824841257

theorem tailTrace_5465146 : CollatzResearch.WordTrace tailWord_5465146 prefixEnd_5465146 2806246744996779824841257 := by
  unfold tailWord_5465146
  simp only [CollatzResearch.WordTrace]
  refine ⟨49832562564679222368079823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132886833505811259648212861 49832562564679222368079823)
  ·
    refine ⟨74748843847018833552119735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49832562564679222368079823 74748843847018833552119735)
    ·
      refine ⟨112123265770528250328179603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74748843847018833552119735 112123265770528250328179603)
      ·
        refine ⟨168184898655792375492269405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112123265770528250328179603 168184898655792375492269405)
        ·
          refine ⟨63069336995922140809601027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168184898655792375492269405 63069336995922140809601027)
          ·
            refine ⟨94604005493883211214401541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63069336995922140809601027 94604005493883211214401541)
            ·
              refine ⟨17738251030103102102700289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94604005493883211214401541 17738251030103102102700289)
              ·
                refine ⟨13303688272577326577025217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17738251030103102102700289 13303688272577326577025217)
                ·
                  refine ⟨9977766204432994932768913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13303688272577326577025217 9977766204432994932768913)
                  ·
                    refine ⟨7483324653324746199576685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9977766204432994932768913 7483324653324746199576685)
                    ·
                      refine ⟨2806246744996779824841257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7483324653324746199576685 2806246744996779824841257)
                      ·
                        rfl

theorem cell23_5465146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 2, 2, 3].length) (baseStart_5465146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5465146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5465146 prefixEnd_5465146 := by exact prefixLift 5465146
  have htrace : WordTrace (prefixWord ++ tailWord_5465146) baseStart_5465146 baseEnd_5465146 := by
    simpa [prefixWord, tailWord_5465146, baseEnd_5465146] using wordTrace_append hprefix tailTrace_5465146
  have hstable : (prefixWord ++ tailWord_5465146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5465146).length < 2 ^ (prefixWord ++ tailWord_5465146).sum := by decide
  have hdescent : baseEnd_5465146 < baseStart_5465146 := by decide
  rcases family_descends (prefixWord ++ tailWord_5465146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5465196 : List Nat := [2, 2, 1, 1, 3, 2, 3, 3, 1, 5]
def baseStart_5465196 : Nat := 118140960795 + 5465196 * 2 ^ 59
def prefixEnd_5465196 : Nat := 4983230072969 + 3 ^ 40 * 5465196 * 2
def baseEnd_5465196 : Nat := 935424139676501543072009

theorem tailTrace_5465196 : CollatzResearch.WordTrace tailWord_5465196 prefixEnd_5465196 935424139676501543072009 := by
  unfold tailWord_5465196
  simp only [CollatzResearch.WordTrace]
  refine ⟨99666036954267874005819721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132888049272357165341092961 99666036954267874005819721)
  ·
    refine ⟨74749527715700905504364791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99666036954267874005819721 74749527715700905504364791)
    ·
      refine ⟨112124291573551358256547187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74749527715700905504364791 112124291573551358256547187)
      ·
        refine ⟨168186437360327037384820781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112124291573551358256547187 168186437360327037384820781)
        ·
          refine ⟨63069914010122639019307793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168186437360327037384820781 63069914010122639019307793)
          ·
            refine ⟨47302435507591979264480845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63069914010122639019307793 47302435507591979264480845)
            ·
              refine ⟨17738413315346992224180317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47302435507591979264480845 17738413315346992224180317)
              ·
                refine ⟨6651904993255122084067619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17738413315346992224180317 6651904993255122084067619)
                ·
                  refine ⟨9977857489882683126101429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6651904993255122084067619 9977857489882683126101429)
                  ·
                    refine ⟨935424139676501543072009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9977857489882683126101429 935424139676501543072009)
                    ·
                      rfl

theorem cell23_5465196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 5].length) (baseStart_5465196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5465196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5465196 prefixEnd_5465196 := by exact prefixLift 5465196
  have htrace : WordTrace (prefixWord ++ tailWord_5465196) baseStart_5465196 baseEnd_5465196 := by
    simpa [prefixWord, tailWord_5465196, baseEnd_5465196] using wordTrace_append hprefix tailTrace_5465196
  have hstable : (prefixWord ++ tailWord_5465196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5465196).length < 2 ^ (prefixWord ++ tailWord_5465196).sum := by decide
  have hdescent : baseEnd_5465196 < baseStart_5465196 := by decide
  rcases family_descends (prefixWord ++ tailWord_5465196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5465253 : List Nat := [1, 3, 1, 2, 1, 4, 2, 3, 1, 2, 3]
def baseStart_5465253 : Nat := 118140960795 + 5465253 * 2 ^ 59
def prefixEnd_5465253 : Nat := 4983230072969 + 3 ^ 40 * 5465253 * 2
def baseEnd_5465253 : Nat := 2806301687426810906203265

theorem tailTrace_5465253 : CollatzResearch.WordTrace tailWord_5465253 prefixEnd_5465253 2806301687426810906203265 := by
  unfold tailWord_5465253
  simp only [CollatzResearch.WordTrace]
  refine ⟨199334152869329246746464413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132889435246219497830976275 199334152869329246746464413)
  ·
    refine ⟨74750307325998467529924155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199334152869329246746464413 74750307325998467529924155)
    ·
      refine ⟨112125460988997701294886233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74750307325998467529924155 112125460988997701294886233)
      ·
        refine ⟨84094095741748275971164675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112125460988997701294886233 84094095741748275971164675)
        ·
          refine ⟨126141143612622413956747013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84094095741748275971164675 126141143612622413956747013)
          ·
            refine ⟨23651464427366702616890065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126141143612622413956747013 23651464427366702616890065)
            ·
              refine ⟨17738598320525026962667549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23651464427366702616890065 17738598320525026962667549)
              ·
                refine ⟨6651974370196885111000331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17738598320525026962667549 6651974370196885111000331)
                ·
                  refine ⟨9977961555295327666500497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6651974370196885111000331 9977961555295327666500497)
                  ·
                    refine ⟨7483471166471495749875373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9977961555295327666500497 7483471166471495749875373)
                    ·
                      refine ⟨2806301687426810906203265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7483471166471495749875373 2806301687426810906203265)
                      ·
                        rfl

theorem cell23_5465253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 3, 1, 2, 3].length) (baseStart_5465253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5465253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5465253 prefixEnd_5465253 := by exact prefixLift 5465253
  have htrace : WordTrace (prefixWord ++ tailWord_5465253) baseStart_5465253 baseEnd_5465253 := by
    simpa [prefixWord, tailWord_5465253, baseEnd_5465253] using wordTrace_append hprefix tailTrace_5465253
  have hstable : (prefixWord ++ tailWord_5465253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5465253).length < 2 ^ (prefixWord ++ tailWord_5465253).sum := by decide
  have hdescent : baseEnd_5465253 < baseStart_5465253 := by decide
  rcases family_descends (prefixWord ++ tailWord_5465253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5465299 : List Nat := [1, 1, 1, 2, 1, 1, 1, 6, 1, 8]
def baseStart_5465299 : Nat := 118140960795 + 5465299 * 2 ^ 59
def prefixEnd_5465299 : Nat := 4983230072969 + 3 ^ 40 * 5465299 * 2
def baseEnd_5465299 : Nat := 935441769178972575409351

theorem tailTrace_5465299 : CollatzResearch.WordTrace tailWord_5465299 prefixEnd_5465299 935441769178972575409351 := by
  unfold tailWord_5465299
  simp only [CollatzResearch.WordTrace]
  refine ⟨199335830627162596602638951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132890553751441731068425967 199335830627162596602638951)
  ·
    refine ⟨299003745940743894903958427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199335830627162596602638951 299003745940743894903958427)
    ·
      refine ⟨448505618911115842355937641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299003745940743894903958427 448505618911115842355937641)
      ·
        refine ⟨336379214183336881766953231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 448505618911115842355937641 336379214183336881766953231)
        ·
          refine ⟨504568821275005322650429847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 336379214183336881766953231 504568821275005322650429847)
          ·
            refine ⟨756853231912507983975644771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 504568821275005322650429847 756853231912507983975644771)
            ·
              refine ⟨1135279847868761975963467157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 756853231912507983975644771 1135279847868761975963467157)
              ·
                refine ⟨53216242868848217623287523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1135279847868761975963467157 53216242868848217623287523)
                ·
                  refine ⟨79824364303272326434931285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53216242868848217623287523 79824364303272326434931285)
                  ·
                    refine ⟨935441769178972575409351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 79824364303272326434931285 935441769178972575409351)
                    ·
                      rfl

theorem cell23_5465299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 8].length) (baseStart_5465299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5465299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5465299 prefixEnd_5465299 := by exact prefixLift 5465299
  have htrace : WordTrace (prefixWord ++ tailWord_5465299) baseStart_5465299 baseEnd_5465299 := by
    simpa [prefixWord, tailWord_5465299, baseEnd_5465299] using wordTrace_append hprefix tailTrace_5465299
  have hstable : (prefixWord ++ tailWord_5465299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5465299).length < 2 ^ (prefixWord ++ tailWord_5465299).sum := by decide
  have hdescent : baseEnd_5465299 < baseStart_5465299 := by decide
  rcases family_descends (prefixWord ++ tailWord_5465299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5465317 : List Nat := [1, 3, 1, 4, 3, 1, 2, 2, 2, 1, 3]
def baseStart_5465317 : Nat := 118140960795 + 5465317 * 2 ^ 59
def prefixEnd_5465317 : Nat := 4983230072969 + 3 ^ 40 * 5465317 * 2
def baseEnd_5465317 : Nat := 2806334550188698655802971

theorem tailTrace_5465317 : CollatzResearch.WordTrace tailWord_5465317 prefixEnd_5465317 2806334550188698655802971 := by
  unfold tailWord_5465317
  simp only [CollatzResearch.WordTrace]
  refine ⟨199336487141097385676794205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132890991427398257117862803 199336487141097385676794205)
  ·
    refine ⟨74751182677911519628797827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199336487141097385676794205 74751182677911519628797827)
    ·
      refine ⟨112126774016867279443196741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74751182677911519628797827 112126774016867279443196741)
      ·
        refine ⟨21023770128162614895599389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112126774016867279443196741 21023770128162614895599389)
        ·
          refine ⟨7883913798060980585849771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21023770128162614895599389 7883913798060980585849771)
          ·
            refine ⟨11825870697091470878774657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7883913798060980585849771 11825870697091470878774657)
            ·
              refine ⟨8869403022818603159080993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11825870697091470878774657 8869403022818603159080993)
              ·
                refine ⟨6652052267113952369310745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8869403022818603159080993 6652052267113952369310745)
                ·
                  refine ⟨4989039200335464276983059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6652052267113952369310745 4989039200335464276983059)
                  ·
                    refine ⟨7483558800503196415474589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4989039200335464276983059 7483558800503196415474589)
                    ·
                      refine ⟨2806334550188698655802971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7483558800503196415474589 2806334550188698655802971)
                      ·
                        rfl

theorem cell23_5465317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_5465317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5465317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5465317 prefixEnd_5465317 := by exact prefixLift 5465317
  have htrace : WordTrace (prefixWord ++ tailWord_5465317) baseStart_5465317 baseEnd_5465317 := by
    simpa [prefixWord, tailWord_5465317, baseEnd_5465317] using wordTrace_append hprefix tailTrace_5465317
  have hstable : (prefixWord ++ tailWord_5465317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5465317).length < 2 ^ (prefixWord ++ tailWord_5465317).sum := by decide
  have hdescent : baseEnd_5465317 < baseStart_5465317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5465317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5465326 : List Nat := [4, 1, 2, 1, 1, 1, 2, 2, 1, 3, 5]
def baseStart_5465326 : Nat := 118140960795 + 5465326 * 2 ^ 59
def prefixEnd_5465326 : Nat := 4983230072969 + 3 ^ 40 * 5465326 * 2
def baseEnd_5465326 : Nat := 2806339171514589120590429

theorem tailTrace_5465326 : CollatzResearch.WordTrace tailWord_5465326 prefixEnd_5465326 2806339171514589120590429 := by
  unfold tailWord_5465326
  simp only [CollatzResearch.WordTrace]
  refine ⟨24917101924758097526733979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132891210265376520142581221 24917101924758097526733979)
  ·
    refine ⟨37375652887137146290100969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24917101924758097526733979 37375652887137146290100969)
    ·
      refine ⟨28031739665352859717575727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37375652887137146290100969 28031739665352859717575727)
      ·
        refine ⟨42047609498029289576363591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28031739665352859717575727 42047609498029289576363591)
        ·
          refine ⟨63071414247043934364545387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42047609498029289576363591 63071414247043934364545387)
          ·
            refine ⟨94607121370565901546818081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63071414247043934364545387 94607121370565901546818081)
            ·
              refine ⟨70955341027924426160113561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94607121370565901546818081 70955341027924426160113561)
              ·
                refine ⟨53216505770943319620085171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70955341027924426160113561 53216505770943319620085171)
                ·
                  refine ⟨79824758656414979430127757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53216505770943319620085171 79824758656414979430127757)
                  ·
                    refine ⟨29934284496155617286297909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 79824758656414979430127757 29934284496155617286297909)
                    ·
                      refine ⟨2806339171514589120590429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29934284496155617286297909 2806339171514589120590429)
                      ·
                        rfl

theorem cell23_5465326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_5465326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5465326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5465326 prefixEnd_5465326 := by exact prefixLift 5465326
  have htrace : WordTrace (prefixWord ++ tailWord_5465326) baseStart_5465326 baseEnd_5465326 := by
    simpa [prefixWord, tailWord_5465326, baseEnd_5465326] using wordTrace_append hprefix tailTrace_5465326
  have hstable : (prefixWord ++ tailWord_5465326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5465326).length < 2 ^ (prefixWord ++ tailWord_5465326).sum := by decide
  have hdescent : baseEnd_5465326 < baseStart_5465326 := by decide
  rcases family_descends (prefixWord ++ tailWord_5465326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5465413 : List Nat := [1, 3, 1, 1, 1, 2, 1, 4, 1, 6, 2]
def baseStart_5465413 : Nat := 118140960795 + 5465413 * 2 ^ 59
def prefixEnd_5465413 : Nat := 4983230072969 + 3 ^ 40 * 5465413 * 2
def baseEnd_5465413 : Nat := 2806383844331530280202529

theorem tailTrace_5465413 : CollatzResearch.WordTrace tailWord_5465413 prefixEnd_5465413 2806383844331530280202529 := by
  unfold tailWord_5465413
  simp only [CollatzResearch.WordTrace]
  refine ⟨199339988548749594072288893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132893325699166396048192595 199339988548749594072288893)
  ·
    refine ⟨74752495705781097777108335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199339988548749594072288893 74752495705781097777108335)
    ·
      refine ⟨112128743558671646665662503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74752495705781097777108335 112128743558671646665662503)
      ·
        refine ⟨168193115338007469998493755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112128743558671646665662503 168193115338007469998493755)
        ·
          refine ⟨252289673007011204997740633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168193115338007469998493755 252289673007011204997740633)
          ·
            refine ⟨189217254755258403748305475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 252289673007011204997740633 189217254755258403748305475)
            ·
              refine ⟨283825882132887605622458213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189217254755258403748305475 283825882132887605622458213)
              ·
                refine ⟨53217352899916426054210915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 283825882132887605622458213 53217352899916426054210915)
                ·
                  refine ⟨79826029349874639081316373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53217352899916426054210915 79826029349874639081316373)
                  ·
                    refine ⟨3741845125775373706936705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 79826029349874639081316373 3741845125775373706936705)
                    ·
                      refine ⟨2806383844331530280202529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3741845125775373706936705 2806383844331530280202529)
                      ·
                        rfl

theorem cell23_5465413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 6, 2].length) (baseStart_5465413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5465413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5465413 prefixEnd_5465413 := by exact prefixLift 5465413
  have htrace : WordTrace (prefixWord ++ tailWord_5465413) baseStart_5465413 baseEnd_5465413 := by
    simpa [prefixWord, tailWord_5465413, baseEnd_5465413] using wordTrace_append hprefix tailTrace_5465413
  have hstable : (prefixWord ++ tailWord_5465413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5465413).length < 2 ^ (prefixWord ++ tailWord_5465413).sum := by decide
  have hdescent : baseEnd_5465413 < baseStart_5465413 := by decide
  rcases family_descends (prefixWord ++ tailWord_5465413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5465416 : List Nat := [2, 1, 3, 1, 1, 2, 1, 2, 2, 3, 5]
def baseStart_5465416 : Nat := 118140960795 + 5465416 * 2 ^ 59
def prefixEnd_5465416 : Nat := 4983230072969 + 3 ^ 40 * 5465416 * 2
def baseEnd_5465416 : Nat := 2806385384773493768465015

theorem tailTrace_5465416 : CollatzResearch.WordTrace tailWord_5465416 prefixEnd_5465416 2806385384773493768465015 := by
  unfold tailWord_5465416
  simp only [CollatzResearch.WordTrace]
  refine ⟨99670048983869362792324051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132893398645159150389765401 99670048983869362792324051)
  ·
    refine ⟨149505073475804044188486077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99670048983869362792324051 149505073475804044188486077)
    ·
      refine ⟨56064402553426516570682279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149505073475804044188486077 56064402553426516570682279)
      ·
        refine ⟨84096603830139774856023419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56064402553426516570682279 84096603830139774856023419)
        ·
          refine ⟨126144905745209662284035129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84096603830139774856023419 126144905745209662284035129)
          ·
            refine ⟨94608679308907246713026347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126144905745209662284035129 94608679308907246713026347)
            ·
              refine ⟨141913018963360870069539521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94608679308907246713026347 141913018963360870069539521)
              ·
                refine ⟨106434764222520652552154641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141913018963360870069539521 106434764222520652552154641)
                ·
                  refine ⟨79826073166890489414115981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106434764222520652552154641 79826073166890489414115981)
                  ·
                    refine ⟨29934777437583933530293493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 79826073166890489414115981 29934777437583933530293493)
                    ·
                      refine ⟨2806385384773493768465015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29934777437583933530293493 2806385384773493768465015)
                      ·
                        rfl

theorem cell23_5465416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_5465416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5465416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5465416 prefixEnd_5465416 := by exact prefixLift 5465416
  have htrace : WordTrace (prefixWord ++ tailWord_5465416) baseStart_5465416 baseEnd_5465416 := by
    simpa [prefixWord, tailWord_5465416, baseEnd_5465416] using wordTrace_append hprefix tailTrace_5465416
  have hstable : (prefixWord ++ tailWord_5465416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5465416).length < 2 ^ (prefixWord ++ tailWord_5465416).sum := by decide
  have hdescent : baseEnd_5465416 < baseStart_5465416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5465416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5465433 : List Nat := [1, 2, 1, 2, 2, 2, 3, 1, 4, 2, 3]
def baseStart_5465433 : Nat := 118140960795 + 5465433 * 2 ^ 59
def prefixEnd_5465433 : Nat := 4983230072969 + 3 ^ 40 * 5465433 * 2
def baseEnd_5465433 : Nat := 2806394113944620201952437

theorem tailTrace_5465433 : CollatzResearch.WordTrace tailWord_5465433 prefixEnd_5465433 2806394113944620201952437 := by
  unfold tailWord_5465433
  simp only [CollatzResearch.WordTrace]
  refine ⟨199340718008677137488016953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132893812005784758325344635 199340718008677137488016953)
  ·
    refine ⟨149505538506507853116012715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199340718008677137488016953 149505538506507853116012715)
    ·
      refine ⟨224258307759761779674019073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149505538506507853116012715 224258307759761779674019073)
      ·
        refine ⟨168193730819821334755514305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224258307759761779674019073 168193730819821334755514305)
        ·
          refine ⟨126145298114866001066635729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168193730819821334755514305 126145298114866001066635729)
          ·
            refine ⟨94608973586149500799976797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126145298114866001066635729 94608973586149500799976797)
            ·
              refine ⟨35478365094806062799991299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94608973586149500799976797 35478365094806062799991299)
              ·
                refine ⟨53217547642209094199986949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35478365094806062799991299 53217547642209094199986949)
                ·
                  refine ⟨9978290182914205162497553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53217547642209094199986949 9978290182914205162497553)
                  ·
                    refine ⟨7483717637185653871873165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9978290182914205162497553 7483717637185653871873165)
                    ·
                      refine ⟨2806394113944620201952437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7483717637185653871873165 2806394113944620201952437)
                      ·
                        rfl

theorem cell23_5465433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 4, 2, 3].length) (baseStart_5465433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5465433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5465433 prefixEnd_5465433 := by exact prefixLift 5465433
  have htrace : WordTrace (prefixWord ++ tailWord_5465433) baseStart_5465433 baseEnd_5465433 := by
    simpa [prefixWord, tailWord_5465433, baseEnd_5465433] using wordTrace_append hprefix tailTrace_5465433
  have hstable : (prefixWord ++ tailWord_5465433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5465433).length < 2 ^ (prefixWord ++ tailWord_5465433).sum := by decide
  have hdescent : baseEnd_5465433 < baseStart_5465433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5465433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5465440 : List Nat := [2, 1, 1, 3, 4, 1, 3, 1, 3, 4]
def baseStart_5465440 : Nat := 118140960795 + 5465440 * 2 ^ 59
def prefixEnd_5465440 : Nat := 4983230072969 + 3 ^ 40 * 5465440 * 2
def baseEnd_5465440 : Nat := 935465902769733891521635

theorem tailTrace_5465440 : CollatzResearch.WordTrace tailWord_5465440 prefixEnd_5465440 935465902769733891521635 := by
  unfold tailWord_5465440
  simp only [CollatzResearch.WordTrace]
  refine ⟨99670486659825888841760887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132893982213101185122347849 99670486659825888841760887)
  ·
    refine ⟨149505729989738833262641331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99670486659825888841760887 149505729989738833262641331)
    ·
      refine ⟨224258594984608249893961997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149505729989738833262641331 224258594984608249893961997)
      ·
        refine ⟨84096973119228093710235749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 224258594984608249893961997 84096973119228093710235749)
        ·
          refine ⟨15768182459855267570669203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84096973119228093710235749 15768182459855267570669203)
          ·
            refine ⟨23652273689782901356003805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15768182459855267570669203 23652273689782901356003805)
            ·
              refine ⟨8869602633668588008501427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23652273689782901356003805 8869602633668588008501427)
              ·
                refine ⟨13304403950502882012752141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8869602633668588008501427 13304403950502882012752141)
                ·
                  refine ⟨4989151481438580754782053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13304403950502882012752141 4989151481438580754782053)
                  ·
                    refine ⟨935465902769733891521635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4989151481438580754782053 935465902769733891521635)
                    ·
                      rfl

theorem cell23_5465440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 3, 4].length) (baseStart_5465440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5465440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5465440 prefixEnd_5465440 := by exact prefixLift 5465440
  have htrace : WordTrace (prefixWord ++ tailWord_5465440) baseStart_5465440 baseEnd_5465440 := by
    simpa [prefixWord, tailWord_5465440, baseEnd_5465440] using wordTrace_append hprefix tailTrace_5465440
  have hstable : (prefixWord ++ tailWord_5465440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5465440).length < 2 ^ (prefixWord ++ tailWord_5465440).sum := by decide
  have hdescent : baseEnd_5465440 < baseStart_5465440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5465440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5465466 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 2, 9]
def baseStart_5465466 : Nat := 118140960795 + 5465466 * 2 ^ 59
def prefixEnd_5465466 : Nat := 4983230072969 + 3 ^ 40 * 5465466 * 2
def baseEnd_5465466 : Nat := 935470352935406190946595

theorem tailTrace_5465466 : CollatzResearch.WordTrace tailWord_5465466 prefixEnd_5465466 935470352935406190946595 := by
  unfold tailWord_5465466
  simp only [CollatzResearch.WordTrace]
  refine ⟨49835480404389396030992063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132894614411705056082645501 49835480404389396030992063)
  ·
    refine ⟨74753220606584094046488095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49835480404389396030992063 74753220606584094046488095)
    ·
      refine ⟨112129830909876141069732143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74753220606584094046488095 112129830909876141069732143)
      ·
        refine ⟨168194746364814211604598215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112129830909876141069732143 168194746364814211604598215)
        ·
          refine ⟨252292119547221317406897323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168194746364814211604598215 252292119547221317406897323)
          ·
            refine ⟨378438179320831976110345985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252292119547221317406897323 378438179320831976110345985)
            ·
              refine ⟨283828634490623982082759489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 378438179320831976110345985 283828634490623982082759489)
              ·
                refine ⟨212871475867967986562069617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 283828634490623982082759489 212871475867967986562069617)
                ·
                  refine ⟨159653606900975989921552213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 212871475867967986562069617 159653606900975989921552213)
                  ·
                    refine ⟨935470352935406190946595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 159653606900975989921552213 935470352935406190946595)
                    ·
                      rfl

theorem cell23_5465466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 2, 9].length) (baseStart_5465466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5465466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5465466 prefixEnd_5465466 := by exact prefixLift 5465466
  have htrace : WordTrace (prefixWord ++ tailWord_5465466) baseStart_5465466 baseEnd_5465466 := by
    simpa [prefixWord, tailWord_5465466, baseEnd_5465466] using wordTrace_append hprefix tailTrace_5465466
  have hstable : (prefixWord ++ tailWord_5465466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5465466).length < 2 ^ (prefixWord ++ tailWord_5465466).sum := by decide
  have hdescent : baseEnd_5465466 < baseStart_5465466 := by decide
  rcases family_descends (prefixWord ++ tailWord_5465466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5465513 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 8, 4]
def baseStart_5465513 : Nat := 118140960795 + 5465513 * 2 ^ 59
def prefixEnd_5465513 : Nat := 4983230072969 + 3 ^ 40 * 5465513 * 2
def baseEnd_5465513 : Nat := 935478397465659962984023

theorem tailTrace_5465513 : CollatzResearch.WordTrace tailWord_5465513 prefixEnd_5465513 935478397465659962984023 := by
  unfold tailWord_5465513
  simp only [CollatzResearch.WordTrace]
  refine ⟨199343635848387311150929193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132895757232258207433952795 199343635848387311150929193)
  ·
    refine ⟨149507726886290483363196895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199343635848387311150929193 149507726886290483363196895)
    ·
      refine ⟨224261590329435725044795343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149507726886290483363196895 224261590329435725044795343)
      ·
        refine ⟨336392385494153587567193015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224261590329435725044795343 336392385494153587567193015)
        ·
          refine ⟨504588578241230381350789523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 336392385494153587567193015 504588578241230381350789523)
          ·
            refine ⟨756882867361845572026184285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 504588578241230381350789523 756882867361845572026184285)
            ·
              refine ⟨283831075260692089509819107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 756882867361845572026184285 283831075260692089509819107)
              ·
                refine ⟨425746612891038134264728661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 283831075260692089509819107 425746612891038134264728661)
                ·
                  refine ⟨4989218119816853135914789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 425746612891038134264728661 4989218119816853135914789)
                  ·
                    refine ⟨935478397465659962984023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4989218119816853135914789 935478397465659962984023)
                    ·
                      rfl

theorem cell23_5465513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 8, 4].length) (baseStart_5465513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5465513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5465513 prefixEnd_5465513 := by exact prefixLift 5465513
  have htrace : WordTrace (prefixWord ++ tailWord_5465513) baseStart_5465513 baseEnd_5465513 := by
    simpa [prefixWord, tailWord_5465513, baseEnd_5465513] using wordTrace_append hprefix tailTrace_5465513
  have hstable : (prefixWord ++ tailWord_5465513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5465513).length < 2 ^ (prefixWord ++ tailWord_5465513).sum := by decide
  have hdescent : baseEnd_5465513 < baseStart_5465513 := by decide
  rcases family_descends (prefixWord ++ tailWord_5465513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5465538 : List Nat := [3, 5, 2, 1, 1, 2, 1, 2, 6]
def baseStart_5465538 : Nat := 118140960795 + 5465538 * 2 ^ 59
def prefixEnd_5465538 : Nat := 4983230072969 + 3 ^ 40 * 5465538 * 2
def baseEnd_5465538 : Nat := 311827558823704699015495

theorem tailTrace_5465538 : CollatzResearch.WordTrace tailWord_5465538 prefixEnd_5465538 311827558823704699015495 := by
  unfold tailWord_5465538
  simp only [CollatzResearch.WordTrace]
  refine ⟨49836136918324185105147317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132896365115531160280392845 49836136918324185105147317)
  ·
    refine ⟨4672137836092892353607561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49836136918324185105147317 4672137836092892353607561)
    ·
      refine ⟨3504103377069669265205671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4672137836092892353607561 3504103377069669265205671)
      ·
        refine ⟨5256155065604503897808507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3504103377069669265205671 5256155065604503897808507)
        ·
          refine ⟨7884232598406755846712761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5256155065604503897808507 7884232598406755846712761)
          ·
            refine ⟨5913174448805066885034571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7884232598406755846712761 5913174448805066885034571)
            ·
              refine ⟨8869761673207600327551857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5913174448805066885034571 8869761673207600327551857)
              ·
                refine ⟨6652321254905700245663893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8869761673207600327551857 6652321254905700245663893)
                ·
                  refine ⟨311827558823704699015495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6652321254905700245663893 311827558823704699015495)
                  ·
                    rfl

theorem cell23_5465538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_5465538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5465538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5465538 prefixEnd_5465538 := by exact prefixLift 5465538
  have htrace : WordTrace (prefixWord ++ tailWord_5465538) baseStart_5465538 baseEnd_5465538 := by
    simpa [prefixWord, tailWord_5465538, baseEnd_5465538] using wordTrace_append hprefix tailTrace_5465538
  have hstable : (prefixWord ++ tailWord_5465538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5465538).length < 2 ^ (prefixWord ++ tailWord_5465538).sum := by decide
  have hdescent : baseEnd_5465538 < baseStart_5465538 := by decide
  rcases family_descends (prefixWord ++ tailWord_5465538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5465553 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 2, 7, 3]
def baseStart_5465553 : Nat := 118140960795 + 5465553 * 2 ^ 59
def prefixEnd_5465553 : Nat := 4983230072969 + 3 ^ 40 * 5465553 * 2
def baseEnd_5465553 : Nat := 2806455731623159732451885

theorem tailTrace_5465553 : CollatzResearch.WordTrace tailWord_5465553 prefixEnd_5465553 2806455731623159732451885 := by
  unfold tailWord_5465553
  simp only [CollatzResearch.WordTrace]
  refine ⟨199345094768242397982385313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132896729845494931988256875 199345094768242397982385313)
  ·
    refine ⟨149508821076181798486788985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199345094768242397982385313 149508821076181798486788985)
    ·
      refine ⟨112131615807136348865091739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149508821076181798486788985 112131615807136348865091739)
      ·
        refine ⟨168197423710704523297637609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112131615807136348865091739 168197423710704523297637609)
        ·
          refine ⟨126148067783028392473228207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168197423710704523297637609 126148067783028392473228207)
          ·
            refine ⟨189222101674542588709842311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126148067783028392473228207 189222101674542588709842311)
            ·
              refine ⟨283833152511813883064763467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189222101674542588709842311 283833152511813883064763467)
              ·
                refine ⟨425749728767720824597145201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 283833152511813883064763467 425749728767720824597145201)
                ·
                  refine ⟨319312296575790618447858901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 425749728767720824597145201 319312296575790618447858901)
                  ·
                    refine ⟨7483881950995092619871693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 319312296575790618447858901 7483881950995092619871693)
                    ·
                      refine ⟨2806455731623159732451885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7483881950995092619871693 2806455731623159732451885)
                      ·
                        rfl

theorem cell23_5465553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 7, 3].length) (baseStart_5465553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5465553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5465553 prefixEnd_5465553 := by exact prefixLift 5465553
  have htrace : WordTrace (prefixWord ++ tailWord_5465553) baseStart_5465553 baseEnd_5465553 := by
    simpa [prefixWord, tailWord_5465553, baseEnd_5465553] using wordTrace_append hprefix tailTrace_5465553
  have hstable : (prefixWord ++ tailWord_5465553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5465553).length < 2 ^ (prefixWord ++ tailWord_5465553).sum := by decide
  have hdescent : baseEnd_5465553 < baseStart_5465553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5465553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5465583 : List Nat := [1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 5]
def baseStart_5465583 : Nat := 118140960795 + 5465583 * 2 ^ 59
def prefixEnd_5465583 : Nat := 4983230072969 + 3 ^ 40 * 5465583 * 2
def baseEnd_5465583 : Nat := 2806471136042794615076747

theorem tailTrace_5465583 : CollatzResearch.WordTrace tailWord_5465583 prefixEnd_5465583 2806471136042794615076747 := by
  unfold tailWord_5465583
  simp only [CollatzResearch.WordTrace]
  refine ⟨199346188958133713105977403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132897459305422475403984935 199346188958133713105977403)
  ·
    refine ⟨299019283437200569658966105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199346188958133713105977403 299019283437200569658966105)
    ·
      refine ⟨224264462577900427244224579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299019283437200569658966105 224264462577900427244224579)
      ·
        refine ⟨336396693866850640866336869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224264462577900427244224579 336396693866850640866336869)
        ·
          refine ⟨63074380100034495162438163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 336396693866850640866336869 63074380100034495162438163)
          ·
            refine ⟨94611570150051742743657245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63074380100034495162438163 94611570150051742743657245)
            ·
              refine ⟨35479338806269403528871467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94611570150051742743657245 35479338806269403528871467)
              ·
                refine ⟨53219008209404105293307201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35479338806269403528871467 53219008209404105293307201)
                ·
                  refine ⟨39914256157053078969980401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53219008209404105293307201 39914256157053078969980401)
                  ·
                    refine ⟨29935692117789809227485301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39914256157053078969980401 29935692117789809227485301)
                    ·
                      refine ⟨2806471136042794615076747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29935692117789809227485301 2806471136042794615076747)
                      ·
                        rfl

theorem cell23_5465583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 5].length) (baseStart_5465583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5465583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5465583 prefixEnd_5465583 := by exact prefixLift 5465583
  have htrace : WordTrace (prefixWord ++ tailWord_5465583) baseStart_5465583 baseEnd_5465583 := by
    simpa [prefixWord, tailWord_5465583, baseEnd_5465583] using wordTrace_append hprefix tailTrace_5465583
  have hstable : (prefixWord ++ tailWord_5465583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5465583).length < 2 ^ (prefixWord ++ tailWord_5465583).sum := by decide
  have hdescent : baseEnd_5465583 < baseStart_5465583 := by decide
  rcases family_descends (prefixWord ++ tailWord_5465583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5465593 : List Nat := [1, 2, 1, 3, 1, 2, 1, 2, 1, 5, 4]
def baseStart_5465593 : Nat := 118140960795 + 5465593 * 2 ^ 59
def prefixEnd_5465593 : Nat := 4983230072969 + 3 ^ 40 * 5465593 * 2
def baseEnd_5465593 : Nat := 2806476270849339575951701

theorem tailTrace_5465593 : CollatzResearch.WordTrace tailWord_5465593 prefixEnd_5465593 2806476270849339575951701 := by
  unfold tailWord_5465593
  simp only [CollatzResearch.WordTrace]
  refine ⟨199346553688097484813841433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132897702458731656542560955 199346553688097484813841433)
  ·
    refine ⟨149509915266073113610381075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199346553688097484813841433 149509915266073113610381075)
    ·
      refine ⟨224264872899109670415571613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149509915266073113610381075 224264872899109670415571613)
      ·
        refine ⟨84099327337166126405839355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 224264872899109670415571613 84099327337166126405839355)
        ·
          refine ⟨126148991005749189608759033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84099327337166126405839355 126148991005749189608759033)
          ·
            refine ⟨94611743254311892206569275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126148991005749189608759033 94611743254311892206569275)
            ·
              refine ⟨141917614881467838309853913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94611743254311892206569275 141917614881467838309853913)
              ·
                refine ⟨106438211161100878732390435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141917614881467838309853913 106438211161100878732390435)
                ·
                  refine ⟨159657316741651318098585653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106438211161100878732390435 159657316741651318098585653)
                  ·
                    refine ⟨14967873444529811071742405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 159657316741651318098585653 14967873444529811071742405)
                    ·
                      refine ⟨2806476270849339575951701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14967873444529811071742405 2806476270849339575951701)
                      ·
                        rfl

theorem cell23_5465593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_5465593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5465593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5465593 prefixEnd_5465593 := by exact prefixLift 5465593
  have htrace : WordTrace (prefixWord ++ tailWord_5465593) baseStart_5465593 baseEnd_5465593 := by
    simpa [prefixWord, tailWord_5465593, baseEnd_5465593] using wordTrace_append hprefix tailTrace_5465593
  have hstable : (prefixWord ++ tailWord_5465593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5465593).length < 2 ^ (prefixWord ++ tailWord_5465593).sum := by decide
  have hdescent : baseEnd_5465593 < baseStart_5465593 := by decide
  rcases family_descends (prefixWord ++ tailWord_5465593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5465603 : List Nat := [1, 1, 1, 3, 2, 1, 2, 4, 2, 6]
def baseStart_5465603 : Nat := 118140960795 + 5465603 * 2 ^ 59
def prefixEnd_5465603 : Nat := 4983230072969 + 3 ^ 40 * 5465603 * 2
def baseEnd_5465603 : Nat := 935493801885294845608885

theorem tailTrace_5465603 : CollatzResearch.WordTrace tailWord_5465603 prefixEnd_5465603 935493801885294845608885 := by
  unfold tailWord_5465603
  simp only [CollatzResearch.WordTrace]
  refine ⟨199346918418061256521705463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132897945612040837681136975 199346918418061256521705463)
  ·
    refine ⟨299020377627091884782558195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199346918418061256521705463 299020377627091884782558195)
    ·
      refine ⟨448530566440637827173837293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299020377627091884782558195 448530566440637827173837293)
      ·
        refine ⟨168198962415239185190188985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 448530566440637827173837293 168198962415239185190188985)
        ·
          refine ⟨126149221811429388892641739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168198962415239185190188985 126149221811429388892641739)
          ·
            refine ⟨189223832717144083338962609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126149221811429388892641739 189223832717144083338962609)
            ·
              refine ⟨141917874537858062504221957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189223832717144083338962609 141917874537858062504221957)
              ·
                refine ⟨26609601475848386719541617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 141917874537858062504221957 26609601475848386719541617)
                ·
                  refine ⟨19957201106886290039656213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26609601475848386719541617 19957201106886290039656213)
                  ·
                    refine ⟨935493801885294845608885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19957201106886290039656213 935493801885294845608885)
                    ·
                      rfl

theorem cell23_5465603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 6].length) (baseStart_5465603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5465603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5465603 prefixEnd_5465603 := by exact prefixLift 5465603
  have htrace : WordTrace (prefixWord ++ tailWord_5465603) baseStart_5465603 baseEnd_5465603 := by
    simpa [prefixWord, tailWord_5465603, baseEnd_5465603] using wordTrace_append hprefix tailTrace_5465603
  have hstable : (prefixWord ++ tailWord_5465603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5465603).length < 2 ^ (prefixWord ++ tailWord_5465603).sum := by decide
  have hdescent : baseEnd_5465603 < baseStart_5465603 := by decide
  rcases family_descends (prefixWord ++ tailWord_5465603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5465621 : List Nat := [1, 3, 2, 1, 3, 4, 2, 1, 2, 1, 3]
def baseStart_5465621 : Nat := 118140960795 + 5465621 * 2 ^ 59
def prefixEnd_5465621 : Nat := 4983230072969 + 3 ^ 40 * 5465621 * 2
def baseEnd_5465621 : Nat := 2806490648307665466401573

theorem tailTrace_5465621 : CollatzResearch.WordTrace tailWord_5465621 prefixEnd_5465621 2806490648307665466401573 := by
  unfold tailWord_5465621
  simp only [CollatzResearch.WordTrace]
  refine ⟨199347574931996045595860717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132898383287997363730573811 199347574931996045595860717)
  ·
    refine ⟨74755340599498517098447769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199347574931996045595860717 74755340599498517098447769)
    ·
      refine ⟨56066505449623887823835827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74755340599498517098447769 56066505449623887823835827)
      ·
        refine ⟨84099758174435831735753741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56066505449623887823835827 84099758174435831735753741)
        ·
          refine ⟨31537409315413436900907653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84099758174435831735753741 31537409315413436900907653)
          ·
            refine ⟨5913264246640019418920185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31537409315413436900907653 5913264246640019418920185)
            ·
              refine ⟨4434948184980014564190139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5913264246640019418920185 4434948184980014564190139)
              ·
                refine ⟨6652422277470021846285209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4434948184980014564190139 6652422277470021846285209)
                ·
                  refine ⟨4989316708102516384713907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6652422277470021846285209 4989316708102516384713907)
                  ·
                    refine ⟨7483975062153774577070861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4989316708102516384713907 7483975062153774577070861)
                    ·
                      refine ⟨2806490648307665466401573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7483975062153774577070861 2806490648307665466401573)
                      ·
                        rfl

theorem cell23_5465621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 1, 2, 1, 3].length) (baseStart_5465621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5465621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5465621 prefixEnd_5465621 := by exact prefixLift 5465621
  have htrace : WordTrace (prefixWord ++ tailWord_5465621) baseStart_5465621 baseEnd_5465621 := by
    simpa [prefixWord, tailWord_5465621, baseEnd_5465621] using wordTrace_append hprefix tailTrace_5465621
  have hstable : (prefixWord ++ tailWord_5465621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5465621).length < 2 ^ (prefixWord ++ tailWord_5465621).sum := by decide
  have hdescent : baseEnd_5465621 < baseStart_5465621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5465621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5465720 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 5, 4, 3]
def baseStart_5465720 : Nat := 118140960795 + 5465720 * 2 ^ 59
def prefixEnd_5465720 : Nat := 4983230072969 + 3 ^ 40 * 5465720 * 2
def baseEnd_5465720 : Nat := 2806541482892460579063617

theorem tailTrace_5465720 : CollatzResearch.WordTrace tailWord_5465720 prefixEnd_5465720 2806541482892460579063617 := by
  unfold tailWord_5465720
  simp only [CollatzResearch.WordTrace]
  refine ⟨99675592879318692751857307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132900790505758257002476409 99675592879318692751857307)
  ·
    refine ⟨149513389318978039127785961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99675592879318692751857307 149513389318978039127785961)
    ·
      refine ⟨112135041989233529345839471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149513389318978039127785961 112135041989233529345839471)
      ·
        refine ⟨168202562983850294018759207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112135041989233529345839471 168202562983850294018759207)
        ·
          refine ⟨252303844475775441028138811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168202562983850294018759207 252303844475775441028138811)
          ·
            refine ⟨378455766713663161542208217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252303844475775441028138811 378455766713663161542208217)
            ·
              refine ⟨283841825035247371156656163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 378455766713663161542208217 283841825035247371156656163)
              ·
                refine ⟨425762737552871056734984245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 283841825035247371156656163 425762737552871056734984245)
                ·
                  refine ⟨39915256645581661568904773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 425762737552871056734984245 39915256645581661568904773)
                  ·
                    refine ⟨7484110621046561544169645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39915256645581661568904773 7484110621046561544169645)
                    ·
                      refine ⟨2806541482892460579063617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7484110621046561544169645 2806541482892460579063617)
                      ·
                        rfl

theorem cell23_5465720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 5, 4, 3].length) (baseStart_5465720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5465720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5465720 prefixEnd_5465720 := by exact prefixLift 5465720
  have htrace : WordTrace (prefixWord ++ tailWord_5465720) baseStart_5465720 baseEnd_5465720 := by
    simpa [prefixWord, tailWord_5465720, baseEnd_5465720] using wordTrace_append hprefix tailTrace_5465720
  have hstable : (prefixWord ++ tailWord_5465720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5465720).length < 2 ^ (prefixWord ++ tailWord_5465720).sum := by decide
  have hdescent : baseEnd_5465720 < baseStart_5465720 := by decide
  rcases family_descends (prefixWord ++ tailWord_5465720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5465761 : List Nat := [1, 2, 3, 3, 2, 1, 3, 3, 1, 4]
def baseStart_5465761 : Nat := 118140960795 + 5465761 * 2 ^ 59
def prefixEnd_5465761 : Nat := 4983230072969 + 3 ^ 40 * 5465761 * 2
def baseEnd_5465761 : Nat := 935520845199764972883643

theorem tailTrace_5465761 : CollatzResearch.WordTrace tailWord_5465761 prefixEnd_5465761 935520845199764972883643 := by
  unfold tailWord_5465761
  simp only [CollatzResearch.WordTrace]
  refine ⟨199352681151488849505957137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132901787434325899670638091 199352681151488849505957137)
  ·
    refine ⟨149514510863616637129467853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199352681151488849505957137 149514510863616637129467853)
    ·
      refine ⟨56067941573856238923550445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149514510863616637129467853 56067941573856238923550445)
      ·
        refine ⟨21025478090196089596331417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56067941573856238923550445 21025478090196089596331417)
        ·
          refine ⟨15769108567647067197248563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21025478090196089596331417 15769108567647067197248563)
          ·
            refine ⟨23653662851470600795872845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15769108567647067197248563 23653662851470600795872845)
            ·
              refine ⟨8870123569301475298452317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23653662851470600795872845 8870123569301475298452317)
              ·
                refine ⟨3326296338488053236919619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8870123569301475298452317 3326296338488053236919619)
                ·
                  refine ⟨4989444507732079855379429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3326296338488053236919619 4989444507732079855379429)
                  ·
                    refine ⟨935520845199764972883643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4989444507732079855379429 935520845199764972883643)
                    ·
                      rfl

theorem cell23_5465761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 3, 1, 4].length) (baseStart_5465761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5465761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5465761 prefixEnd_5465761 := by exact prefixLift 5465761
  have htrace : WordTrace (prefixWord ++ tailWord_5465761) baseStart_5465761 baseEnd_5465761 := by
    simpa [prefixWord, tailWord_5465761, baseEnd_5465761] using wordTrace_append hprefix tailTrace_5465761
  have hstable : (prefixWord ++ tailWord_5465761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5465761).length < 2 ^ (prefixWord ++ tailWord_5465761).sum := by decide
  have hdescent : baseEnd_5465761 < baseStart_5465761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5465761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5465768 : List Nat := [2, 1, 7, 1, 1, 1, 1, 2, 2, 1, 4]
def baseStart_5465768 : Nat := 118140960795 + 5465768 * 2 ^ 59
def prefixEnd_5465768 : Nat := 4983230072969 + 3 ^ 40 * 5465768 * 2
def baseEnd_5465768 : Nat := 2806566129963876391263397

theorem tailTrace_5465768 : CollatzResearch.WordTrace tailWord_5465768 prefixEnd_5465768 2806566129963876391263397 := by
  unfold tailWord_5465768
  simp only [CollatzResearch.WordTrace]
  refine ⟨99676468231231744850730979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132901957641642326467641305 99676468231231744850730979)
  ·
    refine ⟨149514702346847617276096469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99676468231231744850730979 149514702346847617276096469)
    ·
      refine ⟨3504250836254241029908511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 149514702346847617276096469 3504250836254241029908511)
      ·
        refine ⟨5256376254381361544862767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3504250836254241029908511 5256376254381361544862767)
        ·
          refine ⟨7884564381572042317294151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5256376254381361544862767 7884564381572042317294151)
          ·
            refine ⟨11826846572358063475941227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7884564381572042317294151 11826846572358063475941227)
            ·
              refine ⟨17740269858537095213911841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11826846572358063475941227 17740269858537095213911841)
              ·
                refine ⟨13305202393902821410433881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17740269858537095213911841 13305202393902821410433881)
                ·
                  refine ⟨9978901795427116057825411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13305202393902821410433881 9978901795427116057825411)
                  ·
                    refine ⟨14968352693140674086738117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9978901795427116057825411 14968352693140674086738117)
                    ·
                      refine ⟨2806566129963876391263397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14968352693140674086738117 2806566129963876391263397)
                      ·
                        rfl

theorem cell23_5465768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_5465768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5465768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5465768 prefixEnd_5465768 := by exact prefixLift 5465768
  have htrace : WordTrace (prefixWord ++ tailWord_5465768) baseStart_5465768 baseEnd_5465768 := by
    simpa [prefixWord, tailWord_5465768, baseEnd_5465768] using wordTrace_append hprefix tailTrace_5465768
  have hstable : (prefixWord ++ tailWord_5465768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5465768).length < 2 ^ (prefixWord ++ tailWord_5465768).sum := by decide
  have hdescent : baseEnd_5465768 < baseStart_5465768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5465768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5465804 : List Nat := [2, 2, 1, 5, 2, 1, 1, 1, 3, 5]
def baseStart_5465804 : Nat := 118140960795 + 5465804 * 2 ^ 59
def prefixEnd_5465804 : Nat := 4983230072969 + 3 ^ 40 * 5465804 * 2
def baseEnd_5465804 : Nat := 935528205089146083471077

theorem tailTrace_5465804 : CollatzResearch.WordTrace tailWord_5465804 prefixEnd_5465804 935528205089146083471077 := by
  unfold tailWord_5465804
  simp only [CollatzResearch.WordTrace]
  refine ⟨99677124745166533924886233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132902832993555378566514977 99677124745166533924886233)
  ·
    refine ⟨74757843558874900443664675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99677124745166533924886233 74757843558874900443664675)
    ·
      refine ⟨112136765338312350665497013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74757843558874900443664675 112136765338312350665497013)
      ·
        refine ⟨10512821750466782874890345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 112136765338312350665497013 10512821750466782874890345)
        ·
          refine ⟨7884616312850087156167759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10512821750466782874890345 7884616312850087156167759)
          ·
            refine ⟨11826924469275130734251639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7884616312850087156167759 11826924469275130734251639)
            ·
              refine ⟨17740386703912696101377459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11826924469275130734251639 17740386703912696101377459)
              ·
                refine ⟨26610580055869044152066189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17740386703912696101377459 26610580055869044152066189)
                ·
                  refine ⟨9978967520950891557024821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26610580055869044152066189 9978967520950891557024821)
                  ·
                    refine ⟨935528205089146083471077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9978967520950891557024821 935528205089146083471077)
                    ·
                      rfl

theorem cell23_5465804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 3, 5].length) (baseStart_5465804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5465804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5465804 prefixEnd_5465804 := by exact prefixLift 5465804
  have htrace : WordTrace (prefixWord ++ tailWord_5465804) baseStart_5465804 baseEnd_5465804 := by
    simpa [prefixWord, tailWord_5465804, baseEnd_5465804] using wordTrace_append hprefix tailTrace_5465804
  have hstable : (prefixWord ++ tailWord_5465804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5465804).length < 2 ^ (prefixWord ++ tailWord_5465804).sum := by decide
  have hdescent : baseEnd_5465804 < baseStart_5465804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5465804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5465807 : List Nat := [1, 1, 2, 1, 1, 3, 1, 3, 2, 6, 2]
def baseStart_5465807 : Nat := 118140960795 + 5465807 * 2 ^ 59
def prefixEnd_5465807 : Nat := 4983230072969 + 3 ^ 40 * 5465807 * 2
def baseEnd_5465807 : Nat := 2806586155709401738675717

theorem tailTrace_5465807 : CollatzResearch.WordTrace tailWord_5465807 prefixEnd_5465807 2806586155709401738675717 := by
  unfold tailWord_5465807
  simp only [CollatzResearch.WordTrace]
  refine ⟨199354358909322199362131675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132902905939548132908087783 199354358909322199362131675)
  ·
    refine ⟨299031538363983299043197513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199354358909322199362131675 299031538363983299043197513)
    ·
      refine ⟨224273653772987474282398135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299031538363983299043197513 224273653772987474282398135)
      ·
        refine ⟨336410480659481211423597203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224273653772987474282398135 336410480659481211423597203)
        ·
          refine ⟨504615720989221817135395805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 336410480659481211423597203 504615720989221817135395805)
          ·
            refine ⟨189230895370958181425773427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 504615720989221817135395805 189230895370958181425773427)
            ·
              refine ⟨283846343056437272138660141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189230895370958181425773427 283846343056437272138660141)
              ·
                refine ⟨106442378646163977051997553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 283846343056437272138660141 106442378646163977051997553)
                ·
                  refine ⟨79831783984622982788998165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106442378646163977051997553 79831783984622982788998165)
                  ·
                    refine ⟨3742114874279202318234289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 79831783984622982788998165 3742114874279202318234289)
                    ·
                      refine ⟨2806586155709401738675717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3742114874279202318234289 2806586155709401738675717)
                      ·
                        rfl

theorem cell23_5465807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 6, 2].length) (baseStart_5465807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5465807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5465807 prefixEnd_5465807 := by exact prefixLift 5465807
  have htrace : WordTrace (prefixWord ++ tailWord_5465807) baseStart_5465807 baseEnd_5465807 := by
    simpa [prefixWord, tailWord_5465807, baseEnd_5465807] using wordTrace_append hprefix tailTrace_5465807
  have hstable : (prefixWord ++ tailWord_5465807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5465807).length < 2 ^ (prefixWord ++ tailWord_5465807).sum := by decide
  have hdescent : baseEnd_5465807 < baseStart_5465807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5465807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5465817 : List Nat := [1, 2, 1, 2, 3, 4, 1, 2, 1, 6]
def baseStart_5465817 : Nat := 118140960795 + 5465817 * 2 ^ 59
def prefixEnd_5465817 : Nat := 4983230072969 + 3 ^ 40 * 5465817 * 2
def baseEnd_5465817 : Nat := 935530430171982233183557

theorem tailTrace_5465817 : CollatzResearch.WordTrace tailWord_5465817 prefixEnd_5465817 935530430171982233183557 := by
  unfold tailWord_5465817
  simp only [CollatzResearch.WordTrace]
  refine ⟨199354723639285971069995705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132903149092857314046663803 199354723639285971069995705)
  ·
    refine ⟨149516042729464478302496779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199354723639285971069995705 149516042729464478302496779)
    ·
      refine ⟨224274064094196717453745169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149516042729464478302496779 224274064094196717453745169)
      ·
        refine ⟨168205548070647538090308877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224274064094196717453745169 168205548070647538090308877)
        ·
          refine ⟨63077080526492826783865829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168205548070647538090308877 63077080526492826783865829)
          ·
            refine ⟨11826952598717405021974843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63077080526492826783865829 11826952598717405021974843)
            ·
              refine ⟨17740428898076107532962265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11826952598717405021974843 17740428898076107532962265)
              ·
                refine ⟨13305321673557080649721699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17740428898076107532962265 13305321673557080649721699)
                ·
                  refine ⟨19957982510335620974582549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13305321673557080649721699 19957982510335620974582549)
                  ·
                    refine ⟨935530430171982233183557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19957982510335620974582549 935530430171982233183557)
                    ·
                      rfl

theorem cell23_5465817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 6].length) (baseStart_5465817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5465817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5465817 prefixEnd_5465817 := by exact prefixLift 5465817
  have htrace : WordTrace (prefixWord ++ tailWord_5465817) baseStart_5465817 baseEnd_5465817 := by
    simpa [prefixWord, tailWord_5465817, baseEnd_5465817] using wordTrace_append hprefix tailTrace_5465817
  have hstable : (prefixWord ++ tailWord_5465817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5465817).length < 2 ^ (prefixWord ++ tailWord_5465817).sum := by decide
  have hdescent : baseEnd_5465817 < baseStart_5465817 := by decide
  rcases family_descends (prefixWord ++ tailWord_5465817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5465834 : List Nat := [3, 1, 3, 1, 1, 1, 3, 4, 2, 4]
def baseStart_5465834 : Nat := 118140960795 + 5465834 * 2 ^ 59
def prefixEnd_5465834 : Nat := 4983230072969 + 3 ^ 40 * 5465834 * 2
def baseEnd_5465834 : Nat := 935533339895691044346031

theorem tailTrace_5465834 : CollatzResearch.WordTrace tailWord_5465834 prefixEnd_5465834 935533339895691044346031 := by
  unfold tailWord_5465834
  simp only [CollatzResearch.WordTrace]
  refine ⟨49838835920056095743341139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132903562453482921982243037 49838835920056095743341139)
  ·
    refine ⟨74758253880084143615011709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49838835920056095743341139 74758253880084143615011709)
    ·
      refine ⟨28034345205031553855629391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74758253880084143615011709 28034345205031553855629391)
      ·
        refine ⟨42051517807547330783444087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28034345205031553855629391 42051517807547330783444087)
        ·
          refine ⟨63077276711320996175166131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42051517807547330783444087 63077276711320996175166131)
          ·
            refine ⟨94615915066981494262749197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63077276711320996175166131 94615915066981494262749197)
            ·
              refine ⟨35480968150118060348530949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94615915066981494262749197 35480968150118060348530949)
              ·
                refine ⟨6652681528147136315349553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35480968150118060348530949 6652681528147136315349553)
                ·
                  refine ⟨4989511146110352236512165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6652681528147136315349553 4989511146110352236512165)
                  ·
                    refine ⟨935533339895691044346031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4989511146110352236512165 935533339895691044346031)
                    ·
                      rfl

theorem cell23_5465834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_5465834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5465834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5465834 prefixEnd_5465834 := by exact prefixLift 5465834
  have htrace : WordTrace (prefixWord ++ tailWord_5465834) baseStart_5465834 baseEnd_5465834 := by
    simpa [prefixWord, tailWord_5465834, baseEnd_5465834] using wordTrace_append hprefix tailTrace_5465834
  have hstable : (prefixWord ++ tailWord_5465834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5465834).length < 2 ^ (prefixWord ++ tailWord_5465834).sum := by decide
  have hdescent : baseEnd_5465834 < baseStart_5465834 := by decide
  rcases family_descends (prefixWord ++ tailWord_5465834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5465840 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 7]
def baseStart_5465840 : Nat := 118140960795 + 5465840 * 2 ^ 59
def prefixEnd_5465840 : Nat := 4983230072969 + 3 ^ 40 * 5465840 * 2
def baseEnd_5465840 : Nat := 2806603100571000109563065

theorem tailTrace_5465840 : CollatzResearch.WordTrace tailWord_5465840 prefixEnd_5465840 2806603100571000109563065 := by
  unfold tailWord_5465840
  simp only [CollatzResearch.WordTrace]
  refine ⟨99677781259101322999041487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132903708345468430665388649 99677781259101322999041487)
  ·
    refine ⟨149516671888651984498562231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99677781259101322999041487 149516671888651984498562231)
    ·
      refine ⟨224275007832977976747843347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149516671888651984498562231 224275007832977976747843347)
      ·
        refine ⟨336412511749466965121765021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224275007832977976747843347 336412511749466965121765021)
        ·
          refine ⟨126154691906050111920661883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 336412511749466965121765021 126154691906050111920661883)
          ·
            refine ⟨189232037859075167880992825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126154691906050111920661883 189232037859075167880992825)
            ·
              refine ⟨141924028394306375910744619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189232037859075167880992825 141924028394306375910744619)
              ·
                refine ⟨212886042591459563866116929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141924028394306375910744619 212886042591459563866116929)
                ·
                  refine ⟨159664531943594672899587697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 212886042591459563866116929 159664531943594672899587697)
                  ·
                    refine ⟨119748398957696004674690773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 159664531943594672899587697 119748398957696004674690773)
                    ·
                      refine ⟨2806603100571000109563065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 119748398957696004674690773 2806603100571000109563065)
                      ·
                        rfl

theorem cell23_5465840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 7].length) (baseStart_5465840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5465840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5465840 prefixEnd_5465840 := by exact prefixLift 5465840
  have htrace : WordTrace (prefixWord ++ tailWord_5465840) baseStart_5465840 baseEnd_5465840 := by
    simpa [prefixWord, tailWord_5465840, baseEnd_5465840] using wordTrace_append hprefix tailTrace_5465840
  have hstable : (prefixWord ++ tailWord_5465840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5465840).length < 2 ^ (prefixWord ++ tailWord_5465840).sum := by decide
  have hdescent : baseEnd_5465840 < baseStart_5465840 := by decide
  rcases family_descends (prefixWord ++ tailWord_5465840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5465858 : List Nat := [3, 4, 1, 1, 1, 1, 3, 2, 3, 2, 2]
def baseStart_5465858 : Nat := 118140960795 + 5465858 * 2 ^ 59
def prefixEnd_5465858 : Nat := 4983230072969 + 3 ^ 40 * 5465858 * 2
def baseEnd_5465858 : Nat := 2806612343222781039137983

theorem tailTrace_5465858 : CollatzResearch.WordTrace tailWord_5465858 prefixEnd_5465858 2806612343222781039137983 := by
  unfold tailWord_5465858
  simp only [CollatzResearch.WordTrace]
  refine ⟨49839054758034358768059557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132904146021424956714825485 49839054758034358768059557)
  ·
    refine ⟨9344822767131442269011167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49839054758034358768059557 9344822767131442269011167)
    ·
      refine ⟨14017234150697163403516751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9344822767131442269011167 14017234150697163403516751)
      ·
        refine ⟨21025851226045745105275127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14017234150697163403516751 21025851226045745105275127)
        ·
          refine ⟨31538776839068617657912691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21025851226045745105275127 31538776839068617657912691)
          ·
            refine ⟨47308165258602926486869037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31538776839068617657912691 47308165258602926486869037)
            ·
              refine ⟨17740561971976097432575889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47308165258602926486869037 17740561971976097432575889)
              ·
                refine ⟨13305421478982073074431917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17740561971976097432575889 13305421478982073074431917)
                ·
                  refine ⟨4989533054618277402911969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13305421478982073074431917 4989533054618277402911969)
                  ·
                    refine ⟨3742149790963708052183977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4989533054618277402911969 3742149790963708052183977)
                    ·
                      refine ⟨2806612343222781039137983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3742149790963708052183977 2806612343222781039137983)
                      ·
                        rfl

theorem cell23_5465858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_5465858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5465858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5465858 prefixEnd_5465858 := by exact prefixLift 5465858
  have htrace : WordTrace (prefixWord ++ tailWord_5465858) baseStart_5465858 baseEnd_5465858 := by
    simpa [prefixWord, tailWord_5465858, baseEnd_5465858] using wordTrace_append hprefix tailTrace_5465858
  have hstable : (prefixWord ++ tailWord_5465858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5465858).length < 2 ^ (prefixWord ++ tailWord_5465858).sum := by decide
  have hdescent : baseEnd_5465858 < baseStart_5465858 := by decide
  rcases family_descends (prefixWord ++ tailWord_5465858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5465891 : List Nat := [1, 1, 1, 4, 2, 1, 5, 2, 2, 1, 3]
def baseStart_5465891 : Nat := 118140960795 + 5465891 * 2 ^ 59
def prefixEnd_5465891 : Nat := 4983230072969 + 3 ^ 40 * 5465891 * 2
def baseEnd_5465891 : Nat := 2806629288084379410025331

theorem tailTrace_5465891 : CollatzResearch.WordTrace tailWord_5465891 prefixEnd_5465891 2806629288084379410025331 := by
  unfold tailWord_5465891
  simp only [CollatzResearch.WordTrace]
  refine ⟨199357422641017881708189527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132904948427345254472126351 199357422641017881708189527)
  ·
    refine ⟨299036133961526822562284291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199357422641017881708189527 299036133961526822562284291)
    ·
      refine ⟨448554200942290233843426437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299036133961526822562284291 448554200942290233843426437)
      ·
        refine ⟨84103912676679418845642457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 448554200942290233843426437 84103912676679418845642457)
        ·
          refine ⟨63077934507509564134231843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84103912676679418845642457 63077934507509564134231843)
          ·
            refine ⟨94616901761264346201347765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63077934507509564134231843 94616901761264346201347765)
            ·
              refine ⟨8870334540118532456376353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94616901761264346201347765 8870334540118532456376353)
              ·
                refine ⟨6652750905088899342282265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8870334540118532456376353 6652750905088899342282265)
                ·
                  refine ⟨4989563178816674506711699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6652750905088899342282265 4989563178816674506711699)
                  ·
                    refine ⟨7484344768225011760067549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4989563178816674506711699 7484344768225011760067549)
                    ·
                      refine ⟨2806629288084379410025331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7484344768225011760067549 2806629288084379410025331)
                      ·
                        rfl

theorem cell23_5465891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 2, 2, 1, 3].length) (baseStart_5465891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5465891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5465891 prefixEnd_5465891 := by exact prefixLift 5465891
  have htrace : WordTrace (prefixWord ++ tailWord_5465891) baseStart_5465891 baseEnd_5465891 := by
    simpa [prefixWord, tailWord_5465891, baseEnd_5465891] using wordTrace_append hprefix tailTrace_5465891
  have hstable : (prefixWord ++ tailWord_5465891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5465891).length < 2 ^ (prefixWord ++ tailWord_5465891).sum := by decide
  have hdescent : baseEnd_5465891 < baseStart_5465891 := by decide
  rcases family_descends (prefixWord ++ tailWord_5465891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5465908 : List Nat := [2, 5, 1, 1, 2, 3, 1, 1, 1, 3, 3]
def baseStart_5465908 : Nat := 118140960795 + 5465908 * 2 ^ 59
def prefixEnd_5465908 : Nat := 4983230072969 + 3 ^ 40 * 5465908 * 2
def baseEnd_5465908 : Nat := 2806638017255505843512753

theorem tailTrace_5465908 : CollatzResearch.WordTrace tailWord_5465908 prefixEnd_5465908 2806638017255505843512753 := by
  unfold tailWord_5465908
  simp only [CollatzResearch.WordTrace]
  refine ⟨99679021340978146805779189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132905361787970862407705585 99679021340978146805779189)
  ·
    refine ⟨9344908250716701263041799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 99679021340978146805779189 9344908250716701263041799)
    ·
      refine ⟨14017362376075051894562699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9344908250716701263041799 14017362376075051894562699)
      ·
        refine ⟨21026043564112577841844049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14017362376075051894562699 21026043564112577841844049)
        ·
          refine ⟨15769532673084433381383037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21026043564112577841844049 15769532673084433381383037)
          ·
            refine ⟨5913574752406662518018639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15769532673084433381383037 5913574752406662518018639)
            ·
              refine ⟨8870362128609993777027959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5913574752406662518018639 8870362128609993777027959)
              ·
                refine ⟨13305543192914990665541939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8870362128609993777027959 13305543192914990665541939)
                ·
                  refine ⟨19958314789372485998312909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13305543192914990665541939 19958314789372485998312909)
                  ·
                    refine ⟨7484368046014682249367341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19958314789372485998312909 7484368046014682249367341)
                    ·
                      refine ⟨2806638017255505843512753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7484368046014682249367341 2806638017255505843512753)
                      ·
                        rfl

theorem cell23_5465908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_5465908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5465908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5465908 prefixEnd_5465908 := by exact prefixLift 5465908
  have htrace : WordTrace (prefixWord ++ tailWord_5465908) baseStart_5465908 baseEnd_5465908 := by
    simpa [prefixWord, tailWord_5465908, baseEnd_5465908] using wordTrace_append hprefix tailTrace_5465908
  have hstable : (prefixWord ++ tailWord_5465908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5465908).length < 2 ^ (prefixWord ++ tailWord_5465908).sum := by decide
  have hdescent : baseEnd_5465908 < baseStart_5465908 := by decide
  rcases family_descends (prefixWord ++ tailWord_5465908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5465918 : List Nat := [4, 2, 1, 2, 2, 1, 1, 4, 1, 3, 2]
def baseStart_5465918 : Nat := 118140960795 + 5465918 * 2 ^ 59
def prefixEnd_5465918 : Nat := 4983230072969 + 3 ^ 40 * 5465918 * 2
def baseEnd_5465918 : Nat := 2806643152062050804387707

theorem tailTrace_5465918 : CollatzResearch.WordTrace tailWord_5465918 prefixEnd_5465918 2806643152062050804387707 := by
  unfold tailWord_5465918
  simp only [CollatzResearch.WordTrace]
  refine ⟨24919800926490008164927801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132905604941280043546281605 24919800926490008164927801)
  ·
    refine ⟨18689850694867506123695851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24919800926490008164927801 18689850694867506123695851)
    ·
      refine ⟨28034776042301259185543777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18689850694867506123695851 28034776042301259185543777)
      ·
        refine ⟨21026082031725944389157833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28034776042301259185543777 21026082031725944389157833)
        ·
          refine ⟨15769561523794458291868375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21026082031725944389157833 15769561523794458291868375)
          ·
            refine ⟨23654342285691687437802563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15769561523794458291868375 23654342285691687437802563)
            ·
              refine ⟨35481513428537531156703845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23654342285691687437802563 35481513428537531156703845)
              ·
                refine ⟨6652783767850787091881971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35481513428537531156703845 6652783767850787091881971)
                ·
                  refine ⟨9979175651776180637822957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6652783767850787091881971 9979175651776180637822957)
                  ·
                    refine ⟨3742190869416067739183609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9979175651776180637822957 3742190869416067739183609)
                    ·
                      refine ⟨2806643152062050804387707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3742190869416067739183609 2806643152062050804387707)
                      ·
                        rfl

theorem cell23_5465918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_5465918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5465918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5465918 prefixEnd_5465918 := by exact prefixLift 5465918
  have htrace : WordTrace (prefixWord ++ tailWord_5465918) baseStart_5465918 baseEnd_5465918 := by
    simpa [prefixWord, tailWord_5465918, baseEnd_5465918] using wordTrace_append hprefix tailTrace_5465918
  have hstable : (prefixWord ++ tailWord_5465918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5465918).length < 2 ^ (prefixWord ++ tailWord_5465918).sum := by decide
  have hdescent : baseEnd_5465918 < baseStart_5465918 := by decide
  rcases family_descends (prefixWord ++ tailWord_5465918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5465927 : List Nat := [1, 1, 4, 1, 2, 1, 2, 2, 1, 4, 4]
def baseStart_5465927 : Nat := 118140960795 + 5465927 * 2 ^ 59
def prefixEnd_5465927 : Nat := 4983230072969 + 3 ^ 40 * 5465927 * 2
def baseEnd_5465927 : Nat := 2806647773387941269175165

theorem tailTrace_5465927 : CollatzResearch.WordTrace tailWord_5465927 prefixEnd_5465927 2806647773387941269175165 := by
  unfold tailWord_5465927
  simp only [CollatzResearch.WordTrace]
  refine ⟨199358735668887459856500035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132905823779258306571000023 199358735668887459856500035)
  ·
    refine ⟨299038103503331189784750053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199358735668887459856500035 299038103503331189784750053)
    ·
      refine ⟨56069644406874598084640635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 299038103503331189784750053 56069644406874598084640635)
      ·
        refine ⟨84104466610311897126960953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56069644406874598084640635 84104466610311897126960953)
        ·
          refine ⟨63078349957733922845220715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84104466610311897126960953 63078349957733922845220715)
          ·
            refine ⟨94617524936600884267831073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63078349957733922845220715 94617524936600884267831073)
            ·
              refine ⟨70963143702450663200873305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94617524936600884267831073 70963143702450663200873305)
              ·
                refine ⟨53222357776837997400654979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70963143702450663200873305 53222357776837997400654979)
                ·
                  refine ⟨79833536665256996100982469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53222357776837997400654979 79833536665256996100982469)
                  ·
                    refine ⟨14968788124735686768934213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 79833536665256996100982469 14968788124735686768934213)
                    ·
                      refine ⟨2806647773387941269175165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14968788124735686768934213 2806647773387941269175165)
                      ·
                        rfl

theorem cell23_5465927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_5465927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5465927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5465927 prefixEnd_5465927 := by exact prefixLift 5465927
  have htrace : WordTrace (prefixWord ++ tailWord_5465927) baseStart_5465927 baseEnd_5465927 := by
    simpa [prefixWord, tailWord_5465927, baseEnd_5465927] using wordTrace_append hprefix tailTrace_5465927
  have hstable : (prefixWord ++ tailWord_5465927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5465927).length < 2 ^ (prefixWord ++ tailWord_5465927).sum := by decide
  have hdescent : baseEnd_5465927 < baseStart_5465927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5465927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5465965 : List Nat := [1, 5, 1, 1, 1, 1, 6, 1, 2, 2, 2]
def baseStart_5465965 : Nat := 118140960795 + 5465965 * 2 ^ 59
def prefixEnd_5465965 : Nat := 4983230072969 + 3 ^ 40 * 5465965 * 2
def baseEnd_5465965 : Nat := 2806667285652812120499991

theorem tailTrace_5465965 : CollatzResearch.WordTrace tailWord_5465965 prefixEnd_5465965 2806667285652812120499991 := by
  unfold tailWord_5465965
  simp only [CollatzResearch.WordTrace]
  refine ⟨199360121642749792346383349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132906747761833194897588899 199360121642749792346383349)
  ·
    refine ⟨18690011404007793032473439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 199360121642749792346383349 18690011404007793032473439)
    ·
      refine ⟨28035017106011689548710159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18690011404007793032473439 28035017106011689548710159)
      ·
        refine ⟨42052525659017534323065239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28035017106011689548710159 42052525659017534323065239)
        ·
          refine ⟨63078788488526301484597859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42052525659017534323065239 63078788488526301484597859)
          ·
            refine ⟨94618182732789452226896789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63078788488526301484597859 94618182732789452226896789)
            ·
              refine ⟨4435227315599505573135787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 94618182732789452226896789 4435227315599505573135787)
              ·
                refine ⟨6652840973399258359703681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4435227315599505573135787 6652840973399258359703681)
                ·
                  refine ⟨4989630730049443769777761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6652840973399258359703681 4989630730049443769777761)
                  ·
                    refine ⟨3742223047537082827333321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4989630730049443769777761 3742223047537082827333321)
                    ·
                      refine ⟨2806667285652812120499991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3742223047537082827333321 2806667285652812120499991)
                      ·
                        rfl

theorem cell23_5465965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 1, 2, 2, 2].length) (baseStart_5465965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5465965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5465965 prefixEnd_5465965 := by exact prefixLift 5465965
  have htrace : WordTrace (prefixWord ++ tailWord_5465965) baseStart_5465965 baseEnd_5465965 := by
    simpa [prefixWord, tailWord_5465965, baseEnd_5465965] using wordTrace_append hprefix tailTrace_5465965
  have hstable : (prefixWord ++ tailWord_5465965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5465965).length < 2 ^ (prefixWord ++ tailWord_5465965).sum := by decide
  have hdescent : baseEnd_5465965 < baseStart_5465965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5465965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5465977 : List Nat := [1, 2, 1, 3, 2, 2, 1, 2, 1, 1, 7]
def baseStart_5465977 : Nat := 118140960795 + 5465977 * 2 ^ 59
def prefixEnd_5465977 : Nat := 4983230072969 + 3 ^ 40 * 5465977 * 2
def baseEnd_5465977 : Nat := 2806673447420666073549935

theorem tailTrace_5465977 : CollatzResearch.WordTrace tailWord_5465977 prefixEnd_5465977 2806673447420666073549935 := by
  unfold tailWord_5465977
  simp only [CollatzResearch.WordTrace]
  refine ⟨199360559318706318395820185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132907039545804212263880123 199360559318706318395820185)
  ·
    refine ⟨149520419489029738796865139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199360559318706318395820185 149520419489029738796865139)
    ·
      refine ⟨224280629233544608195297709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149520419489029738796865139 224280629233544608195297709)
      ·
        refine ⟨84105235962579228073236641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 224280629233544608195297709 84105235962579228073236641)
        ·
          refine ⟨63078926971934421054927481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84105235962579228073236641 63078926971934421054927481)
          ·
            refine ⟨47309195228950815791195611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63078926971934421054927481 47309195228950815791195611)
            ·
              refine ⟨70963792843426223686793417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47309195228950815791195611 70963792843426223686793417)
              ·
                refine ⟨53222844632569667765095063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70963792843426223686793417 53222844632569667765095063)
                ·
                  refine ⟨79834266948854501647642595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53222844632569667765095063 79834266948854501647642595)
                  ·
                    refine ⟨119751400423281752471463893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 79834266948854501647642595 119751400423281752471463893)
                    ·
                      refine ⟨2806673447420666073549935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 119751400423281752471463893 2806673447420666073549935)
                      ·
                        rfl

theorem cell23_5465977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_5465977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5465977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5465977 prefixEnd_5465977 := by exact prefixLift 5465977
  have htrace : WordTrace (prefixWord ++ tailWord_5465977) baseStart_5465977 baseEnd_5465977 := by
    simpa [prefixWord, tailWord_5465977, baseEnd_5465977] using wordTrace_append hprefix tailTrace_5465977
  have hstable : (prefixWord ++ tailWord_5465977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5465977).length < 2 ^ (prefixWord ++ tailWord_5465977).sum := by decide
  have hdescent : baseEnd_5465977 < baseStart_5465977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5465977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5465984 : List Nat := [2, 1, 1, 2, 1, 2, 6, 1, 2, 5]
def baseStart_5465984 : Nat := 118140960795 + 5465984 * 2 ^ 59
def prefixEnd_5465984 : Nat := 4983230072969 + 3 ^ 40 * 5465984 * 2
def baseEnd_5465984 : Nat := 935559013928415848720801

theorem tailTrace_5465984 : CollatzResearch.WordTrace tailWord_5465984 prefixEnd_5465984 935559013928415848720801 := by
  unfold tailWord_5465984
  simp only [CollatzResearch.WordTrace]
  refine ⟨99680407314840479295662503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132907209753120639060883337 99680407314840479295662503)
  ·
    refine ⟨149520610972260718943493755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99680407314840479295662503 149520610972260718943493755)
    ·
      refine ⟨224280916458391078415240633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149520610972260718943493755 224280916458391078415240633)
      ·
        refine ⟨168210687343793308811430475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224280916458391078415240633 168210687343793308811430475)
        ·
          refine ⟨252316031015689963217145713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168210687343793308811430475 252316031015689963217145713)
          ·
            refine ⟨189237023261767472412859285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 252316031015689963217145713 189237023261767472412859285)
            ·
              refine ⟨8870485465395350269352779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 189237023261767472412859285 8870485465395350269352779)
              ·
                refine ⟨13305728198093025404029169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8870485465395350269352779 13305728198093025404029169)
                ·
                  refine ⟨9979296148569769053021877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13305728198093025404029169 9979296148569769053021877)
                  ·
                    refine ⟨935559013928415848720801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9979296148569769053021877 935559013928415848720801)
                    ·
                      rfl

theorem cell23_5465984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 2, 5].length) (baseStart_5465984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5465984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5465984 prefixEnd_5465984 := by exact prefixLift 5465984
  have htrace : WordTrace (prefixWord ++ tailWord_5465984) baseStart_5465984 baseEnd_5465984 := by
    simpa [prefixWord, tailWord_5465984, baseEnd_5465984] using wordTrace_append hprefix tailTrace_5465984
  have hstable : (prefixWord ++ tailWord_5465984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5465984).length < 2 ^ (prefixWord ++ tailWord_5465984).sum := by decide
  have hdescent : baseEnd_5465984 < baseStart_5465984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5465984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466048 : List Nat := [2, 1, 1, 2, 3, 2, 4, 3, 1, 4]
def baseStart_5466048 : Nat := 118140960795 + 5466048 * 2 ^ 59
def prefixEnd_5466048 : Nat := 4983230072969 + 3 ^ 40 * 5466048 * 2
def baseEnd_5466048 : Nat := 935569968182378431920703

theorem tailTrace_5466048 : CollatzResearch.WordTrace tailWord_5466048 prefixEnd_5466048 935569968182378431920703 := by
  unfold tailWord_5466048
  simp only [CollatzResearch.WordTrace]
  refine ⟨99681574450724548760827399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132908765934299398347769865 99681574450724548760827399)
  ·
    refine ⟨149522361676086823141241099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99681574450724548760827399 149522361676086823141241099)
    ·
      refine ⟨224283542514130234711861649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149522361676086823141241099 224283542514130234711861649)
      ·
        refine ⟨168212656885597676033896237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224283542514130234711861649 168212656885597676033896237)
        ·
          refine ⟨63079746332099128512711089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168212656885597676033896237 63079746332099128512711089)
          ·
            refine ⟨47309809749074346384533317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63079746332099128512711089 47309809749074346384533317)
            ·
              refine ⟨8870589327951439947099997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47309809749074346384533317 8870589327951439947099997)
              ·
                refine ⟨3326470997981789980162499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8870589327951439947099997 3326470997981789980162499)
                ·
                  refine ⟨4989706496972684970243749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3326470997981789980162499 4989706496972684970243749)
                  ·
                    refine ⟨935569968182378431920703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4989706496972684970243749 935569968182378431920703)
                    ·
                      rfl

theorem cell23_5466048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 3, 1, 4].length) (baseStart_5466048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466048 prefixEnd_5466048 := by exact prefixLift 5466048
  have htrace : WordTrace (prefixWord ++ tailWord_5466048) baseStart_5466048 baseEnd_5466048 := by
    simpa [prefixWord, tailWord_5466048, baseEnd_5466048] using wordTrace_append hprefix tailTrace_5466048
  have hstable : (prefixWord ++ tailWord_5466048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466048).length < 2 ^ (prefixWord ++ tailWord_5466048).sum := by decide
  have hdescent : baseEnd_5466048 < baseStart_5466048 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466081 : List Nat := [1, 2, 3, 1, 2, 1, 3, 2, 1, 5, 2]
def baseStart_5466081 : Nat := 118140960795 + 5466081 * 2 ^ 59
def prefixEnd_5466081 : Nat := 4983230072969 + 3 ^ 40 * 5466081 * 2
def baseEnd_5466081 : Nat := 2806726849408733666649457

theorem tailTrace_5466081 : CollatzResearch.WordTrace tailWord_5466081 prefixEnd_5466081 2806726849408733666649457 := by
  unfold tailWord_5466081
  simp only [CollatzResearch.WordTrace]
  refine ⟨199364352510329544157606097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132909568340219696105070731 199364352510329544157606097)
  ·
    refine ⟨149523264382747158118204573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199364352510329544157606097 149523264382747158118204573)
    ·
      refine ⟨56071224143530184294326715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149523264382747158118204573 56071224143530184294326715)
      ·
        refine ⟨84106836215295276441490073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56071224143530184294326715 84106836215295276441490073)
        ·
          refine ⟨63080127161471457331117555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84106836215295276441490073 63080127161471457331117555)
          ·
            refine ⟨94620190742207185996676333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63080127161471457331117555 94620190742207185996676333)
            ·
              refine ⟨35482571528327694748753625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94620190742207185996676333 35482571528327694748753625)
              ·
                refine ⟨26611928646245771061565219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35482571528327694748753625 26611928646245771061565219)
                ·
                  refine ⟨39917892969368656592347829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26611928646245771061565219 39917892969368656592347829)
                  ·
                    refine ⟨3742302465878311555532609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39917892969368656592347829 3742302465878311555532609)
                    ·
                      refine ⟨2806726849408733666649457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3742302465878311555532609 2806726849408733666649457)
                      ·
                        rfl

theorem cell23_5466081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 5, 2].length) (baseStart_5466081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466081 prefixEnd_5466081 := by exact prefixLift 5466081
  have htrace : WordTrace (prefixWord ++ tailWord_5466081) baseStart_5466081 baseEnd_5466081 := by
    simpa [prefixWord, tailWord_5466081, baseEnd_5466081] using wordTrace_append hprefix tailTrace_5466081
  have hstable : (prefixWord ++ tailWord_5466081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466081).length < 2 ^ (prefixWord ++ tailWord_5466081).sum := by decide
  have hdescent : baseEnd_5466081 < baseStart_5466081 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466104 : List Nat := [2, 1, 2, 1, 1, 3, 2, 4, 1, 6]
def baseStart_5466104 : Nat := 118140960795 + 5466104 * 2 ^ 59
def prefixEnd_5466104 : Nat := 4983230072969 + 3 ^ 40 * 5466104 * 2
def baseEnd_5466104 : Nat := 935579553154595692220617

theorem tailTrace_5466104 : CollatzResearch.WordTrace tailWord_5466104 prefixEnd_5466104 935579553154595692220617 := by
  unfold tailWord_5466104
  simp only [CollatzResearch.WordTrace]
  refine ⟨99682595694623109542846683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132910127592830812723795577 99682595694623109542846683)
  ·
    refine ⟨149523893541934664314270025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99682595694623109542846683 149523893541934664314270025)
    ·
      refine ⟨112142920156450998235702519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149523893541934664314270025 112142920156450998235702519)
      ·
        refine ⟨168214380234676497353553779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112142920156450998235702519 168214380234676497353553779)
        ·
          refine ⟨252321570352014746030330669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168214380234676497353553779 252321570352014746030330669)
          ·
            refine ⟨94620588882005529761374001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 252321570352014746030330669 94620588882005529761374001)
            ·
              refine ⟨70965441661504147321030501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94620588882005529761374001 70965441661504147321030501)
              ·
                refine ⟨13306020311532027622693219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70965441661504147321030501 13306020311532027622693219)
                ·
                  refine ⟨19959030467298041434039829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13306020311532027622693219 19959030467298041434039829)
                  ·
                    refine ⟨935579553154595692220617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19959030467298041434039829 935579553154595692220617)
                    ·
                      rfl

theorem cell23_5466104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 1, 6].length) (baseStart_5466104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466104 prefixEnd_5466104 := by exact prefixLift 5466104
  have htrace : WordTrace (prefixWord ++ tailWord_5466104) baseStart_5466104 baseEnd_5466104 := by
    simpa [prefixWord, tailWord_5466104, baseEnd_5466104] using wordTrace_append hprefix tailTrace_5466104
  have hstable : (prefixWord ++ tailWord_5466104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466104).length < 2 ^ (prefixWord ++ tailWord_5466104).sum := by decide
  have hdescent : baseEnd_5466104 < baseStart_5466104 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466105 : List Nat := [1, 2, 1, 3, 1, 4, 3, 3, 1, 1, 3]
def baseStart_5466105 : Nat := 118140960795 + 5466105 * 2 ^ 59
def prefixEnd_5466105 : Nat := 4983230072969 + 3 ^ 40 * 5466105 * 2
def baseEnd_5466105 : Nat := 2806739172944441572749347

theorem tailTrace_5466105 : CollatzResearch.WordTrace tailWord_5466105 prefixEnd_5466105 2806739172944441572749347 := by
  unfold tailWord_5466105
  simp only [CollatzResearch.WordTrace]
  refine ⟨199365227862242596256479769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132910151908161730837653179 199365227862242596256479769)
  ·
    refine ⟨149523920896681947192359827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199365227862242596256479769 149523920896681947192359827)
    ·
      refine ⟨224285881345022920788539741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149523920896681947192359827 224285881345022920788539741)
      ·
        refine ⟨84107205504383595295702403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 224285881345022920788539741 84107205504383595295702403)
        ·
          refine ⟨126160808256575392943553605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84107205504383595295702403 126160808256575392943553605)
          ·
            refine ⟨23655151548107886176916301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126160808256575392943553605 23655151548107886176916301)
            ·
              refine ⟨8870681830540457316343613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23655151548107886176916301 8870681830540457316343613)
              ·
                refine ⟨3326505686452671493628855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8870681830540457316343613 3326505686452671493628855)
                ·
                  refine ⟨4989758529679007240443283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3326505686452671493628855 4989758529679007240443283)
                  ·
                    refine ⟨7484637794518510860664925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4989758529679007240443283 7484637794518510860664925)
                    ·
                      refine ⟨2806739172944441572749347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7484637794518510860664925 2806739172944441572749347)
                      ·
                        rfl

theorem cell23_5466105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 3, 1, 1, 3].length) (baseStart_5466105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466105 prefixEnd_5466105 := by exact prefixLift 5466105
  have htrace : WordTrace (prefixWord ++ tailWord_5466105) baseStart_5466105 baseEnd_5466105 := by
    simpa [prefixWord, tailWord_5466105, baseEnd_5466105] using wordTrace_append hprefix tailTrace_5466105
  have hstable : (prefixWord ++ tailWord_5466105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466105).length < 2 ^ (prefixWord ++ tailWord_5466105).sum := by decide
  have hdescent : baseEnd_5466105 < baseStart_5466105 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466122 : List Nat := [3, 1, 2, 2, 5, 1, 1, 1, 3, 1, 3]
def baseStart_5466122 : Nat := 118140960795 + 5466122 * 2 ^ 59
def prefixEnd_5466122 : Nat := 4983230072969 + 3 ^ 40 * 5466122 * 2
def baseEnd_5466122 : Nat := 2806747902115568006236769

theorem tailTrace_5466122 : CollatzResearch.WordTrace tailWord_5466122 prefixEnd_5466122 2806747902115568006236769 := by
  unfold tailWord_5466122
  simp only [CollatzResearch.WordTrace]
  refine ⟨49841461975795252039962155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132910565268787338773232413 49841461975795252039962155)
  ·
    refine ⟨74762192963692878059943233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49841461975795252039962155 74762192963692878059943233)
    ·
      refine ⟨56071644722769658544957425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74762192963692878059943233 56071644722769658544957425)
      ·
        refine ⟨42053733542077243908718069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56071644722769658544957425 42053733542077243908718069)
        ·
          refine ⟨3942537519569741616442319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42053733542077243908718069 3942537519569741616442319)
          ·
            refine ⟨5913806279354612424663479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3942537519569741616442319 5913806279354612424663479)
            ·
              refine ⟨8870709419031918636995219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5913806279354612424663479 8870709419031918636995219)
              ·
                refine ⟨13306064128547877955492829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8870709419031918636995219 13306064128547877955492829)
                ·
                  refine ⟨4989774048205454233309811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13306064128547877955492829 4989774048205454233309811)
                  ·
                    refine ⟨7484661072308181349964717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4989774048205454233309811 7484661072308181349964717)
                    ·
                      refine ⟨2806747902115568006236769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7484661072308181349964717 2806747902115568006236769)
                      ·
                        rfl

theorem cell23_5466122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 3, 1, 3].length) (baseStart_5466122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466122 prefixEnd_5466122 := by exact prefixLift 5466122
  have htrace : WordTrace (prefixWord ++ tailWord_5466122) baseStart_5466122 baseEnd_5466122 := by
    simpa [prefixWord, tailWord_5466122, baseEnd_5466122] using wordTrace_append hprefix tailTrace_5466122
  have hstable : (prefixWord ++ tailWord_5466122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466122).length < 2 ^ (prefixWord ++ tailWord_5466122).sum := by decide
  have hdescent : baseEnd_5466122 < baseStart_5466122 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466124 : List Nat := [2, 2, 1, 2, 3, 1, 1, 1, 3, 1, 6]
def baseStart_5466124 : Nat := 118140960795 + 5466124 * 2 ^ 59
def prefixEnd_5466124 : Nat := 4983230072969 + 3 ^ 40 * 5466124 * 2
def baseEnd_5466124 : Nat := 2806748929076876998411759

theorem tailTrace_5466124 : CollatzResearch.WordTrace tailWord_5466124 prefixEnd_5466124 2806748929076876998411759 := by
  unfold tailWord_5466124
  simp only [CollatzResearch.WordTrace]
  refine ⟨99682960424586881250710713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132910613899449175000947617 99682960424586881250710713)
  ·
    refine ⟨74762220318440160938033035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99682960424586881250710713 74762220318440160938033035)
    ·
      refine ⟨112143330477660241407049553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74762220318440160938033035 112143330477660241407049553)
      ·
        refine ⟨84107497858245181055287165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112143330477660241407049553 84107497858245181055287165)
        ·
          refine ⟨31540311696841942895732687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84107497858245181055287165 31540311696841942895732687)
          ·
            refine ⟨47310467545262914343599031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31540311696841942895732687 47310467545262914343599031)
            ·
              refine ⟨70965701317894371515398547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47310467545262914343599031 70965701317894371515398547)
              ·
                refine ⟨106448551976841557273097821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70965701317894371515398547 106448551976841557273097821)
                ·
                  refine ⟨39918206991315583977411683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106448551976841557273097821 39918206991315583977411683)
                  ·
                    refine ⟨59877310486973375966117525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39918206991315583977411683 59877310486973375966117525)
                    ·
                      refine ⟨2806748929076876998411759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59877310486973375966117525 2806748929076876998411759)
                      ·
                        rfl

theorem cell23_5466124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_5466124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466124 prefixEnd_5466124 := by exact prefixLift 5466124
  have htrace : WordTrace (prefixWord ++ tailWord_5466124) baseStart_5466124 baseEnd_5466124 := by
    simpa [prefixWord, tailWord_5466124, baseEnd_5466124] using wordTrace_append hprefix tailTrace_5466124
  have hstable : (prefixWord ++ tailWord_5466124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466124).length < 2 ^ (prefixWord ++ tailWord_5466124).sum := by decide
  have hdescent : baseEnd_5466124 < baseStart_5466124 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466138 : List Nat := [3, 1, 1, 3, 1, 4, 1, 3, 2, 4]
def baseStart_5466138 : Nat := 118140960795 + 5466138 * 2 ^ 59
def prefixEnd_5466138 : Nat := 4983230072969 + 3 ^ 40 * 5466138 * 2
def baseEnd_5466138 : Nat := 935585372602013314545565

theorem tailTrace_5466138 : CollatzResearch.WordTrace tailWord_5466138 prefixEnd_5466138 935585372602013314545565 := by
  unfold tailWord_5466138
  simp only [CollatzResearch.WordTrace]
  refine ⟨49841607867780760723107767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132910954314082028594954045 49841607867780760723107767)
  ·
    refine ⟨74762411801671141084661651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49841607867780760723107767 74762411801671141084661651)
    ·
      refine ⟨112143617702506711626992477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74762411801671141084661651 112143617702506711626992477)
      ·
        refine ⟨42053856638440016860122179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112143617702506711626992477 42053856638440016860122179)
        ·
          refine ⟨63080784957660025290183269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42053856638440016860122179 63080784957660025290183269)
          ·
            refine ⟨11827647179561254741909363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63080784957660025290183269 11827647179561254741909363)
            ·
              refine ⟨17741470769341882112864045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11827647179561254741909363 17741470769341882112864045)
              ·
                refine ⟨6653051538503205792324017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17741470769341882112864045 6653051538503205792324017)
                ·
                  refine ⟨4989788653877404344243013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6653051538503205792324017 4989788653877404344243013)
                  ·
                    refine ⟨935585372602013314545565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4989788653877404344243013 935585372602013314545565)
                    ·
                      rfl

theorem cell23_5466138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 3, 2, 4].length) (baseStart_5466138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466138 prefixEnd_5466138 := by exact prefixLift 5466138
  have htrace : WordTrace (prefixWord ++ tailWord_5466138) baseStart_5466138 baseEnd_5466138 := by
    simpa [prefixWord, tailWord_5466138, baseEnd_5466138] using wordTrace_append hprefix tailTrace_5466138
  have hstable : (prefixWord ++ tailWord_5466138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466138).length < 2 ^ (prefixWord ++ tailWord_5466138).sum := by decide
  have hdescent : baseEnd_5466138 < baseStart_5466138 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466141 : List Nat := [1, 4, 2, 2, 2, 1, 2, 1, 1, 1, 6]
def baseStart_5466141 : Nat := 118140960795 + 5466141 * 2 ^ 59
def prefixEnd_5466141 : Nat := 4983230072969 + 3 ^ 40 * 5466141 * 2
def baseEnd_5466141 : Nat := 2806757658248003431899181

theorem tailTrace_5466141 : CollatzResearch.WordTrace tailWord_5466141 prefixEnd_5466141 2806757658248003431899181 := by
  unfold tailWord_5466141
  simp only [CollatzResearch.WordTrace]
  refine ⟨199366540890112174404790277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132911027260074782936526851 199366540890112174404790277)
  ·
    refine ⟨37381226416896032700898177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 199366540890112174404790277 37381226416896032700898177)
    ·
      refine ⟨28035919812672024525673633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37381226416896032700898177 28035919812672024525673633)
      ·
        refine ⟨21026939859504018394255225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28035919812672024525673633 21026939859504018394255225)
        ·
          refine ⟨15770204894628013795691419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21026939859504018394255225 15770204894628013795691419)
          ·
            refine ⟨23655307341942020693537129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15770204894628013795691419 23655307341942020693537129)
            ·
              refine ⟨17741480506456515520152847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23655307341942020693537129 17741480506456515520152847)
              ·
                refine ⟨26612220759684773280229271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17741480506456515520152847 26612220759684773280229271)
                ·
                  refine ⟨39918331139527159920343907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26612220759684773280229271 39918331139527159920343907)
                  ·
                    refine ⟨59877496709290739880515861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39918331139527159920343907 59877496709290739880515861)
                    ·
                      refine ⟨2806757658248003431899181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59877496709290739880515861 2806757658248003431899181)
                      ·
                        rfl

theorem cell23_5466141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_5466141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466141 prefixEnd_5466141 := by exact prefixLift 5466141
  have htrace : WordTrace (prefixWord ++ tailWord_5466141) baseStart_5466141 baseEnd_5466141 := by
    simpa [prefixWord, tailWord_5466141, baseEnd_5466141] using wordTrace_append hprefix tailTrace_5466141
  have hstable : (prefixWord ++ tailWord_5466141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466141).length < 2 ^ (prefixWord ++ tailWord_5466141).sum := by decide
  have hdescent : baseEnd_5466141 < baseStart_5466141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466145 : List Nat := [1, 2, 3, 2, 4, 2, 1, 2, 1, 1, 4]
def baseStart_5466145 : Nat := 118140960795 + 5466145 * 2 ^ 59
def prefixEnd_5466145 : Nat := 4983230072969 + 3 ^ 40 * 5466145 * 2
def baseEnd_5466145 : Nat := 2806759712170621416249163

theorem tailTrace_5466145 : CollatzResearch.WordTrace tailWord_5466145 prefixEnd_5466145 2806759712170621416249163 := by
  unfold tailWord_5466145
  simp only [CollatzResearch.WordTrace]
  refine ⟨199366686782097683087935889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132911124521398455391957259 199366686782097683087935889)
  ·
    refine ⟨149525015086573262315951917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199366686782097683087935889 149525015086573262315951917)
    ·
      refine ⟨56071880657464973368481969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149525015086573262315951917 56071880657464973368481969)
      ·
        refine ⟨42053910493098730026361477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56071880657464973368481969 42053910493098730026361477)
        ·
          refine ⟨7885108217456011879942777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42053910493098730026361477 7885108217456011879942777)
          ·
            refine ⟨5913831163092008909957083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7885108217456011879942777 5913831163092008909957083)
            ·
              refine ⟨8870746744638013364935625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5913831163092008909957083 8870746744638013364935625)
              ·
                refine ⟨6653060058478510023701719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8870746744638013364935625 6653060058478510023701719)
                ·
                  refine ⟨9979590087717765035552579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6653060058478510023701719 9979590087717765035552579)
                  ·
                    refine ⟨14969385131576647553328869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9979590087717765035552579 14969385131576647553328869)
                    ·
                      refine ⟨2806759712170621416249163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14969385131576647553328869 2806759712170621416249163)
                      ·
                        rfl

theorem cell23_5466145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_5466145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466145 prefixEnd_5466145 := by exact prefixLift 5466145
  have htrace : WordTrace (prefixWord ++ tailWord_5466145) baseStart_5466145 baseEnd_5466145 := by
    simpa [prefixWord, tailWord_5466145, baseEnd_5466145] using wordTrace_append hprefix tailTrace_5466145
  have hstable : (prefixWord ++ tailWord_5466145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466145).length < 2 ^ (prefixWord ++ tailWord_5466145).sum := by decide
  have hdescent : baseEnd_5466145 < baseStart_5466145 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466158 : List Nat := [4, 1, 3, 1, 1, 3, 1, 2, 1, 2, 4]
def baseStart_5466158 : Nat := 118140960795 + 5466158 * 2 ^ 59
def prefixEnd_5466158 : Nat := 4983230072969 + 3 ^ 40 * 5466158 * 2
def baseEnd_5466158 : Nat := 2806766387419129865386603

theorem tailTrace_5466158 : CollatzResearch.WordTrace tailWord_5466158 prefixEnd_5466158 2806766387419129865386603 := by
  unfold tailWord_5466158
  simp only [CollatzResearch.WordTrace]
  refine ⟨24920895116381323288519891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132911440620700390872106085 24920895116381323288519891)
  ·
    refine ⟨37381342674571984932779837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24920895116381323288519891 37381342674571984932779837)
    ·
      refine ⟨14018003502964494349792439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37381342674571984932779837 14018003502964494349792439)
      ·
        refine ⟨21027005254446741524688659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14018003502964494349792439 21027005254446741524688659)
        ·
          refine ⟨31540507881670112287032989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21027005254446741524688659 31540507881670112287032989)
          ·
            refine ⟨11827690455626292107637371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31540507881670112287032989 11827690455626292107637371)
            ·
              refine ⟨17741535683439438161456057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11827690455626292107637371 17741535683439438161456057)
              ·
                refine ⟨13306151762579578621092043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17741535683439438161456057 13306151762579578621092043)
                ·
                  refine ⟨19959227643869367931638065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13306151762579578621092043 19959227643869367931638065)
                  ·
                    refine ⟨14969420732902025948728549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19959227643869367931638065 14969420732902025948728549)
                    ·
                      refine ⟨2806766387419129865386603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14969420732902025948728549 2806766387419129865386603)
                      ·
                        rfl

theorem cell23_5466158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_5466158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466158 prefixEnd_5466158 := by exact prefixLift 5466158
  have htrace : WordTrace (prefixWord ++ tailWord_5466158) baseStart_5466158 baseEnd_5466158 := by
    simpa [prefixWord, tailWord_5466158, baseEnd_5466158] using wordTrace_append hprefix tailTrace_5466158
  have hstable : (prefixWord ++ tailWord_5466158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466158).length < 2 ^ (prefixWord ++ tailWord_5466158).sum := by decide
  have hdescent : baseEnd_5466158 < baseStart_5466158 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466161 : List Nat := [1, 2, 2, 3, 1, 3, 1, 1, 3, 3, 3]
def baseStart_5466161 : Nat := 118140960795 + 5466161 * 2 ^ 59
def prefixEnd_5466161 : Nat := 4983230072969 + 3 ^ 40 * 5466161 * 2
def baseEnd_5466161 : Nat := 2806767927861093353649089

theorem tailTrace_5466161 : CollatzResearch.WordTrace tailWord_5466161 prefixEnd_5466161 2806767927861093353649089 := by
  unfold tailWord_5466161
  simp only [CollatzResearch.WordTrace]
  refine ⟨199367270350039717820518337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132911513566693145213678891 199367270350039717820518337)
  ·
    refine ⟨149525452762529788365388753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199367270350039717820518337 149525452762529788365388753)
    ·
      refine ⟨112144089571897341274041565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149525452762529788365388753 112144089571897341274041565)
      ·
        refine ⟨42054033589461502977765587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112144089571897341274041565 42054033589461502977765587)
        ·
          refine ⟨63081050384192254466648381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42054033589461502977765587 63081050384192254466648381)
          ·
            refine ⟨23655393894072095424993143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63081050384192254466648381 23655393894072095424993143)
            ·
              refine ⟨35483090841108143137489715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23655393894072095424993143 35483090841108143137489715)
              ·
                refine ⟨53224636261662214706234573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35483090841108143137489715 53224636261662214706234573)
                ·
                  refine ⟨19959238598123330514837965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53224636261662214706234573 19959238598123330514837965)
                  ·
                    refine ⟨7484714474296248943064237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19959238598123330514837965 7484714474296248943064237)
                    ·
                      refine ⟨2806767927861093353649089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7484714474296248943064237 2806767927861093353649089)
                      ·
                        rfl

theorem cell23_5466161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_5466161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466161 prefixEnd_5466161 := by exact prefixLift 5466161
  have htrace : WordTrace (prefixWord ++ tailWord_5466161) baseStart_5466161 baseEnd_5466161 := by
    simpa [prefixWord, tailWord_5466161, baseEnd_5466161] using wordTrace_append hprefix tailTrace_5466161
  have hstable : (prefixWord ++ tailWord_5466161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466161).length < 2 ^ (prefixWord ++ tailWord_5466161).sum := by decide
  have hdescent : baseEnd_5466161 < baseStart_5466161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466188 : List Nat := [2, 2, 1, 3, 1, 1, 3, 2, 3, 3, 2]
def baseStart_5466188 : Nat := 118140960795 + 5466188 * 2 ^ 59
def prefixEnd_5466188 : Nat := 4983230072969 + 3 ^ 40 * 5466188 * 2
def baseEnd_5466188 : Nat := 2806781791838764748011465

theorem tailTrace_5466188 : CollatzResearch.WordTrace tailWord_5466188 prefixEnd_5466188 2806781791838764748011465 := by
  unfold tailWord_5466188
  simp only [CollatzResearch.WordTrace]
  refine ⟨99684127560470950715875609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132912170080627934287834145 99684127560470950715875609)
  ·
    refine ⟨74763095670353213036906707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99684127560470950715875609 74763095670353213036906707)
    ·
      refine ⟨112144643505529819555360061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74763095670353213036906707 112144643505529819555360061)
      ·
        refine ⟨42054241314573682333260023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112144643505529819555360061 42054241314573682333260023)
        ·
          refine ⟨63081361971860523499890035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42054241314573682333260023 63081361971860523499890035)
          ·
            refine ⟨94622042957790785249835053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63081361971860523499890035 94622042957790785249835053)
            ·
              refine ⟨35483266109171544468688145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94622042957790785249835053 35483266109171544468688145)
              ·
                refine ⟨26612449581878658351516109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35483266109171544468688145 26612449581878658351516109)
                ·
                  refine ⟨9979668593204496881818541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26612449581878658351516109 9979668593204496881818541)
                  ·
                    refine ⟨3742375722451686330681953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9979668593204496881818541 3742375722451686330681953)
                    ·
                      refine ⟨2806781791838764748011465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3742375722451686330681953 2806781791838764748011465)
                      ·
                        rfl

theorem cell23_5466188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 3, 3, 2].length) (baseStart_5466188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466188 prefixEnd_5466188 := by exact prefixLift 5466188
  have htrace : WordTrace (prefixWord ++ tailWord_5466188) baseStart_5466188 baseEnd_5466188 := by
    simpa [prefixWord, tailWord_5466188, baseEnd_5466188] using wordTrace_append hprefix tailTrace_5466188
  have hstable : (prefixWord ++ tailWord_5466188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466188).length < 2 ^ (prefixWord ++ tailWord_5466188).sum := by decide
  have hdescent : baseEnd_5466188 < baseStart_5466188 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466221 : List Nat := [1, 5, 1, 1, 2, 1, 2, 1, 1, 3, 5]
def baseStart_5466221 : Nat := 118140960795 + 5466221 * 2 ^ 59
def prefixEnd_5466221 : Nat := 4983230072969 + 3 ^ 40 * 5466221 * 2
def baseEnd_5466221 : Nat := 2806798736700363118898813

theorem tailTrace_5466221 : CollatzResearch.WordTrace tailWord_5466221 prefixEnd_5466221 2806798736700363118898813 := by
  unfold tailWord_5466221
  simp only [CollatzResearch.WordTrace]
  refine ⟨199369458729822348067702517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132912972486548232045135011 199369458729822348067702517)
  ·
    refine ⟨18690886755920845131347111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 199369458729822348067702517 18690886755920845131347111)
    ·
      refine ⟨28036330133881267697020667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18690886755920845131347111 28036330133881267697020667)
      ·
        refine ⟨42054495200821901545531001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28036330133881267697020667 42054495200821901545531001)
        ·
          refine ⟨31540871400616426159148251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42054495200821901545531001 31540871400616426159148251)
          ·
            refine ⟨47311307100924639238722377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31540871400616426159148251 47311307100924639238722377)
            ·
              refine ⟨35483480325693479429041783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47311307100924639238722377 35483480325693479429041783)
              ·
                refine ⟨53225220488540219143562675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35483480325693479429041783 53225220488540219143562675)
                ·
                  refine ⟨79837830732810328715344013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53225220488540219143562675 79837830732810328715344013)
                  ·
                    refine ⟨29939186524803873268254005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 79837830732810328715344013 29939186524803873268254005)
                    ·
                      refine ⟨2806798736700363118898813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29939186524803873268254005 2806798736700363118898813)
                      ·
                        rfl

theorem cell23_5466221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_5466221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466221 prefixEnd_5466221 := by exact prefixLift 5466221
  have htrace : WordTrace (prefixWord ++ tailWord_5466221) baseStart_5466221 baseEnd_5466221 := by
    simpa [prefixWord, tailWord_5466221, baseEnd_5466221] using wordTrace_append hprefix tailTrace_5466221
  have hstable : (prefixWord ++ tailWord_5466221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466221).length < 2 ^ (prefixWord ++ tailWord_5466221).sum := by decide
  have hdescent : baseEnd_5466221 < baseStart_5466221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466231 : List Nat := [1, 1, 3, 1, 1, 5, 1, 2, 2, 2, 4]
def baseStart_5466231 : Nat := 118140960795 + 5466231 * 2 ^ 59
def prefixEnd_5466231 : Nat := 4983230072969 + 3 ^ 40 * 5466231 * 2
def baseEnd_5466231 : Nat := 2806803871506908079773767

theorem tailTrace_5466231 : CollatzResearch.WordTrace tailWord_5466231 prefixEnd_5466231 2806803871506908079773767 := by
  unfold tailWord_5466231
  simp only [CollatzResearch.WordTrace]
  refine ⟨199369823459786119775566547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132913215639857413183711031 199369823459786119775566547)
  ·
    refine ⟨299054735189679179663349821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199369823459786119775566547 299054735189679179663349821)
    ·
      refine ⟨112145525696129692373756183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 299054735189679179663349821 112145525696129692373756183)
      ·
        refine ⟨168218288544194538560634275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112145525696129692373756183 168218288544194538560634275)
        ·
          refine ⟨252327432816291807840951413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168218288544194538560634275 252327432816291807840951413)
          ·
            refine ⟨23655696826527356985089195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 252327432816291807840951413 23655696826527356985089195)
            ·
              refine ⟨35483545239791035477633793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23655696826527356985089195 35483545239791035477633793)
              ·
                refine ⟨26612658929843276608225345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35483545239791035477633793 26612658929843276608225345)
                ·
                  refine ⟨19959494197382457456169009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26612658929843276608225345 19959494197382457456169009)
                  ·
                    refine ⟨14969620648036843092126757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19959494197382457456169009 14969620648036843092126757)
                    ·
                      refine ⟨2806803871506908079773767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14969620648036843092126757 2806803871506908079773767)
                      ·
                        rfl

theorem cell23_5466231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 2, 4].length) (baseStart_5466231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466231 prefixEnd_5466231 := by exact prefixLift 5466231
  have htrace : WordTrace (prefixWord ++ tailWord_5466231) baseStart_5466231 baseEnd_5466231 := by
    simpa [prefixWord, tailWord_5466231, baseEnd_5466231] using wordTrace_append hprefix tailTrace_5466231
  have hstable : (prefixWord ++ tailWord_5466231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466231).length < 2 ^ (prefixWord ++ tailWord_5466231).sum := by decide
  have hdescent : baseEnd_5466231 < baseStart_5466231 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466248 : List Nat := [2, 1, 3, 4, 1, 1, 2, 1, 2, 2, 4]
def baseStart_5466248 : Nat := 118140960795 + 5466248 * 2 ^ 59
def prefixEnd_5466248 : Nat := 4983230072969 + 3 ^ 40 * 5466248 * 2
def baseEnd_5466248 : Nat := 2806812600678034513261189

theorem tailTrace_5466248 : CollatzResearch.WordTrace tailWord_5466248 prefixEnd_5466248 2806812600678034513261189 := by
  unfold tailWord_5466248
  simp only [CollatzResearch.WordTrace]
  refine ⟨99685221750362265839467699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132913629000483021119290265 99685221750362265839467699)
  ·
    refine ⟨149527832625543398759201549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99685221750362265839467699 149527832625543398759201549)
    ·
      refine ⟨56072937234578774534700581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149527832625543398759201549 56072937234578774534700581)
      ·
        refine ⟨10513675731483520225256359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56072937234578774534700581 10513675731483520225256359)
        ·
          refine ⟨15770513597225280337884539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10513675731483520225256359 15770513597225280337884539)
          ·
            refine ⟨23655770395837920506826809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15770513597225280337884539 23655770395837920506826809)
            ·
              refine ⟨17741827796878440380120107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23655770395837920506826809 17741827796878440380120107)
              ·
                refine ⟨26612741695317660570180161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17741827796878440380120107 26612741695317660570180161)
                ·
                  refine ⟨19959556271488245427635121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26612741695317660570180161 19959556271488245427635121)
                  ·
                    refine ⟨14969667203616184070726341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19959556271488245427635121 14969667203616184070726341)
                    ·
                      refine ⟨2806812600678034513261189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14969667203616184070726341 2806812600678034513261189)
                      ·
                        rfl

theorem cell23_5466248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_5466248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466248 prefixEnd_5466248 := by exact prefixLift 5466248
  have htrace : WordTrace (prefixWord ++ tailWord_5466248) baseStart_5466248 baseEnd_5466248 := by
    simpa [prefixWord, tailWord_5466248, baseEnd_5466248] using wordTrace_append hprefix tailTrace_5466248
  have hstable : (prefixWord ++ tailWord_5466248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466248).length < 2 ^ (prefixWord ++ tailWord_5466248).sum := by decide
  have hdescent : baseEnd_5466248 < baseStart_5466248 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466321 : List Nat := [1, 2, 2, 1, 2, 2, 2, 1, 2, 4, 4]
def baseStart_5466321 : Nat := 118140960795 + 5466321 * 2 ^ 59
def prefixEnd_5466321 : Nat := 4983230072969 + 3 ^ 40 * 5466321 * 2
def baseEnd_5466321 : Nat := 2806850084765812727648353

theorem tailTrace_5466321 : CollatzResearch.WordTrace tailWord_5466321 prefixEnd_5466321 2806850084765812727648353 := by
  unfold tailWord_5466321
  simp only [CollatzResearch.WordTrace]
  refine ⟨199373106029460065146342817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132915404019640043430895211 199373106029460065146342817)
  ·
    refine ⟨149529829522095048859757113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199373106029460065146342817 149529829522095048859757113)
    ·
      refine ⟨112147372141571286644817835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149529829522095048859757113 112147372141571286644817835)
      ·
        refine ⟨168221058212356929967226753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112147372141571286644817835 168221058212356929967226753)
        ·
          refine ⟨126165793659267697475420065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168221058212356929967226753 126165793659267697475420065)
          ·
            refine ⟨94624345244450773106565049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126165793659267697475420065 94624345244450773106565049)
            ·
              refine ⟨70968258933338079829923787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94624345244450773106565049 70968258933338079829923787)
              ·
                refine ⟨106452388400007119744885681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70968258933338079829923787 106452388400007119744885681)
                ·
                  refine ⟨79839291300005339808664261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106452388400007119744885681 79839291300005339808664261)
                  ·
                    refine ⟨14969867118751001214124549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 79839291300005339808664261 14969867118751001214124549)
                    ·
                      refine ⟨2806850084765812727648353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14969867118751001214124549 2806850084765812727648353)
                      ·
                        rfl

theorem cell23_5466321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 4, 4].length) (baseStart_5466321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466321 prefixEnd_5466321 := by exact prefixLift 5466321
  have htrace : WordTrace (prefixWord ++ tailWord_5466321) baseStart_5466321 baseEnd_5466321 := by
    simpa [prefixWord, tailWord_5466321, baseEnd_5466321] using wordTrace_append hprefix tailTrace_5466321
  have hstable : (prefixWord ++ tailWord_5466321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466321).length < 2 ^ (prefixWord ++ tailWord_5466321).sum := by decide
  have hdescent : baseEnd_5466321 < baseStart_5466321 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466335 : List Nat := [1, 1, 2, 3, 2, 1, 1, 7, 1, 4]
def baseStart_5466335 : Nat := 118140960795 + 5466335 * 2 ^ 59
def prefixEnd_5466335 : Nat := 4983230072969 + 3 ^ 40 * 5466335 * 2
def baseEnd_5466335 : Nat := 935619091164991890957763

theorem tailTrace_5466335 : CollatzResearch.WordTrace tailWord_5466335 prefixEnd_5466335 935619091164991890957763 := by
  unfold tailWord_5466335
  simp only [CollatzResearch.WordTrace]
  refine ⟨199373616651409345537352459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132915744434272897024901639 199373616651409345537352459)
  ·
    refine ⟨299060424977114018306028689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199373616651409345537352459 299060424977114018306028689)
    ·
      refine ⟨224295318732835513729521517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299060424977114018306028689 224295318732835513729521517)
      ·
        refine ⟨84110744524813317648570569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 224295318732835513729521517 84110744524813317648570569)
        ·
          refine ⟨63083058393609988236427927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84110744524813317648570569 63083058393609988236427927)
          ·
            refine ⟨94624587590414982354641891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63083058393609988236427927 94624587590414982354641891)
            ·
              refine ⟨141936881385622473531962837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94624587590414982354641891 141936881385622473531962837)
              ·
                refine ⟨3326645657475526723405379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 141936881385622473531962837 3326645657475526723405379)
                ·
                  refine ⟨4989968486213290085108069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3326645657475526723405379 4989968486213290085108069)
                  ·
                    refine ⟨935619091164991890957763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4989968486213290085108069 935619091164991890957763)
                    ·
                      rfl

theorem cell23_5466335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 7, 1, 4].length) (baseStart_5466335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466335 prefixEnd_5466335 := by exact prefixLift 5466335
  have htrace : WordTrace (prefixWord ++ tailWord_5466335) baseStart_5466335 baseEnd_5466335 := by
    simpa [prefixWord, tailWord_5466335, baseEnd_5466335] using wordTrace_append hprefix tailTrace_5466335
  have hstable : (prefixWord ++ tailWord_5466335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466335).length < 2 ^ (prefixWord ++ tailWord_5466335).sum := by decide
  have hdescent : baseEnd_5466335 < baseStart_5466335 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466348 : List Nat := [2, 2, 1, 1, 2, 3, 4, 2, 6]
def baseStart_5466348 : Nat := 118140960795 + 5466348 * 2 ^ 59
def prefixEnd_5466348 : Nat := 4983230072969 + 3 ^ 40 * 5466348 * 2
def baseEnd_5466348 : Nat := 311873772082609346890081

theorem tailTrace_5466348 : CollatzResearch.WordTrace tailWord_5466348 prefixEnd_5466348 311873772082609346890081 := by
  unfold tailWord_5466348
  simp only [CollatzResearch.WordTrace]
  refine ⟨99687045400181124378787849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132916060533574832505050465 99687045400181124378787849)
  ·
    refine ⟨74765284050135843284090887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99687045400181124378787849 74765284050135843284090887)
    ·
      refine ⟨112147926075203764926136331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74765284050135843284090887 112147926075203764926136331)
      ·
        refine ⟨168221889112805647389204497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112147926075203764926136331 168221889112805647389204497)
        ·
          refine ⟨126166416834604235541903373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168221889112805647389204497 126166416834604235541903373)
          ·
            refine ⟨47312406312976588328213765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126166416834604235541903373 47312406312976588328213765)
            ·
              refine ⟨8871076183683110311540081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47312406312976588328213765 8871076183683110311540081)
              ·
                refine ⟨6653307137762332733655061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8871076183683110311540081 6653307137762332733655061)
                ·
                  refine ⟨311873772082609346890081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6653307137762332733655061 311873772082609346890081)
                  ·
                    rfl

theorem cell23_5466348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 6].length) (baseStart_5466348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466348 prefixEnd_5466348 := by exact prefixLift 5466348
  have htrace : WordTrace (prefixWord ++ tailWord_5466348) baseStart_5466348 baseEnd_5466348 := by
    simpa [prefixWord, tailWord_5466348, baseEnd_5466348] using wordTrace_append hprefix tailTrace_5466348
  have hstable : (prefixWord ++ tailWord_5466348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466348).length < 2 ^ (prefixWord ++ tailWord_5466348).sum := by decide
  have hdescent : baseEnd_5466348 < baseStart_5466348 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466371 : List Nat := [1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 7]
def baseStart_5466371 : Nat := 118140960795 + 5466371 * 2 ^ 59
def prefixEnd_5466371 : Nat := 4983230072969 + 3 ^ 40 * 5466371 * 2
def baseEnd_5466371 : Nat := 2806875758798537532023123

theorem tailTrace_5466371 : CollatzResearch.WordTrace tailWord_5466371 prefixEnd_5466371 2806875758798537532023123 := by
  unfold tailWord_5466371
  simp only [CollatzResearch.WordTrace]
  refine ⟨199374929679278923685662967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132916619786185949123775311 199374929679278923685662967)
  ·
    refine ⟨299062394518918385528494451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199374929679278923685662967 299062394518918385528494451)
    ·
      refine ⟨448593591778377578292741677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299062394518918385528494451 448593591778377578292741677)
      ·
        refine ⟨168222596916891591859778129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 448593591778377578292741677 168222596916891591859778129)
        ·
          refine ⟨126166947687668693894833597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168222596916891591859778129 126166947687668693894833597)
          ·
            refine ⟨47312605382875760210562599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126166947687668693894833597 47312605382875760210562599)
            ·
              refine ⟨70968908074313640315843899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47312605382875760210562599 70968908074313640315843899)
              ·
                refine ⟨106453362111470460473765849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70968908074313640315843899 106453362111470460473765849)
                ·
                  refine ⟨79840021583602845355324387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106453362111470460473765849 79840021583602845355324387)
                  ·
                    refine ⟨119760032375404268032986581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 79840021583602845355324387 119760032375404268032986581)
                    ·
                      refine ⟨2806875758798537532023123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 119760032375404268032986581 2806875758798537532023123)
                      ·
                        rfl

theorem cell23_5466371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 7].length) (baseStart_5466371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466371 prefixEnd_5466371 := by exact prefixLift 5466371
  have htrace : WordTrace (prefixWord ++ tailWord_5466371) baseStart_5466371 baseEnd_5466371 := by
    simpa [prefixWord, tailWord_5466371, baseEnd_5466371] using wordTrace_append hprefix tailTrace_5466371
  have hstable : (prefixWord ++ tailWord_5466371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466371).length < 2 ^ (prefixWord ++ tailWord_5466371).sum := by decide
  have hdescent : baseEnd_5466371 < baseStart_5466371 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466378 : List Nat := [3, 1, 2, 2, 1, 1, 4, 1, 3, 5]
def baseStart_5466378 : Nat := 118140960795 + 5466378 * 2 ^ 59
def prefixEnd_5466378 : Nat := 4983230072969 + 3 ^ 40 * 5466378 * 2
def baseEnd_5466378 : Nat := 935626451054373001545197

theorem tailTrace_5466378 : CollatzResearch.WordTrace tailWord_5466378 prefixEnd_5466378 935626451054373001545197 := by
  unfold tailWord_5466378
  simp only [CollatzResearch.WordTrace]
  refine ⟨49843796247563390970291947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132916789993502375920778525 49843796247563390970291947)
  ·
    refine ⟨74765694371345086455437921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49843796247563390970291947 74765694371345086455437921)
    ·
      refine ⟨56074270778508814841578441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74765694371345086455437921 56074270778508814841578441)
      ·
        refine ⟨42055703083881611131183831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56074270778508814841578441 42055703083881611131183831)
        ·
          refine ⟨63083554625822416696775747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42055703083881611131183831 63083554625822416696775747)
          ·
            refine ⟨94625331938733625045163621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63083554625822416696775747 94625331938733625045163621)
            ·
              refine ⟨17742249738512554695968179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94625331938733625045163621 17742249738512554695968179)
              ·
                refine ⟨26613374607768832043952269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17742249738512554695968179 26613374607768832043952269)
                ·
                  refine ⟨9980015477913312016482101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26613374607768832043952269 9980015477913312016482101)
                  ·
                    refine ⟨935626451054373001545197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9980015477913312016482101 935626451054373001545197)
                    ·
                      rfl

theorem cell23_5466378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 3, 5].length) (baseStart_5466378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466378 prefixEnd_5466378 := by exact prefixLift 5466378
  have htrace : WordTrace (prefixWord ++ tailWord_5466378) baseStart_5466378 baseEnd_5466378 := by
    simpa [prefixWord, tailWord_5466378, baseEnd_5466378] using wordTrace_append hprefix tailTrace_5466378
  have hstable : (prefixWord ++ tailWord_5466378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466378).length < 2 ^ (prefixWord ++ tailWord_5466378).sum := by decide
  have hdescent : baseEnd_5466378 < baseStart_5466378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466385 : List Nat := [1, 2, 2, 1, 1, 6, 1, 1, 1, 5, 2]
def baseStart_5466385 : Nat := 118140960795 + 5466385 * 2 ^ 59
def prefixEnd_5466385 : Nat := 4983230072969 + 3 ^ 40 * 5466385 * 2
def baseEnd_5466385 : Nat := 2806882947527700477248059

theorem tailTrace_5466385 : CollatzResearch.WordTrace tailWord_5466385 prefixEnd_5466385 2806882947527700477248059 := by
  unfold tailWord_5466385
  simp only [CollatzResearch.WordTrace]
  refine ⟨199375440301228204076672609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132916960200818802717781739 199375440301228204076672609)
  ·
    refine ⟨149531580225921153057504457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199375440301228204076672609 149531580225921153057504457)
    ·
      refine ⟨112148685169440864793128343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149531580225921153057504457 112148685169440864793128343)
      ·
        refine ⟨168223027754161297189692515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112148685169440864793128343 168223027754161297189692515)
        ·
          refine ⟨252334541631241945784538773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168223027754161297189692515 252334541631241945784538773)
          ·
            refine ⟨11828181638964466208650255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 252334541631241945784538773 11828181638964466208650255)
            ·
              refine ⟨17742272458446699312975383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11828181638964466208650255 17742272458446699312975383)
              ·
                refine ⟨26613408687670048969463075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17742272458446699312975383 26613408687670048969463075)
                ·
                  refine ⟨39920113031505073454194613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26613408687670048969463075 39920113031505073454194613)
                  ·
                    refine ⟨3742510596703600636330745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39920113031505073454194613 3742510596703600636330745)
                    ·
                      refine ⟨2806882947527700477248059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3742510596703600636330745 2806882947527700477248059)
                      ·
                        rfl

theorem cell23_5466385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 5, 2].length) (baseStart_5466385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466385 prefixEnd_5466385 := by exact prefixLift 5466385
  have htrace : WordTrace (prefixWord ++ tailWord_5466385) baseStart_5466385 baseEnd_5466385 := by
    simpa [prefixWord, tailWord_5466385, baseEnd_5466385] using wordTrace_append hprefix tailTrace_5466385
  have hstable : (prefixWord ++ tailWord_5466385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466385).length < 2 ^ (prefixWord ++ tailWord_5466385).sum := by decide
  have hdescent : baseEnd_5466385 < baseStart_5466385 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466395 : List Nat := [1, 1, 1, 1, 1, 1, 10, 1, 1, 5]
def baseStart_5466395 : Nat := 118140960795 + 5466395 * 2 ^ 59
def prefixEnd_5466395 : Nat := 4983230072969 + 3 ^ 40 * 5466395 * 2
def baseEnd_5466395 : Nat := 935629360778081812707671

theorem tailTrace_5466395 : CollatzResearch.WordTrace tailWord_5466395 prefixEnd_5466395 935629360778081812707671 := by
  unfold tailWord_5466395
  simp only [CollatzResearch.WordTrace]
  refine ⟨199375805031191975784536639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132917203354127983856357759 199375805031191975784536639)
  ·
    refine ⟨299063707546787963676804959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199375805031191975784536639 299063707546787963676804959)
    ·
      refine ⟨448595561320181945515207439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299063707546787963676804959 448595561320181945515207439)
      ·
        refine ⟨672893341980272918272811159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 448595561320181945515207439 672893341980272918272811159)
        ·
          refine ⟨1009340012970409377409216739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 672893341980272918272811159 1009340012970409377409216739)
          ·
            refine ⟨1514010019455614066113825109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1009340012970409377409216739 1514010019455614066113825109)
            ·
              refine ⟨4435576228873869334317847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1514010019455614066113825109 4435576228873869334317847)
              ·
                refine ⟨6653364343310804001476771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4435576228873869334317847 6653364343310804001476771)
                ·
                  refine ⟨9980046514966206002215157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6653364343310804001476771 9980046514966206002215157)
                  ·
                    refine ⟨935629360778081812707671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9980046514966206002215157 935629360778081812707671)
                    ·
                      rfl

theorem cell23_5466395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 1, 1, 5].length) (baseStart_5466395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466395 prefixEnd_5466395 := by exact prefixLift 5466395
  have htrace : WordTrace (prefixWord ++ tailWord_5466395) baseStart_5466395 baseEnd_5466395 := by
    simpa [prefixWord, tailWord_5466395, baseEnd_5466395] using wordTrace_append hprefix tailTrace_5466395
  have hstable : (prefixWord ++ tailWord_5466395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466395).length < 2 ^ (prefixWord ++ tailWord_5466395).sum := by decide
  have hdescent : baseEnd_5466395 < baseStart_5466395 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466425 : List Nat := [1, 2, 1, 6, 1, 1, 3, 1, 1, 6]
def baseStart_5466425 : Nat := 118140960795 + 5466425 * 2 ^ 59
def prefixEnd_5466425 : Nat := 4983230072969 + 3 ^ 40 * 5466425 * 2
def baseEnd_5466425 : Nat := 935634495584626773582625

theorem tailTrace_5466425 : CollatzResearch.WordTrace tailWord_5466425 prefixEnd_5466425 935634495584626773582625 := by
  unfold tailWord_5466425
  simp only [CollatzResearch.WordTrace]
  refine ⟨199376899221083290908128729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132917932814055527272085819 199376899221083290908128729)
  ·
    refine ⟨149532674415812468181096547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199376899221083290908128729 149532674415812468181096547)
    ·
      refine ⟨224299011623718702271644821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149532674415812468181096547 224299011623718702271644821)
      ·
        refine ⟨10514016169861814168983351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 224299011623718702271644821 10514016169861814168983351)
        ·
          refine ⟨15771024254792721253475027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10514016169861814168983351 15771024254792721253475027)
          ·
            refine ⟨23656536382189081880212541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15771024254792721253475027 23656536382189081880212541)
            ·
              refine ⟨8871201143320905705079703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23656536382189081880212541 8871201143320905705079703)
              ·
                refine ⟨13306801714981358557619555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8871201143320905705079703 13306801714981358557619555)
                ·
                  refine ⟨19960202572472037836429333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13306801714981358557619555 19960202572472037836429333)
                  ·
                    refine ⟨935634495584626773582625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19960202572472037836429333 935634495584626773582625)
                    ·
                      rfl

theorem cell23_5466425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 6].length) (baseStart_5466425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466425 prefixEnd_5466425 := by exact prefixLift 5466425
  have htrace : WordTrace (prefixWord ++ tailWord_5466425) baseStart_5466425 baseEnd_5466425 := by
    simpa [prefixWord, tailWord_5466425, baseEnd_5466425] using wordTrace_append hprefix tailTrace_5466425
  have hstable : (prefixWord ++ tailWord_5466425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466425).length < 2 ^ (prefixWord ++ tailWord_5466425).sum := by decide
  have hdescent : baseEnd_5466425 < baseStart_5466425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466428 : List Nat := [2, 2, 2, 2, 1, 2, 3, 1, 1, 1, 6]
def baseStart_5466428 : Nat := 118140960795 + 5466428 * 2 ^ 59
def prefixEnd_5466428 : Nat := 4983230072969 + 3 ^ 40 * 5466428 * 2
def baseEnd_5466428 : Nat := 2806905027195843809010361

theorem tailTrace_5466428 : CollatzResearch.WordTrace tailWord_5466428 prefixEnd_5466428 2806905027195843809010361 := by
  unfold tailWord_5466428
  simp only [CollatzResearch.WordTrace]
  refine ⟨99688504320036211210243969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132918005760048281613658625 99688504320036211210243969)
  ·
    refine ⟨74766378240027158407682977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99688504320036211210243969 74766378240027158407682977)
    ·
      refine ⟨56074783680020368805762233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74766378240027158407682977 56074783680020368805762233)
      ·
        refine ⟨42056087760015276604321675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56074783680020368805762233 42056087760015276604321675)
        ·
          refine ⟨63084131640022914906482513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42056087760015276604321675 63084131640022914906482513)
          ·
            refine ⟨47313098730017186179861885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63084131640022914906482513 47313098730017186179861885)
            ·
              refine ⟨17742412023756444817448207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47313098730017186179861885 17742412023756444817448207)
              ·
                refine ⟨26613618035634667226172311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17742412023756444817448207 26613618035634667226172311)
                ·
                  refine ⟨39920427053452000839258467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26613618035634667226172311 39920427053452000839258467)
                  ·
                    refine ⟨59880640580178001258887701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39920427053452000839258467 59880640580178001258887701)
                    ·
                      refine ⟨2806905027195843809010361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59880640580178001258887701 2806905027195843809010361)
                      ·
                        rfl

theorem cell23_5466428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_5466428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466428 prefixEnd_5466428 := by exact prefixLift 5466428
  have htrace : WordTrace (prefixWord ++ tailWord_5466428) baseStart_5466428 baseEnd_5466428 := by
    simpa [prefixWord, tailWord_5466428, baseEnd_5466428] using wordTrace_append hprefix tailTrace_5466428
  have hstable : (prefixWord ++ tailWord_5466428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466428).length < 2 ^ (prefixWord ++ tailWord_5466428).sum := by decide
  have hdescent : baseEnd_5466428 < baseStart_5466428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466435 : List Nat := [1, 1, 1, 3, 1, 3, 3, 4, 1, 2, 3]
def baseStart_5466435 : Nat := 118140960795 + 5466435 * 2 ^ 59
def prefixEnd_5466435 : Nat := 4983230072969 + 3 ^ 40 * 5466435 * 2
def baseEnd_5466435 : Nat := 2806908621560425281622829

theorem tailTrace_5466435 : CollatzResearch.WordTrace tailWord_5466435 prefixEnd_5466435 2806908621560425281622829 := by
  unfold tailWord_5466435
  simp only [CollatzResearch.WordTrace]
  refine ⟨199377263951047062615992759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132918175967364708410661839 199377263951047062615992759)
  ·
    refine ⟨299065895926570593923989139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199377263951047062615992759 299065895926570593923989139)
    ·
      refine ⟨448598843889855890885983709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299065895926570593923989139 448598843889855890885983709)
      ·
        refine ⟨168224566458695959082243891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 448598843889855890885983709 168224566458695959082243891)
        ·
          refine ⟨252336849688043938623365837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168224566458695959082243891 252336849688043938623365837)
          ·
            refine ⟨94626318633016476983762189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 252336849688043938623365837 94626318633016476983762189)
            ·
              refine ⟨35484869487381178868910821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94626318633016476983762189 35484869487381178868910821)
              ·
                refine ⟨6653413028883971037920779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35484869487381178868910821 6653413028883971037920779)
                ·
                  refine ⟨9980119543325956556881169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6653413028883971037920779 9980119543325956556881169)
                  ·
                    refine ⟨7485089657494467417660877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9980119543325956556881169 7485089657494467417660877)
                    ·
                      refine ⟨2806908621560425281622829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7485089657494467417660877 2806908621560425281622829)
                      ·
                        rfl

theorem cell23_5466435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 4, 1, 2, 3].length) (baseStart_5466435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466435 prefixEnd_5466435 := by exact prefixLift 5466435
  have htrace : WordTrace (prefixWord ++ tailWord_5466435) baseStart_5466435 baseEnd_5466435 := by
    simpa [prefixWord, tailWord_5466435, baseEnd_5466435] using wordTrace_append hprefix tailTrace_5466435
  have hstable : (prefixWord ++ tailWord_5466435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466435).length < 2 ^ (prefixWord ++ tailWord_5466435).sum := by decide
  have hdescent : baseEnd_5466435 < baseStart_5466435 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466452 : List Nat := [2, 4, 1, 1, 2, 2, 2, 3, 1, 2, 3]
def baseStart_5466452 : Nat := 118140960795 + 5466452 * 2 ^ 59
def prefixEnd_5466452 : Nat := 4983230072969 + 3 ^ 40 * 5466452 * 2
def baseEnd_5466452 : Nat := 2806917350731551715110251

theorem tailTrace_5466452 : CollatzResearch.WordTrace tailWord_5466452 prefixEnd_5466452 2806917350731551715110251 := by
  unfold tailWord_5466452
  simp only [CollatzResearch.WordTrace]
  refine ⟨99688941995992737259680805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132918589327990316346241073 99688941995992737259680805)
  ·
    refine ⟨18691676624248638236190151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99688941995992737259680805 18691676624248638236190151)
    ·
      refine ⟨28037514936372957354285227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18691676624248638236190151 28037514936372957354285227)
      ·
        refine ⟨42056272404559436031427841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28037514936372957354285227 42056272404559436031427841)
        ·
          refine ⟨31542204303419577023570881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42056272404559436031427841 31542204303419577023570881)
          ·
            refine ⟨23656653227564682767678161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31542204303419577023570881 23656653227564682767678161)
            ·
              refine ⟨17742489920673512075758621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23656653227564682767678161 17742489920673512075758621)
              ·
                refine ⟨6653433720252567028409483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17742489920673512075758621 6653433720252567028409483)
                ·
                  refine ⟨9980150580378850542614225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6653433720252567028409483 9980150580378850542614225)
                  ·
                    refine ⟨7485112935284137906960669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9980150580378850542614225 7485112935284137906960669)
                    ·
                      refine ⟨2806917350731551715110251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7485112935284137906960669 2806917350731551715110251)
                      ·
                        rfl

theorem cell23_5466452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_5466452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466452 prefixEnd_5466452 := by exact prefixLift 5466452
  have htrace : WordTrace (prefixWord ++ tailWord_5466452) baseStart_5466452 baseEnd_5466452 := by
    simpa [prefixWord, tailWord_5466452, baseEnd_5466452] using wordTrace_append hprefix tailTrace_5466452
  have hstable : (prefixWord ++ tailWord_5466452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466452).length < 2 ^ (prefixWord ++ tailWord_5466452).sum := by decide
  have hdescent : baseEnd_5466452 < baseStart_5466452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466466 : List Nat := [3, 3, 2, 1, 1, 4, 1, 1, 3, 2, 2]
def baseStart_5466466 : Nat := 118140960795 + 5466466 * 2 ^ 59
def prefixEnd_5466466 : Nat := 4983230072969 + 3 ^ 40 * 5466466 * 2
def baseEnd_5466466 : Nat := 2806924539460714660335187

theorem tailTrace_5466466 : CollatzResearch.WordTrace tailWord_5466466 prefixEnd_5466466 2806924539460714660335187 := by
  unfold tailWord_5466466
  simp only [CollatzResearch.WordTrace]
  refine ⟨49844598653483688727592813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132918929742623169940247501 49844598653483688727592813)
  ·
    refine ⟨18691724495056383272847305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49844598653483688727592813 18691724495056383272847305)
    ·
      refine ⟨14018793371292287454635479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18691724495056383272847305 14018793371292287454635479)
      ·
        refine ⟨21028190056938431181953219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14018793371292287454635479 21028190056938431181953219)
        ·
          refine ⟨31542285085407646772929829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21028190056938431181953219 31542285085407646772929829)
          ·
            refine ⟨5914178453513933769924343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31542285085407646772929829 5914178453513933769924343)
            ·
              refine ⟨8871267680270900654886515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5914178453513933769924343 8871267680270900654886515)
              ·
                refine ⟨13306901520406350982329773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8871267680270900654886515 13306901520406350982329773)
                ·
                  refine ⟨4990088070152381618373665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13306901520406350982329773 4990088070152381618373665)
                  ·
                    refine ⟨3742566052614286213780249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4990088070152381618373665 3742566052614286213780249)
                    ·
                      refine ⟨2806924539460714660335187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3742566052614286213780249 2806924539460714660335187)
                      ·
                        rfl

theorem cell23_5466466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_5466466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466466 prefixEnd_5466466 := by exact prefixLift 5466466
  have htrace : WordTrace (prefixWord ++ tailWord_5466466) baseStart_5466466 baseEnd_5466466 := by
    simpa [prefixWord, tailWord_5466466, baseEnd_5466466] using wordTrace_append hprefix tailTrace_5466466
  have hstable : (prefixWord ++ tailWord_5466466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466466).length < 2 ^ (prefixWord ++ tailWord_5466466).sum := by decide
  have hdescent : baseEnd_5466466 < baseStart_5466466 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466468 : List Nat := [2, 3, 1, 1, 3, 1, 2, 1, 2, 7]
def baseStart_5466468 : Nat := 118140960795 + 5466468 * 2 ^ 59
def prefixEnd_5466468 : Nat := 4983230072969 + 3 ^ 40 * 5466468 * 2
def baseEnd_5466468 : Nat := 935641855474007884170059

theorem tailTrace_5466468 : CollatzResearch.WordTrace tailWord_5466468 prefixEnd_5466468 935641855474007884170059 := by
  unfold tailWord_5466468
  simp only [CollatzResearch.WordTrace]
  refine ⟨99689233779963754625972029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132918978373285006167962705 99689233779963754625972029)
  ·
    refine ⟨37383462667486407984739511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99689233779963754625972029 37383462667486407984739511)
    ·
      refine ⟨56075194001229611977109267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37383462667486407984739511 56075194001229611977109267)
      ·
        refine ⟨84112791001844417965663901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56075194001229611977109267 84112791001844417965663901)
        ·
          refine ⟨31542296625691656737123963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84112791001844417965663901 31542296625691656737123963)
          ·
            refine ⟨47313444938537485105685945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31542296625691656737123963 47313444938537485105685945)
            ·
              refine ⟨35485083703903113829264459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47313444938537485105685945 35485083703903113829264459)
              ·
                refine ⟨53227625555854670743896689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35485083703903113829264459 53227625555854670743896689)
                ·
                  refine ⟨39920719166891003057922517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53227625555854670743896689 39920719166891003057922517)
                  ·
                    refine ⟨935641855474007884170059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39920719166891003057922517 935641855474007884170059)
                    ·
                      rfl

theorem cell23_5466468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 2, 7].length) (baseStart_5466468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466468 prefixEnd_5466468 := by exact prefixLift 5466468
  have htrace : WordTrace (prefixWord ++ tailWord_5466468) baseStart_5466468 baseEnd_5466468 := by
    simpa [prefixWord, tailWord_5466468, baseEnd_5466468] using wordTrace_append hprefix tailTrace_5466468
  have hstable : (prefixWord ++ tailWord_5466468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466468).length < 2 ^ (prefixWord ++ tailWord_5466468).sum := by decide
  have hdescent : baseEnd_5466468 < baseStart_5466468 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466475 : List Nat := [1, 1, 1, 1, 2, 2, 2, 3, 5, 3, 2]
def baseStart_5466475 : Nat := 118140960795 + 5466475 * 2 ^ 59
def prefixEnd_5466475 : Nat := 4983230072969 + 3 ^ 40 * 5466475 * 2
def baseEnd_5466475 : Nat := 2806929160786605125122645

theorem tailTrace_5466475 : CollatzResearch.WordTrace tailWord_5466475 prefixEnd_5466475 2806929160786605125122645 := by
  unfold tailWord_5466475
  simp only [CollatzResearch.WordTrace]
  refine ⟨199378722870902149447448879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132919148580601432964965919 199378722870902149447448879)
  ·
    refine ⟨299068084306353224171173319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199378722870902149447448879 299068084306353224171173319)
    ·
      refine ⟨448602126459529836256759979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299068084306353224171173319 448602126459529836256759979)
      ·
        refine ⟨672903189689294754385139969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 448602126459529836256759979 672903189689294754385139969)
        ·
          refine ⟨504677392266971065788854977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 672903189689294754385139969 504677392266971065788854977)
          ·
            refine ⟨378508044200228299341641233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 504677392266971065788854977 378508044200228299341641233)
            ·
              refine ⟨283881033150171224506230925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 378508044200228299341641233 283881033150171224506230925)
              ·
                refine ⟨106455387431314209189836597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 283881033150171224506230925 106455387431314209189836597)
                ·
                  refine ⟨9980192571685707111547181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 106455387431314209189836597 9980192571685707111547181)
                  ·
                    refine ⟨3742572214382140166830193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9980192571685707111547181 3742572214382140166830193)
                    ·
                      refine ⟨2806929160786605125122645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3742572214382140166830193 2806929160786605125122645)
                      ·
                        rfl

theorem cell23_5466475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 5, 3, 2].length) (baseStart_5466475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466475 prefixEnd_5466475 := by exact prefixLift 5466475
  have htrace : WordTrace (prefixWord ++ tailWord_5466475) baseStart_5466475 baseEnd_5466475 := by
    simpa [prefixWord, tailWord_5466475, baseEnd_5466475] using wordTrace_append hprefix tailTrace_5466475
  have hstable : (prefixWord ++ tailWord_5466475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466475).length < 2 ^ (prefixWord ++ tailWord_5466475).sum := by decide
  have hdescent : baseEnd_5466475 < baseStart_5466475 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466476 : List Nat := [2, 2, 1, 1, 7, 1, 2, 1, 2, 4]
def baseStart_5466476 : Nat := 118140960795 + 5466476 * 2 ^ 59
def prefixEnd_5466476 : Nat := 4983230072969 + 3 ^ 40 * 5466476 * 2
def baseEnd_5466476 : Nat := 935643224755753207070047

theorem tailTrace_5466476 : CollatzResearch.WordTrace tailWord_5466476 prefixEnd_5466476 935643224755753207070047 := by
  unfold tailWord_5466476
  simp only [CollatzResearch.WordTrace]
  refine ⟨99689379671949263309117641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132919172895932351078823521 99689379671949263309117641)
  ·
    refine ⟨74767034753961947481838231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99689379671949263309117641 74767034753961947481838231)
    ·
      refine ⟨112150552130942921222757347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74767034753961947481838231 112150552130942921222757347)
      ·
        refine ⟨168225828196414381834136021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112150552130942921222757347 168225828196414381834136021)
        ·
          refine ⟨3942792848353462074237563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 168225828196414381834136021 3942792848353462074237563)
          ·
            refine ⟨5914189272530193111356345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3942792848353462074237563 5914189272530193111356345)
            ·
              refine ⟨4435641954397644833517259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5914189272530193111356345 4435641954397644833517259)
              ·
                refine ⟨6653462931596467250275889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4435641954397644833517259 6653462931596467250275889)
                ·
                  refine ⟨4990097198697350437706917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6653462931596467250275889 4990097198697350437706917)
                  ·
                    refine ⟨935643224755753207070047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4990097198697350437706917 935643224755753207070047)
                    ·
                      rfl

theorem cell23_5466476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 1, 2, 4].length) (baseStart_5466476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466476 prefixEnd_5466476 := by exact prefixLift 5466476
  have htrace : WordTrace (prefixWord ++ tailWord_5466476) baseStart_5466476 baseEnd_5466476 := by
    simpa [prefixWord, tailWord_5466476, baseEnd_5466476] using wordTrace_append hprefix tailTrace_5466476
  have hstable : (prefixWord ++ tailWord_5466476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466476).length < 2 ^ (prefixWord ++ tailWord_5466476).sum := by decide
  have hdescent : baseEnd_5466476 < baseStart_5466476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466492 : List Nat := [2, 2, 2, 1, 1, 1, 2, 6, 1, 3, 2]
def baseStart_5466492 : Nat := 118140960795 + 5466492 * 2 ^ 59
def prefixEnd_5466492 : Nat := 4983230072969 + 3 ^ 40 * 5466492 * 2
def baseEnd_5466492 : Nat := 2806937889957731558610067

theorem tailTrace_5466492 : CollatzResearch.WordTrace tailWord_5466492 prefixEnd_5466492 2806937889957731558610067 := by
  unfold tailWord_5466492
  simp only [CollatzResearch.WordTrace]
  refine ⟨99689671455920280675408865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132919561941227040900545153 99689671455920280675408865)
  ·
    refine ⟨74767253591940210506556649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99689671455920280675408865 74767253591940210506556649)
    ·
      refine ⟨56075440193955157879917487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74767253591940210506556649 56075440193955157879917487)
      ·
        refine ⟨84113160290932736819876231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56075440193955157879917487 84113160290932736819876231)
        ·
          refine ⟨126169740436399105229814347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84113160290932736819876231 126169740436399105229814347)
          ·
            refine ⟨189254610654598657844721521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126169740436399105229814347 189254610654598657844721521)
            ·
              refine ⟨141940957990948993383541141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189254610654598657844721521 141940957990948993383541141)
              ·
                refine ⟨6653482405825734064853491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 141940957990948993383541141 6653482405825734064853491)
                ·
                  refine ⟨9980223608738601097280237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6653482405825734064853491 9980223608738601097280237)
                  ·
                    refine ⟨3742583853276975411480089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9980223608738601097280237 3742583853276975411480089)
                    ·
                      refine ⟨2806937889957731558610067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3742583853276975411480089 2806937889957731558610067)
                      ·
                        rfl

theorem cell23_5466492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 6, 1, 3, 2].length) (baseStart_5466492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466492 prefixEnd_5466492 := by exact prefixLift 5466492
  have htrace : WordTrace (prefixWord ++ tailWord_5466492) baseStart_5466492 baseEnd_5466492 := by
    simpa [prefixWord, tailWord_5466492, baseEnd_5466492] using wordTrace_append hprefix tailTrace_5466492
  have hstable : (prefixWord ++ tailWord_5466492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466492).length < 2 ^ (prefixWord ++ tailWord_5466492).sum := by decide
  have hdescent : baseEnd_5466492 < baseStart_5466492 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466516 : List Nat := [2, 4, 2, 1, 3, 1, 2, 2, 2, 1, 3]
def baseStart_5466516 : Nat := 118140960795 + 5466516 * 2 ^ 59
def prefixEnd_5466516 : Nat := 4983230072969 + 3 ^ 40 * 5466516 * 2
def baseEnd_5466516 : Nat := 2806950213493439464709957

theorem tailTrace_5466516 : CollatzResearch.WordTrace tailWord_5466516 prefixEnd_5466516 2806950213493439464709957 := by
  unfold tailWord_5466516
  simp only [CollatzResearch.WordTrace]
  refine ⟨99690109131876806724845701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132920145509169075633127601 99690109131876806724845701)
  ·
    refine ⟨18691895462226901260908569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99690109131876806724845701 18691895462226901260908569)
    ·
      refine ⟨14018921596670175945681427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18691895462226901260908569 14018921596670175945681427)
      ·
        refine ⟨21028382395005263918522141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14018921596670175945681427 21028382395005263918522141)
        ·
          refine ⟨7885643398126973969445803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21028382395005263918522141 7885643398126973969445803)
          ·
            refine ⟨11828465097190460954168705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7885643398126973969445803 11828465097190460954168705)
            ·
              refine ⟨8871348822892845715626529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11828465097190460954168705 8871348822892845715626529)
              ·
                refine ⟨6653511617169634286719897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8871348822892845715626529 6653511617169634286719897)
                ·
                  refine ⟨4990133712877225715039923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6653511617169634286719897 4990133712877225715039923)
                  ·
                    refine ⟨7485200569315838572559885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4990133712877225715039923 7485200569315838572559885)
                    ·
                      refine ⟨2806950213493439464709957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7485200569315838572559885 2806950213493439464709957)
                      ·
                        rfl

theorem cell23_5466516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_5466516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466516 prefixEnd_5466516 := by exact prefixLift 5466516
  have htrace : WordTrace (prefixWord ++ tailWord_5466516) baseStart_5466516 baseEnd_5466516 := by
    simpa [prefixWord, tailWord_5466516, baseEnd_5466516] using wordTrace_append hprefix tailTrace_5466516
  have hstable : (prefixWord ++ tailWord_5466516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466516).length < 2 ^ (prefixWord ++ tailWord_5466516).sum := by decide
  have hdescent : baseEnd_5466516 < baseStart_5466516 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466535 : List Nat := [1, 1, 6, 1, 1, 2, 1, 1, 1, 4, 4]
def baseStart_5466535 : Nat := 118140960795 + 5466535 * 2 ^ 59
def prefixEnd_5466535 : Nat := 4983230072969 + 3 ^ 40 * 5466535 * 2
def baseEnd_5466535 : Nat := 2806959969625874890372369

theorem tailTrace_5466535 : CollatzResearch.WordTrace tailWord_5466535 prefixEnd_5466535 2806959969625874890372369 := by
  unfold tailWord_5466535
  simp only [CollatzResearch.WordTrace]
  refine ⟨199380911250684779694633059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132920607500456519796422039 199380911250684779694633059)
  ·
    refine ⟨299071366876027169541949589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199380911250684779694633059 299071366876027169541949589)
    ·
      refine ⟨14018970322313773572278887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 299071366876027169541949589 14018970322313773572278887)
      ·
        refine ⟨21028455483470660358418331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14018970322313773572278887 21028455483470660358418331)
        ·
          refine ⟨31542683225205990537627497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21028455483470660358418331 31542683225205990537627497)
          ·
            refine ⟨23657012418904492903220623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31542683225205990537627497 23657012418904492903220623)
            ·
              refine ⟨35485518628356739354830935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23657012418904492903220623 35485518628356739354830935)
              ·
                refine ⟨53228277942535109032246403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35485518628356739354830935 53228277942535109032246403)
                ·
                  refine ⟨79842416913802663548369605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53228277942535109032246403 79842416913802663548369605)
                  ·
                    refine ⟨14970453171337999415319301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 79842416913802663548369605 14970453171337999415319301)
                    ·
                      refine ⟨2806959969625874890372369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14970453171337999415319301 2806959969625874890372369)
                      ·
                        rfl

theorem cell23_5466535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_5466535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466535 prefixEnd_5466535 := by exact prefixLift 5466535
  have htrace : WordTrace (prefixWord ++ tailWord_5466535) baseStart_5466535 baseEnd_5466535 := by
    simpa [prefixWord, tailWord_5466535, baseEnd_5466535] using wordTrace_append hprefix tailTrace_5466535
  have hstable : (prefixWord ++ tailWord_5466535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466535).length < 2 ^ (prefixWord ++ tailWord_5466535).sum := by decide
  have hdescent : baseEnd_5466535 < baseStart_5466535 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466545 : List Nat := [1, 2, 2, 4, 1, 3, 1, 2, 7]
def baseStart_5466545 : Nat := 118140960795 + 5466545 * 2 ^ 59
def prefixEnd_5466545 : Nat := 4983230072969 + 3 ^ 40 * 5466545 * 2
def baseEnd_5466545 : Nat := 311885011603602205694147

theorem tailTrace_5466545 : CollatzResearch.WordTrace tailWord_5466545 prefixEnd_5466545 311885011603602205694147 := by
  unfold tailWord_5466545
  simp only [CollatzResearch.WordTrace]
  refine ⟨199381275980648551402497089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132920850653765700934998059 199381275980648551402497089)
  ·
    refine ⟨149535956985486413551872817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199381275980648551402497089 149535956985486413551872817)
    ·
      refine ⟨112151967739114810163904613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149535956985486413551872817 112151967739114810163904613)
      ·
        refine ⟨21028493951084026905732115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112151967739114810163904613 21028493951084026905732115)
        ·
          refine ⟨31542740926626040358598173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21028493951084026905732115 31542740926626040358598173)
          ·
            refine ⟨11828527847484765134474315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31542740926626040358598173 11828527847484765134474315)
            ·
              refine ⟨17742791771227147701711473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11828527847484765134474315 17742791771227147701711473)
              ·
                refine ⟨13307093828420360776283605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17742791771227147701711473 13307093828420360776283605)
                ·
                  refine ⟨311885011603602205694147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13307093828420360776283605 311885011603602205694147)
                  ·
                    rfl

theorem cell23_5466545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 7].length) (baseStart_5466545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466545 prefixEnd_5466545 := by exact prefixLift 5466545
  have htrace : WordTrace (prefixWord ++ tailWord_5466545) baseStart_5466545 baseEnd_5466545 := by
    simpa [prefixWord, tailWord_5466545, baseEnd_5466545] using wordTrace_append hprefix tailTrace_5466545
  have hstable : (prefixWord ++ tailWord_5466545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466545).length < 2 ^ (prefixWord ++ tailWord_5466545).sum := by decide
  have hdescent : baseEnd_5466545 < baseStart_5466545 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466613 : List Nat := [1, 3, 5, 1, 3, 1, 1, 3, 5]
def baseStart_5466613 : Nat := 118140960795 + 5466613 * 2 ^ 59
def prefixEnd_5466613 : Nat := 4983230072969 + 3 ^ 40 * 5466613 * 2
def baseEnd_5466613 : Nat := 311888891235213953910779

theorem tailTrace_5466613 : CollatzResearch.WordTrace tailWord_5466613 prefixEnd_5466613 311888891235213953910779 := by
  unfold tailWord_5466613
  simp only [CollatzResearch.WordTrace]
  refine ⟨199383756144402199015972493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132922504096268132677314995 199383756144402199015972493)
  ·
    refine ⟨74768908554150824630989685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199383756144402199015972493 74768908554150824630989685)
    ·
      refine ⟨7009585176951639809155283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 74768908554150824630989685 7009585176951639809155283)
      ·
        refine ⟨10514377765427459713732925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7009585176951639809155283 10514377765427459713732925)
        ·
          refine ⟨3942891662035297392649847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10514377765427459713732925 3942891662035297392649847)
          ·
            refine ⟨5914337493052946088974771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3942891662035297392649847 5914337493052946088974771)
            ·
              refine ⟨8871506239579419133462157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5914337493052946088974771 8871506239579419133462157)
              ·
                refine ⟨3326814839842282175048309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8871506239579419133462157 3326814839842282175048309)
                ·
                  refine ⟨311888891235213953910779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3326814839842282175048309 311888891235213953910779)
                  ·
                    rfl

theorem cell23_5466613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 3, 5].length) (baseStart_5466613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466613 prefixEnd_5466613 := by exact prefixLift 5466613
  have htrace : WordTrace (prefixWord ++ tailWord_5466613) baseStart_5466613 baseEnd_5466613 := by
    simpa [prefixWord, tailWord_5466613, baseEnd_5466613] using wordTrace_append hprefix tailTrace_5466613
  have hstable : (prefixWord ++ tailWord_5466613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466613).length < 2 ^ (prefixWord ++ tailWord_5466613).sum := by decide
  have hdescent : baseEnd_5466613 < baseStart_5466613 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466630 : List Nat := [6, 2, 1, 1, 1, 2, 3, 2, 5]
def baseStart_5466630 : Nat := 118140960795 + 5466630 * 2 ^ 59
def prefixEnd_5466630 : Nat := 4983230072969 + 3 ^ 40 * 5466630 * 2
def baseEnd_5466630 : Nat := 311889861143116890964937

theorem tailTrace_5466630 : CollatzResearch.WordTrace tailWord_5466630 prefixEnd_5466630 311889861143116890964937 := by
  unfold tailWord_5466630
  simp only [CollatzResearch.WordTrace]
  refine ⟨6230761755791894091229417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 132922917456893740612894229 6230761755791894091229417)
  ·
    refine ⟨4673071316843920568422063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6230761755791894091229417 4673071316843920568422063)
    ·
      refine ⟨7009606975265880852633095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4673071316843920568422063 7009606975265880852633095)
      ·
        refine ⟨10514410462898821278949643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7009606975265880852633095 10514410462898821278949643)
        ·
          refine ⟨15771615694348231918424465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10514410462898821278949643 15771615694348231918424465)
          ·
            refine ⟨11828711770761173938818349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15771615694348231918424465 11828711770761173938818349)
            ·
              refine ⟨4435766914035440227056881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11828711770761173938818349 4435766914035440227056881)
              ·
                refine ⟨3326825185526580170292661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4435766914035440227056881 3326825185526580170292661)
                ·
                  refine ⟨311889861143116890964937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3326825185526580170292661 311889861143116890964937)
                  ·
                    rfl

theorem cell23_5466630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_5466630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466630 prefixEnd_5466630 := by exact prefixLift 5466630
  have htrace : WordTrace (prefixWord ++ tailWord_5466630) baseStart_5466630 baseEnd_5466630 := by
    simpa [prefixWord, tailWord_5466630, baseEnd_5466630] using wordTrace_append hprefix tailTrace_5466630
  have hstable : (prefixWord ++ tailWord_5466630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466630).length < 2 ^ (prefixWord ++ tailWord_5466630).sum := by decide
  have hdescent : baseEnd_5466630 < baseStart_5466630 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466635 : List Nat := [1, 1, 1, 1, 7, 1, 2, 1, 8]
def baseStart_5466635 : Nat := 118140960795 + 5466635 * 2 ^ 59
def prefixEnd_5466635 : Nat := 4983230072969 + 3 ^ 40 * 5466635 * 2
def baseEnd_5466635 : Nat := 311890146410147166569101

theorem tailTrace_5466635 : CollatzResearch.WordTrace tailWord_5466635 prefixEnd_5466635 311890146410147166569101 := by
  unfold tailWord_5466635
  simp only [CollatzResearch.WordTrace]
  refine ⟨199384558550322496773273359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132923039033548331182182239 199384558550322496773273359)
  ·
    refine ⟨299076837825483745159910039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199384558550322496773273359 299076837825483745159910039)
    ·
      refine ⟨448615256738225617739865059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299076837825483745159910039 448615256738225617739865059)
      ·
        refine ⟨672922885107338426609797589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 448615256738225617739865059 672922885107338426609797589)
        ·
          refine ⟨15771630119703244373667131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 672922885107338426609797589 15771630119703244373667131)
          ·
            refine ⟨23657445179554866560500697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15771630119703244373667131 23657445179554866560500697)
            ·
              refine ⟨17743083884666149920375523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23657445179554866560500697 17743083884666149920375523)
              ·
                refine ⟨26614625826999224880563285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17743083884666149920375523 26614625826999224880563285)
                ·
                  refine ⟨311890146410147166569101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26614625826999224880563285 311890146410147166569101)
                  ·
                    rfl

theorem cell23_5466635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 8].length) (baseStart_5466635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466635 prefixEnd_5466635 := by exact prefixLift 5466635
  have htrace : WordTrace (prefixWord ++ tailWord_5466635) baseStart_5466635 baseEnd_5466635 := by
    simpa [prefixWord, tailWord_5466635, baseEnd_5466635] using wordTrace_append hprefix tailTrace_5466635
  have hstable : (prefixWord ++ tailWord_5466635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466635).length < 2 ^ (prefixWord ++ tailWord_5466635).sum := by decide
  have hdescent : baseEnd_5466635 < baseStart_5466635 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466652 : List Nat := [2, 2, 3, 1, 2, 3, 1, 3, 6]
def baseStart_5466652 : Nat := 118140960795 + 5466652 * 2 ^ 59
def prefixEnd_5466652 : Nat := 4983230072969 + 3 ^ 40 * 5466652 * 2
def baseEnd_5466652 : Nat := 311891116318050103623259

theorem tailTrace_5466652 : CollatzResearch.WordTrace tailWord_5466652 prefixEnd_5466652 311891116318050103623259 := by
  unfold tailWord_5466652
  simp only [CollatzResearch.WordTrace]
  refine ⟨99692589295630454338321105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132923452394173939117761473 99692589295630454338321105)
  ·
    refine ⟨74769441971722840753740829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99692589295630454338321105 74769441971722840753740829)
    ·
      refine ⟨28038540739396065282652811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74769441971722840753740829 28038540739396065282652811)
      ·
        refine ⟨42057811109094097923979217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28038540739396065282652811 42057811109094097923979217)
        ·
          refine ⟨31543358331820573442984413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42057811109094097923979217 31543358331820573442984413)
          ·
            refine ⟨11828759374432715041119155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31543358331820573442984413 11828759374432715041119155)
            ·
              refine ⟨17743139061649072561678733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11828759374432715041119155 17743139061649072561678733)
              ·
                refine ⟨6653677148118402210629525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17743139061649072561678733 6653677148118402210629525)
                ·
                  refine ⟨311891116318050103623259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6653677148118402210629525 311891116318050103623259)
                  ·
                    rfl

theorem cell23_5466652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 3, 6].length) (baseStart_5466652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466652 prefixEnd_5466652 := by exact prefixLift 5466652
  have htrace : WordTrace (prefixWord ++ tailWord_5466652) baseStart_5466652 baseEnd_5466652 := by
    simpa [prefixWord, tailWord_5466652, baseEnd_5466652] using wordTrace_append hprefix tailTrace_5466652
  have hstable : (prefixWord ++ tailWord_5466652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466652).length < 2 ^ (prefixWord ++ tailWord_5466652).sum := by decide
  have hdescent : baseEnd_5466652 < baseStart_5466652 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466672 : List Nat := [2, 1, 1, 1, 2, 3, 2, 3, 1, 5, 2]
def baseStart_5466672 : Nat := 118140960795 + 5466672 * 2 ^ 59
def prefixEnd_5466672 : Nat := 4983230072969 + 3 ^ 40 * 5466672 * 2
def baseEnd_5466672 : Nat := 2807030316475540854359239

theorem tailTrace_5466672 : CollatzResearch.WordTrace tailWord_5466672 prefixEnd_5466672 2807030316475540854359239 := by
  unfold tailWord_5466672
  simp only [CollatzResearch.WordTrace]
  refine ⟨99692954025594226046185135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132923938700792301394913513 99692954025594226046185135)
  ·
    refine ⟨149539431038391339069277703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99692954025594226046185135 149539431038391339069277703)
    ·
      refine ⟨224309146557587008603916555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149539431038391339069277703 224309146557587008603916555)
      ·
        refine ⟨336463719836380512905874833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224309146557587008603916555 336463719836380512905874833)
        ·
          refine ⟨252347789877285384679406125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 336463719836380512905874833 252347789877285384679406125)
          ·
            refine ⟨94630421203982019254777297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 252347789877285384679406125 94630421203982019254777297)
            ·
              refine ⟨70972815902986514441082973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94630421203982019254777297 70972815902986514441082973)
              ·
                refine ⟨26614805963619942915406115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70972815902986514441082973 26614805963619942915406115)
                ·
                  refine ⟨39922208945429914373109173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26614805963619942915406115 39922208945429914373109173)
                  ·
                    refine ⟨3742707088634054472478985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39922208945429914373109173 3742707088634054472478985)
                    ·
                      refine ⟨2807030316475540854359239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3742707088634054472478985 2807030316475540854359239)
                      ·
                        rfl

theorem cell23_5466672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 1, 5, 2].length) (baseStart_5466672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466672 prefixEnd_5466672 := by exact prefixLift 5466672
  have htrace : WordTrace (prefixWord ++ tailWord_5466672) baseStart_5466672 baseEnd_5466672 := by
    simpa [prefixWord, tailWord_5466672, baseEnd_5466672] using wordTrace_append hprefix tailTrace_5466672
  have hstable : (prefixWord ++ tailWord_5466672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466672).length < 2 ^ (prefixWord ++ tailWord_5466672).sum := by decide
  have hdescent : baseEnd_5466672 < baseStart_5466672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466686 : List Nat := [4, 2, 1, 4, 1, 1, 2, 2, 6]
def baseStart_5466686 : Nat := 118140960795 + 5466686 * 2 ^ 59
def prefixEnd_5466686 : Nat := 4983230072969 + 3 ^ 40 * 5466686 * 2
def baseEnd_5466686 : Nat := 311893056133855977731575

theorem tailTrace_5466686 : CollatzResearch.WordTrace tailWord_5466686 prefixEnd_5466686 311893056133855977731575 := by
  unfold tailWord_5466686
  simp only [CollatzResearch.WordTrace]
  refine ⟨24923302334142216560422489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132924279115425154988919941 24923302334142216560422489)
  ·
    refine ⟨18692476750606662420316867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24923302334142216560422489 18692476750606662420316867)
    ·
      refine ⟨28038715125909993630475301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18692476750606662420316867 28038715125909993630475301)
      ·
        refine ⟨5257259086108123805714119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28038715125909993630475301 5257259086108123805714119)
        ·
          refine ⟨7885888629162185708571179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5257259086108123805714119 7885888629162185708571179)
          ·
            refine ⟨11828832943743278562856769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7885888629162185708571179 11828832943743278562856769)
            ·
              refine ⟨8871624707807458922142577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11828832943743278562856769 8871624707807458922142577)
              ·
                refine ⟨6653718530855594191606933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8871624707807458922142577 6653718530855594191606933)
                ·
                  refine ⟨311893056133855977731575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6653718530855594191606933 311893056133855977731575)
                  ·
                    rfl

theorem cell23_5466686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 2, 6].length) (baseStart_5466686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466686 prefixEnd_5466686 := by exact prefixLift 5466686
  have htrace : WordTrace (prefixWord ++ tailWord_5466686) baseStart_5466686 baseEnd_5466686 := by
    simpa [prefixWord, tailWord_5466686, baseEnd_5466686] using wordTrace_append hprefix tailTrace_5466686
  have hstable : (prefixWord ++ tailWord_5466686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466686).length < 2 ^ (prefixWord ++ tailWord_5466686).sum := by decide
  have hdescent : baseEnd_5466686 < baseStart_5466686 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466702 : List Nat := [4, 1, 1, 1, 1, 2, 3, 2, 3, 1, 4]
def baseStart_5466702 : Nat := 118140960795 + 5466702 * 2 ^ 59
def prefixEnd_5466702 : Nat := 4983230072969 + 3 ^ 40 * 5466702 * 2
def baseEnd_5466702 : Nat := 2807045720895175736984101

theorem tailTrace_5466702 : CollatzResearch.WordTrace tailWord_5466702 prefixEnd_5466702 2807045720895175736984101 := by
  unfold tailWord_5466702
  simp only [CollatzResearch.WordTrace]
  refine ⟨24923375280134970901995295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132924668160719844810641573 24923375280134970901995295)
  ·
    refine ⟨37385062920202456352992943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24923375280134970901995295 37385062920202456352992943)
    ·
      refine ⟨56077594380303684529489415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37385062920202456352992943 56077594380303684529489415)
      ·
        refine ⟨84116391570455526794234123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56077594380303684529489415 84116391570455526794234123)
        ·
          refine ⟨126174587355683290191351185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84116391570455526794234123 126174587355683290191351185)
          ·
            refine ⟨94630940516762467643513389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126174587355683290191351185 94630940516762467643513389)
            ·
              refine ⟨35486602693785925366317521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94630940516762467643513389 35486602693785925366317521)
              ·
                refine ⟨26614952020339444024738141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35486602693785925366317521 26614952020339444024738141)
                ·
                  refine ⟨9980607007627291509276803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26614952020339444024738141 9980607007627291509276803)
                  ·
                    refine ⟨14970910511440937263915205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9980607007627291509276803 14970910511440937263915205)
                    ·
                      refine ⟨2807045720895175736984101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14970910511440937263915205 2807045720895175736984101)
                      ·
                        rfl

theorem cell23_5466702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_5466702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466702 prefixEnd_5466702 := by exact prefixLift 5466702
  have htrace : WordTrace (prefixWord ++ tailWord_5466702) baseStart_5466702 baseEnd_5466702 := by
    simpa [prefixWord, tailWord_5466702, baseEnd_5466702] using wordTrace_append hprefix tailTrace_5466702
  have hstable : (prefixWord ++ tailWord_5466702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466702).length < 2 ^ (prefixWord ++ tailWord_5466702).sum := by decide
  have hdescent : baseEnd_5466702 < baseStart_5466702 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466732 : List Nat := [2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 4]
def baseStart_5466732 : Nat := 118140960795 + 5466732 * 2 ^ 59
def prefixEnd_5466732 : Nat := 4983230072969 + 3 ^ 40 * 5466732 * 2
def baseEnd_5466732 : Nat := 2807061125314810619608963

theorem tailTrace_5466732 : CollatzResearch.WordTrace tailWord_5466732 prefixEnd_5466732 2807061125314810619608963 := by
  unfold tailWord_5466732
  simp only [CollatzResearch.WordTrace]
  refine ⟨99694048215485541169777225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132925397620647388226369633 99694048215485541169777225)
  ·
    refine ⟨74770536161614155877332919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99694048215485541169777225 74770536161614155877332919)
    ·
      refine ⟨112155804242421233815999379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74770536161614155877332919 112155804242421233815999379)
      ·
        refine ⟨168233706363631850723999069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112155804242421233815999379 168233706363631850723999069)
        ·
          refine ⟨63087639886361944021499651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168233706363631850723999069 63087639886361944021499651)
          ·
            refine ⟨94631459829542916032249477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63087639886361944021499651 94631459829542916032249477)
            ·
              refine ⟨17743398718039296756046777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94631459829542916032249477 17743398718039296756046777)
              ·
                refine ⟨13307549038529472567035083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17743398718039296756046777 13307549038529472567035083)
                ·
                  refine ⟨19961323557794208850552625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13307549038529472567035083 19961323557794208850552625)
                  ·
                    refine ⟨14970992668345656637914469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19961323557794208850552625 14970992668345656637914469)
                    ·
                      refine ⟨2807061125314810619608963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14970992668345656637914469 2807061125314810619608963)
                      ·
                        rfl

theorem cell23_5466732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 4].length) (baseStart_5466732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466732 prefixEnd_5466732 := by exact prefixLift 5466732
  have htrace : WordTrace (prefixWord ++ tailWord_5466732) baseStart_5466732 baseEnd_5466732 := by
    simpa [prefixWord, tailWord_5466732, baseEnd_5466732] using wordTrace_append hprefix tailTrace_5466732
  have hstable : (prefixWord ++ tailWord_5466732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466732).length < 2 ^ (prefixWord ++ tailWord_5466732).sum := by decide
  have hdescent : baseEnd_5466732 < baseStart_5466732 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466753 : List Nat := [1, 2, 4, 2, 1, 1, 1, 6, 1, 2, 2]
def baseStart_5466753 : Nat := 118140960795 + 5466753 * 2 ^ 59
def prefixEnd_5466753 : Nat := 4983230072969 + 3 ^ 40 * 5466753 * 2
def baseEnd_5466753 : Nat := 2807071908408555037446367

theorem tailTrace_5466753 : CollatzResearch.WordTrace tailWord_5466753 prefixEnd_5466753 2807071908408555037446367 := by
  unfold tailWord_5466753
  simp only [CollatzResearch.WordTrace]
  refine ⟨199388862363895002926068913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132925908242596668617379275 199388862363895002926068913)
  ·
    refine ⟨149541646772921252194551685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199388862363895002926068913 149541646772921252194551685)
    ·
      refine ⟨28039058769922734786478441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149541646772921252194551685 28039058769922734786478441)
      ·
        refine ⟨21029294077442051089858831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28039058769922734786478441 21029294077442051089858831)
        ·
          refine ⟨31543941116163076634788247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21029294077442051089858831 31543941116163076634788247)
          ·
            refine ⟨47315911674244614952182371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31543941116163076634788247 47315911674244614952182371)
            ·
              refine ⟨70973867511366922428273557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47315911674244614952182371 70973867511366922428273557)
              ·
                refine ⟨3326900039595324488825323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 70973867511366922428273557 3326900039595324488825323)
                ·
                  refine ⟨4990350059392986733237985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3326900039595324488825323 4990350059392986733237985)
                  ·
                    refine ⟨3742762544544740049928489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4990350059392986733237985 3742762544544740049928489)
                    ·
                      refine ⟨2807071908408555037446367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3742762544544740049928489 2807071908408555037446367)
                      ·
                        rfl

theorem cell23_5466753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_5466753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466753 prefixEnd_5466753 := by exact prefixLift 5466753
  have htrace : WordTrace (prefixWord ++ tailWord_5466753) baseStart_5466753 baseEnd_5466753 := by
    simpa [prefixWord, tailWord_5466753, baseEnd_5466753] using wordTrace_append hprefix tailTrace_5466753
  have hstable : (prefixWord ++ tailWord_5466753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466753).length < 2 ^ (prefixWord ++ tailWord_5466753).sum := by decide
  have hdescent : baseEnd_5466753 < baseStart_5466753 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466755 : List Nat := [1, 1, 1, 3, 3, 1, 2, 1, 1, 9]
def baseStart_5466755 : Nat := 118140960795 + 5466755 * 2 ^ 59
def prefixEnd_5466755 : Nat := 4983230072969 + 3 ^ 40 * 5466755 * 2
def baseEnd_5466755 : Nat := 935690978456621343207119

theorem tailTrace_5466755 : CollatzResearch.WordTrace tailWord_5466755 prefixEnd_5466755 935690978456621343207119 := by
  unfold tailWord_5466755
  simp only [CollatzResearch.WordTrace]
  refine ⟨199388935309887757267641719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132925956873258504845094479 199388935309887757267641719)
  ·
    refine ⟨299083402964831635901462579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199388935309887757267641719 299083402964831635901462579)
    ·
      refine ⟨448625104447247453852193869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299083402964831635901462579 448625104447247453852193869)
      ·
        refine ⟨168234414167717795194572701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 448625104447247453852193869 168234414167717795194572701)
        ·
          refine ⟨63087905312894173197964763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168234414167717795194572701 63087905312894173197964763)
          ·
            refine ⟨94631857969341259796947145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63087905312894173197964763 94631857969341259796947145)
            ·
              refine ⟨70973893477005944847710359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94631857969341259796947145 70973893477005944847710359)
              ·
                refine ⟨106460840215508917271565539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70973893477005944847710359 106460840215508917271565539)
                ·
                  refine ⟨159691260323263375907348309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106460840215508917271565539 159691260323263375907348309)
                  ·
                    refine ⟨935690978456621343207119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 159691260323263375907348309 935690978456621343207119)
                    ·
                      rfl

theorem cell23_5466755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 9].length) (baseStart_5466755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466755 prefixEnd_5466755 := by exact prefixLift 5466755
  have htrace : WordTrace (prefixWord ++ tailWord_5466755) baseStart_5466755 baseEnd_5466755 := by
    simpa [prefixWord, tailWord_5466755, baseEnd_5466755] using wordTrace_append hprefix tailTrace_5466755
  have hstable : (prefixWord ++ tailWord_5466755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466755).length < 2 ^ (prefixWord ++ tailWord_5466755).sum := by decide
  have hdescent : baseEnd_5466755 < baseStart_5466755 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466812 : List Nat := [2, 2, 2, 3, 1, 1, 1, 2, 1, 3, 5]
def baseStart_5466812 : Nat := 118140960795 + 5466812 * 2 ^ 59
def prefixEnd_5466812 : Nat := 4983230072969 + 3 ^ 40 * 5466812 * 2
def baseEnd_5466812 : Nat := 2807102203767170306608595

theorem tailTrace_5466812 : CollatzResearch.WordTrace tailWord_5466812 prefixEnd_5466812 2807102203767170306608595 := by
  unfold tailWord_5466812
  simp only [CollatzResearch.WordTrace]
  refine ⟨99695507135340628001233345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132927342847120837334977793 99695507135340628001233345)
  ·
    refine ⟨74771630351505471000925009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99695507135340628001233345 74771630351505471000925009)
    ·
      refine ⟨56078722763629103250693757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74771630351505471000925009 56078722763629103250693757)
      ·
        refine ⟨21029521036360913719010159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56078722763629103250693757 21029521036360913719010159)
        ·
          refine ⟨31544281554541370578515239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21029521036360913719010159 31544281554541370578515239)
          ·
            refine ⟨47316422331812055867772859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31544281554541370578515239 47316422331812055867772859)
            ·
              refine ⟨70974633497718083801659289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47316422331812055867772859 70974633497718083801659289)
              ·
                refine ⟨53230975123288562851244467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70974633497718083801659289 53230975123288562851244467)
                ·
                  refine ⟨79846462684932844276866701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53230975123288562851244467 79846462684932844276866701)
                  ·
                    refine ⟨29942423506849816603825013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 79846462684932844276866701 29942423506849816603825013)
                    ·
                      refine ⟨2807102203767170306608595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29942423506849816603825013 2807102203767170306608595)
                      ·
                        rfl

theorem cell23_5466812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_5466812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466812 prefixEnd_5466812 := by exact prefixLift 5466812
  have htrace : WordTrace (prefixWord ++ tailWord_5466812) baseStart_5466812 baseEnd_5466812 := by
    simpa [prefixWord, tailWord_5466812, baseEnd_5466812] using wordTrace_append hprefix tailTrace_5466812
  have hstable : (prefixWord ++ tailWord_5466812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466812).length < 2 ^ (prefixWord ++ tailWord_5466812).sum := by decide
  have hdescent : baseEnd_5466812 < baseStart_5466812 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466820 : List Nat := [2, 3, 3, 1, 1, 4, 2, 1, 2, 1, 3]
def baseStart_5466820 : Nat := 118140960795 + 5466820 * 2 ^ 59
def prefixEnd_5466820 : Nat := 4983230072969 + 3 ^ 40 * 5466820 * 2
def baseEnd_5466820 : Nat := 2807106311612406275308559

theorem tailTrace_5466820 : CollatzResearch.WordTrace tailWord_5466820 prefixEnd_5466820 2807106311612406275308559 := by
  unfold tailWord_5466820
  simp only [CollatzResearch.WordTrace]
  refine ⟨99695653027326136684378957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132927537369768182245838609 99695653027326136684378957)
  ·
    refine ⟨37385869885247301256642109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99695653027326136684378957 37385869885247301256642109)
    ·
      refine ⟨14019701206967737971240791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37385869885247301256642109 14019701206967737971240791)
      ·
        refine ⟨21029551810451606956861187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14019701206967737971240791 21029551810451606956861187)
        ·
          refine ⟨31544327715677410435291781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21029551810451606956861187 31544327715677410435291781)
          ·
            refine ⟨5914561446689514456617209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31544327715677410435291781 5914561446689514456617209)
            ·
              refine ⟨4435921085017135842462907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5914561446689514456617209 4435921085017135842462907)
              ·
                refine ⟨6653881627525703763694361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4435921085017135842462907 6653881627525703763694361)
                ·
                  refine ⟨4990411220644277822770771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6653881627525703763694361 4990411220644277822770771)
                  ·
                    refine ⟨7485616830966416734156157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4990411220644277822770771 7485616830966416734156157)
                    ·
                      refine ⟨2807106311612406275308559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7485616830966416734156157 2807106311612406275308559)
                      ·
                        rfl

theorem cell23_5466820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_5466820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466820 prefixEnd_5466820 := by exact prefixLift 5466820
  have htrace : WordTrace (prefixWord ++ tailWord_5466820) baseStart_5466820 baseEnd_5466820 := by
    simpa [prefixWord, tailWord_5466820, baseEnd_5466820] using wordTrace_append hprefix tailTrace_5466820
  have hstable : (prefixWord ++ tailWord_5466820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466820).length < 2 ^ (prefixWord ++ tailWord_5466820).sum := by decide
  have hdescent : baseEnd_5466820 < baseStart_5466820 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466866 : List Nat := [3, 2, 1, 3, 1, 3, 1, 4, 5]
def baseStart_5466866 : Nat := 118140960795 + 5466866 * 2 ^ 59
def prefixEnd_5466866 : Nat := 4983230072969 + 3 ^ 40 * 5466866 * 2
def baseEnd_5466866 : Nat := 311903325746945899481483

theorem tailTrace_5466866 : CollatzResearch.WordTrace tailWord_5466866 prefixEnd_5466866 311903325746945899481483 := by
  unfold tailWord_5466866
  simp only [CollatzResearch.WordTrace]
  refine ⟨49848245953121405806233113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132928655874990415483288301 49848245953121405806233113)
  ·
    refine ⟨37386184464841054354674835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49848245953121405806233113 37386184464841054354674835)
    ·
      refine ⟨56079276697261581532012253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37386184464841054354674835 56079276697261581532012253)
      ·
        refine ⟨21029728761473093074504595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56079276697261581532012253 21029728761473093074504595)
        ·
          refine ⟨31544593142209639611756893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21029728761473093074504595 31544593142209639611756893)
          ·
            refine ⟨11829222428328614854408835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31544593142209639611756893 11829222428328614854408835)
            ·
              refine ⟨17743833642492922281613253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11829222428328614854408835 17743833642492922281613253)
              ·
                refine ⟨3326968807967422927802485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17743833642492922281613253 3326968807967422927802485)
                ·
                  refine ⟨311903325746945899481483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3326968807967422927802485 311903325746945899481483)
                  ·
                    rfl

theorem cell23_5466866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 4, 5].length) (baseStart_5466866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466866 prefixEnd_5466866 := by exact prefixLift 5466866
  have htrace : WordTrace (prefixWord ++ tailWord_5466866) baseStart_5466866 baseEnd_5466866 := by
    simpa [prefixWord, tailWord_5466866, baseEnd_5466866] using wordTrace_append hprefix tailTrace_5466866
  have hstable : (prefixWord ++ tailWord_5466866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466866).length < 2 ^ (prefixWord ++ tailWord_5466866).sum := by decide
  have hdescent : baseEnd_5466866 < baseStart_5466866 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466872 : List Nat := [2, 1, 2, 1, 1, 2, 3, 3, 1, 2, 5]
def baseStart_5466872 : Nat := 118140960795 + 5466872 * 2 ^ 59
def prefixEnd_5466872 : Nat := 4983230072969 + 3 ^ 40 * 5466872 * 2
def baseEnd_5466872 : Nat := 2807133012606440071858319

theorem tailTrace_5466872 : CollatzResearch.WordTrace tailWord_5466872 prefixEnd_5466872 2807133012606440071858319 := by
  unfold tailWord_5466872
  simp only [CollatzResearch.WordTrace]
  refine ⟨99696601325231943124825435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132928801766975924166433913 99696601325231943124825435)
  ·
    refine ⟨149544901987847914687238153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99696601325231943124825435 149544901987847914687238153)
    ·
      refine ⟨112158676490885936015428615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149544901987847914687238153 112158676490885936015428615)
      ·
        refine ⟨168238014736328904023142923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112158676490885936015428615 168238014736328904023142923)
        ·
          refine ⟨252357022104493356034714385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168238014736328904023142923 252357022104493356034714385)
          ·
            refine ⟨189267766578370017026035789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 252357022104493356034714385 189267766578370017026035789)
            ·
              refine ⟨70975412466888756384763421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 189267766578370017026035789 70975412466888756384763421)
              ·
                refine ⟨26615779675083283644286283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70975412466888756384763421 26615779675083283644286283)
                ·
                  refine ⟨39923669512624925466429425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26615779675083283644286283 39923669512624925466429425)
                  ·
                    refine ⟨29942752134468694099822069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39923669512624925466429425 29942752134468694099822069)
                    ·
                      refine ⟨2807133012606440071858319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29942752134468694099822069 2807133012606440071858319)
                      ·
                        rfl

theorem cell23_5466872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 1, 2, 5].length) (baseStart_5466872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466872 prefixEnd_5466872 := by exact prefixLift 5466872
  have htrace : WordTrace (prefixWord ++ tailWord_5466872) baseStart_5466872 baseEnd_5466872 := by
    simpa [prefixWord, tailWord_5466872, baseEnd_5466872] using wordTrace_append hprefix tailTrace_5466872
  have hstable : (prefixWord ++ tailWord_5466872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466872).length < 2 ^ (prefixWord ++ tailWord_5466872).sum := by decide
  have hdescent : baseEnd_5466872 < baseStart_5466872 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466899 : List Nat := [1, 1, 1, 2, 1, 3, 3, 2, 1, 6, 2]
def baseStart_5466899 : Nat := 118140960795 + 5466899 * 2 ^ 59
def prefixEnd_5466899 : Nat := 4983230072969 + 3 ^ 40 * 5466899 * 2
def baseEnd_5466899 : Nat := 2807146876584111466220695

theorem tailTrace_5466899 : CollatzResearch.WordTrace tailWord_5466899 prefixEnd_5466899 2807146876584111466220695 := by
  unfold tailWord_5466899
  simp only [CollatzResearch.WordTrace]
  refine ⟨199394187421366069860883751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132929458280910713240589167 199394187421366069860883751)
  ·
    refine ⟨299091281132049104791325627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199394187421366069860883751 299091281132049104791325627)
    ·
      refine ⟨448636921698073657186988441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299091281132049104791325627 448636921698073657186988441)
      ·
        refine ⟨336477691273555242890241331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 448636921698073657186988441 336477691273555242890241331)
        ·
          refine ⟨504716536910332864335361997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 336477691273555242890241331 504716536910332864335361997)
          ·
            refine ⟨189268701341374824125760749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 504716536910332864335361997 189268701341374824125760749)
            ·
              refine ⟨70975763003015559047160281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 189268701341374824125760749 70975763003015559047160281)
              ·
                refine ⟨53231822252261669285370211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70975763003015559047160281 53231822252261669285370211)
                ·
                  refine ⟨79847733378392503928055317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53231822252261669285370211 79847733378392503928055317)
                  ·
                    refine ⟨3742862502112148621627593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 79847733378392503928055317 3742862502112148621627593)
                    ·
                      refine ⟨2807146876584111466220695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3742862502112148621627593 2807146876584111466220695)
                      ·
                        rfl

theorem cell23_5466899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 6, 2].length) (baseStart_5466899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466899 prefixEnd_5466899 := by exact prefixLift 5466899
  have htrace : WordTrace (prefixWord ++ tailWord_5466899) baseStart_5466899 baseEnd_5466899 := by
    simpa [prefixWord, tailWord_5466899, baseEnd_5466899] using wordTrace_append hprefix tailTrace_5466899
  have hstable : (prefixWord ++ tailWord_5466899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466899).length < 2 ^ (prefixWord ++ tailWord_5466899).sum := by decide
  have hdescent : baseEnd_5466899 < baseStart_5466899 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466983 : List Nat := [1, 1, 5, 1, 2, 2, 3, 1, 3, 1, 3]
def baseStart_5466983 : Nat := 118140960795 + 5466983 * 2 ^ 59
def prefixEnd_5466983 : Nat := 4983230072969 + 3 ^ 40 * 5466983 * 2
def baseEnd_5466983 : Nat := 2807190008959089137570309

theorem tailTrace_5466983 : CollatzResearch.WordTrace tailWord_5466983 prefixEnd_5466983 2807190008959089137570309 := by
  unfold tailWord_5466983
  simp only [CollatzResearch.WordTrace]
  refine ⟨199397251153061752206941603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132931500768707834804627735 199397251153061752206941603)
  ·
    refine ⟨299095876729592628310412405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199397251153061752206941603 299095876729592628310412405)
    ·
      refine ⟨28040238443399308904101163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 299095876729592628310412405 28040238443399308904101163)
      ·
        refine ⟨42060357665098963356151745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28040238443399308904101163 42060357665098963356151745)
        ·
          refine ⟨31545268248824222517113809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42060357665098963356151745 31545268248824222517113809)
          ·
            refine ⟨23658951186618166887835357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31545268248824222517113809 23658951186618166887835357)
            ·
              refine ⟨8872106694981812582938259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23658951186618166887835357 8872106694981812582938259)
              ·
                refine ⟨13308160042472718874407389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8872106694981812582938259 13308160042472718874407389)
                ·
                  refine ⟨4990560015927269577902771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13308160042472718874407389 4990560015927269577902771)
                  ·
                    refine ⟨7485840023890904366854157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4990560015927269577902771 7485840023890904366854157)
                    ·
                      refine ⟨2807190008959089137570309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7485840023890904366854157 2807190008959089137570309)
                      ·
                        rfl

theorem cell23_5466983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_5466983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466983 prefixEnd_5466983 := by exact prefixLift 5466983
  have htrace : WordTrace (prefixWord ++ tailWord_5466983) baseStart_5466983 baseEnd_5466983 := by
    simpa [prefixWord, tailWord_5466983, baseEnd_5466983] using wordTrace_append hprefix tailTrace_5466983
  have hstable : (prefixWord ++ tailWord_5466983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466983).length < 2 ^ (prefixWord ++ tailWord_5466983).sum := by decide
  have hdescent : baseEnd_5466983 < baseStart_5466983 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466989 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 2, 5, 4]
def baseStart_5466989 : Nat := 118140960795 + 5466989 * 2 ^ 59
def prefixEnd_5466989 : Nat := 4983230072969 + 3 ^ 40 * 5466989 * 2
def baseEnd_5466989 : Nat := 2807193089843016114095281

theorem tailTrace_5466989 : CollatzResearch.WordTrace tailWord_5466989 prefixEnd_5466989 2807193089843016114095281 := by
  unfold tailWord_5466989
  simp only [CollatzResearch.WordTrace]
  refine ⟨199397469991040015231660021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132931646660693343487773347 199397469991040015231660021)
  ·
    refine ⟨18693512811660001427968127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 199397469991040015231660021 18693512811660001427968127)
    ·
      refine ⟨28040269217490002141952191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18693512811660001427968127 28040269217490002141952191)
      ·
        refine ⟨42060403826235003212928287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28040269217490002141952191 42060403826235003212928287)
        ·
          refine ⟨63090605739352504819392431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42060403826235003212928287 63090605739352504819392431)
          ·
            refine ⟨94635908609028757229088647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63090605739352504819392431 94635908609028757229088647)
            ·
              refine ⟨141953862913543135843632971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94635908609028757229088647 141953862913543135843632971)
              ·
                refine ⟨212930794370314703765449457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141953862913543135843632971 212930794370314703765449457)
                ·
                  refine ⟨159698095777736027824087093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 212930794370314703765449457 159698095777736027824087093)
                  ·
                    refine ⟨14971696479162752608508165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 159698095777736027824087093 14971696479162752608508165)
                    ·
                      refine ⟨2807193089843016114095281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14971696479162752608508165 2807193089843016114095281)
                      ·
                        rfl

theorem cell23_5466989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_5466989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466989 prefixEnd_5466989 := by exact prefixLift 5466989
  have htrace : WordTrace (prefixWord ++ tailWord_5466989) baseStart_5466989 baseEnd_5466989 := by
    simpa [prefixWord, tailWord_5466989, baseEnd_5466989] using wordTrace_append hprefix tailTrace_5466989
  have hstable : (prefixWord ++ tailWord_5466989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466989).length < 2 ^ (prefixWord ++ tailWord_5466989).sum := by decide
  have hdescent : baseEnd_5466989 < baseStart_5466989 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5466990 : List Nat := [4, 1, 2, 3, 2, 2, 2, 1, 6]
def baseStart_5466990 : Nat := 118140960795 + 5466990 * 2 ^ 59
def prefixEnd_5466990 : Nat := 4983230072969 + 3 ^ 40 * 5466990 * 2
def baseEnd_5466990 : Nat := 311910400369296734464753

theorem tailTrace_5466990 : CollatzResearch.WordTrace tailWord_5466990 prefixEnd_5466990 311910400369296734464753 := by
  unfold tailWord_5466990
  simp only [CollatzResearch.WordTrace]
  refine ⟨24924688308004549050305803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132931670976024261601630949 24924688308004549050305803)
  ·
    refine ⟨37387032462006823575458705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24924688308004549050305803 37387032462006823575458705)
    ·
      refine ⟨28040274346505117681594029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37387032462006823575458705 28040274346505117681594029)
      ·
        refine ⟨10515102879939419130597761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28040274346505117681594029 10515102879939419130597761)
        ·
          refine ⟨7886327159954564347948321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10515102879939419130597761 7886327159954564347948321)
          ·
            refine ⟨5914745369965923260961241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7886327159954564347948321 5914745369965923260961241)
            ·
              refine ⟨4436059027474442445720931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5914745369965923260961241 4436059027474442445720931)
              ·
                refine ⟨6654088541211663668581397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4436059027474442445720931 6654088541211663668581397)
                ·
                  refine ⟨311910400369296734464753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6654088541211663668581397 311910400369296734464753)
                  ·
                    rfl

theorem cell23_5466990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 1, 6].length) (baseStart_5466990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5466990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5466990 prefixEnd_5466990 := by exact prefixLift 5466990
  have htrace : WordTrace (prefixWord ++ tailWord_5466990) baseStart_5466990 baseEnd_5466990 := by
    simpa [prefixWord, tailWord_5466990, baseEnd_5466990] using wordTrace_append hprefix tailTrace_5466990
  have hstable : (prefixWord ++ tailWord_5466990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5466990).length < 2 ^ (prefixWord ++ tailWord_5466990).sum := by decide
  have hdescent : baseEnd_5466990 < baseStart_5466990 := by decide
  rcases family_descends (prefixWord ++ tailWord_5466990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5467016 : List Nat := [2, 1, 3, 3, 2, 2, 1, 2, 1, 6]
def baseStart_5467016 : Nat := 118140960795 + 5467016 * 2 ^ 59
def prefixEnd_5467016 : Nat := 4983230072969 + 3 ^ 40 * 5467016 * 2
def baseEnd_5467016 : Nat := 935735651273562502819219

theorem tailTrace_5467016 : CollatzResearch.WordTrace tailWord_5467016 prefixEnd_5467016 935735651273562502819219 := by
  unfold tailWord_5467016
  simp only [CollatzResearch.WordTrace]
  refine ⟨99699227380971099421446451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132932303174628132561928601 99699227380971099421446451)
  ·
    refine ⟨149548841071456649132169677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99699227380971099421446451 149548841071456649132169677)
    ·
      refine ⟨56080815401796243424563629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149548841071456649132169677 56080815401796243424563629)
      ·
        refine ⟨21030305775673591284211361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56080815401796243424563629 21030305775673591284211361)
        ·
          refine ⟨15772729331755193463158521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21030305775673591284211361 15772729331755193463158521)
          ·
            refine ⟨11829546998816395097368891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15772729331755193463158521 11829546998816395097368891)
            ·
              refine ⟨17744320498224592646053337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11829546998816395097368891 17744320498224592646053337)
              ·
                refine ⟨13308240373668444484540003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17744320498224592646053337 13308240373668444484540003)
                ·
                  refine ⟨19962360560502666726810005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13308240373668444484540003 19962360560502666726810005)
                  ·
                    refine ⟨935735651273562502819219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19962360560502666726810005 935735651273562502819219)
                    ·
                      rfl

theorem cell23_5467016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 1, 6].length) (baseStart_5467016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5467016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5467016 prefixEnd_5467016 := by exact prefixLift 5467016
  have htrace : WordTrace (prefixWord ++ tailWord_5467016) baseStart_5467016 baseEnd_5467016 := by
    simpa [prefixWord, tailWord_5467016, baseEnd_5467016] using wordTrace_append hprefix tailTrace_5467016
  have hstable : (prefixWord ++ tailWord_5467016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5467016).length < 2 ^ (prefixWord ++ tailWord_5467016).sum := by decide
  have hdescent : baseEnd_5467016 < baseStart_5467016 := by decide
  rcases family_descends (prefixWord ++ tailWord_5467016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5467019 : List Nat := [1, 1, 1, 1, 4, 2, 3, 1, 3, 2, 4]
def baseStart_5467019 : Nat := 118140960795 + 5467019 * 2 ^ 59
def prefixEnd_5467019 : Nat := 4983230072969 + 3 ^ 40 * 5467019 * 2
def baseEnd_5467019 : Nat := 2807208494262650996720143

theorem tailTrace_5467019 : CollatzResearch.WordTrace tailWord_5467019 prefixEnd_5467019 2807208494262650996720143 := by
  unfold tailWord_5467019
  simp only [CollatzResearch.WordTrace]
  refine ⟨199398564180931330355252111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132932376120620886903501407 199398564180931330355252111)
  ·
    refine ⟨299097846271396995532878167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199398564180931330355252111 299097846271396995532878167)
    ·
      refine ⟨448646769407095493299317251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299097846271396995532878167 448646769407095493299317251)
      ·
        refine ⟨672970154110643239948975877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 448646769407095493299317251 672970154110643239948975877)
        ·
          refine ⟨126181903895745607490432977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 672970154110643239948975877 126181903895745607490432977)
          ·
            refine ⟨94636427921809205617824733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126181903895745607490432977 94636427921809205617824733)
            ·
              refine ⟨35488660470678452106684275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94636427921809205617824733 35488660470678452106684275)
              ·
                refine ⟨53232990706017678160026413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35488660470678452106684275 53232990706017678160026413)
                ·
                  refine ⟨19962371514756629310009905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53232990706017678160026413 19962371514756629310009905)
                  ·
                    refine ⟨14971778636067471982507429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19962371514756629310009905 14971778636067471982507429)
                    ·
                      refine ⟨2807208494262650996720143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14971778636067471982507429 2807208494262650996720143)
                      ·
                        rfl

theorem cell23_5467019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 2, 4].length) (baseStart_5467019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5467019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5467019 prefixEnd_5467019 := by exact prefixLift 5467019
  have htrace : WordTrace (prefixWord ++ tailWord_5467019) baseStart_5467019 baseEnd_5467019 := by
    simpa [prefixWord, tailWord_5467019, baseEnd_5467019] using wordTrace_append hprefix tailTrace_5467019
  have hstable : (prefixWord ++ tailWord_5467019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5467019).length < 2 ^ (prefixWord ++ tailWord_5467019).sum := by decide
  have hdescent : baseEnd_5467019 < baseStart_5467019 := by decide
  rcases family_descends (prefixWord ++ tailWord_5467019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5467034 : List Nat := [3, 1, 1, 4, 3, 2, 2, 2, 1, 1, 3]
def baseStart_5467034 : Nat := 118140960795 + 5467034 * 2 ^ 59
def prefixEnd_5467034 : Nat := 4983230072969 + 3 ^ 40 * 5467034 * 2
def baseEnd_5467034 : Nat := 2807216196472468438032575

theorem tailTrace_5467034 : CollatzResearch.WordTrace tailWord_5467034 prefixEnd_5467034 2807216196472468438032575 := by
  unfold tailWord_5467034
  simp only [CollatzResearch.WordTrace]
  refine ⟨49849777818969246979262039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132932740850584658611365437 49849777818969246979262039)
  ·
    refine ⟨74774666728453870468893059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49849777818969246979262039 74774666728453870468893059)
    ·
      refine ⟨112162000092680805703339589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74774666728453870468893059 112162000092680805703339589)
      ·
        refine ⟨21030375017377651069376173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112162000092680805703339589 21030375017377651069376173)
        ·
          refine ⟨7886390631516619151016065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21030375017377651069376173 7886390631516619151016065)
          ·
            refine ⟨5914792973637464363262049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7886390631516619151016065 5914792973637464363262049)
            ·
              refine ⟨4436094730228098272446537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5914792973637464363262049 4436094730228098272446537)
              ·
                refine ⟨3327071047671073704334903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4436094730228098272446537 3327071047671073704334903)
                ·
                  refine ⟨4990606571506610556502355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3327071047671073704334903 4990606571506610556502355)
                  ·
                    refine ⟨7485909857259915834753533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4990606571506610556502355 7485909857259915834753533)
                    ·
                      refine ⟨2807216196472468438032575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7485909857259915834753533 2807216196472468438032575)
                      ·
                        rfl

theorem cell23_5467034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_5467034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5467034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5467034 prefixEnd_5467034 := by exact prefixLift 5467034
  have htrace : WordTrace (prefixWord ++ tailWord_5467034) baseStart_5467034 baseEnd_5467034 := by
    simpa [prefixWord, tailWord_5467034, baseEnd_5467034] using wordTrace_append hprefix tailTrace_5467034
  have hstable : (prefixWord ++ tailWord_5467034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5467034).length < 2 ^ (prefixWord ++ tailWord_5467034).sum := by decide
  have hdescent : baseEnd_5467034 < baseStart_5467034 := by decide
  rcases family_descends (prefixWord ++ tailWord_5467034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5467060 : List Nat := [2, 5, 2, 1, 1, 1, 2, 1, 3, 2, 3]
def baseStart_5467060 : Nat := 118140960795 + 5467060 * 2 ^ 59
def prefixEnd_5467060 : Nat := 4983230072969 + 3 ^ 40 * 5467060 * 2
def baseEnd_5467060 : Nat := 2807229546969485336307455

theorem tailTrace_5467060 : CollatzResearch.WordTrace tailWord_5467060 prefixEnd_5467060 2807229546969485336307455 := by
  unfold tailWord_5467060
  simp only [CollatzResearch.WordTrace]
  refine ⟨99700029786891397178747317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132933373049188529571663089 99700029786891397178747317)
  ·
    refine ⟨9346877792521068485507561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 99700029786891397178747317 9346877792521068485507561)
    ·
      refine ⟨7010158344390801364130671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9346877792521068485507561 7010158344390801364130671)
      ·
        refine ⟨10515237516586202046196007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7010158344390801364130671 10515237516586202046196007)
        ·
          refine ⟨15772856274879303069294011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10515237516586202046196007 15772856274879303069294011)
          ·
            refine ⟨23659284412318954603941017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15772856274879303069294011 23659284412318954603941017)
            ·
              refine ⟨17744463309239215952955763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23659284412318954603941017 17744463309239215952955763)
              ·
                refine ⟨26616694963858823929433645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17744463309239215952955763 26616694963858823929433645)
                ·
                  refine ⟨9981260611447058973537617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26616694963858823929433645 9981260611447058973537617)
                  ·
                    refine ⟨7485945458585294230153213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9981260611447058973537617 7485945458585294230153213)
                    ·
                      refine ⟨2807229546969485336307455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7485945458585294230153213 2807229546969485336307455)
                      ·
                        rfl

theorem cell23_5467060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_5467060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5467060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5467060 prefixEnd_5467060 := by exact prefixLift 5467060
  have htrace : WordTrace (prefixWord ++ tailWord_5467060) baseStart_5467060 baseEnd_5467060 := by
    simpa [prefixWord, tailWord_5467060, baseEnd_5467060] using wordTrace_append hprefix tailTrace_5467060
  have hstable : (prefixWord ++ tailWord_5467060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5467060).length < 2 ^ (prefixWord ++ tailWord_5467060).sum := by decide
  have hdescent : baseEnd_5467060 < baseStart_5467060 := by decide
  rcases family_descends (prefixWord ++ tailWord_5467060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5467089 : List Nat := [1, 2, 2, 1, 2, 1, 3, 1, 4, 6]
def baseStart_5467089 : Nat := 118140960795 + 5467089 * 2 ^ 59
def prefixEnd_5467089 : Nat := 4983230072969 + 3 ^ 40 * 5467089 * 2
def baseEnd_5467089 : Nat := 935748145969488574281607

theorem tailTrace_5467089 : CollatzResearch.WordTrace tailWord_5467089 prefixEnd_5467089 935748145969488574281607 := by
  unfold tailWord_5467089
  simp only [CollatzResearch.WordTrace]
  refine ⟨199401117290677732310300321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132934078193785154873533547 199401117290677732310300321)
  ·
    refine ⟨149550837968008299232725241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199401117290677732310300321 149550837968008299232725241)
    ·
      refine ⟨112163128476006224424543931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149550837968008299232725241 112163128476006224424543931)
      ·
        refine ⟨168244692714009336636815897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112163128476006224424543931 168244692714009336636815897)
        ·
          refine ⟨126183519535507002477611923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168244692714009336636815897 126183519535507002477611923)
          ·
            refine ⟨189275279303260503716417885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126183519535507002477611923 189275279303260503716417885)
            ·
              refine ⟨70978229738722688893656707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 189275279303260503716417885 70978229738722688893656707)
              ·
                refine ⟨106467344608084033340485061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70978229738722688893656707 106467344608084033340485061)
                ·
                  refine ⟨19962627114015756251340949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 106467344608084033340485061 19962627114015756251340949)
                  ·
                    refine ⟨935748145969488574281607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19962627114015756251340949 935748145969488574281607)
                    ·
                      rfl

theorem cell23_5467089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 6].length) (baseStart_5467089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5467089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5467089 prefixEnd_5467089 := by exact prefixLift 5467089
  have htrace : WordTrace (prefixWord ++ tailWord_5467089) baseStart_5467089 baseEnd_5467089 := by
    simpa [prefixWord, tailWord_5467089, baseEnd_5467089] using wordTrace_append hprefix tailTrace_5467089
  have hstable : (prefixWord ++ tailWord_5467089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5467089).length < 2 ^ (prefixWord ++ tailWord_5467089).sum := by decide
  have hdescent : baseEnd_5467089 < baseStart_5467089 := by decide
  rcases family_descends (prefixWord ++ tailWord_5467089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5467090 : List Nat := [3, 2, 2, 3, 1, 2, 1, 1, 4, 1, 3]
def baseStart_5467090 : Nat := 118140960795 + 5467090 * 2 ^ 59
def prefixEnd_5467090 : Nat := 4983230072969 + 3 ^ 40 * 5467090 * 2
def baseEnd_5467090 : Nat := 2807244951389120218932317

theorem tailTrace_5467090 : CollatzResearch.WordTrace tailWord_5467090 prefixEnd_5467090 2807244951389120218932317 := by
  unfold tailWord_5467090
  simp only [CollatzResearch.WordTrace]
  refine ⟨49850288440918527370271681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132934102509116072987391149 49850288440918527370271681)
  ·
    refine ⟨37387716330688895527703761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49850288440918527370271681 37387716330688895527703761)
    ·
      refine ⟨28040787248016671645777821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37387716330688895527703761 28040787248016671645777821)
      ·
        refine ⟨10515295218006251867166683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28040787248016671645777821 10515295218006251867166683)
        ·
          refine ⟨15772942827009377800750025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10515295218006251867166683 15772942827009377800750025)
          ·
            refine ⟨11829707120257033350562519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15772942827009377800750025 11829707120257033350562519)
            ·
              refine ⟨17744560680385550025843779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11829707120257033350562519 17744560680385550025843779)
              ·
                refine ⟨26616841020578325038765669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17744560680385550025843779 26616841020578325038765669)
                ·
                  refine ⟨4990657691358435944768563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26616841020578325038765669 4990657691358435944768563)
                  ·
                    refine ⟨7485986537037653917152845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4990657691358435944768563 7485986537037653917152845)
                    ·
                      refine ⟨2807244951389120218932317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7485986537037653917152845 2807244951389120218932317)
                      ·
                        rfl

theorem cell23_5467090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_5467090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5467090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5467090 prefixEnd_5467090 := by exact prefixLift 5467090
  have htrace : WordTrace (prefixWord ++ tailWord_5467090) baseStart_5467090 baseEnd_5467090 := by
    simpa [prefixWord, tailWord_5467090, baseEnd_5467090] using wordTrace_append hprefix tailTrace_5467090
  have hstable : (prefixWord ++ tailWord_5467090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5467090).length < 2 ^ (prefixWord ++ tailWord_5467090).sum := by decide
  have hdescent : baseEnd_5467090 < baseStart_5467090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5467090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5467139 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 6]
def baseStart_5467139 : Nat := 118140960795 + 5467139 * 2 ^ 59
def prefixEnd_5467139 : Nat := 4983230072969 + 3 ^ 40 * 5467139 * 2
def baseEnd_5467139 : Nat := 2807270111941190527219591

theorem tailTrace_5467139 : CollatzResearch.WordTrace tailWord_5467139 prefixEnd_5467139 2807270111941190527219591 := by
  unfold tailWord_5467139
  simp only [CollatzResearch.WordTrace]
  refine ⟨199402940940496590849620471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132935293960331060566413647 199402940940496590849620471)
  ·
    refine ⟨299104411410744886274430707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199402940940496590849620471 299104411410744886274430707)
    ·
      refine ⟨448656617116117329411646061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299104411410744886274430707 448656617116117329411646061)
      ·
        refine ⟨168246231418543998529367273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 448656617116117329411646061 168246231418543998529367273)
        ·
          refine ⟨126184673563907998897025455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168246231418543998529367273 126184673563907998897025455)
          ·
            refine ⟨189277010345861998345538183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126184673563907998897025455 189277010345861998345538183)
            ·
              refine ⟨283915515518792997518307275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189277010345861998345538183 283915515518792997518307275)
              ·
                refine ⟨425873273278189496277460913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 283915515518792997518307275 425873273278189496277460913)
                ·
                  refine ⟨319404954958642122208095685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 425873273278189496277460913 319404954958642122208095685)
                  ·
                    refine ⟨59888429054745397914017941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 319404954958642122208095685 59888429054745397914017941)
                    ·
                      refine ⟨2807270111941190527219591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59888429054745397914017941 2807270111941190527219591)
                      ·
                        rfl

theorem cell23_5467139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 6].length) (baseStart_5467139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5467139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5467139 prefixEnd_5467139 := by exact prefixLift 5467139
  have htrace : WordTrace (prefixWord ++ tailWord_5467139) baseStart_5467139 baseEnd_5467139 := by
    simpa [prefixWord, tailWord_5467139, baseEnd_5467139] using wordTrace_append hprefix tailTrace_5467139
  have hstable : (prefixWord ++ tailWord_5467139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5467139).length < 2 ^ (prefixWord ++ tailWord_5467139).sum := by decide
  have hdescent : baseEnd_5467139 < baseStart_5467139 := by decide
  rcases family_descends (prefixWord ++ tailWord_5467139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5467203 : List Nat := [1, 1, 1, 3, 1, 2, 4, 2, 2, 4, 2]
def baseStart_5467203 : Nat := 118140960795 + 5467203 * 2 ^ 59
def prefixEnd_5467203 : Nat := 4983230072969 + 3 ^ 40 * 5467203 * 2
def baseEnd_5467203 : Nat := 2807302974703078276819297

theorem tailTrace_5467203 : CollatzResearch.WordTrace tailWord_5467203 prefixEnd_5467203 2807302974703078276819297 := by
  unfold tailWord_5467203
  simp only [CollatzResearch.WordTrace]
  refine ⟨199405275212264729779950263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132936850141509819853300175 199405275212264729779950263)
  ·
    refine ⟨299107912818397094669925395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199405275212264729779950263 299107912818397094669925395)
    ·
      refine ⟨448661869227595642004888093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299107912818397094669925395 448661869227595642004888093)
      ·
        refine ⟨168248200960348365751833035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 448661869227595642004888093 168248200960348365751833035)
        ·
          refine ⟨252372301440522548627749553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168248200960348365751833035 252372301440522548627749553)
          ·
            refine ⟨189279226080391911470812165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 252372301440522548627749553 189279226080391911470812165)
            ·
              refine ⟨35489854890073483400777281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 189279226080391911470812165 35489854890073483400777281)
              ·
                refine ⟨26617391167555112550582961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35489854890073483400777281 26617391167555112550582961)
                ·
                  refine ⟨19963043375666334412937221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26617391167555112550582961 19963043375666334412937221)
                  ·
                    refine ⟨3743070632937437702425729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19963043375666334412937221 3743070632937437702425729)
                    ·
                      refine ⟨2807302974703078276819297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3743070632937437702425729 2807302974703078276819297)
                      ·
                        rfl

theorem cell23_5467203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 4, 2].length) (baseStart_5467203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5467203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5467203 prefixEnd_5467203 := by exact prefixLift 5467203
  have htrace : WordTrace (prefixWord ++ tailWord_5467203) baseStart_5467203 baseEnd_5467203 := by
    simpa [prefixWord, tailWord_5467203, baseEnd_5467203] using wordTrace_append hprefix tailTrace_5467203
  have hstable : (prefixWord ++ tailWord_5467203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5467203).length < 2 ^ (prefixWord ++ tailWord_5467203).sum := by decide
  have hdescent : baseEnd_5467203 < baseStart_5467203 := by decide
  rcases family_descends (prefixWord ++ tailWord_5467203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5467290 : List Nat := [3, 1, 1, 5, 1, 1, 1, 4, 1, 5]
def baseStart_5467290 : Nat := 118140960795 + 5467290 * 2 ^ 59
def prefixEnd_5467290 : Nat := 4983230072969 + 3 ^ 40 * 5467290 * 2
def baseEnd_5467290 : Nat := 935782549173339812143799

theorem tailTrace_5467290 : CollatzResearch.WordTrace tailWord_5467290 prefixEnd_5467290 935782549173339812143799 := by
  unfold tailWord_5467290
  simp only [CollatzResearch.WordTrace]
  refine ⟨49852112090737385909591831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132938965575299695758911549 49852112090737385909591831)
  ·
    refine ⟨74778168136106078864387747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49852112090737385909591831 74778168136106078864387747)
    ·
      refine ⟨112167252204159118296581621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74778168136106078864387747 112167252204159118296581621)
      ·
        refine ⟨10515679894139917340304527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 112167252204159118296581621 10515679894139917340304527)
        ·
          refine ⟨15773519841209876010456791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10515679894139917340304527 15773519841209876010456791)
          ·
            refine ⟨23660279761814814015685187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15773519841209876010456791 23660279761814814015685187)
            ·
              refine ⟨35490419642722221023527781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23660279761814814015685187 35490419642722221023527781)
              ·
                refine ⟨6654453683010416441911459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35490419642722221023527781 6654453683010416441911459)
                ·
                  refine ⟨9981680524515624662867189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6654453683010416441911459 9981680524515624662867189)
                  ·
                    refine ⟨935782549173339812143799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9981680524515624662867189 935782549173339812143799)
                    ·
                      rfl

theorem cell23_5467290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 4, 1, 5].length) (baseStart_5467290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5467290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5467290 prefixEnd_5467290 := by exact prefixLift 5467290
  have htrace : WordTrace (prefixWord ++ tailWord_5467290) baseStart_5467290 baseEnd_5467290 := by
    simpa [prefixWord, tailWord_5467290, baseEnd_5467290] using wordTrace_append hprefix tailTrace_5467290
  have hstable : (prefixWord ++ tailWord_5467290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5467290).length < 2 ^ (prefixWord ++ tailWord_5467290).sum := by decide
  have hdescent : baseEnd_5467290 < baseStart_5467290 := by decide
  rcases family_descends (prefixWord ++ tailWord_5467290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5467327 : List Nat := [1, 1, 2, 2, 2, 2, 5, 1, 3, 2, 2]
def baseStart_5467327 : Nat := 118140960795 + 5467327 * 2 ^ 59
def prefixEnd_5467327 : Nat := 4983230072969 + 3 ^ 40 * 5467327 * 2
def baseEnd_5467327 : Nat := 2807366646304235791668727

theorem tailTrace_5467327 : CollatzResearch.WordTrace tailWord_5467327 prefixEnd_5467327 2807366646304235791668727 := by
  unfold tailWord_5467327
  simp only [CollatzResearch.WordTrace]
  refine ⟨199409797863815498957464235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132939865242543665971642823 199409797863815498957464235)
  ·
    refine ⟨299114696795723248436196353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199409797863815498957464235 299114696795723248436196353)
    ·
      refine ⟨224336022596792436327147265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299114696795723248436196353 224336022596792436327147265)
      ·
        refine ⟨168252016947594327245360449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224336022596792436327147265 168252016947594327245360449)
        ·
          refine ⟨126189012710695745434020337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168252016947594327245360449 126189012710695745434020337)
          ·
            refine ⟨94641759533021809075515253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126189012710695745434020337 94641759533021809075515253)
            ·
              refine ⟨8872664956220794600829555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94641759533021809075515253 8872664956220794600829555)
              ·
                refine ⟨13308997434331191901244333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8872664956220794600829555 13308997434331191901244333)
                ·
                  refine ⟨4990874037874196962966625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13308997434331191901244333 4990874037874196962966625)
                  ·
                    refine ⟨3743155528405647722224969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4990874037874196962966625 3743155528405647722224969)
                    ·
                      refine ⟨2807366646304235791668727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3743155528405647722224969 2807366646304235791668727)
                      ·
                        rfl

theorem cell23_5467327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 3, 2, 2].length) (baseStart_5467327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5467327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5467327 prefixEnd_5467327 := by exact prefixLift 5467327
  have htrace : WordTrace (prefixWord ++ tailWord_5467327) baseStart_5467327 baseEnd_5467327 := by
    simpa [prefixWord, tailWord_5467327, baseEnd_5467327] using wordTrace_append hprefix tailTrace_5467327
  have hstable : (prefixWord ++ tailWord_5467327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5467327).length < 2 ^ (prefixWord ++ tailWord_5467327).sum := by decide
  have hdescent : baseEnd_5467327 < baseStart_5467327 := by decide
  rcases family_descends (prefixWord ++ tailWord_5467327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5467341 : List Nat := [1, 6, 2, 2, 1, 2, 1, 2, 1, 5]
def baseStart_5467341 : Nat := 118140960795 + 5467341 * 2 ^ 59
def prefixEnd_5467341 : Nat := 4983230072969 + 3 ^ 40 * 5467341 * 2
def baseEnd_5467341 : Nat := 935791278344466245631221

theorem tailTrace_5467341 : CollatzResearch.WordTrace tailWord_5467341 prefixEnd_5467341 935791278344466245631221 := by
  unfold tailWord_5467341
  simp only [CollatzResearch.WordTrace]
  refine ⟨199410308485764779348473877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132940205657176519565649251 199410308485764779348473877)
  ·
    refine ⟨9347358210270224031959713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 199410308485764779348473877 9347358210270224031959713)
    ·
      refine ⟨7010518657702668023969785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9347358210270224031959713 7010518657702668023969785)
      ·
        refine ⟨5257888993277001017977339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7010518657702668023969785 5257888993277001017977339)
        ·
          refine ⟨7886833489915501526966009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5257888993277001017977339 7886833489915501526966009)
          ·
            refine ⟨5915125117436626145224507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7886833489915501526966009 5915125117436626145224507)
            ·
              refine ⟨8872687676154939217836761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5915125117436626145224507 8872687676154939217836761)
              ·
                refine ⟨6654515757116204413377571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8872687676154939217836761 6654515757116204413377571)
                ·
                  refine ⟨9981773635674306620066357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6654515757116204413377571 9981773635674306620066357)
                  ·
                    refine ⟨935791278344466245631221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9981773635674306620066357 935791278344466245631221)
                    ·
                      rfl

theorem cell23_5467341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_5467341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5467341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5467341 prefixEnd_5467341 := by exact prefixLift 5467341
  have htrace : WordTrace (prefixWord ++ tailWord_5467341) baseStart_5467341 baseEnd_5467341 := by
    simpa [prefixWord, tailWord_5467341, baseEnd_5467341] using wordTrace_append hprefix tailTrace_5467341
  have hstable : (prefixWord ++ tailWord_5467341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5467341).length < 2 ^ (prefixWord ++ tailWord_5467341).sum := by decide
  have hdescent : baseEnd_5467341 < baseStart_5467341 := by decide
  rcases family_descends (prefixWord ++ tailWord_5467341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5467357 : List Nat := [1, 4, 3, 2, 2, 1, 1, 2, 1, 2, 4]
def baseStart_5467357 : Nat := 118140960795 + 5467357 * 2 ^ 59
def prefixEnd_5467357 : Nat := 4983230072969 + 3 ^ 40 * 5467357 * 2
def baseEnd_5467357 : Nat := 2807382050723870674293589

theorem tailTrace_5467357 : CollatzResearch.WordTrace tailWord_5467357 prefixEnd_5467357 2807382050723870674293589 := by
  unfold tailWord_5467357
  simp only [CollatzResearch.WordTrace]
  refine ⟨199410892053706814081056325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132940594702471209387370883 199410892053706814081056325)
  ·
    refine ⟨37389542260070027640198061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 199410892053706814081056325 37389542260070027640198061)
    ·
      refine ⟨14021078347526260365074273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37389542260070027640198061 14021078347526260365074273)
      ·
        refine ⟨10515808760644695273805705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14021078347526260365074273 10515808760644695273805705)
        ·
          refine ⟨7886856570483521455354279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10515808760644695273805705 7886856570483521455354279)
          ·
            refine ⟨11830284855725282183031419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7886856570483521455354279 11830284855725282183031419)
            ·
              refine ⟨17745427283587923274547129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11830284855725282183031419 17745427283587923274547129)
              ·
                refine ⟨13309070462690942455910347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17745427283587923274547129 13309070462690942455910347)
                ·
                  refine ⟨19963605694036413683865521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13309070462690942455910347 19963605694036413683865521)
                  ·
                    refine ⟨14972704270527310262899141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19963605694036413683865521 14972704270527310262899141)
                    ·
                      refine ⟨2807382050723870674293589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14972704270527310262899141 2807382050723870674293589)
                      ·
                        rfl

theorem cell23_5467357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_5467357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5467357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5467357 prefixEnd_5467357 := by exact prefixLift 5467357
  have htrace : WordTrace (prefixWord ++ tailWord_5467357) baseStart_5467357 baseEnd_5467357 := by
    simpa [prefixWord, tailWord_5467357, baseEnd_5467357] using wordTrace_append hprefix tailTrace_5467357
  have hstable : (prefixWord ++ tailWord_5467357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5467357).length < 2 ^ (prefixWord ++ tailWord_5467357).sum := by decide
  have hdescent : baseEnd_5467357 < baseStart_5467357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5467357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5467360 : List Nat := [2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 3]
def baseStart_5467360 : Nat := 118140960795 + 5467360 * 2 ^ 59
def prefixEnd_5467360 : Nat := 4983230072969 + 3 ^ 40 * 5467360 * 2
def baseEnd_5467360 : Nat := 2807383591165834162556075

theorem tailTrace_5467360 : CollatzResearch.WordTrace tailWord_5467360 prefixEnd_5467360 2807383591165834162556075 := by
  unfold tailWord_5467360
  simp only [CollatzResearch.WordTrace]
  refine ⟨99705500736347972796707767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132940667648463963728943689 99705500736347972796707767)
  ·
    refine ⟨149558251104521959195061651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99705500736347972796707767 149558251104521959195061651)
    ·
      refine ⟨224337376656782938792592477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149558251104521959195061651 224337376656782938792592477)
      ·
        refine ⟨84126516246293602047222179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 224337376656782938792592477 84126516246293602047222179)
        ·
          refine ⟨126189774369440403070833269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84126516246293602047222179 126189774369440403070833269)
          ·
            refine ⟨11830291347135037787890619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 126189774369440403070833269 11830291347135037787890619)
            ·
              refine ⟨17745437020702556681835929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11830291347135037787890619 17745437020702556681835929)
              ·
                refine ⟨13309077765526917511376947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17745437020702556681835929 13309077765526917511376947)
                ·
                  refine ⟨19963616648290376267065421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13309077765526917511376947 19963616648290376267065421)
                  ·
                    refine ⟨7486356243108891100149533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19963616648290376267065421 7486356243108891100149533)
                    ·
                      refine ⟨2807383591165834162556075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7486356243108891100149533 2807383591165834162556075)
                      ·
                        rfl

theorem cell23_5467360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 3].length) (baseStart_5467360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5467360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5467360 prefixEnd_5467360 := by exact prefixLift 5467360
  have htrace : WordTrace (prefixWord ++ tailWord_5467360) baseStart_5467360 baseEnd_5467360 := by
    simpa [prefixWord, tailWord_5467360, baseEnd_5467360] using wordTrace_append hprefix tailTrace_5467360
  have hstable : (prefixWord ++ tailWord_5467360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5467360).length < 2 ^ (prefixWord ++ tailWord_5467360).sum := by decide
  have hdescent : baseEnd_5467360 < baseStart_5467360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5467360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5467393 : List Nat := [1, 2, 4, 1, 1, 3, 1, 1, 1, 8]
def baseStart_5467393 : Nat := 118140960795 + 5467393 * 2 ^ 59
def prefixEnd_5467393 : Nat := 4983230072969 + 3 ^ 40 * 5467393 * 2
def baseEnd_5467393 : Nat := 935800178675810844481141

theorem tailTrace_5467393 : CollatzResearch.WordTrace tailWord_5467393 prefixEnd_5467393 935800178675810844481141 := by
  unfold tailWord_5467393
  simp only [CollatzResearch.WordTrace]
  refine ⟨199412205081576392229366833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132941470054384261486244555 199412205081576392229366833)
  ·
    refine ⟨149559153811182294172025125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199412205081576392229366833 149559153811182294172025125)
    ·
      refine ⟨28042341339596680157254711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149559153811182294172025125 28042341339596680157254711)
      ·
        refine ⟨42063512009395020235882067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28042341339596680157254711 42063512009395020235882067)
        ·
          refine ⟨63095268014092530353823101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42063512009395020235882067 63095268014092530353823101)
          ·
            refine ⟨23660725505284698882683663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63095268014092530353823101 23660725505284698882683663)
            ·
              refine ⟨35491088257927048324025495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23660725505284698882683663 35491088257927048324025495)
              ·
                refine ⟨53236632386890572486038243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35491088257927048324025495 53236632386890572486038243)
                ·
                  refine ⟨79854948580335858729057365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53236632386890572486038243 79854948580335858729057365)
                  ·
                    refine ⟨935800178675810844481141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 79854948580335858729057365 935800178675810844481141)
                    ·
                      rfl

theorem cell23_5467393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_5467393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5467393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5467393 prefixEnd_5467393 := by exact prefixLift 5467393
  have htrace : WordTrace (prefixWord ++ tailWord_5467393) baseStart_5467393 baseEnd_5467393 := by
    simpa [prefixWord, tailWord_5467393, baseEnd_5467393] using wordTrace_append hprefix tailTrace_5467393
  have hstable : (prefixWord ++ tailWord_5467393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5467393).length < 2 ^ (prefixWord ++ tailWord_5467393).sum := by decide
  have hdescent : baseEnd_5467393 < baseStart_5467393 := by decide
  rcases family_descends (prefixWord ++ tailWord_5467393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5467394 : List Nat := [3, 4, 1, 1, 3, 1, 2, 1, 1, 3, 3]
def baseStart_5467394 : Nat := 118140960795 + 5467394 * 2 ^ 59
def prefixEnd_5467394 : Nat := 4983230072969 + 3 ^ 40 * 5467394 * 2
def baseEnd_5467394 : Nat := 2807401049508087029530919

theorem tailTrace_5467394 : CollatzResearch.WordTrace tailWord_5467394 prefixEnd_5467394 2807401049508087029530919 := by
  unfold tailWord_5467394
  simp only [CollatzResearch.WordTrace]
  refine ⟨49853060388643192350038309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132941494369715179600102157 49853060388643192350038309)
  ·
    refine ⟨9347448822870598565632183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49853060388643192350038309 9347448822870598565632183)
    ·
      refine ⟨14021173234305897848448275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9347448822870598565632183 14021173234305897848448275)
      ·
        refine ⟨21031759851458846772672413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14021173234305897848448275 21031759851458846772672413)
        ·
          refine ⟨7886909944297067539752155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21031759851458846772672413 7886909944297067539752155)
          ·
            refine ⟨11830364916445601309628233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7886909944297067539752155 11830364916445601309628233)
            ·
              refine ⟨8872773687334200982221175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11830364916445601309628233 8872773687334200982221175)
              ·
                refine ⟨13309160531001301473331763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8872773687334200982221175 13309160531001301473331763)
                ·
                  refine ⟨19963740796501952209997645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13309160531001301473331763 19963740796501952209997645)
                  ·
                    refine ⟨7486402798688232078749117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19963740796501952209997645 7486402798688232078749117)
                    ·
                      refine ⟨2807401049508087029530919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7486402798688232078749117 2807401049508087029530919)
                      ·
                        rfl

theorem cell23_5467394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_5467394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5467394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5467394 prefixEnd_5467394 := by exact prefixLift 5467394
  have htrace : WordTrace (prefixWord ++ tailWord_5467394) baseStart_5467394 baseEnd_5467394 := by
    simpa [prefixWord, tailWord_5467394, baseEnd_5467394] using wordTrace_append hprefix tailTrace_5467394
  have hstable : (prefixWord ++ tailWord_5467394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5467394).length < 2 ^ (prefixWord ++ tailWord_5467394).sum := by decide
  have hdescent : baseEnd_5467394 < baseStart_5467394 := by decide
  rcases family_descends (prefixWord ++ tailWord_5467394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5467413 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 3, 4, 4]
def baseStart_5467413 : Nat := 118140960795 + 5467413 * 2 ^ 59
def prefixEnd_5467413 : Nat := 4983230072969 + 3 ^ 40 * 5467413 * 2
def baseEnd_5467413 : Nat := 2807410805640522455193331

theorem tailTrace_5467413 : CollatzResearch.WordTrace tailWord_5467413 prefixEnd_5467413 2807410805640522455193331 := by
  unfold tailWord_5467413
  simp only [CollatzResearch.WordTrace]
  refine ⟨199412934541503935645094893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132941956361002623763396595 199412934541503935645094893)
  ·
    refine ⟨74779850453063975866910585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199412934541503935645094893 74779850453063975866910585)
    ·
      refine ⟨56084887839797981900182939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74779850453063975866910585 56084887839797981900182939)
      ·
        refine ⟨84127331759696972850274409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56084887839797981900182939 84127331759696972850274409)
        ·
          refine ⟨63095498819772729637705807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84127331759696972850274409 63095498819772729637705807)
          ·
            refine ⟨94643248229659094456558711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63095498819772729637705807 94643248229659094456558711)
            ·
              refine ⟨141964872344488641684838067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94643248229659094456558711 141964872344488641684838067)
              ·
                refine ⟨212947308516732962527257101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141964872344488641684838067 212947308516732962527257101)
                ·
                  refine ⟨79855240693774860947721413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 212947308516732962527257101 79855240693774860947721413)
                  ·
                    refine ⟨14972857630082786427697765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 79855240693774860947721413 14972857630082786427697765)
                    ·
                      refine ⟨2807410805640522455193331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14972857630082786427697765 2807410805640522455193331)
                      ·
                        rfl

theorem cell23_5467413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_5467413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5467413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5467413 prefixEnd_5467413 := by exact prefixLift 5467413
  have htrace : WordTrace (prefixWord ++ tailWord_5467413) baseStart_5467413 baseEnd_5467413 := by
    simpa [prefixWord, tailWord_5467413, baseEnd_5467413] using wordTrace_append hprefix tailTrace_5467413
  have hstable : (prefixWord ++ tailWord_5467413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5467413).length < 2 ^ (prefixWord ++ tailWord_5467413).sum := by decide
  have hdescent : baseEnd_5467413 < baseStart_5467413 := by decide
  rcases family_descends (prefixWord ++ tailWord_5467413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5467421 : List Nat := [1, 4, 2, 3, 1, 1, 4, 1, 1, 3, 2]
def baseStart_5467421 : Nat := 118140960795 + 5467421 * 2 ^ 59
def prefixEnd_5467421 : Nat := 4983230072969 + 3 ^ 40 * 5467421 * 2
def baseEnd_5467421 : Nat := 2807414913485758423893295

theorem tailTrace_5467421 : CollatzResearch.WordTrace tailWord_5467421 prefixEnd_5467421 2807414913485758423893295 := by
  unfold tailWord_5467421
  simp only [CollatzResearch.WordTrace]
  refine ⟨199413226325474953011386117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132942150883649968674257411 199413226325474953011386117)
  ·
    refine ⟨37389979936026553689634897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 199413226325474953011386117 37389979936026553689634897)
    ·
      refine ⟨28042484952019915267226173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37389979936026553689634897 28042484952019915267226173)
      ·
        refine ⟨10515931857007468225209815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28042484952019915267226173 10515931857007468225209815)
        ·
          refine ⟨15773897785511202337814723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10515931857007468225209815 15773897785511202337814723)
          ·
            refine ⟨23660846678266803506722085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15773897785511202337814723 23660846678266803506722085)
            ·
              refine ⟨4436408752175025657510391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23660846678266803506722085 4436408752175025657510391)
              ·
                refine ⟨6654613128262538486265587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4436408752175025657510391 6654613128262538486265587)
                ·
                  refine ⟨9981919692393807729398381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6654613128262538486265587 9981919692393807729398381)
                  ·
                    refine ⟨3743219884647677898524393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9981919692393807729398381 3743219884647677898524393)
                    ·
                      refine ⟨2807414913485758423893295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3743219884647677898524393 2807414913485758423893295)
                      ·
                        rfl

theorem cell23_5467421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_5467421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5467421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5467421 prefixEnd_5467421 := by exact prefixLift 5467421
  have htrace : WordTrace (prefixWord ++ tailWord_5467421) baseStart_5467421 baseEnd_5467421 := by
    simpa [prefixWord, tailWord_5467421, baseEnd_5467421] using wordTrace_append hprefix tailTrace_5467421
  have hstable : (prefixWord ++ tailWord_5467421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5467421).length < 2 ^ (prefixWord ++ tailWord_5467421).sum := by decide
  have hdescent : baseEnd_5467421 < baseStart_5467421 := by decide
  rcases family_descends (prefixWord ++ tailWord_5467421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5467440 : List Nat := [2, 1, 1, 1, 2, 2, 3, 6, 5]
def baseStart_5467440 : Nat := 118140960795 + 5467440 * 2 ^ 59
def prefixEnd_5467440 : Nat := 4983230072969 + 3 ^ 40 * 5467440 * 2
def baseEnd_5467440 : Nat := 311936074402021538839523

theorem tailTrace_5467440 : CollatzResearch.WordTrace tailWord_5467440 prefixEnd_5467440 311936074402021538839523 := by
  unfold tailWord_5467440
  simp only [CollatzResearch.WordTrace]
  refine ⟨99706959656203059628163887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132942612874937412837551849 99706959656203059628163887)
  ·
    refine ⟨149560439484304589442245831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99706959656203059628163887 149560439484304589442245831)
    ·
      refine ⟨224340659226456884163368747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149560439484304589442245831 224340659226456884163368747)
      ·
        refine ⟨336510988839685326245053121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224340659226456884163368747 336510988839685326245053121)
        ·
          refine ⟨252383241629763994683789841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 336510988839685326245053121 252383241629763994683789841)
          ·
            refine ⟨189287431222322996012842381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 252383241629763994683789841 189287431222322996012842381)
            ·
              refine ⟨70982786708371123504815893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 189287431222322996012842381 70982786708371123504815893)
              ·
                refine ⟨3327318126954896414288245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 70982786708371123504815893 3327318126954896414288245)
                ·
                  refine ⟨311936074402021538839523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3327318126954896414288245 311936074402021538839523)
                  ·
                    rfl

theorem cell23_5467440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 6, 5].length) (baseStart_5467440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5467440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5467440 prefixEnd_5467440 := by exact prefixLift 5467440
  have htrace : WordTrace (prefixWord ++ tailWord_5467440) baseStart_5467440 baseEnd_5467440 := by
    simpa [prefixWord, tailWord_5467440, baseEnd_5467440] using wordTrace_append hprefix tailTrace_5467440
  have hstable : (prefixWord ++ tailWord_5467440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5467440).length < 2 ^ (prefixWord ++ tailWord_5467440).sum := by decide
  have hdescent : baseEnd_5467440 < baseStart_5467440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5467440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5467450 : List Nat := [3, 1, 1, 1, 4, 1, 1, 3, 2, 3, 3]
def baseStart_5467450 : Nat := 118140960795 + 5467450 * 2 ^ 59
def prefixEnd_5467450 : Nat := 4983230072969 + 3 ^ 40 * 5467450 * 2
def baseEnd_5467450 : Nat := 2807429804424738810430661

theorem tailTrace_5467450 : CollatzResearch.WordTrace tailWord_5467450 prefixEnd_5467450 2807429804424738810430661 := by
  unfold tailWord_5467450
  simp only [CollatzResearch.WordTrace]
  refine ⟨49853571010592472741047951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132942856028246593976127869 49853571010592472741047951)
  ·
    refine ⟨74780356515888709111571927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49853571010592472741047951 74780356515888709111571927)
    ·
      refine ⟨112170534773833063667357891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74780356515888709111571927 112170534773833063667357891)
      ·
        refine ⟨168255802160749595501036837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112170534773833063667357891 168255802160749595501036837)
        ·
          refine ⟨31547962905140549156444407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 168255802160749595501036837 31547962905140549156444407)
          ·
            refine ⟨47321944357710823734666611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31547962905140549156444407 47321944357710823734666611)
            ·
              refine ⟨70982916536566235601999917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47321944357710823734666611 70982916536566235601999917)
              ·
                refine ⟨26618593701212338350749969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70982916536566235601999917 26618593701212338350749969)
                ·
                  refine ⟨19963945275909253763062477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26618593701212338350749969 19963945275909253763062477)
                  ·
                    refine ⟨7486479478465970161148429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19963945275909253763062477 7486479478465970161148429)
                    ·
                      refine ⟨2807429804424738810430661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7486479478465970161148429 2807429804424738810430661)
                      ·
                        rfl

theorem cell23_5467450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 2, 3, 3].length) (baseStart_5467450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5467450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5467450 prefixEnd_5467450 := by exact prefixLift 5467450
  have htrace : WordTrace (prefixWord ++ tailWord_5467450) baseStart_5467450 baseEnd_5467450 := by
    simpa [prefixWord, tailWord_5467450, baseEnd_5467450] using wordTrace_append hprefix tailTrace_5467450
  have hstable : (prefixWord ++ tailWord_5467450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5467450).length < 2 ^ (prefixWord ++ tailWord_5467450).sum := by decide
  have hdescent : baseEnd_5467450 < baseStart_5467450 := by decide
  rcases family_descends (prefixWord ++ tailWord_5467450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5467470 : List Nat := [4, 1, 1, 1, 1, 1, 4, 3, 2, 5]
def baseStart_5467470 : Nat := 118140960795 + 5467470 * 2 ^ 59
def prefixEnd_5467470 : Nat := 4983230072969 + 3 ^ 40 * 5467470 * 2
def baseEnd_5467470 : Nat := 935813358012609577393523

theorem tailTrace_5467470 : CollatzResearch.WordTrace tailWord_5467470 prefixEnd_5467470 935813358012609577393523 := by
  unfold tailWord_5467470
  simp only [CollatzResearch.WordTrace]
  refine ⟨24926876687787179297489983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132943342334864956253279909 24926876687787179297489983)
  ·
    refine ⟨37390315031680768946234975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24926876687787179297489983 37390315031680768946234975)
    ·
      refine ⟨56085472547521153419352463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37390315031680768946234975 56085472547521153419352463)
      ·
        refine ⟨84128208821281730129028695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56085472547521153419352463 84128208821281730129028695)
        ·
          refine ⟨126192313231922595193543043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84128208821281730129028695 126192313231922595193543043)
          ·
            refine ⟨189288469847883892790314565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126192313231922595193543043 189288469847883892790314565)
            ·
              refine ⟨35491588096478229898183981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 189288469847883892790314565 35491588096478229898183981)
              ·
                refine ⟨13309345536179336211818993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35491588096478229898183981 13309345536179336211818993)
                ·
                  refine ⟨9982009152134502158864245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13309345536179336211818993 9982009152134502158864245)
                  ·
                    refine ⟨935813358012609577393523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9982009152134502158864245 935813358012609577393523)
                    ·
                      rfl

theorem cell23_5467470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 2, 5].length) (baseStart_5467470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5467470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5467470 prefixEnd_5467470 := by exact prefixLift 5467470
  have htrace : WordTrace (prefixWord ++ tailWord_5467470) baseStart_5467470 baseEnd_5467470 := by
    simpa [prefixWord, tailWord_5467470, baseEnd_5467470] using wordTrace_append hprefix tailTrace_5467470
  have hstable : (prefixWord ++ tailWord_5467470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5467470).length < 2 ^ (prefixWord ++ tailWord_5467470).sum := by decide
  have hdescent : baseEnd_5467470 < baseStart_5467470 := by decide
  rcases family_descends (prefixWord ++ tailWord_5467470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5467502 : List Nat := [4, 1, 2, 4, 2, 1, 2, 1, 2, 2, 2]
def baseStart_5467502 : Nat := 118140960795 + 5467502 * 2 ^ 59
def prefixEnd_5467502 : Nat := 4983230072969 + 3 ^ 40 * 5467502 * 2
def baseEnd_5467502 : Nat := 2807456505418772606980423

theorem tailTrace_5467502 : CollatzResearch.WordTrace tailWord_5467502 prefixEnd_5467502 2807456505418772606980423 := by
  unfold tailWord_5467502
  simp only [CollatzResearch.WordTrace]
  refine ⟨24927022579772687980635595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132944120425454335896723173 24927022579772687980635595)
  ·
    refine ⟨37390533869659031970953393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24927022579772687980635595 37390533869659031970953393)
    ·
      refine ⟨28042900402244273978215045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37390533869659031970953393 28042900402244273978215045)
      ·
        refine ⟨5258043825420801370915321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28042900402244273978215045 5258043825420801370915321)
        ·
          refine ⟨3943532869065601028186491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5258043825420801370915321 3943532869065601028186491)
          ·
            refine ⟨5915299303598401542279737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3943532869065601028186491 5915299303598401542279737)
            ·
              refine ⟨4436474477698801156709803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5915299303598401542279737 4436474477698801156709803)
              ·
                refine ⟨6654711716548201735064705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4436474477698801156709803 6654711716548201735064705)
                ·
                  refine ⟨4991033787411151301298529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6654711716548201735064705 4991033787411151301298529)
                  ·
                    refine ⟨3743275340558363475973897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4991033787411151301298529 3743275340558363475973897)
                    ·
                      refine ⟨2807456505418772606980423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3743275340558363475973897 2807456505418772606980423)
                      ·
                        rfl

theorem cell23_5467502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_5467502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5467502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5467502 prefixEnd_5467502 := by exact prefixLift 5467502
  have htrace : WordTrace (prefixWord ++ tailWord_5467502) baseStart_5467502 baseEnd_5467502 := by
    simpa [prefixWord, tailWord_5467502, baseEnd_5467502] using wordTrace_append hprefix tailTrace_5467502
  have hstable : (prefixWord ++ tailWord_5467502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5467502).length < 2 ^ (prefixWord ++ tailWord_5467502).sum := by decide
  have hdescent : baseEnd_5467502 < baseStart_5467502 := by decide
  rcases family_descends (prefixWord ++ tailWord_5467502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5467527 : List Nat := [1, 1, 4, 2, 2, 2, 1, 3, 2, 2, 3]
def baseStart_5467527 : Nat := 118140960795 + 5467527 * 2 ^ 59
def prefixEnd_5467527 : Nat := 4983230072969 + 3 ^ 40 * 5467527 * 2
def baseEnd_5467527 : Nat := 2807469342435135009167807

theorem tailTrace_5467527 : CollatzResearch.WordTrace tailWord_5467527 prefixEnd_5467527 2807469342435135009167807 := by
  unfold tailWord_5467527
  simp only [CollatzResearch.WordTrace]
  refine ⟨199417092463090933114744835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132944728308727288743163223 199417092463090933114744835)
  ·
    refine ⟨299125638694636399672117253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199417092463090933114744835 299125638694636399672117253)
    ·
      refine ⟨56086057255244324938521985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 299125638694636399672117253 56086057255244324938521985)
      ·
        refine ⟨42064542941433243703891489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56086057255244324938521985 42064542941433243703891489)
        ·
          refine ⟨31548407206074932777918617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42064542941433243703891489 31548407206074932777918617)
          ·
            refine ⟨23661305404556199583438963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31548407206074932777918617 23661305404556199583438963)
            ·
              refine ⟨35491958106834299375158445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23661305404556199583438963 35491958106834299375158445)
              ·
                refine ⟨13309484290062862265684417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35491958106834299375158445 13309484290062862265684417)
                ·
                  refine ⟨9982113217547146699263313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13309484290062862265684417 9982113217547146699263313)
                  ·
                    refine ⟨7486584913160360024447485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9982113217547146699263313 7486584913160360024447485)
                    ·
                      refine ⟨2807469342435135009167807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7486584913160360024447485 2807469342435135009167807)
                      ·
                        rfl

theorem cell23_5467527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_5467527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5467527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5467527 prefixEnd_5467527 := by exact prefixLift 5467527
  have htrace : WordTrace (prefixWord ++ tailWord_5467527) baseStart_5467527 baseEnd_5467527 := by
    simpa [prefixWord, tailWord_5467527, baseEnd_5467527] using wordTrace_append hprefix tailTrace_5467527
  have hstable : (prefixWord ++ tailWord_5467527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5467527).length < 2 ^ (prefixWord ++ tailWord_5467527).sum := by decide
  have hdescent : baseEnd_5467527 < baseStart_5467527 := by decide
  rcases family_descends (prefixWord ++ tailWord_5467527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5467551 : List Nat := [1, 1, 2, 5, 1, 2, 4, 2, 1, 4]
def baseStart_5467551 : Nat := 118140960795 + 5467551 * 2 ^ 59
def prefixEnd_5467551 : Nat := 4983230072969 + 3 ^ 40 * 5467551 * 2
def baseEnd_5467551 : Nat := 935827221990280971755899

theorem tailTrace_5467551 : CollatzResearch.WordTrace tailWord_5467551 prefixEnd_5467551 935827221990280971755899 := by
  unfold tailWord_5467551
  simp only [CollatzResearch.WordTrace]
  refine ⟨199417967815003985213618507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132945311876669323475745671 199417967815003985213618507)
  ·
    refine ⟨299126951722505977820427761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199417967815003985213618507 299126951722505977820427761)
    ·
      refine ⟨224345213791879483365320821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299126951722505977820427761 224345213791879483365320821)
      ·
        refine ⟨21032363792988701565498827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 224345213791879483365320821 21032363792988701565498827)
        ·
          refine ⟨31548545689483052348248241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21032363792988701565498827 31548545689483052348248241)
          ·
            refine ⟨23661409267112289261186181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31548545689483052348248241 23661409267112289261186181)
            ·
              refine ⟨4436514237583554236472409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23661409267112289261186181 4436514237583554236472409)
              ·
                refine ⟨3327385678187665677354307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4436514237583554236472409 3327385678187665677354307)
                ·
                  refine ⟨4991078517281498516031461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3327385678187665677354307 4991078517281498516031461)
                  ·
                    refine ⟨935827221990280971755899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4991078517281498516031461 935827221990280971755899)
                    ·
                      rfl

theorem cell23_5467551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 2, 1, 4].length) (baseStart_5467551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5467551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5467551 prefixEnd_5467551 := by exact prefixLift 5467551
  have htrace : WordTrace (prefixWord ++ tailWord_5467551) baseStart_5467551 baseEnd_5467551 := by
    simpa [prefixWord, tailWord_5467551, baseEnd_5467551] using wordTrace_append hprefix tailTrace_5467551
  have hstable : (prefixWord ++ tailWord_5467551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5467551).length < 2 ^ (prefixWord ++ tailWord_5467551).sum := by decide
  have hdescent : baseEnd_5467551 < baseStart_5467551 := by decide
  rcases family_descends (prefixWord ++ tailWord_5467551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5467567 : List Nat := [1, 1, 2, 1, 2, 2, 1, 4, 4, 3, 2]
def baseStart_5467567 : Nat := 118140960795 + 5467567 * 2 ^ 59
def prefixEnd_5467567 : Nat := 4983230072969 + 3 ^ 40 * 5467567 * 2
def baseEnd_5467567 : Nat := 2807489881661314852667623

theorem tailTrace_5467567 : CollatzResearch.WordTrace tailWord_5467567 prefixEnd_5467567 2807489881661314852667623 := by
  unfold tailWord_5467567
  simp only [CollatzResearch.WordTrace]
  refine ⟨199418551382946019946200955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132945700921964013297467303 199418551382946019946200955)
  ·
    refine ⟨299127827074419029919301433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199418551382946019946200955 299127827074419029919301433)
    ·
      refine ⟨224345870305814272439476075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299127827074419029919301433 224345870305814272439476075)
      ·
        refine ⟨336518805458721408659214113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224345870305814272439476075 336518805458721408659214113)
        ·
          refine ⟨252389104094041056494410585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 336518805458721408659214113 252389104094041056494410585)
          ·
            refine ⟨189291828070530792370807939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 252389104094041056494410585 189291828070530792370807939)
            ·
              refine ⟨283937742105796188556211909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189291828070530792370807939 283937742105796188556211909)
              ·
                refine ⟨53238326644836785354289733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 283937742105796188556211909 53238326644836785354289733)
                ·
                  refine ⟨9982186245906897253929325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53238326644836785354289733 9982186245906897253929325)
                  ·
                    refine ⟨3743319842215086470223497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9982186245906897253929325 3743319842215086470223497)
                    ·
                      refine ⟨2807489881661314852667623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3743319842215086470223497 2807489881661314852667623)
                      ·
                        rfl

theorem cell23_5467567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 4, 3, 2].length) (baseStart_5467567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5467567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5467567 prefixEnd_5467567 := by exact prefixLift 5467567
  have htrace : WordTrace (prefixWord ++ tailWord_5467567) baseStart_5467567 baseEnd_5467567 := by
    simpa [prefixWord, tailWord_5467567, baseEnd_5467567] using wordTrace_append hprefix tailTrace_5467567
  have hstable : (prefixWord ++ tailWord_5467567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5467567).length < 2 ^ (prefixWord ++ tailWord_5467567).sum := by decide
  have hdescent : baseEnd_5467567 < baseStart_5467567 := by decide
  rcases family_descends (prefixWord ++ tailWord_5467567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5467584 : List Nat := [2, 1, 1, 2, 3, 1, 5, 1, 2, 3, 2]
def baseStart_5467584 : Nat := 118140960795 + 5467584 * 2 ^ 59
def prefixEnd_5467584 : Nat := 4983230072969 + 3 ^ 40 * 5467584 * 2
def baseEnd_5467584 : Nat := 2807498610832441286155045

theorem tailTrace_5467584 : CollatzResearch.WordTrace tailWord_5467584 prefixEnd_5467584 2807498610832441286155045 := by
  unfold tailWord_5467584
  simp only [CollatzResearch.WordTrace]
  refine ⟨99709585711942215924784903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132946114282589621233046537 99709585711942215924784903)
  ·
    refine ⟨149564378567913323887177355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99709585711942215924784903 149564378567913323887177355)
    ·
      refine ⟨224346567851869985830766033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149564378567913323887177355 224346567851869985830766033)
      ·
        refine ⟨168259925888902489373074525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224346567851869985830766033 168259925888902489373074525)
        ·
          refine ⟨63097472208338433514902947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168259925888902489373074525 63097472208338433514902947)
          ·
            refine ⟨94646208312507650272354421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63097472208338433514902947 94646208312507650272354421)
            ·
              refine ⟨8873082029297592213033227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94646208312507650272354421 8873082029297592213033227)
              ·
                refine ⟨13309623043946388319549841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8873082029297592213033227 13309623043946388319549841)
                ·
                  refine ⟨9982217282959791239662381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13309623043946388319549841 9982217282959791239662381)
                  ·
                    refine ⟨3743331481109921714873393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9982217282959791239662381 3743331481109921714873393)
                    ·
                      refine ⟨2807498610832441286155045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3743331481109921714873393 2807498610832441286155045)
                      ·
                        rfl

theorem cell23_5467584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 2, 3, 2].length) (baseStart_5467584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5467584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5467584 prefixEnd_5467584 := by exact prefixLift 5467584
  have htrace : WordTrace (prefixWord ++ tailWord_5467584) baseStart_5467584 baseEnd_5467584 := by
    simpa [prefixWord, tailWord_5467584, baseEnd_5467584] using wordTrace_append hprefix tailTrace_5467584
  have hstable : (prefixWord ++ tailWord_5467584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5467584).length < 2 ^ (prefixWord ++ tailWord_5467584).sum := by decide
  have hdescent : baseEnd_5467584 < baseStart_5467584 := by decide
  rcases family_descends (prefixWord ++ tailWord_5467584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5467591 : List Nat := [1, 1, 4, 1, 1, 3, 4, 3, 1, 1, 3]
def baseStart_5467591 : Nat := 118140960795 + 5467591 * 2 ^ 59
def prefixEnd_5467591 : Nat := 4983230072969 + 3 ^ 40 * 5467591 * 2
def baseEnd_5467591 : Nat := 2807502205197022758767513

theorem tailTrace_5467591 : CollatzResearch.WordTrace tailWord_5467591 prefixEnd_5467591 2807502205197022758767513 := by
  unfold tailWord_5467591
  simp only [CollatzResearch.WordTrace]
  refine ⟨199419426734859072045074627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132946284489906048030049751 199419426734859072045074627)
  ·
    refine ⟨299129140102288608067611941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199419426734859072045074627 299129140102288608067611941)
    ·
      refine ⟨56086713769179114012677239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 299129140102288608067611941 56086713769179114012677239)
      ·
        refine ⟨84130070653768671019015859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56086713769179114012677239 84130070653768671019015859)
        ·
          refine ⟨126195105980653006528523789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84130070653768671019015859 126195105980653006528523789)
          ·
            refine ⟨47323164742744877448196421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126195105980653006528523789 47323164742744877448196421)
            ·
              refine ⟨8873093389264664521536829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47323164742744877448196421 8873093389264664521536829)
              ·
                refine ⟨3327410020974249195576311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8873093389264664521536829 3327410020974249195576311)
                ·
                  refine ⟨4991115031461373793364467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3327410020974249195576311 4991115031461373793364467)
                  ·
                    refine ⟨7486672547192060690046701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4991115031461373793364467 7486672547192060690046701)
                    ·
                      refine ⟨2807502205197022758767513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7486672547192060690046701 2807502205197022758767513)
                      ·
                        rfl

theorem cell23_5467591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 3, 1, 1, 3].length) (baseStart_5467591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5467591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5467591 prefixEnd_5467591 := by exact prefixLift 5467591
  have htrace : WordTrace (prefixWord ++ tailWord_5467591) baseStart_5467591 baseEnd_5467591 := by
    simpa [prefixWord, tailWord_5467591, baseEnd_5467591] using wordTrace_append hprefix tailTrace_5467591
  have hstable : (prefixWord ++ tailWord_5467591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5467591).length < 2 ^ (prefixWord ++ tailWord_5467591).sum := by decide
  have hdescent : baseEnd_5467591 < baseStart_5467591 := by decide
  rcases family_descends (prefixWord ++ tailWord_5467591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5467594 : List Nat := [3, 1, 2, 1, 2, 3, 4, 1, 1, 5]
def baseStart_5467594 : Nat := 118140960795 + 5467594 * 2 ^ 59
def prefixEnd_5467594 : Nat := 4983230072969 + 3 ^ 40 * 5467594 * 2
def baseEnd_5467594 : Nat := 935834581879662082343333

theorem tailTrace_5467594 : CollatzResearch.WordTrace tailWord_5467594 prefixEnd_5467594 935834581879662082343333 := by
  unfold tailWord_5467594
  simp only [CollatzResearch.WordTrace]
  refine ⟨49854884038462050889358459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132946357435898802371622557 49854884038462050889358459)
  ·
    refine ⟨74782326057693076334037689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49854884038462050889358459 74782326057693076334037689)
    ·
      refine ⟨56086744543269807250528267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74782326057693076334037689 56086744543269807250528267)
      ·
        refine ⟨84130116814904710875792401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56086744543269807250528267 84130116814904710875792401)
        ·
          refine ⟨63097587611178533156844301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84130116814904710875792401 63097587611178533156844301)
          ·
            refine ⟨23661595354191949933816613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63097587611178533156844301 23661595354191949933816613)
            ·
              refine ⟨4436549128910990612590615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23661595354191949933816613 4436549128910990612590615)
              ·
                refine ⟨6654823693366485918885923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4436549128910990612590615 6654823693366485918885923)
                ·
                  refine ⟨9982235540049728878328885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6654823693366485918885923 9982235540049728878328885)
                  ·
                    refine ⟨935834581879662082343333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9982235540049728878328885 935834581879662082343333)
                    ·
                      rfl

theorem cell23_5467594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 1, 1, 5].length) (baseStart_5467594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5467594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5467594 prefixEnd_5467594 := by exact prefixLift 5467594
  have htrace : WordTrace (prefixWord ++ tailWord_5467594) baseStart_5467594 baseEnd_5467594 := by
    simpa [prefixWord, tailWord_5467594, baseEnd_5467594] using wordTrace_append hprefix tailTrace_5467594
  have hstable : (prefixWord ++ tailWord_5467594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5467594).length < 2 ^ (prefixWord ++ tailWord_5467594).sum := by decide
  have hdescent : baseEnd_5467594 < baseStart_5467594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5467594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5467617 : List Nat := [1, 2, 3, 1, 2, 4, 1, 2, 1, 1, 5]
def baseStart_5467617 : Nat := 118140960795 + 5467617 * 2 ^ 59
def prefixEnd_5467617 : Nat := 4983230072969 + 3 ^ 40 * 5467617 * 2
def baseEnd_5467617 : Nat := 2807515555694039657042393

theorem tailTrace_5467617 : CollatzResearch.WordTrace tailWord_5467617 prefixEnd_5467617 2807515555694039657042393 := by
  unfold tailWord_5467617
  simp only [CollatzResearch.WordTrace]
  refine ⟨199420375032764878485521105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132946916688509918990347403 199420375032764878485521105)
  ·
    refine ⟨149565281274573658864140829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199420375032764878485521105 149565281274573658864140829)
    ·
      refine ⟨56086980477965122074052811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149565281274573658864140829 56086980477965122074052811)
      ·
        refine ⟨84130470716947683111079217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56086980477965122074052811 84130470716947683111079217)
        ·
          refine ⟨63097853037710762333309413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84130470716947683111079217 63097853037710762333309413)
          ·
            refine ⟨11830847444570767937495515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63097853037710762333309413 11830847444570767937495515)
            ·
              refine ⟨17746271166856151906243273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11830847444570767937495515 17746271166856151906243273)
              ·
                refine ⟨13309703375142113929682455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17746271166856151906243273 13309703375142113929682455)
                ·
                  refine ⟨19964555062713170894523683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13309703375142113929682455 19964555062713170894523683)
                  ·
                    refine ⟨29946832594069756341785525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19964555062713170894523683 29946832594069756341785525)
                    ·
                      refine ⟨2807515555694039657042393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29946832594069756341785525 2807515555694039657042393)
                      ·
                        rfl

theorem cell23_5467617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_5467617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5467617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5467617 prefixEnd_5467617 := by exact prefixLift 5467617
  have htrace : WordTrace (prefixWord ++ tailWord_5467617) baseStart_5467617 baseEnd_5467617 := by
    simpa [prefixWord, tailWord_5467617, baseEnd_5467617] using wordTrace_append hprefix tailTrace_5467617
  have hstable : (prefixWord ++ tailWord_5467617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5467617).length < 2 ^ (prefixWord ++ tailWord_5467617).sum := by decide
  have hdescent : baseEnd_5467617 < baseStart_5467617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5467617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5467674 : List Nat := [3, 1, 1, 3, 1, 1, 1, 4, 3, 3, 2]
def baseStart_5467674 : Nat := 118140960795 + 5467674 * 2 ^ 59
def prefixEnd_5467674 : Nat := 4983230072969 + 3 ^ 40 * 5467674 * 2
def baseEnd_5467674 : Nat := 2807544824091345934029631

theorem tailTrace_5467674 : CollatzResearch.WordTrace tailWord_5467674 prefixEnd_5467674 2807544824091345934029631 := by
  unfold tailWord_5467674
  simp only [CollatzResearch.WordTrace]
  refine ⟨49855613498389594305086519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132948302662372251480230717 49855613498389594305086519)
  ·
    refine ⟨74783420247584391457629779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49855613498389594305086519 74783420247584391457629779)
    ·
      refine ⟨112175130371376587186444669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74783420247584391457629779 112175130371376587186444669)
      ·
        refine ⟨42065673889266220194916751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112175130371376587186444669 42065673889266220194916751)
        ·
          refine ⟨63098510833899330292375127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42065673889266220194916751 63098510833899330292375127)
          ·
            refine ⟨94647766250848995438562691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63098510833899330292375127 94647766250848995438562691)
            ·
              refine ⟨141971649376273493157844037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94647766250848995438562691 141971649376273493157844037)
              ·
                refine ⟨26619684258051279967095757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 141971649376273493157844037 26619684258051279967095757)
                ·
                  refine ⟨9982381596769229987660909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26619684258051279967095757 9982381596769229987660909)
                  ·
                    refine ⟨3743393098788461245372841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9982381596769229987660909 3743393098788461245372841)
                    ·
                      refine ⟨2807544824091345934029631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3743393098788461245372841 2807544824091345934029631)
                      ·
                        rfl

theorem cell23_5467674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 3, 3, 2].length) (baseStart_5467674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5467674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5467674 prefixEnd_5467674 := by exact prefixLift 5467674
  have htrace : WordTrace (prefixWord ++ tailWord_5467674) baseStart_5467674 baseEnd_5467674 := by
    simpa [prefixWord, tailWord_5467674, baseEnd_5467674] using wordTrace_append hprefix tailTrace_5467674
  have hstable : (prefixWord ++ tailWord_5467674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5467674).length < 2 ^ (prefixWord ++ tailWord_5467674).sum := by decide
  have hdescent : baseEnd_5467674 < baseStart_5467674 := by decide
  rcases family_descends (prefixWord ++ tailWord_5467674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5467681 : List Nat := [1, 2, 3, 2, 2, 3, 1, 3, 2, 1, 3]
def baseStart_5467681 : Nat := 118140960795 + 5467681 * 2 ^ 59
def prefixEnd_5467681 : Nat := 4983230072969 + 3 ^ 40 * 5467681 * 2
def baseEnd_5467681 : Nat := 2807548418455927406642099

theorem tailTrace_5467681 : CollatzResearch.WordTrace tailWord_5467681 prefixEnd_5467681 2807548418455927406642099 := by
  unfold tailWord_5467681
  simp only [CollatzResearch.WordTrace]
  refine ⟨199422709304533017415850897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132948472869688678277233931 199422709304533017415850897)
  ·
    refine ⟨149567031978399763061888173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199422709304533017415850897 149567031978399763061888173)
    ·
      refine ⟨56087636991899911148208065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149567031978399763061888173 56087636991899911148208065)
      ·
        refine ⟨42065727743924933361156049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56087636991899911148208065 42065727743924933361156049)
        ·
          refine ⟨31549295807943700020867037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42065727743924933361156049 31549295807943700020867037)
          ·
            refine ⟨11830985927978887507825139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31549295807943700020867037 11830985927978887507825139)
            ·
              refine ⟨17746478891968331261737709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11830985927978887507825139 17746478891968331261737709)
              ·
                refine ⟨6654929584488124223151641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17746478891968331261737709 6654929584488124223151641)
                ·
                  refine ⟨4991197188366093167363731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6654929584488124223151641 4991197188366093167363731)
                  ·
                    refine ⟨7486795782549139751045597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4991197188366093167363731 7486795782549139751045597)
                    ·
                      refine ⟨2807548418455927406642099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7486795782549139751045597 2807548418455927406642099)
                      ·
                        rfl

theorem cell23_5467681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_5467681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5467681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5467681 prefixEnd_5467681 := by exact prefixLift 5467681
  have htrace : WordTrace (prefixWord ++ tailWord_5467681) baseStart_5467681 baseEnd_5467681 := by
    simpa [prefixWord, tailWord_5467681, baseEnd_5467681] using wordTrace_append hprefix tailTrace_5467681
  have hstable : (prefixWord ++ tailWord_5467681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5467681).length < 2 ^ (prefixWord ++ tailWord_5467681).sum := by decide
  have hdescent : baseEnd_5467681 < baseStart_5467681 := by decide
  rcases family_descends (prefixWord ++ tailWord_5467681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5467704 : List Nat := [2, 1, 2, 1, 4, 2, 1, 1, 3, 4, 2]
def baseStart_5467704 : Nat := 118140960795 + 5467704 * 2 ^ 59
def prefixEnd_5467704 : Nat := 4983230072969 + 3 ^ 40 * 5467704 * 2
def baseEnd_5467704 : Nat := 2807560228510980816654493

theorem tailTrace_5467704 : CollatzResearch.WordTrace tailWord_5467704 prefixEnd_5467704 2807560228510980816654493 := by
  unfold tailWord_5467704
  simp only [CollatzResearch.WordTrace]
  refine ⟨99711774091724846171969083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132949032122299794895958777 99711774091724846171969083)
  ·
    refine ⟨149567661137587269257953625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99711774091724846171969083 149567661137587269257953625)
    ·
      refine ⟨112175745853190451943465219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149567661137587269257953625 112175745853190451943465219)
      ·
        refine ⟨168263618779785677915197829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112175745853190451943465219 168263618779785677915197829)
        ·
          refine ⟨31549428521209814609099593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 168263618779785677915197829 31549428521209814609099593)
          ·
            refine ⟨23662071390907360956824695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31549428521209814609099593 23662071390907360956824695)
            ·
              refine ⟨35493107086361041435237043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23662071390907360956824695 35493107086361041435237043)
              ·
                refine ⟨53239660629541562152855565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35493107086361041435237043 53239660629541562152855565)
                ·
                  refine ⟨19964872736078085807320837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53239660629541562152855565 19964872736078085807320837)
                  ·
                    refine ⟨3743413638014641088872657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19964872736078085807320837 3743413638014641088872657)
                    ·
                      refine ⟨2807560228510980816654493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3743413638014641088872657 2807560228510980816654493)
                      ·
                        rfl

theorem cell23_5467704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 3, 4, 2].length) (baseStart_5467704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5467704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5467704 prefixEnd_5467704 := by exact prefixLift 5467704
  have htrace : WordTrace (prefixWord ++ tailWord_5467704) baseStart_5467704 baseEnd_5467704 := by
    simpa [prefixWord, tailWord_5467704, baseEnd_5467704] using wordTrace_append hprefix tailTrace_5467704
  have hstable : (prefixWord ++ tailWord_5467704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5467704).length < 2 ^ (prefixWord ++ tailWord_5467704).sum := by decide
  have hdescent : baseEnd_5467704 < baseStart_5467704 := by decide
  rcases family_descends (prefixWord ++ tailWord_5467704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5467717 : List Nat := [1, 3, 1, 1, 1, 4, 2, 2, 2, 2, 4]
def baseStart_5467717 : Nat := 118140960795 + 5467717 * 2 ^ 59
def prefixEnd_5467717 : Nat := 4983230072969 + 3 ^ 40 * 5467717 * 2
def baseEnd_5467717 : Nat := 2807566903759489265791933

theorem tailTrace_5467717 : CollatzResearch.WordTrace tailWord_5467717 prefixEnd_5467717 2807566903759489265791933 := by
  unfold tailWord_5467717
  simp only [CollatzResearch.WordTrace]
  refine ⟨199424022332402595564161405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132949348221601730376107603 199424022332402595564161405)
  ·
    refine ⟨74784008374650973336560527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199424022332402595564161405 74784008374650973336560527)
    ·
      refine ⟨112176012561976460004840791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74784008374650973336560527 112176012561976460004840791)
      ·
        refine ⟨168264018842964690007261187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112176012561976460004840791 168264018842964690007261187)
        ·
          refine ⟨252396028264447035010891781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168264018842964690007261187 252396028264447035010891781)
          ·
            refine ⟨47324255299583819064542209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 252396028264447035010891781 47324255299583819064542209)
            ·
              refine ⟨35493191474687864298406657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47324255299583819064542209 35493191474687864298406657)
              ·
                refine ⟨26619893606015898223804993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35493191474687864298406657 26619893606015898223804993)
                ·
                  refine ⟨19964920204511923667853745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26619893606015898223804993 19964920204511923667853745)
                  ·
                    refine ⟨14973690153383942750890309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19964920204511923667853745 14973690153383942750890309)
                    ·
                      refine ⟨2807566903759489265791933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14973690153383942750890309 2807566903759489265791933)
                      ·
                        rfl

theorem cell23_5467717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 2, 4].length) (baseStart_5467717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5467717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5467717 prefixEnd_5467717 := by exact prefixLift 5467717
  have htrace : WordTrace (prefixWord ++ tailWord_5467717) baseStart_5467717 baseEnd_5467717 := by
    simpa [prefixWord, tailWord_5467717, baseEnd_5467717] using wordTrace_append hprefix tailTrace_5467717
  have hstable : (prefixWord ++ tailWord_5467717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5467717).length < 2 ^ (prefixWord ++ tailWord_5467717).sum := by decide
  have hdescent : baseEnd_5467717 < baseStart_5467717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5467717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5467831 : List Nat := [1, 1, 3, 1, 5, 2, 1, 2, 2, 2, 3]
def baseStart_5467831 : Nat := 118140960795 + 5467831 * 2 ^ 59
def prefixEnd_5467831 : Nat := 4983230072969 + 3 ^ 40 * 5467831 * 2
def baseEnd_5467831 : Nat := 2807625440554101819766409

theorem tailTrace_5467831 : CollatzResearch.WordTrace tailWord_5467831 prefixEnd_5467831 2807625440554101819766409 := by
  unfold tailWord_5467831
  simp only [CollatzResearch.WordTrace]
  refine ⟨199428180253989593033811347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132952120169326395355874231 199428180253989593033811347)
  ·
    refine ⟨299142270380984389550717021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199428180253989593033811347 299142270380984389550717021)
    ·
      refine ⟨112178351392869146081518883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 299142270380984389550717021 112178351392869146081518883)
      ·
        refine ⟨168267527089303719122278325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112178351392869146081518883 168267527089303719122278325)
        ·
          refine ⟨15775080664622223667713593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 168267527089303719122278325 15775080664622223667713593)
          ·
            refine ⟨11831310498466667750785195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15775080664622223667713593 11831310498466667750785195)
            ·
              refine ⟨17746965747700001626177793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11831310498466667750785195 17746965747700001626177793)
              ·
                refine ⟨13310224310775001219633345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17746965747700001626177793 13310224310775001219633345)
                ·
                  refine ⟨9982668233081250914725009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13310224310775001219633345 9982668233081250914725009)
                  ·
                    refine ⟨7487001174810938186043757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9982668233081250914725009 7487001174810938186043757)
                    ·
                      refine ⟨2807625440554101819766409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7487001174810938186043757 2807625440554101819766409)
                      ·
                        rfl

theorem cell23_5467831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 2, 2, 3].length) (baseStart_5467831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5467831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5467831 prefixEnd_5467831 := by exact prefixLift 5467831
  have htrace : WordTrace (prefixWord ++ tailWord_5467831) baseStart_5467831 baseEnd_5467831 := by
    simpa [prefixWord, tailWord_5467831, baseEnd_5467831] using wordTrace_append hprefix tailTrace_5467831
  have hstable : (prefixWord ++ tailWord_5467831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5467831).length < 2 ^ (prefixWord ++ tailWord_5467831).sum := by decide
  have hdescent : baseEnd_5467831 < baseStart_5467831 := by decide
  rcases family_descends (prefixWord ++ tailWord_5467831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5467838 : List Nat := [4, 2, 1, 1, 2, 4, 1, 1, 3, 4]
def baseStart_5467838 : Nat := 118140960795 + 5467838 * 2 ^ 59
def prefixEnd_5467838 : Nat := 4983230072969 + 3 ^ 40 * 5467838 * 2
def baseEnd_5467838 : Nat := 935876344972894430792959

theorem tailTrace_5467838 : CollatzResearch.WordTrace tailWord_5467838 prefixEnd_5467838 935876344972894430792959 := by
  unfold tailWord_5467838
  simp only [CollatzResearch.WordTrace]
  refine ⟨24928554445620529153664521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132952290376642822152877445 24928554445620529153664521)
  ·
    refine ⟨18696415834215396865248391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24928554445620529153664521 18696415834215396865248391)
    ·
      refine ⟨28044623751323095297872587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18696415834215396865248391 28044623751323095297872587)
      ·
        refine ⟨42066935626984642946808881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28044623751323095297872587 42066935626984642946808881)
        ·
          refine ⟨31550201720238482210106661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42066935626984642946808881 31550201720238482210106661)
          ·
            refine ⟨5915662822544715414394999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31550201720238482210106661 5915662822544715414394999)
            ·
              refine ⟨8873494233817073121592499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5915662822544715414394999 8873494233817073121592499)
              ·
                refine ⟨13310241350725609682388749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8873494233817073121592499 13310241350725609682388749)
                ·
                  refine ⟨4991340506522103630895781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13310241350725609682388749 4991340506522103630895781)
                  ·
                    refine ⟨935876344972894430792959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4991340506522103630895781 935876344972894430792959)
                    ·
                      rfl

theorem cell23_5467838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_5467838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5467838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5467838 prefixEnd_5467838 := by exact prefixLift 5467838
  have htrace : WordTrace (prefixWord ++ tailWord_5467838) baseStart_5467838 baseEnd_5467838 := by
    simpa [prefixWord, tailWord_5467838, baseEnd_5467838] using wordTrace_append hprefix tailTrace_5467838
  have hstable : (prefixWord ++ tailWord_5467838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5467838).length < 2 ^ (prefixWord ++ tailWord_5467838).sum := by decide
  have hdescent : baseEnd_5467838 < baseStart_5467838 := by decide
  rcases family_descends (prefixWord ++ tailWord_5467838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5467864 : List Nat := [2, 1, 2, 2, 3, 1, 3, 1, 3, 5]
def baseStart_5467864 : Nat := 118140960795 + 5467864 * 2 ^ 59
def prefixEnd_5467864 : Nat := 4983230072969 + 3 ^ 40 * 5467864 * 2
def baseEnd_5467864 : Nat := 935880795138566730217919

theorem tailTrace_5467864 : CollatzResearch.WordTrace tailWord_5467864 prefixEnd_5467864 935880795138566730217919 := by
  unfold tailWord_5467864
  simp only [CollatzResearch.WordTrace]
  refine ⟨99714691931435019834881323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132952922575246693113175097 99714691931435019834881323)
  ·
    refine ⟨149572037897152529752321985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99714691931435019834881323 149572037897152529752321985)
    ·
      refine ⟨112179028422864397314241489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149572037897152529752321985 112179028422864397314241489)
      ·
        refine ⟨84134271317148297985681117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112179028422864397314241489 84134271317148297985681117)
        ·
          refine ⟨31550351743930611744630419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84134271317148297985681117 31550351743930611744630419)
          ·
            refine ⟨47325527615895917616945629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31550351743930611744630419 47325527615895917616945629)
            ·
              refine ⟨17747072855960969106354611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47325527615895917616945629 17747072855960969106354611)
              ·
                refine ⟨26620609283941453659531917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17747072855960969106354611 26620609283941453659531917)
                ·
                  refine ⟨9982728481478045122324469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26620609283941453659531917 9982728481478045122324469)
                  ·
                    refine ⟨935880795138566730217919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9982728481478045122324469 935880795138566730217919)
                    ·
                      rfl

theorem cell23_5467864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 3, 5].length) (baseStart_5467864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5467864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5467864 prefixEnd_5467864 := by exact prefixLift 5467864
  have htrace : WordTrace (prefixWord ++ tailWord_5467864) baseStart_5467864 baseEnd_5467864 := by
    simpa [prefixWord, tailWord_5467864, baseEnd_5467864] using wordTrace_append hprefix tailTrace_5467864
  have hstable : (prefixWord ++ tailWord_5467864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5467864).length < 2 ^ (prefixWord ++ tailWord_5467864).sum := by decide
  have hdescent : baseEnd_5467864 < baseStart_5467864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5467864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5467895 : List Nat := [1, 1, 3, 1, 1, 1, 8, 2, 1, 1, 3]
def baseStart_5467895 : Nat := 118140960795 + 5467895 * 2 ^ 59
def prefixEnd_5467895 : Nat := 4983230072969 + 3 ^ 40 * 5467895 * 2
def baseEnd_5467895 : Nat := 2807658303315989569366115

theorem tailTrace_5467895 : CollatzResearch.WordTrace tailWord_5467895 prefixEnd_5467895 2807658303315989569366115 := by
  unfold tailWord_5467895
  simp only [CollatzResearch.WordTrace]
  refine ⟨199430514525757731964141139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132953676350505154642760759 199430514525757731964141139)
  ·
    refine ⟨299145771788636597946211709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199430514525757731964141139 299145771788636597946211709)
    ·
      refine ⟨112179664420738724229829391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 299145771788636597946211709 112179664420738724229829391)
      ·
        refine ⟨168269496631108086344744087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112179664420738724229829391 168269496631108086344744087)
        ·
          refine ⟨252404244946662129517116131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168269496631108086344744087 252404244946662129517116131)
          ·
            refine ⟨378606367419993194275674197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252404244946662129517116131 378606367419993194275674197)
            ·
              refine ⟨4436793368203045245418057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 378606367419993194275674197 4436793368203045245418057)
              ·
                refine ⟨3327595026152283934063543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4436793368203045245418057 3327595026152283934063543)
                ·
                  refine ⟨4991392539228425901095315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3327595026152283934063543 4991392539228425901095315)
                  ·
                    refine ⟨7487088808842638851642973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4991392539228425901095315 7487088808842638851642973)
                    ·
                      refine ⟨2807658303315989569366115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7487088808842638851642973 2807658303315989569366115)
                      ·
                        rfl

theorem cell23_5467895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 2, 1, 1, 3].length) (baseStart_5467895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5467895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5467895 prefixEnd_5467895 := by exact prefixLift 5467895
  have htrace : WordTrace (prefixWord ++ tailWord_5467895) baseStart_5467895 baseEnd_5467895 := by
    simpa [prefixWord, tailWord_5467895, baseEnd_5467895] using wordTrace_append hprefix tailTrace_5467895
  have hstable : (prefixWord ++ tailWord_5467895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5467895).length < 2 ^ (prefixWord ++ tailWord_5467895).sum := by decide
  have hdescent : baseEnd_5467895 < baseStart_5467895 := by decide
  rcases family_descends (prefixWord ++ tailWord_5467895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5467918 : List Nat := [4, 1, 1, 2, 1, 1, 3, 1, 5, 2, 2]
def baseStart_5467918 : Nat := 118140960795 + 5467918 * 2 ^ 59
def prefixEnd_5467918 : Nat := 4983230072969 + 3 ^ 40 * 5467918 * 2
def baseEnd_5467918 : Nat := 2807670113371042979378509

theorem tailTrace_5467918 : CollatzResearch.WordTrace tailWord_5467918 prefixEnd_5467918 2807670113371042979378509 := by
  unfold tailWord_5467918
  simp only [CollatzResearch.WordTrace]
  refine ⟨24928919175584300861528551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132954235603116271261485605 24928919175584300861528551)
  ·
    refine ⟨37393378763376451292292827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24928919175584300861528551 37393378763376451292292827)
    ·
      refine ⟨56090068145064676938439241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37393378763376451292292827 56090068145064676938439241)
      ·
        refine ⟨42067551108798507703829431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56090068145064676938439241 42067551108798507703829431)
        ·
          refine ⟨63101326663197761555744147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42067551108798507703829431 63101326663197761555744147)
          ·
            refine ⟨94651989994796642333616221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63101326663197761555744147 94651989994796642333616221)
            ·
              refine ⟨35494496248048740875106083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94651989994796642333616221 35494496248048740875106083)
              ·
                refine ⟨53241744372073111312659125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35494496248048740875106083 53241744372073111312659125)
                ·
                  refine ⟨4991413534881854185561793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53241744372073111312659125 4991413534881854185561793)
                  ·
                    refine ⟨3743560151161390639171345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4991413534881854185561793 3743560151161390639171345)
                    ·
                      refine ⟨2807670113371042979378509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3743560151161390639171345 2807670113371042979378509)
                      ·
                        rfl

theorem cell23_5467918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 5, 2, 2].length) (baseStart_5467918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5467918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5467918 prefixEnd_5467918 := by exact prefixLift 5467918
  have htrace : WordTrace (prefixWord ++ tailWord_5467918) baseStart_5467918 baseEnd_5467918 := by
    simpa [prefixWord, tailWord_5467918, baseEnd_5467918] using wordTrace_append hprefix tailTrace_5467918
  have hstable : (prefixWord ++ tailWord_5467918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5467918).length < 2 ^ (prefixWord ++ tailWord_5467918).sum := by decide
  have hdescent : baseEnd_5467918 < baseStart_5467918 := by decide
  rcases family_descends (prefixWord ++ tailWord_5467918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5467921 : List Nat := [1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 3]
def baseStart_5467921 : Nat := 118140960795 + 5467921 * 2 ^ 59
def prefixEnd_5467921 : Nat := 4983230072969 + 3 ^ 40 * 5467921 * 2
def baseEnd_5467921 : Nat := 2807671653813006467640995

theorem tailTrace_5467921 : CollatzResearch.WordTrace tailWord_5467921 prefixEnd_5467921 2807671653813006467640995 := by
  unfold tailWord_5467921
  simp only [CollatzResearch.WordTrace]
  refine ⟨199431462823663538404587617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132954308549109025603058411 199431462823663538404587617)
  ·
    refine ⟨149573597117747653803440713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199431462823663538404587617 149573597117747653803440713)
    ·
      refine ⟨112180197838310740352580535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149573597117747653803440713 112180197838310740352580535)
      ·
        refine ⟨168270296757466110528870803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112180197838310740352580535 168270296757466110528870803)
        ·
          refine ⟨252405445136199165793306205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168270296757466110528870803 252405445136199165793306205)
          ·
            refine ⟨94652041926074687172489827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 252405445136199165793306205 94652041926074687172489827)
            ·
              refine ⟨141978062889112030758734741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94652041926074687172489827 141978062889112030758734741)
              ·
                refine ⟨6655221697927126441815691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 141978062889112030758734741 6655221697927126441815691)
                ·
                  refine ⟨9982832546890689662723537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6655221697927126441815691 9982832546890689662723537)
                  ·
                    refine ⟨7487124410168017247042653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9982832546890689662723537 7487124410168017247042653)
                    ·
                      refine ⟨2807671653813006467640995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7487124410168017247042653 2807671653813006467640995)
                      ·
                        rfl

theorem cell23_5467921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 3].length) (baseStart_5467921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5467921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5467921 prefixEnd_5467921 := by exact prefixLift 5467921
  have htrace : WordTrace (prefixWord ++ tailWord_5467921) baseStart_5467921 baseEnd_5467921 := by
    simpa [prefixWord, tailWord_5467921, baseEnd_5467921] using wordTrace_append hprefix tailTrace_5467921
  have hstable : (prefixWord ++ tailWord_5467921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5467921).length < 2 ^ (prefixWord ++ tailWord_5467921).sum := by decide
  have hdescent : baseEnd_5467921 < baseStart_5467921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5467921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5467922 : List Nat := [3, 2, 4, 1, 1, 3, 1, 1, 2, 3, 2]
def baseStart_5467922 : Nat := 118140960795 + 5467922 * 2 ^ 59
def prefixEnd_5467922 : Nat := 4983230072969 + 3 ^ 40 * 5467922 * 2
def baseEnd_5467922 : Nat := 2807672167293660963728491

theorem tailTrace_5467922 : CollatzResearch.WordTrace tailWord_5467922 prefixEnd_5467922 2807672167293660963728491 := by
  unfold tailWord_5467922
  simp only [CollatzResearch.WordTrace]
  refine ⟨49857874824164978893843505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132954332864439943716916013 49857874824164978893843505)
  ·
    refine ⟨37393406118123734170382629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49857874824164978893843505 37393406118123734170382629)
    ·
      refine ⟨7011263647148200156946743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37393406118123734170382629 7011263647148200156946743)
      ·
        refine ⟨10516895470722300235420115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7011263647148200156946743 10516895470722300235420115)
        ·
          refine ⟨15775343206083450353130173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10516895470722300235420115 15775343206083450353130173)
          ·
            refine ⟨5915753702281293882423815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15775343206083450353130173 5915753702281293882423815)
            ·
              refine ⟨8873630553421940823635723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5915753702281293882423815 8873630553421940823635723)
              ·
                refine ⟨13310445830132911235453585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8873630553421940823635723 13310445830132911235453585)
                ·
                  refine ⟨9982834372599683426590189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13310445830132911235453585 9982834372599683426590189)
                  ·
                    refine ⟨3743562889724881284971321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9982834372599683426590189 3743562889724881284971321)
                    ·
                      refine ⟨2807672167293660963728491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3743562889724881284971321 2807672167293660963728491)
                      ·
                        rfl

theorem cell23_5467922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_5467922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5467922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5467922 prefixEnd_5467922 := by exact prefixLift 5467922
  have htrace : WordTrace (prefixWord ++ tailWord_5467922) baseStart_5467922 baseEnd_5467922 := by
    simpa [prefixWord, tailWord_5467922, baseEnd_5467922] using wordTrace_append hprefix tailTrace_5467922
  have hstable : (prefixWord ++ tailWord_5467922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5467922).length < 2 ^ (prefixWord ++ tailWord_5467922).sum := by decide
  have hdescent : baseEnd_5467922 < baseStart_5467922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5467922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5467938 : List Nat := [3, 3, 1, 1, 2, 1, 3, 3, 1, 2, 3]
def baseStart_5467938 : Nat := 118140960795 + 5467938 * 2 ^ 59
def prefixEnd_5467938 : Nat := 4983230072969 + 3 ^ 40 * 5467938 * 2
def baseEnd_5467938 : Nat := 2807680382984132901128417

theorem tailTrace_5467938 : CollatzResearch.WordTrace tailWord_5467938 prefixEnd_5467938 2807680382984132901128417 := by
  unfold tailWord_5467938
  simp only [CollatzResearch.WordTrace]
  refine ⟨49858020716150487576989117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132954721909734633538637645 49858020716150487576989117)
  ·
    refine ⟨18696757768556432841370919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49858020716150487576989117 18696757768556432841370919)
    ·
      refine ⟨28045136652834649262056379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18696757768556432841370919 28045136652834649262056379)
      ·
        refine ⟨42067704979251973893084569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28045136652834649262056379 42067704979251973893084569)
        ·
          refine ⟨31550778734438980419813427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42067704979251973893084569 31550778734438980419813427)
          ·
            refine ⟨47326168101658470629720141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31550778734438980419813427 47326168101658470629720141)
            ·
              refine ⟨17747313038121926486145053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47326168101658470629720141 17747313038121926486145053)
              ·
                refine ⟨6655242389295722432304395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17747313038121926486145053 6655242389295722432304395)
                ·
                  refine ⟨9982863583943583648456593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6655242389295722432304395 9982863583943583648456593)
                  ·
                    refine ⟨7487147687957687736342445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9982863583943583648456593 7487147687957687736342445)
                    ·
                      refine ⟨2807680382984132901128417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7487147687957687736342445 2807680382984132901128417)
                      ·
                        rfl

theorem cell23_5467938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_5467938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5467938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5467938 prefixEnd_5467938 := by exact prefixLift 5467938
  have htrace : WordTrace (prefixWord ++ tailWord_5467938) baseStart_5467938 baseEnd_5467938 := by
    simpa [prefixWord, tailWord_5467938, baseEnd_5467938] using wordTrace_append hprefix tailTrace_5467938
  have hstable : (prefixWord ++ tailWord_5467938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5467938).length < 2 ^ (prefixWord ++ tailWord_5467938).sum := by decide
  have hdescent : baseEnd_5467938 < baseStart_5467938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5467938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5467951 : List Nat := [1, 1, 2, 1, 2, 1, 2, 5, 4, 1, 3]
def baseStart_5467951 : Nat := 118140960795 + 5467951 * 2 ^ 59
def prefixEnd_5467951 : Nat := 4983230072969 + 3 ^ 40 * 5467951 * 2
def baseEnd_5467951 : Nat := 2807687058232641350265857

theorem tailTrace_5467951 : CollatzResearch.WordTrace tailWord_5467951 prefixEnd_5467951 2807687058232641350265857 := by
  unfold tailWord_5467951
  simp only [CollatzResearch.WordTrace]
  refine ⟨199432557013554853528179707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132955038009036569018786471 199432557013554853528179707)
  ·
    refine ⟨299148835520332280292269561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199432557013554853528179707 299148835520332280292269561)
    ·
      refine ⟨224361626640249210219202171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299148835520332280292269561 224361626640249210219202171)
      ·
        refine ⟨336542439960373815328803257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224361626640249210219202171 336542439960373815328803257)
        ·
          refine ⟨252406829970280361496602443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 336542439960373815328803257 252406829970280361496602443)
          ·
            refine ⟨378610244955420542244903665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252406829970280361496602443 378610244955420542244903665)
            ·
              refine ⟨283957683716565406683677749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 378610244955420542244903665 283957683716565406683677749)
              ·
                refine ⟨26621032848428006876594789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 283957683716565406683677749 26621032848428006876594789)
                ·
                  refine ⟨4991443659080251289361523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26621032848428006876594789 4991443659080251289361523)
                  ·
                    refine ⟨7487165488620376934042285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4991443659080251289361523 7487165488620376934042285)
                    ·
                      refine ⟨2807687058232641350265857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7487165488620376934042285 2807687058232641350265857)
                      ·
                        rfl

theorem cell23_5467951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 4, 1, 3].length) (baseStart_5467951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5467951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5467951 prefixEnd_5467951 := by exact prefixLift 5467951
  have htrace : WordTrace (prefixWord ++ tailWord_5467951) baseStart_5467951 baseEnd_5467951 := by
    simpa [prefixWord, tailWord_5467951, baseEnd_5467951] using wordTrace_append hprefix tailTrace_5467951
  have hstable : (prefixWord ++ tailWord_5467951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5467951).length < 2 ^ (prefixWord ++ tailWord_5467951).sum := by decide
  have hdescent : baseEnd_5467951 < baseStart_5467951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5467951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5468021 : List Nat := [1, 3, 4, 1, 1, 1, 2, 1, 1, 4, 4]
def baseStart_5468021 : Nat := 118140960795 + 5468021 * 2 ^ 59
def prefixEnd_5468021 : Nat := 4983230072969 + 3 ^ 40 * 5468021 * 2
def baseEnd_5468021 : Nat := 2807723001878456076390535

theorem tailTrace_5468021 : CollatzResearch.WordTrace tailWord_5468021 prefixEnd_5468021 2807723001878456076390535 := by
  unfold tailWord_5468021
  simp only [CollatzResearch.WordTrace]
  refine ⟨199435110123301255483227917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132956740082200836988818611 199435110123301255483227917)
  ·
    refine ⟨74788166296237970806210469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199435110123301255483227917 74788166296237970806210469)
    ·
      refine ⟨14022781180544619526164463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74788166296237970806210469 14022781180544619526164463)
      ·
        refine ⟨21034171770816929289246695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14022781180544619526164463 21034171770816929289246695)
        ·
          refine ⟨31551257656225393933870043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21034171770816929289246695 31551257656225393933870043)
          ·
            refine ⟨47326886484338090900805065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31551257656225393933870043 47326886484338090900805065)
            ·
              refine ⟨35495164863253568175603799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47326886484338090900805065 35495164863253568175603799)
              ·
                refine ⟨53242747294880352263405699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35495164863253568175603799 53242747294880352263405699)
                ·
                  refine ⟨79864120942320528395108549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53242747294880352263405699 79864120942320528395108549)
                  ·
                    refine ⟨14974522676685099074082853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 79864120942320528395108549 14974522676685099074082853)
                    ·
                      refine ⟨2807723001878456076390535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14974522676685099074082853 2807723001878456076390535)
                      ·
                        rfl

theorem cell23_5468021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_5468021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5468021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5468021 prefixEnd_5468021 := by exact prefixLift 5468021
  have htrace : WordTrace (prefixWord ++ tailWord_5468021) baseStart_5468021 baseEnd_5468021 := by
    simpa [prefixWord, tailWord_5468021, baseEnd_5468021] using wordTrace_append hprefix tailTrace_5468021
  have hstable : (prefixWord ++ tailWord_5468021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5468021).length < 2 ^ (prefixWord ++ tailWord_5468021).sum := by decide
  have hdescent : baseEnd_5468021 < baseStart_5468021 := by decide
  rcases family_descends (prefixWord ++ tailWord_5468021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5468025 : List Nat := [1, 2, 1, 3, 2, 2, 3, 3, 2, 2, 2]
def baseStart_5468025 : Nat := 118140960795 + 5468025 * 2 ^ 59
def prefixEnd_5468025 : Nat := 4983230072969 + 3 ^ 40 * 5468025 * 2
def baseEnd_5468025 : Nat := 2807725055801074060740517

theorem tailTrace_5468025 : CollatzResearch.WordTrace tailWord_5468025 prefixEnd_5468025 2807725055801074060740517 := by
  unfold tailWord_5468025
  simp only [CollatzResearch.WordTrace]
  refine ⟨199435256015286764166373529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132956837343524509444249019 199435256015286764166373529)
  ·
    refine ⟨149576442011465073124780147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199435256015286764166373529 149576442011465073124780147)
    ·
      refine ⟨224364663017197609687170221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149576442011465073124780147 224364663017197609687170221)
      ·
        refine ⟨84136748631449103632688833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 224364663017197609687170221 84136748631449103632688833)
        ·
          refine ⟨63102561473586827724516625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84136748631449103632688833 63102561473586827724516625)
          ·
            refine ⟨47326921105190120793387469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63102561473586827724516625 47326921105190120793387469)
            ·
              refine ⟨17747595414446295297520301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47326921105190120793387469 17747595414446295297520301)
              ·
                refine ⟨6655348280417360736570113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17747595414446295297520301 6655348280417360736570113)
                ·
                  refine ⟨4991511210313020552427585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6655348280417360736570113 4991511210313020552427585)
                  ·
                    refine ⟨3743633407734765414320689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4991511210313020552427585 3743633407734765414320689)
                    ·
                      refine ⟨2807725055801074060740517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3743633407734765414320689 2807725055801074060740517)
                      ·
                        rfl

theorem cell23_5468025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 3, 2, 2, 2].length) (baseStart_5468025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5468025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5468025 prefixEnd_5468025 := by exact prefixLift 5468025
  have htrace : WordTrace (prefixWord ++ tailWord_5468025) baseStart_5468025 baseEnd_5468025 := by
    simpa [prefixWord, tailWord_5468025, baseEnd_5468025] using wordTrace_append hprefix tailTrace_5468025
  have hstable : (prefixWord ++ tailWord_5468025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5468025).length < 2 ^ (prefixWord ++ tailWord_5468025).sum := by decide
  have hdescent : baseEnd_5468025 < baseStart_5468025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5468025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5468065 : List Nat := [1, 2, 3, 4, 2, 1, 1, 4, 5]
def baseStart_5468065 : Nat := 118140960795 + 5468065 * 2 ^ 59
def prefixEnd_5468065 : Nat := 4983230072969 + 3 ^ 40 * 5468065 * 2
def baseEnd_5468065 : Nat := 311971732780805989360037

theorem tailTrace_5468065 : CollatzResearch.WordTrace tailWord_5468065 prefixEnd_5468065 311971732780805989360037 := by
  unfold tailWord_5468065
  simp only [CollatzResearch.WordTrace]
  refine ⟨199436714935141850997829649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132957809956761233998553099 199436714935141850997829649)
  ·
    refine ⟨149577536201356388248372237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199436714935141850997829649 149577536201356388248372237)
    ·
      refine ⟨56091576075508645593139589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149577536201356388248372237 56091576075508645593139589)
      ·
        refine ⟨10517170514157871048713673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56091576075508645593139589 10517170514157871048713673)
        ·
          refine ⟨7887877885618403286535255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10517170514157871048713673 7887877885618403286535255)
          ·
            refine ⟨11831816828427604929802883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7887877885618403286535255 11831816828427604929802883)
            ·
              refine ⟨17747725242641407394704325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11831816828427604929802883 17747725242641407394704325)
              ·
                refine ⟨3327698482995263886507061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17747725242641407394704325 3327698482995263886507061)
                ·
                  refine ⟨311971732780805989360037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3327698482995263886507061 311971732780805989360037)
                  ·
                    rfl

theorem cell23_5468065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 4, 5].length) (baseStart_5468065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5468065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5468065 prefixEnd_5468065 := by exact prefixLift 5468065
  have htrace : WordTrace (prefixWord ++ tailWord_5468065) baseStart_5468065 baseEnd_5468065 := by
    simpa [prefixWord, tailWord_5468065, baseEnd_5468065] using wordTrace_append hprefix tailTrace_5468065
  have hstable : (prefixWord ++ tailWord_5468065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5468065).length < 2 ^ (prefixWord ++ tailWord_5468065).sum := by decide
  have hdescent : baseEnd_5468065 < baseStart_5468065 := by decide
  rcases family_descends (prefixWord ++ tailWord_5468065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5468068 : List Nat := [2, 3, 1, 2, 1, 3, 1, 1, 2, 5, 2]
def baseStart_5468068 : Nat := 118140960795 + 5468068 * 2 ^ 59
def prefixEnd_5468068 : Nat := 4983230072969 + 3 ^ 40 * 5468068 * 2
def baseEnd_5468068 : Nat := 2807747135469217392502819

theorem tailTrace_5468068 : CollatzResearch.WordTrace tailWord_5468068 prefixEnd_5468068 2807747135469217392502819 := by
  unfold tailWord_5468068
  simp only [CollatzResearch.WordTrace]
  refine ⟨99718412177065491255094429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132957882902753988340125905 99718412177065491255094429)
  ·
    refine ⟨37394404566399559220660411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99718412177065491255094429 37394404566399559220660411)
    ·
      refine ⟨56091606849599338830990617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37394404566399559220660411 56091606849599338830990617)
      ·
        refine ⟨42068705137199504123242963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56091606849599338830990617 42068705137199504123242963)
        ·
          refine ⟨63103057705799256184864445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42068705137199504123242963 63103057705799256184864445)
          ·
            refine ⟨23663646639674721069324167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63103057705799256184864445 23663646639674721069324167)
            ·
              refine ⟨35495469959512081603986251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23663646639674721069324167 35495469959512081603986251)
              ·
                refine ⟨53243204939268122405979377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35495469959512081603986251 53243204939268122405979377)
                ·
                  refine ⟨39932403704451091804484533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53243204939268122405979377 39932403704451091804484533)
                  ·
                    refine ⟨3743662847292289856670425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39932403704451091804484533 3743662847292289856670425)
                    ·
                      refine ⟨2807747135469217392502819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3743662847292289856670425 2807747135469217392502819)
                      ·
                        rfl

theorem cell23_5468068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 2, 5, 2].length) (baseStart_5468068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5468068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5468068 prefixEnd_5468068 := by exact prefixLift 5468068
  have htrace : WordTrace (prefixWord ++ tailWord_5468068) baseStart_5468068 baseEnd_5468068 := by
    simpa [prefixWord, tailWord_5468068, baseEnd_5468068] using wordTrace_append hprefix tailTrace_5468068
  have hstable : (prefixWord ++ tailWord_5468068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5468068).length < 2 ^ (prefixWord ++ tailWord_5468068).sum := by decide
  have hdescent : baseEnd_5468068 < baseStart_5468068 := by decide
  rcases family_descends (prefixWord ++ tailWord_5468068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5468091 : List Nat := [1, 1, 1, 1, 1, 2, 2, 5, 5, 4]
def baseStart_5468091 : Nat := 118140960795 + 5468091 * 2 ^ 59
def prefixEnd_5468091 : Nat := 4983230072969 + 3 ^ 40 * 5468091 * 2
def baseEnd_5468091 : Nat := 935919648508090267505071

theorem tailTrace_5468091 : CollatzResearch.WordTrace tailWord_5468091 prefixEnd_5468091 935919648508090267505071 := by
  unfold tailWord_5468091
  simp only [CollatzResearch.WordTrace]
  refine ⟨199437663233047657438276127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132958442155365104958850751 199437663233047657438276127)
  ·
    refine ⟨299156494849571486157414191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199437663233047657438276127 299156494849571486157414191)
    ·
      refine ⟨448734742274357229236121287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299156494849571486157414191 448734742274357229236121287)
      ·
        refine ⟨673102113411535843854181931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 448734742274357229236121287 673102113411535843854181931)
        ·
          refine ⟨1009653170117303765781272897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 673102113411535843854181931 1009653170117303765781272897)
          ·
            refine ⟨757239877587977824335954673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1009653170117303765781272897 757239877587977824335954673)
            ·
              refine ⟨567929908190983368251966005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 757239877587977824335954673 567929908190983368251966005)
              ·
                refine ⟨53243428892904690773621813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 567929908190983368251966005 53243428892904690773621813)
                ·
                  refine ⟨4991571458709814760027045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53243428892904690773621813 4991571458709814760027045)
                  ·
                    refine ⟨935919648508090267505071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4991571458709814760027045 935919648508090267505071)
                    ·
                      rfl

theorem cell23_5468091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5, 4].length) (baseStart_5468091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5468091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5468091 prefixEnd_5468091 := by exact prefixLift 5468091
  have htrace : WordTrace (prefixWord ++ tailWord_5468091) baseStart_5468091 baseEnd_5468091 := by
    simpa [prefixWord, tailWord_5468091, baseEnd_5468091] using wordTrace_append hprefix tailTrace_5468091
  have hstable : (prefixWord ++ tailWord_5468091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5468091).length < 2 ^ (prefixWord ++ tailWord_5468091).sum := by decide
  have hdescent : baseEnd_5468091 < baseStart_5468091 := by decide
  rcases family_descends (prefixWord ++ tailWord_5468091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5468166 : List Nat := [6, 2, 1, 2, 1, 1, 1, 2, 2, 1, 4]
def baseStart_5468166 : Nat := 118140960795 + 5468166 * 2 ^ 59
def prefixEnd_5468166 : Nat := 4983230072969 + 3 ^ 40 * 5468166 * 2
def baseEnd_5468166 : Nat := 2807797456573358009077369

theorem tailTrace_5468166 : CollatzResearch.WordTrace tailWord_5468166 prefixEnd_5468166 2807797456573358009077369 := by
  unfold tailWord_5468166
  simp only [CollatzResearch.WordTrace]
  refine ⟨6232512459617998288976761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 132960265805183963498170901 6232512459617998288976761)
  ·
    refine ⟨4674384344713498716732571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6232512459617998288976761 4674384344713498716732571)
    ·
      refine ⟨7011576517070248075098857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4674384344713498716732571 7011576517070248075098857)
      ·
        refine ⟨5258682387802686056324143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7011576517070248075098857 5258682387802686056324143)
        ·
          refine ⟨7888023581704029084486215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5258682387802686056324143 7888023581704029084486215)
          ·
            refine ⟨11832035372556043626729323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7888023581704029084486215 11832035372556043626729323)
            ·
              refine ⟨17748053058834065440093985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11832035372556043626729323 17748053058834065440093985)
              ·
                refine ⟨13311039794125549080070489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17748053058834065440093985 13311039794125549080070489)
                ·
                  refine ⟨9983279845594161810052867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13311039794125549080070489 9983279845594161810052867)
                  ·
                    refine ⟨14974919768391242715079301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9983279845594161810052867 14974919768391242715079301)
                    ·
                      refine ⟨2807797456573358009077369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14974919768391242715079301 2807797456573358009077369)
                      ·
                        rfl

theorem cell23_5468166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_5468166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5468166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5468166 prefixEnd_5468166 := by exact prefixLift 5468166
  have htrace : WordTrace (prefixWord ++ tailWord_5468166) baseStart_5468166 baseEnd_5468166 := by
    simpa [prefixWord, tailWord_5468166, baseEnd_5468166] using wordTrace_append hprefix tailTrace_5468166
  have hstable : (prefixWord ++ tailWord_5468166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5468166).length < 2 ^ (prefixWord ++ tailWord_5468166).sum := by decide
  have hdescent : baseEnd_5468166 < baseStart_5468166 := by decide
  rcases family_descends (prefixWord ++ tailWord_5468166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5468168 : List Nat := [2, 1, 3, 2, 1, 2, 1, 5, 1, 5]
def baseStart_5468168 : Nat := 118140960795 + 5468168 * 2 ^ 59
def prefixEnd_5468168 : Nat := 4983230072969 + 3 ^ 40 * 5468168 * 2
def baseEnd_5468168 : Nat := 935932827844889000417453

theorem tailTrace_5468168 : CollatzResearch.WordTrace tailWord_5468168 prefixEnd_5468168 935932827844889000417453 := by
  unfold tailWord_5468168
  simp only [CollatzResearch.WordTrace]
  refine ⟨99720235826884349794414579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132960314435845799725886105 99720235826884349794414579)
  ·
    refine ⟨149580353740326524691621869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99720235826884349794414579 149580353740326524691621869)
    ·
      refine ⟨56092632652622446759358201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149580353740326524691621869 56092632652622446759358201)
      ·
        refine ⟨42069474489466835069518651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56092632652622446759358201 42069474489466835069518651)
        ·
          refine ⟨63104211734200252604277977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42069474489466835069518651 63104211734200252604277977)
          ·
            refine ⟨47328158800650189453208483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63104211734200252604277977 47328158800650189453208483)
            ·
              refine ⟨70992238200975284179812725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47328158800650189453208483 70992238200975284179812725)
              ·
                refine ⟨6655522331341432891857443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70992238200975284179812725 6655522331341432891857443)
                ·
                  refine ⟨9983283497012149337786165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6655522331341432891857443 9983283497012149337786165)
                  ·
                    refine ⟨935932827844889000417453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9983283497012149337786165 935932827844889000417453)
                    ·
                      rfl

theorem cell23_5468168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 5, 1, 5].length) (baseStart_5468168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5468168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5468168 prefixEnd_5468168 := by exact prefixLift 5468168
  have htrace : WordTrace (prefixWord ++ tailWord_5468168) baseStart_5468168 baseEnd_5468168 := by
    simpa [prefixWord, tailWord_5468168, baseEnd_5468168] using wordTrace_append hprefix tailTrace_5468168
  have hstable : (prefixWord ++ tailWord_5468168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5468168).length < 2 ^ (prefixWord ++ tailWord_5468168).sum := by decide
  have hdescent : baseEnd_5468168 < baseStart_5468168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5468168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5468202 : List Nat := [3, 1, 4, 1, 2, 3, 1, 2, 1, 5]
def baseStart_5468202 : Nat := 118140960795 + 5468202 * 2 ^ 59
def prefixEnd_5468202 : Nat := 4983230072969 + 3 ^ 40 * 5468202 * 2
def baseEnd_5468202 : Nat := 935938647292306622742401

theorem tailTrace_5468202 : CollatzResearch.WordTrace tailWord_5468202 prefixEnd_5468202 935938647292306622742401 := by
  unfold tailWord_5468202
  simp only [CollatzResearch.WordTrace]
  refine ⟨49860427933911380848891715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132961141157097015597044573 49860427933911380848891715)
  ·
    refine ⟨74790641900867071273337573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49860427933911380848891715 74790641900867071273337573)
    ·
      refine ⟨14023245356412575863750795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74790641900867071273337573 14023245356412575863750795)
      ·
        refine ⟨21034868034618863795626193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14023245356412575863750795 21034868034618863795626193)
        ·
          refine ⟨15776151025964147846719645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21034868034618863795626193 15776151025964147846719645)
          ·
            refine ⟨5916056634736555442519867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15776151025964147846719645 5916056634736555442519867)
            ·
              refine ⟨8874084952104833163779801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5916056634736555442519867 8874084952104833163779801)
              ·
                refine ⟨6655563714078624872834851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8874084952104833163779801 6655563714078624872834851)
                ·
                  refine ⟨9983345571117937309252277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6655563714078624872834851 9983345571117937309252277)
                  ·
                    refine ⟨935938647292306622742401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9983345571117937309252277 935938647292306622742401)
                    ·
                      rfl

theorem cell23_5468202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_5468202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5468202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5468202 prefixEnd_5468202 := by exact prefixLift 5468202
  have htrace : WordTrace (prefixWord ++ tailWord_5468202) baseStart_5468202 baseEnd_5468202 := by
    simpa [prefixWord, tailWord_5468202, baseEnd_5468202] using wordTrace_append hprefix tailTrace_5468202
  have hstable : (prefixWord ++ tailWord_5468202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5468202).length < 2 ^ (prefixWord ++ tailWord_5468202).sum := by decide
  have hdescent : baseEnd_5468202 < baseStart_5468202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5468202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5468211 : List Nat := [1, 1, 1, 2, 4, 1, 4, 9]
def baseStart_5468211 : Nat := 118140960795 + 5468211 * 2 ^ 59
def prefixEnd_5468211 : Nat := 4983230072969 + 3 ^ 40 * 5468211 * 2
def baseEnd_5468211 : Nat := 103993354192696679000543

theorem tailTrace_5468211 : CollatzResearch.WordTrace tailWord_5468211 prefixEnd_5468211 103993354192696679000543 := by
  unfold tailWord_5468211
  simp only [CollatzResearch.WordTrace]
  refine ⟨199442039992612917932644487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132961359995075278621762991 199442039992612917932644487)
  ·
    refine ⟨299163059988919376898966731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199442039992612917932644487 299163059988919376898966731)
    ·
      refine ⟨448744589983379065348450097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299163059988919376898966731 448744589983379065348450097)
      ·
        refine ⟨336558442487534299011337573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 448744589983379065348450097 336558442487534299011337573)
        ·
          refine ⟨63104707966412681064625795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 336558442487534299011337573 63104707966412681064625795)
          ·
            refine ⟨94657061949619021596938693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63104707966412681064625795 94657061949619021596938693)
            ·
              refine ⟨17748199115553566549426005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94657061949619021596938693 17748199115553566549426005)
              ·
                refine ⟨103993354192696679000543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17748199115553566549426005 103993354192696679000543)
                ·
                  rfl

theorem cell23_5468211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 9].length) (baseStart_5468211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5468211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5468211 prefixEnd_5468211 := by exact prefixLift 5468211
  have htrace : WordTrace (prefixWord ++ tailWord_5468211) baseStart_5468211 baseEnd_5468211 := by
    simpa [prefixWord, tailWord_5468211, baseEnd_5468211] using wordTrace_append hprefix tailTrace_5468211
  have hstable : (prefixWord ++ tailWord_5468211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5468211).length < 2 ^ (prefixWord ++ tailWord_5468211).sum := by decide
  have hdescent : baseEnd_5468211 < baseStart_5468211 := by decide
  rcases family_descends (prefixWord ++ tailWord_5468211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5468225 : List Nat := [1, 2, 5, 1, 2, 1, 3, 1, 1, 1, 5]
def baseStart_5468225 : Nat := 118140960795 + 5468225 * 2 ^ 59
def prefixEnd_5468225 : Nat := 4983230072969 + 3 ^ 40 * 5468225 * 2
def baseEnd_5468225 : Nat := 2807827751931973278239597

theorem tailTrace_5468225 : CollatzResearch.WordTrace tailWord_5468225 prefixEnd_5468225 2807827751931973278239597 := by
  unfold tailWord_5468225
  simp only [CollatzResearch.WordTrace]
  refine ⟨199442550614562198323654129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132961700409708132215769419 199442550614562198323654129)
  ·
    refine ⟨149581912960921648742740597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199442550614562198323654129 149581912960921648742740597)
    ·
      refine ⟨14023304340086404569631931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 149581912960921648742740597 14023304340086404569631931)
      ·
        refine ⟨21034956510129606854447897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14023304340086404569631931 21034956510129606854447897)
        ·
          refine ⟨15776217382597205140835923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21034956510129606854447897 15776217382597205140835923)
          ·
            refine ⟨23664326073895807711253885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15776217382597205140835923 23664326073895807711253885)
            ·
              refine ⟨8874122277710927891720207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23664326073895807711253885 8874122277710927891720207)
              ·
                refine ⟨13311183416566391837580311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8874122277710927891720207 13311183416566391837580311)
                ·
                  refine ⟨19966775124849587756370467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13311183416566391837580311 19966775124849587756370467)
                  ·
                    refine ⟨29950162687274381634555701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19966775124849587756370467 29950162687274381634555701)
                    ·
                      refine ⟨2807827751931973278239597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29950162687274381634555701 2807827751931973278239597)
                      ·
                        rfl

theorem cell23_5468225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_5468225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5468225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5468225 prefixEnd_5468225 := by exact prefixLift 5468225
  have htrace : WordTrace (prefixWord ++ tailWord_5468225) baseStart_5468225 baseEnd_5468225 := by
    simpa [prefixWord, tailWord_5468225, baseEnd_5468225] using wordTrace_append hprefix tailTrace_5468225
  have hstable : (prefixWord ++ tailWord_5468225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5468225).length < 2 ^ (prefixWord ++ tailWord_5468225).sum := by decide
  have hdescent : baseEnd_5468225 < baseStart_5468225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5468225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5468265 : List Nat := [1, 2, 1, 1, 1, 5, 1, 3, 3, 3, 2]
def baseStart_5468265 : Nat := 118140960795 + 5468265 * 2 ^ 59
def prefixEnd_5468265 : Nat := 4983230072969 + 3 ^ 40 * 5468265 * 2
def baseEnd_5468265 : Nat := 2807848291158153121739413

theorem tailTrace_5468265 : CollatzResearch.WordTrace tailWord_5468265 prefixEnd_5468265 2807848291158153121739413 := by
  unfold tailWord_5468265
  simp only [CollatzResearch.WordTrace]
  refine ⟨199444009534417285155110249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132962673022944856770073499 199444009534417285155110249)
  ·
    refine ⟨149583007150812963866332687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199444009534417285155110249 149583007150812963866332687)
    ·
      refine ⟨224374510726219445799499031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149583007150812963866332687 224374510726219445799499031)
      ·
        refine ⟨336561766089329168699248547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224374510726219445799499031 336561766089329168699248547)
        ·
          refine ⟨504842649133993753048872821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 336561766089329168699248547 504842649133993753048872821)
          ·
            refine ⟨47328998356311914348331827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 504842649133993753048872821 47328998356311914348331827)
            ·
              refine ⟨70993497534467871522497741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47328998356311914348331827 70993497534467871522497741)
              ·
                refine ⟨26622561575425451820936653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70993497534467871522497741 26622561575425451820936653)
                ·
                  refine ⟨9983460590784544432851245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26622561575425451820936653 9983460590784544432851245)
                  ·
                    refine ⟨3743797721544204162319217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9983460590784544432851245 3743797721544204162319217)
                    ·
                      refine ⟨2807848291158153121739413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3743797721544204162319217 2807848291158153121739413)
                      ·
                        rfl

theorem cell23_5468265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 3, 3, 2].length) (baseStart_5468265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5468265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5468265 prefixEnd_5468265 := by exact prefixLift 5468265
  have htrace : WordTrace (prefixWord ++ tailWord_5468265) baseStart_5468265 baseEnd_5468265 := by
    simpa [prefixWord, tailWord_5468265, baseEnd_5468265] using wordTrace_append hprefix tailTrace_5468265
  have hstable : (prefixWord ++ tailWord_5468265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5468265).length < 2 ^ (prefixWord ++ tailWord_5468265).sum := by decide
  have hdescent : baseEnd_5468265 < baseStart_5468265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5468265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5468295 : List Nat := [1, 1, 4, 2, 1, 1, 2, 2, 3, 4, 2]
def baseStart_5468295 : Nat := 118140960795 + 5468295 * 2 ^ 59
def prefixEnd_5468295 : Nat := 4983230072969 + 3 ^ 40 * 5468295 * 2
def baseEnd_5468295 : Nat := 2807863695577788004364275

theorem tailTrace_5468295 : CollatzResearch.WordTrace tailWord_5468295 prefixEnd_5468295 2807863695577788004364275 := by
  unfold tailWord_5468295
  simp only [CollatzResearch.WordTrace]
  refine ⟨199445103724308600278702339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132963402482872400185801559 199445103724308600278702339)
  ·
    refine ⟨299167655586462900418053509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199445103724308600278702339 299167655586462900418053509)
    ·
      refine ⟨56093935422461793828385033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 299167655586462900418053509 56093935422461793828385033)
      ·
        refine ⟨42070451566846345371288775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56093935422461793828385033 42070451566846345371288775)
        ·
          refine ⟨63105677350269518056933163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42070451566846345371288775 63105677350269518056933163)
          ·
            refine ⟨94658516025404277085399745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63105677350269518056933163 94658516025404277085399745)
            ·
              refine ⟨70993887019053207814049809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94658516025404277085399745 70993887019053207814049809)
              ·
                refine ⟨53245415264289905860537357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70993887019053207814049809 53245415264289905860537357)
                ·
                  refine ⟨19967030724108714697701509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53245415264289905860537357 19967030724108714697701509)
                  ·
                    refine ⟨3743818260770384005819033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19967030724108714697701509 3743818260770384005819033)
                    ·
                      refine ⟨2807863695577788004364275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3743818260770384005819033 2807863695577788004364275)
                      ·
                        rfl

theorem cell23_5468295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 4, 2].length) (baseStart_5468295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5468295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5468295 prefixEnd_5468295 := by exact prefixLift 5468295
  have htrace : WordTrace (prefixWord ++ tailWord_5468295) baseStart_5468295 baseEnd_5468295 := by
    simpa [prefixWord, tailWord_5468295, baseEnd_5468295] using wordTrace_append hprefix tailTrace_5468295
  have hstable : (prefixWord ++ tailWord_5468295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5468295).length < 2 ^ (prefixWord ++ tailWord_5468295).sum := by decide
  have hdescent : baseEnd_5468295 < baseStart_5468295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5468295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5468310 : List Nat := [5, 3, 2, 1, 1, 1, 2, 2, 1, 2, 3]
def baseStart_5468310 : Nat := 118140960795 + 5468310 * 2 ^ 59
def prefixEnd_5468310 : Nat := 4983230072969 + 3 ^ 40 * 5468310 * 2
def baseEnd_5468310 : Nat := 2807871397787605445676707

theorem tailTrace_5468310 : CollatzResearch.WordTrace tailWord_5468310 prefixEnd_5468310 2807871397787605445676707 := by
  unfold tailWord_5468310
  simp only [CollatzResearch.WordTrace]
  refine ⟨12465353176203391115031149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 132963767212836171893665589 12465353176203391115031149)
  ·
    refine ⟨4674507441076271668136681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12465353176203391115031149 4674507441076271668136681)
    ·
      refine ⟨3505880580807203751102511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4674507441076271668136681 3505880580807203751102511)
      ·
        refine ⟨5258820871210805626653767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3505880580807203751102511 5258820871210805626653767)
        ·
          refine ⟨7888231306816208439980651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5258820871210805626653767 7888231306816208439980651)
          ·
            refine ⟨11832346960224312659970977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7888231306816208439980651 11832346960224312659970977)
            ·
              refine ⟨8874260220168234494978233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11832346960224312659970977 8874260220168234494978233)
              ·
                refine ⟨6655695165126175871233675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8874260220168234494978233 6655695165126175871233675)
                ·
                  refine ⟨9983542747689263806850513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6655695165126175871233675 9983542747689263806850513)
                  ·
                    refine ⟨7487657060766947855137885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9983542747689263806850513 7487657060766947855137885)
                    ·
                      refine ⟨2807871397787605445676707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7487657060766947855137885 2807871397787605445676707)
                      ·
                        rfl

theorem cell23_5468310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_5468310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5468310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5468310 prefixEnd_5468310 := by exact prefixLift 5468310
  have htrace : WordTrace (prefixWord ++ tailWord_5468310) baseStart_5468310 baseEnd_5468310 := by
    simpa [prefixWord, tailWord_5468310, baseEnd_5468310] using wordTrace_append hprefix tailTrace_5468310
  have hstable : (prefixWord ++ tailWord_5468310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5468310).length < 2 ^ (prefixWord ++ tailWord_5468310).sum := by decide
  have hdescent : baseEnd_5468310 < baseStart_5468310 := by decide
  rcases family_descends (prefixWord ++ tailWord_5468310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5468378 : List Nat := [3, 1, 1, 2, 2, 1, 2, 1, 2, 8]
def baseStart_5468378 : Nat := 118140960795 + 5468378 * 2 ^ 59
def prefixEnd_5468378 : Nat := 4983230072969 + 3 ^ 40 * 5468378 * 2
def baseEnd_5468378 : Nat := 935968771490703726542131

theorem tailTrace_5468378 : CollatzResearch.WordTrace tailWord_5468378 prefixEnd_5468378 935968771490703726542131 := by
  unfold tailWord_5468378
  simp only [CollatzResearch.WordTrace]
  refine ⟨49862032745751976363493447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132965420655338603635982525 49862032745751976363493447)
  ·
    refine ⟨74793049118627964545240171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49862032745751976363493447 74793049118627964545240171)
    ·
      refine ⟨112189573677941946817860257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74793049118627964545240171 112189573677941946817860257)
      ·
        refine ⟨84142180258456460113395193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112189573677941946817860257 84142180258456460113395193)
        ·
          refine ⟨63106635193842345085046395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84142180258456460113395193 63106635193842345085046395)
          ·
            refine ⟨94659952790763517627569593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63106635193842345085046395 94659952790763517627569593)
            ·
              refine ⟨70994964593072638220677195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94659952790763517627569593 70994964593072638220677195)
              ·
                refine ⟨106492446889608957331015793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70994964593072638220677195 106492446889608957331015793)
                ·
                  refine ⟨79869335167206717998261845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106492446889608957331015793 79869335167206717998261845)
                  ·
                    refine ⟨935968771490703726542131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 79869335167206717998261845 935968771490703726542131)
                    ·
                      rfl

theorem cell23_5468378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 2, 8].length) (baseStart_5468378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5468378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5468378 prefixEnd_5468378 := by exact prefixLift 5468378
  have htrace : WordTrace (prefixWord ++ tailWord_5468378) baseStart_5468378 baseEnd_5468378 := by
    simpa [prefixWord, tailWord_5468378, baseEnd_5468378] using wordTrace_append hprefix tailTrace_5468378
  have hstable : (prefixWord ++ tailWord_5468378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5468378).length < 2 ^ (prefixWord ++ tailWord_5468378).sum := by decide
  have hdescent : baseEnd_5468378 < baseStart_5468378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5468378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5468402 : List Nat := [3, 2, 1, 3, 2, 1, 2, 2, 2, 1, 4]
def baseStart_5468402 : Nat := 118140960795 + 5468402 * 2 ^ 59
def prefixEnd_5468402 : Nat := 4983230072969 + 3 ^ 40 * 5468402 * 2
def baseEnd_5468402 : Nat := 2807918638007819085726283

theorem tailTrace_5468402 : CollatzResearch.WordTrace tailWord_5468402 prefixEnd_5468402 2807918638007819085726283 := by
  unfold tailWord_5468402
  simp only [CollatzResearch.WordTrace]
  refine ⟨49862251583730239388211865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132966004223280638368564973 49862251583730239388211865)
  ·
    refine ⟨37396688687797679541158899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49862251583730239388211865 37396688687797679541158899)
    ·
      refine ⟨56095033031696519311738349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37396688687797679541158899 56095033031696519311738349)
      ·
        refine ⟨21035637386886194741901881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56095033031696519311738349 21035637386886194741901881)
        ·
          refine ⟨15776728040164646056426411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21035637386886194741901881 15776728040164646056426411)
          ·
            refine ⟨23665092060246969084639617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15776728040164646056426411 23665092060246969084639617)
            ·
              refine ⟨17748819045185226813479713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23665092060246969084639617 17748819045185226813479713)
              ·
                refine ⟨13311614283888920110109785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17748819045185226813479713 13311614283888920110109785)
                ·
                  refine ⟨9983710712916690082582339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13311614283888920110109785 9983710712916690082582339)
                  ·
                    refine ⟨14975566069375035123873509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9983710712916690082582339 14975566069375035123873509)
                    ·
                      refine ⟨2807918638007819085726283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14975566069375035123873509 2807918638007819085726283)
                      ·
                        rfl

theorem cell23_5468402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_5468402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5468402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5468402 prefixEnd_5468402 := by exact prefixLift 5468402
  have htrace : WordTrace (prefixWord ++ tailWord_5468402) baseStart_5468402 baseEnd_5468402 := by
    simpa [prefixWord, tailWord_5468402, baseEnd_5468402] using wordTrace_append hprefix tailTrace_5468402
  have hstable : (prefixWord ++ tailWord_5468402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5468402).length < 2 ^ (prefixWord ++ tailWord_5468402).sum := by decide
  have hdescent : baseEnd_5468402 < baseStart_5468402 := by decide
  rcases family_descends (prefixWord ++ tailWord_5468402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5468408 : List Nat := [2, 1, 2, 1, 1, 2, 1, 5, 8]
def baseStart_5468408 : Nat := 118140960795 + 5468408 * 2 ^ 59
def prefixEnd_5468408 : Nat := 4983230072969 + 3 ^ 40 * 5468408 * 2
def baseEnd_5468408 : Nat := 311991302099082895805695

theorem tailTrace_5468408 : CollatzResearch.WordTrace tailWord_5468408 prefixEnd_5468408 311991302099082895805695 := by
  unfold tailWord_5468408
  simp only [CollatzResearch.WordTrace]
  refine ⟨99724612586449610288782939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132966150115266147051710585 99724612586449610288782939)
  ·
    refine ⟨149586918879674415433174409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99724612586449610288782939 149586918879674415433174409)
    ·
      refine ⟨112190189159755811574880807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149586918879674415433174409 112190189159755811574880807)
      ·
        refine ⟨168285283739633717362321211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112190189159755811574880807 168285283739633717362321211)
        ·
          refine ⟨252427925609450576043481817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168285283739633717362321211 252427925609450576043481817)
          ·
            refine ⟨189320944207087932032611363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 252427925609450576043481817 189320944207087932032611363)
            ·
              refine ⟨283981416310631898048917045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189320944207087932032611363 283981416310631898048917045)
              ·
                refine ⟨26623257779121740442085973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 283981416310631898048917045 26623257779121740442085973)
                ·
                  refine ⟨311991302099082895805695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26623257779121740442085973 311991302099082895805695)
                  ·
                    rfl

theorem cell23_5468408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 8].length) (baseStart_5468408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5468408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5468408 prefixEnd_5468408 := by exact prefixLift 5468408
  have htrace : WordTrace (prefixWord ++ tailWord_5468408) baseStart_5468408 baseEnd_5468408 := by
    simpa [prefixWord, tailWord_5468408, baseEnd_5468408] using wordTrace_append hprefix tailTrace_5468408
  have hstable : (prefixWord ++ tailWord_5468408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5468408).length < 2 ^ (prefixWord ++ tailWord_5468408).sum := by decide
  have hdescent : baseEnd_5468408 < baseStart_5468408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5468408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5468425 : List Nat := [1, 2, 1, 1, 3, 4, 2, 3, 6]
def baseStart_5468425 : Nat := 118140960795 + 5468425 * 2 ^ 59
def prefixEnd_5468425 : Nat := 4983230072969 + 3 ^ 40 * 5468425 * 2
def baseEnd_5468425 : Nat := 311992272006985832859853

theorem tailTrace_5468425 : CollatzResearch.WordTrace tailWord_5468425 prefixEnd_5468425 311992272006985832859853 := by
  unfold tailWord_5468425
  simp only [CollatzResearch.WordTrace]
  refine ⟨199449845213837632480934729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132966563475891754987289819 199449845213837632480934729)
  ·
    refine ⟨149587383910378224360701047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199449845213837632480934729 149587383910378224360701047)
    ·
      refine ⟨224381075865567336541051571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149587383910378224360701047 224381075865567336541051571)
      ·
        refine ⟨336571613798351004811577357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224381075865567336541051571 336571613798351004811577357)
        ·
          refine ⟨126214355174381626804341509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 336571613798351004811577357 126214355174381626804341509)
          ·
            refine ⟨23665191595196555025814033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126214355174381626804341509 23665191595196555025814033)
            ·
              refine ⟨17748893696397416269360525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23665191595196555025814033 17748893696397416269360525)
              ·
                refine ⟨6655835136149031101010197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17748893696397416269360525 6655835136149031101010197)
                ·
                  refine ⟨311992272006985832859853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6655835136149031101010197 311992272006985832859853)
                  ·
                    rfl

theorem cell23_5468425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 3, 6].length) (baseStart_5468425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5468425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5468425 prefixEnd_5468425 := by exact prefixLift 5468425
  have htrace : WordTrace (prefixWord ++ tailWord_5468425) baseStart_5468425 baseEnd_5468425 := by
    simpa [prefixWord, tailWord_5468425, baseEnd_5468425] using wordTrace_append hprefix tailTrace_5468425
  have hstable : (prefixWord ++ tailWord_5468425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5468425).length < 2 ^ (prefixWord ++ tailWord_5468425).sum := by decide
  have hdescent : baseEnd_5468425 < baseStart_5468425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5468425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5468439 : List Nat := [1, 1, 3, 4, 1, 4, 1, 1, 2, 2, 3]
def baseStart_5468439 : Nat := 118140960795 + 5468439 * 2 ^ 59
def prefixEnd_5468439 : Nat := 4983230072969 + 3 ^ 40 * 5468439 * 2
def baseEnd_5468439 : Nat := 2807937636792035440963613

theorem tailTrace_5468439 : CollatzResearch.WordTrace tailWord_5468439 prefixEnd_5468439 2807937636792035440963613 := by
  unfold tailWord_5468439
  simp only [CollatzResearch.WordTrace]
  refine ⟨199450355835786912871944371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132966903890524608581296247 199450355835786912871944371)
  ·
    refine ⟨299175533753680369307916557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199450355835786912871944371 299175533753680369307916557)
    ·
      refine ⟨112190825157630138490468709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 299175533753680369307916557 112190825157630138490468709)
      ·
        refine ⟨21035779717055650966962883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112190825157630138490468709 21035779717055650966962883)
        ·
          refine ⟨31553669575583476450444325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21035779717055650966962883 31553669575583476450444325)
          ·
            refine ⟨5916313045421901834458311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31553669575583476450444325 5916313045421901834458311)
            ·
              refine ⟨8874469568132852751687467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5916313045421901834458311 8874469568132852751687467)
              ·
                refine ⟨13311704352199279127531201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8874469568132852751687467 13311704352199279127531201)
                ·
                  refine ⟨9983778264149459345648401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13311704352199279127531201 9983778264149459345648401)
                  ·
                    refine ⟨7487833698112094509236301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9983778264149459345648401 7487833698112094509236301)
                    ·
                      refine ⟨2807937636792035440963613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7487833698112094509236301 2807937636792035440963613)
                      ·
                        rfl

theorem cell23_5468439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_5468439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5468439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5468439 prefixEnd_5468439 := by exact prefixLift 5468439
  have htrace : WordTrace (prefixWord ++ tailWord_5468439) baseStart_5468439 baseEnd_5468439 := by
    simpa [prefixWord, tailWord_5468439, baseEnd_5468439] using wordTrace_append hprefix tailTrace_5468439
  have hstable : (prefixWord ++ tailWord_5468439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5468439).length < 2 ^ (prefixWord ++ tailWord_5468439).sum := by decide
  have hdescent : baseEnd_5468439 < baseStart_5468439 := by decide
  rcases family_descends (prefixWord ++ tailWord_5468439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5468469 : List Nat := [1, 3, 3, 1, 2, 1, 4, 1, 3, 1, 3]
def baseStart_5468469 : Nat := 118140960795 + 5468469 * 2 ^ 59
def prefixEnd_5468469 : Nat := 4983230072969 + 3 ^ 40 * 5468469 * 2
def baseEnd_5468469 : Nat := 2807953041211670323588475

theorem tailTrace_5468469 : CollatzResearch.WordTrace tailWord_5468469 prefixEnd_5468469 2807953041211670323588475 := by
  unfold tailWord_5468469
  simp only [CollatzResearch.WordTrace]
  refine ⟨199451450025678227995536461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132967633350452151997024307 199451450025678227995536461)
  ·
    refine ⟨74794293759629335498326173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199451450025678227995536461 74794293759629335498326173)
    ·
      refine ⟨28047860159861000811872315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74794293759629335498326173 28047860159861000811872315)
      ·
        refine ⟨42071790239791501217808473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28047860159861000811872315 42071790239791501217808473)
        ·
          refine ⟨31553842679843625913356355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42071790239791501217808473 31553842679843625913356355)
          ·
            refine ⟨47330764019765438870034533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31553842679843625913356355 47330764019765438870034533)
            ·
              refine ⟨8874518253706019788131475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47330764019765438870034533 8874518253706019788131475)
              ·
                refine ⟨13311777380559029682197213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8874518253706019788131475 13311777380559029682197213)
                ·
                  refine ⟨4991916517709636130823955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13311777380559029682197213 4991916517709636130823955)
                  ·
                    refine ⟨7487874776564454196235933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4991916517709636130823955 7487874776564454196235933)
                    ·
                      refine ⟨2807953041211670323588475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7487874776564454196235933 2807953041211670323588475)
                      ·
                        rfl

theorem cell23_5468469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_5468469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5468469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5468469 prefixEnd_5468469 := by exact prefixLift 5468469
  have htrace : WordTrace (prefixWord ++ tailWord_5468469) baseStart_5468469 baseEnd_5468469 := by
    simpa [prefixWord, tailWord_5468469, baseEnd_5468469] using wordTrace_append hprefix tailTrace_5468469
  have hstable : (prefixWord ++ tailWord_5468469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5468469).length < 2 ^ (prefixWord ++ tailWord_5468469).sum := by decide
  have hdescent : baseEnd_5468469 < baseStart_5468469 := by decide
  rcases family_descends (prefixWord ++ tailWord_5468469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5468492 : List Nat := [2, 2, 1, 3, 2, 1, 1, 1, 2, 6, 2]
def baseStart_5468492 : Nat := 118140960795 + 5468492 * 2 ^ 59
def prefixEnd_5468492 : Nat := 4983230072969 + 3 ^ 40 * 5468492 * 2
def baseEnd_5468492 : Nat := 2807964851266723733600869

theorem tailTrace_5468492 : CollatzResearch.WordTrace tailWord_5468492 prefixEnd_5468492 2807964851266723733600869 := by
  unfold tailWord_5468492
  simp only [CollatzResearch.WordTrace]
  refine ⟨99726144452297451461811865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132968192603063268615749153 99726144452297451461811865)
  ·
    refine ⟨74794608339223088596358899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99726144452297451461811865 74794608339223088596358899)
    ·
      refine ⟨112191912508834632894538349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74794608339223088596358899 112191912508834632894538349)
      ·
        refine ⟨42071967190812987335451881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112191912508834632894538349 42071967190812987335451881)
        ·
          refine ⟨31553975393109740501588911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42071967190812987335451881 31553975393109740501588911)
          ·
            refine ⟨47330963089664610752383367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31553975393109740501588911 47330963089664610752383367)
            ·
              refine ⟨70996444634496916128575051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47330963089664610752383367 70996444634496916128575051)
              ·
                refine ⟨106494666951745374192862577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70996444634496916128575051 106494666951745374192862577)
                ·
                  refine ⟨79871000213809030644646933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106494666951745374192862577 79871000213809030644646933)
                  ·
                    refine ⟨3743953135022298311467825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 79871000213809030644646933 3743953135022298311467825)
                    ·
                      refine ⟨2807964851266723733600869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3743953135022298311467825 2807964851266723733600869)
                      ·
                        rfl

theorem cell23_5468492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 2, 6, 2].length) (baseStart_5468492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5468492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5468492 prefixEnd_5468492 := by exact prefixLift 5468492
  have htrace : WordTrace (prefixWord ++ tailWord_5468492) baseStart_5468492 baseEnd_5468492 := by
    simpa [prefixWord, tailWord_5468492, baseEnd_5468492] using wordTrace_append hprefix tailTrace_5468492
  have hstable : (prefixWord ++ tailWord_5468492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5468492).length < 2 ^ (prefixWord ++ tailWord_5468492).sum := by decide
  have hdescent : baseEnd_5468492 < baseStart_5468492 := by decide
  rcases family_descends (prefixWord ++ tailWord_5468492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5468505 : List Nat := [1, 2, 1, 2, 2, 2, 1, 3, 3, 2, 4]
def baseStart_5468505 : Nat := 118140960795 + 5468505 * 2 ^ 59
def prefixEnd_5468505 : Nat := 4983230072969 + 3 ^ 40 * 5468505 * 2
def baseEnd_5468505 : Nat := 2807971526515232182738309

theorem tailTrace_5468505 : CollatzResearch.WordTrace tailWord_5468505 prefixEnd_5468505 2807971526515232182738309 := by
  unfold tailWord_5468505
  simp only [CollatzResearch.WordTrace]
  refine ⟨199452763053547806143846969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132968508702365204095897979 199452763053547806143846969)
  ·
    refine ⟨149589572290160854607885227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199452763053547806143846969 149589572290160854607885227)
    ·
      refine ⟨224384358435241281911827841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149589572290160854607885227 224384358435241281911827841)
      ·
        refine ⟨168288268826430961433870881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224384358435241281911827841 168288268826430961433870881)
        ·
          refine ⟨126216201619823221075403161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168288268826430961433870881 126216201619823221075403161)
          ·
            refine ⟨94662151214867415806552371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126216201619823221075403161 94662151214867415806552371)
            ·
              refine ⟨141993226822301123709828557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94662151214867415806552371 141993226822301123709828557)
              ·
                refine ⟨53247460058362921391185709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 141993226822301123709828557 53247460058362921391185709)
                ·
                  refine ⟨19967797521886095521694641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53247460058362921391185709 19967797521886095521694641)
                  ·
                    refine ⟨14975848141414571641270981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19967797521886095521694641 14975848141414571641270981)
                    ·
                      refine ⟨2807971526515232182738309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14975848141414571641270981 2807971526515232182738309)
                      ·
                        rfl

theorem cell23_5468505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 2, 4].length) (baseStart_5468505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5468505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5468505 prefixEnd_5468505 := by exact prefixLift 5468505
  have htrace : WordTrace (prefixWord ++ tailWord_5468505) baseStart_5468505 baseEnd_5468505 := by
    simpa [prefixWord, tailWord_5468505, baseEnd_5468505] using wordTrace_append hprefix tailTrace_5468505
  have hstable : (prefixWord ++ tailWord_5468505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5468505).length < 2 ^ (prefixWord ++ tailWord_5468505).sum := by decide
  have hdescent : baseEnd_5468505 < baseStart_5468505 := by decide
  rcases family_descends (prefixWord ++ tailWord_5468505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5468522 : List Nat := [3, 1, 3, 3, 1, 1, 1, 2, 1, 1, 6]
def baseStart_5468522 : Nat := 118140960795 + 5468522 * 2 ^ 59
def prefixEnd_5468522 : Nat := 4983230072969 + 3 ^ 40 * 5468522 * 2
def baseEnd_5468522 : Nat := 2807980255686358616225731

theorem tailTrace_5468522 : CollatzResearch.WordTrace tailWord_5468522 prefixEnd_5468522 2807980255686358616225731 := by
  unfold tailWord_5468522
  simp only [CollatzResearch.WordTrace]
  refine ⟨49863345773621554511803955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132968922062990812031477213 49863345773621554511803955)
  ·
    refine ⟨74795018660432331767705933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49863345773621554511803955 74795018660432331767705933)
    ·
      refine ⟨28048131997662124412889725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74795018660432331767705933 28048131997662124412889725)
      ·
        refine ⟨10518049499123296654833647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28048131997662124412889725 10518049499123296654833647)
        ·
          refine ⟨15777074248684944982250471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10518049499123296654833647 15777074248684944982250471)
          ·
            refine ⟨23665611373027417473375707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15777074248684944982250471 23665611373027417473375707)
            ·
              refine ⟨35498417059541126210063561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23665611373027417473375707 35498417059541126210063561)
              ·
                refine ⟨26623812794655844657547671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35498417059541126210063561 26623812794655844657547671)
                ·
                  refine ⟨39935719191983766986321507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26623812794655844657547671 39935719191983766986321507)
                  ·
                    refine ⟨59903578787975650479482261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39935719191983766986321507 59903578787975650479482261)
                    ·
                      refine ⟨2807980255686358616225731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59903578787975650479482261 2807980255686358616225731)
                      ·
                        rfl

theorem cell23_5468522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_5468522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5468522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5468522 prefixEnd_5468522 := by exact prefixLift 5468522
  have htrace : WordTrace (prefixWord ++ tailWord_5468522) baseStart_5468522 baseEnd_5468522 := by
    simpa [prefixWord, tailWord_5468522, baseEnd_5468522] using wordTrace_append hprefix tailTrace_5468522
  have hstable : (prefixWord ++ tailWord_5468522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5468522).length < 2 ^ (prefixWord ++ tailWord_5468522).sum := by decide
  have hdescent : baseEnd_5468522 < baseStart_5468522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5468522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5468566 : List Nat := [5, 3, 1, 2, 1, 11]
def baseStart_5468566 : Nat := 118140960795 + 5468566 * 2 ^ 59
def prefixEnd_5468566 : Nat := 4983230072969 + 3 ^ 40 * 5468566 * 2
def baseEnd_5468566 : Nat := 11555567279157022403603

theorem tailTrace_5468566 : CollatzResearch.WordTrace tailWord_5468566 prefixEnd_5468566 11555567279157022403603 := by
  unfold tailWord_5468566
  simp only [CollatzResearch.WordTrace]
  refine ⟨12465936744145425847613597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 132969991937551209041211701 12465936744145425847613597)
  ·
    refine ⟨4674726279054534692855099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12465936744145425847613597 4674726279054534692855099)
    ·
      refine ⟨7012089418581802039282649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4674726279054534692855099 7012089418581802039282649)
      ·
        refine ⟨5259067063936351529461987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7012089418581802039282649 5259067063936351529461987)
        ·
          refine ⟨7888600595904527294192981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5259067063936351529461987 7888600595904527294192981)
          ·
            refine ⟨11555567279157022403603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7888600595904527294192981 11555567279157022403603)
            ·
              rfl

theorem cell23_5468566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 11].length) (baseStart_5468566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5468566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5468566 prefixEnd_5468566 := by exact prefixLift 5468566
  have htrace : WordTrace (prefixWord ++ tailWord_5468566) baseStart_5468566 baseEnd_5468566 := by
    simpa [prefixWord, tailWord_5468566, baseEnd_5468566] using wordTrace_append hprefix tailTrace_5468566
  have hstable : (prefixWord ++ tailWord_5468566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5468566).length < 2 ^ (prefixWord ++ tailWord_5468566).sum := by decide
  have hdescent : baseEnd_5468566 < baseStart_5468566 := by decide
  rcases family_descends (prefixWord ++ tailWord_5468566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5468576 : List Nat := [2, 1, 1, 4, 1, 4, 2, 2, 2, 1, 3]
def baseStart_5468576 : Nat := 118140960795 + 5468576 * 2 ^ 59
def prefixEnd_5468576 : Nat := 4983230072969 + 3 ^ 40 * 5468576 * 2
def baseEnd_5468576 : Nat := 2808007983641701404950483

theorem tailTrace_5468576 : CollatzResearch.WordTrace tailWord_5468576 prefixEnd_5468576 2808007983641701404950483 := by
  unfold tailWord_5468576
  simp only [CollatzResearch.WordTrace]
  refine ⟨99727676318145292634840791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132970235090860390179787721 99727676318145292634840791)
  ·
    refine ⟨149591514477217938952261187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99727676318145292634840791 149591514477217938952261187)
    ·
      refine ⟨224387271715826908428391781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149591514477217938952261187 224387271715826908428391781)
      ·
        refine ⟨42072613446717545330323459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 224387271715826908428391781 42072613446717545330323459)
        ·
          refine ⟨63108920170076317995485189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42072613446717545330323459 63108920170076317995485189)
          ·
            refine ⟨11832922531889309624153473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63108920170076317995485189 11832922531889309624153473)
            ·
              refine ⟨8874691898916982218115105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11832922531889309624153473 8874691898916982218115105)
              ·
                refine ⟨6656018924187736663586329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8874691898916982218115105 6656018924187736663586329)
                ·
                  refine ⟨4992014193140802497689747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6656018924187736663586329 4992014193140802497689747)
                  ·
                    refine ⟨7488021289711203746534621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4992014193140802497689747 7488021289711203746534621)
                    ·
                      refine ⟨2808007983641701404950483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7488021289711203746534621 2808007983641701404950483)
                      ·
                        rfl

theorem cell23_5468576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_5468576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5468576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5468576 prefixEnd_5468576 := by exact prefixLift 5468576
  have htrace : WordTrace (prefixWord ++ tailWord_5468576) baseStart_5468576 baseEnd_5468576 := by
    simpa [prefixWord, tailWord_5468576, baseEnd_5468576] using wordTrace_append hprefix tailTrace_5468576
  have hstable : (prefixWord ++ tailWord_5468576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5468576).length < 2 ^ (prefixWord ++ tailWord_5468576).sum := by decide
  have hdescent : baseEnd_5468576 < baseStart_5468576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5468576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5468585 : List Nat := [1, 2, 1, 1, 1, 1, 3, 4, 1, 3, 5]
def baseStart_5468585 : Nat := 118140960795 + 5468585 * 2 ^ 59
def prefixEnd_5468585 : Nat := 4983230072969 + 3 ^ 40 * 5468585 * 2
def baseEnd_5468585 : Nat := 2808012604967591869737941

theorem tailTrace_5468585 : CollatzResearch.WordTrace tailWord_5468585 prefixEnd_5468585 2808012604967591869737941 := by
  unfold tailWord_5468585
  simp only [CollatzResearch.WordTrace]
  refine ⟨199455680893257979806759209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132970453928838653204506139 199455680893257979806759209)
  ·
    refine ⟨149591760669943484855069407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199455680893257979806759209 149591760669943484855069407)
    ·
      refine ⟨224387641004915227282604111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149591760669943484855069407 224387641004915227282604111)
      ·
        refine ⟨336581461507372840923906167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224387641004915227282604111 336581461507372840923906167)
        ·
          refine ⟨504872192261059261385859251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 336581461507372840923906167 504872192261059261385859251)
          ·
            refine ⟨757308288391588892078788877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 504872192261059261385859251 757308288391588892078788877)
            ·
              refine ⟨283990608146845834529545829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 757308288391588892078788877 283990608146845834529545829)
              ·
                refine ⟨53248239027533593974289843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 283990608146845834529545829 53248239027533593974289843)
                ·
                  refine ⟨79872358541300390961434765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53248239027533593974289843 79872358541300390961434765)
                  ·
                    refine ⟨29952134452987646610538037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 79872358541300390961434765 29952134452987646610538037)
                    ·
                      refine ⟨2808012604967591869737941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29952134452987646610538037 2808012604967591869737941)
                      ·
                        rfl

theorem cell23_5468585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 3, 5].length) (baseStart_5468585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5468585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5468585 prefixEnd_5468585 := by exact prefixLift 5468585
  have htrace : WordTrace (prefixWord ++ tailWord_5468585) baseStart_5468585 baseEnd_5468585 := by
    simpa [prefixWord, tailWord_5468585, baseEnd_5468585] using wordTrace_append hprefix tailTrace_5468585
  have hstable : (prefixWord ++ tailWord_5468585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5468585).length < 2 ^ (prefixWord ++ tailWord_5468585).sum := by decide
  have hdescent : baseEnd_5468585 < baseStart_5468585 := by decide
  rcases family_descends (prefixWord ++ tailWord_5468585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5468599 : List Nat := [1, 1, 3, 1, 3, 3, 1, 3, 1, 4, 2]
def baseStart_5468599 : Nat := 118140960795 + 5468599 * 2 ^ 59
def prefixEnd_5468599 : Nat := 4983230072969 + 3 ^ 40 * 5468599 * 2
def baseEnd_5468599 : Nat := 2808019793696754814962877

theorem tailTrace_5468599 : CollatzResearch.WordTrace tailWord_5468599 prefixEnd_5468599 2808019793696754814962877 := by
  unfold tailWord_5468599
  simp only [CollatzResearch.WordTrace]
  refine ⟨199456191515207260197768851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132970794343471506798512567 199456191515207260197768851)
  ·
    refine ⟨299184287272810890296653277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199456191515207260197768851 299184287272810890296653277)
    ·
      refine ⟨112194107727304083861244979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 299184287272810890296653277 112194107727304083861244979)
      ·
        refine ⟨168291161590956125791867469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112194107727304083861244979 168291161590956125791867469)
        ·
          refine ⟨63109185596608547171950301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168291161590956125791867469 63109185596608547171950301)
          ·
            refine ⟨23665944598728205189481363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63109185596608547171950301 23665944598728205189481363)
            ·
              refine ⟨35498916898092307784222045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23665944598728205189481363 35498916898092307784222045)
              ·
                refine ⟨13312093836784615419083267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35498916898092307784222045 13312093836784615419083267)
                ·
                  refine ⟨19968140755176923128624901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13312093836784615419083267 19968140755176923128624901)
                  ·
                    refine ⟨3744026391595673086617169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19968140755176923128624901 3744026391595673086617169)
                    ·
                      refine ⟨2808019793696754814962877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3744026391595673086617169 2808019793696754814962877)
                      ·
                        rfl

theorem cell23_5468599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 4, 2].length) (baseStart_5468599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5468599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5468599 prefixEnd_5468599 := by exact prefixLift 5468599
  have htrace : WordTrace (prefixWord ++ tailWord_5468599) baseStart_5468599 baseEnd_5468599 := by
    simpa [prefixWord, tailWord_5468599, baseEnd_5468599] using wordTrace_append hprefix tailTrace_5468599
  have hstable : (prefixWord ++ tailWord_5468599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5468599).length < 2 ^ (prefixWord ++ tailWord_5468599).sum := by decide
  have hdescent : baseEnd_5468599 < baseStart_5468599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5468599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5468620 : List Nat := [2, 2, 1, 4, 3, 2, 2, 1, 1, 3, 2]
def baseStart_5468620 : Nat := 118140960795 + 5468620 * 2 ^ 59
def prefixEnd_5468620 : Nat := 4983230072969 + 3 ^ 40 * 5468620 * 2
def baseEnd_5468620 : Nat := 2808030576790499232800281

theorem tailTrace_5468620 : CollatzResearch.WordTrace tailWord_5468620 prefixEnd_5468620 2808030576790499232800281 := by
  unfold tailWord_5468620
  simp only [CollatzResearch.WordTrace]
  refine ⟨99728478724065590392141657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132971304965420787189522209 99728478724065590392141657)
  ·
    refine ⟨74796359043049192794106243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99728478724065590392141657 74796359043049192794106243)
    ·
      refine ⟨112194538564573789191159365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74796359043049192794106243 112194538564573789191159365)
      ·
        refine ⟨21036475980857585473342381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112194538564573789191159365 21036475980857585473342381)
        ·
          refine ⟨7888678492821594552503393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21036475980857585473342381 7888678492821594552503393)
          ·
            refine ⟨5916508869616195914377545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7888678492821594552503393 5916508869616195914377545)
            ·
              refine ⟨4437381652212146935783159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5916508869616195914377545 4437381652212146935783159)
              ·
                refine ⟨6656072478318220403674739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4437381652212146935783159 6656072478318220403674739)
                ·
                  refine ⟨9984108717477330605512109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6656072478318220403674739 9984108717477330605512109)
                  ·
                    refine ⟨3744040769053998977067041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9984108717477330605512109 3744040769053998977067041)
                    ·
                      refine ⟨2808030576790499232800281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3744040769053998977067041 2808030576790499232800281)
                      ·
                        rfl

theorem cell23_5468620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_5468620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5468620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5468620 prefixEnd_5468620 := by exact prefixLift 5468620
  have htrace : WordTrace (prefixWord ++ tailWord_5468620) baseStart_5468620 baseEnd_5468620 := by
    simpa [prefixWord, tailWord_5468620, baseEnd_5468620] using wordTrace_append hprefix tailTrace_5468620
  have hstable : (prefixWord ++ tailWord_5468620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5468620).length < 2 ^ (prefixWord ++ tailWord_5468620).sum := by decide
  have hdescent : baseEnd_5468620 < baseStart_5468620 := by decide
  rcases family_descends (prefixWord ++ tailWord_5468620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5468639 : List Nat := [1, 1, 2, 3, 3, 2, 2, 4, 5]
def baseStart_5468639 : Nat := 118140960795 + 5468639 * 2 ^ 59
def prefixEnd_5468639 : Nat := 4983230072969 + 3 ^ 40 * 5468639 * 2
def baseEnd_5468639 : Nat := 312004481435881628718077

theorem tailTrace_5468639 : CollatzResearch.WordTrace tailWord_5468639 prefixEnd_5468639 312004481435881628718077 := by
  unfold tailWord_5468639
  simp only [CollatzResearch.WordTrace]
  refine ⟨199457650435062347029224971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132971766956708231352816647 199457650435062347029224971)
  ·
    refine ⟨299186475652593520543837457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199457650435062347029224971 299186475652593520543837457)
    ·
      refine ⟨224389856739445140407878093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299186475652593520543837457 224389856739445140407878093)
      ·
        refine ⟨84146196277291927652954285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 224389856739445140407878093 84146196277291927652954285)
        ·
          refine ⟨31554823603984472869857857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84146196277291927652954285 31554823603984472869857857)
          ·
            refine ⟨23666117702988354652393393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31554823603984472869857857 23666117702988354652393393)
            ·
              refine ⟨17749588277241265989295045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23666117702988354652393393 17749588277241265989295045)
              ·
                refine ⟨3328047801982737372992821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17749588277241265989295045 3328047801982737372992821)
                ·
                  refine ⟨312004481435881628718077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3328047801982737372992821 312004481435881628718077)
                  ·
                    rfl

theorem cell23_5468639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 4, 5].length) (baseStart_5468639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5468639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5468639 prefixEnd_5468639 := by exact prefixLift 5468639
  have htrace : WordTrace (prefixWord ++ tailWord_5468639) baseStart_5468639 baseEnd_5468639 := by
    simpa [prefixWord, tailWord_5468639, baseEnd_5468639] using wordTrace_append hprefix tailTrace_5468639
  have hstable : (prefixWord ++ tailWord_5468639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5468639).length < 2 ^ (prefixWord ++ tailWord_5468639).sum := by decide
  have hdescent : baseEnd_5468639 < baseStart_5468639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5468639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5468650 : List Nat := [3, 1, 3, 1, 3, 2, 3, 1, 2, 2, 2]
def baseStart_5468650 : Nat := 118140960795 + 5468650 * 2 ^ 59
def prefixEnd_5468650 : Nat := 4983230072969 + 3 ^ 40 * 5468650 * 2
def baseEnd_5468650 : Nat := 2808045981210134115425143

theorem tailTrace_5468650 : CollatzResearch.WordTrace tailWord_5468650 prefixEnd_5468650 2808045981210134115425143 := by
  unfold tailWord_5468650
  simp only [CollatzResearch.WordTrace]
  refine ⟨49864512909505623976968851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132972034425348330605250269 49864512909505623976968851)
  ·
    refine ⟨74796769364258435965453277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49864512909505623976968851 74796769364258435965453277)
    ·
      refine ⟨28048788511596913487044979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74796769364258435965453277 28048788511596913487044979)
      ·
        refine ⟨42073182767395370230567469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28048788511596913487044979 42073182767395370230567469)
        ·
          refine ⟨15777443537773263836462801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42073182767395370230567469 15777443537773263836462801)
          ·
            refine ⟨11833082653329947877347101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15777443537773263836462801 11833082653329947877347101)
            ·
              refine ⟨4437405994998730454005163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11833082653329947877347101 4437405994998730454005163)
              ·
                refine ⟨6656108992498095681007745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4437405994998730454005163 6656108992498095681007745)
                ·
                  refine ⟨4992081744373571760755809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6656108992498095681007745 4992081744373571760755809)
                  ·
                    refine ⟨3744061308280178820566857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4992081744373571760755809 3744061308280178820566857)
                    ·
                      refine ⟨2808045981210134115425143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3744061308280178820566857 2808045981210134115425143)
                      ·
                        rfl

theorem cell23_5468650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 1, 2, 2, 2].length) (baseStart_5468650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5468650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5468650 prefixEnd_5468650 := by exact prefixLift 5468650
  have htrace : WordTrace (prefixWord ++ tailWord_5468650) baseStart_5468650 baseEnd_5468650 := by
    simpa [prefixWord, tailWord_5468650, baseEnd_5468650] using wordTrace_append hprefix tailTrace_5468650
  have hstable : (prefixWord ++ tailWord_5468650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5468650).length < 2 ^ (prefixWord ++ tailWord_5468650).sum := by decide
  have hdescent : baseEnd_5468650 < baseStart_5468650 := by decide
  rcases family_descends (prefixWord ++ tailWord_5468650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
