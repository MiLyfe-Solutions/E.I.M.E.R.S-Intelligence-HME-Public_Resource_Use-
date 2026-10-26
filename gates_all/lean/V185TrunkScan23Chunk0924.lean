import V185TrunkScan23Chunk0923

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5468672 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 4]
def baseStart_5468672 : Nat := 118140960795 + 5468672 * 2 ^ 59
def prefixEnd_5468672 : Nat := 4983230072969 + 3 ^ 40 * 5468672 * 2
def baseEnd_5468672 : Nat := 2808057277784533029350041

theorem tailTrace_5468672 : CollatzResearch.WordTrace tailWord_5468672 prefixEnd_5468672 2808057277784533029350041 := by
  unfold tailWord_5468672
  simp only [CollatzResearch.WordTrace]
  refine ⟨99729427021971396832588135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132972569362628529110117513 99729427021971396832588135)
  ·
    refine ⟨149594140532957095248882203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99729427021971396832588135 149594140532957095248882203)
    ·
      refine ⟨224391210799435642873323305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149594140532957095248882203 224391210799435642873323305)
      ·
        refine ⟨168293408099576732154992479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224391210799435642873323305 168293408099576732154992479)
        ·
          refine ⟨252440112149365098232488719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168293408099576732154992479 252440112149365098232488719)
          ·
            refine ⟨378660168224047647348733079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252440112149365098232488719 378660168224047647348733079)
            ·
              refine ⟨567990252336071471023099619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 378660168224047647348733079 567990252336071471023099619)
              ·
                refine ⟨851985378504107206534649429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 567990252336071471023099619 851985378504107206534649429)
                ·
                  refine ⟨9984203654345006326577923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 851985378504107206534649429 9984203654345006326577923)
                  ·
                    refine ⟨14976305481517509489866885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9984203654345006326577923 14976305481517509489866885)
                    ·
                      refine ⟨2808057277784533029350041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14976305481517509489866885 2808057277784533029350041)
                      ·
                        rfl

theorem cell23_5468672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 4].length) (baseStart_5468672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5468672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5468672 prefixEnd_5468672 := by exact prefixLift 5468672
  have htrace : WordTrace (prefixWord ++ tailWord_5468672) baseStart_5468672 baseEnd_5468672 := by
    simpa [prefixWord, tailWord_5468672, baseEnd_5468672] using wordTrace_append hprefix tailTrace_5468672
  have hstable : (prefixWord ++ tailWord_5468672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5468672).length < 2 ^ (prefixWord ++ tailWord_5468672).sum := by decide
  have hdescent : baseEnd_5468672 < baseStart_5468672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5468672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5468689 : List Nat := [1, 2, 2, 1, 1, 2, 2, 4, 2, 4, 2]
def baseStart_5468689 : Nat := 118140960795 + 5468689 * 2 ^ 59
def prefixEnd_5468689 : Nat := 4983230072969 + 3 ^ 40 * 5468689 * 2
def baseEnd_5468689 : Nat := 2808066006955659462837463

theorem tailTrace_5468689 : CollatzResearch.WordTrace tailWord_5468689 prefixEnd_5468689 2808066006955659462837463 := by
  unfold tailWord_5468689
  simp only [CollatzResearch.WordTrace]
  refine ⟨199459474084881205568545121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132972982723254137045696747 199459474084881205568545121)
  ·
    refine ⟨149594605563660904176408841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199459474084881205568545121 149594605563660904176408841)
    ·
      refine ⟨112195954172745678132306631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149594605563660904176408841 112195954172745678132306631)
      ·
        refine ⟨168293931259118517198459947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112195954172745678132306631 168293931259118517198459947)
        ·
          refine ⟨252440896888677775797689921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168293931259118517198459947 252440896888677775797689921)
          ·
            refine ⟨189330672666508331848267441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 252440896888677775797689921 189330672666508331848267441)
            ·
              refine ⟨141998004499881248886200581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189330672666508331848267441 141998004499881248886200581)
              ·
                refine ⟨26624625843727734166162609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 141998004499881248886200581 26624625843727734166162609)
                ·
                  refine ⟨19968469382795800624621957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26624625843727734166162609 19968469382795800624621957)
                  ·
                    refine ⟨3744088009274212617116617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19968469382795800624621957 3744088009274212617116617)
                    ·
                      refine ⟨2808066006955659462837463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3744088009274212617116617 2808066006955659462837463)
                      ·
                        rfl

theorem cell23_5468689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 4, 2].length) (baseStart_5468689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5468689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5468689 prefixEnd_5468689 := by exact prefixLift 5468689
  have htrace : WordTrace (prefixWord ++ tailWord_5468689) baseStart_5468689 baseEnd_5468689 := by
    simpa [prefixWord, tailWord_5468689, baseEnd_5468689] using wordTrace_append hprefix tailTrace_5468689
  have hstable : (prefixWord ++ tailWord_5468689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5468689).length < 2 ^ (prefixWord ++ tailWord_5468689).sum := by decide
  have hdescent : baseEnd_5468689 < baseStart_5468689 := by decide
  rcases family_descends (prefixWord ++ tailWord_5468689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5468773 : List Nat := [1, 3, 1, 3, 4, 1, 1, 2, 3, 1, 3]
def baseStart_5468773 : Nat := 118140960795 + 5468773 * 2 ^ 59
def prefixEnd_5468773 : Nat := 4983230072969 + 3 ^ 40 * 5468773 * 2
def baseEnd_5468773 : Nat := 2808109139330637134187077

theorem tailTrace_5468773 : CollatzResearch.WordTrace tailWord_5468773 prefixEnd_5468773 2808109139330637134187077 := by
  unfold tailWord_5468773
  simp only [CollatzResearch.WordTrace]
  refine ⟨199462537816576887914602973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132975025211051258609735315 199462537816576887914602973)
  ·
    refine ⟨74798451681216332967976115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199462537816576887914602973 74798451681216332967976115)
    ·
      refine ⟨112197677521824499451964173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74798451681216332967976115 112197677521824499451964173)
      ·
        refine ⟨42074129070684187294486565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112197677521824499451964173 42074129070684187294486565)
        ·
          refine ⟨7888899200753285117716231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42074129070684187294486565 7888899200753285117716231)
          ·
            refine ⟨11833348801129927676574347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7888899200753285117716231 11833348801129927676574347)
            ·
              refine ⟨17750023201694891514861521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11833348801129927676574347 17750023201694891514861521)
              ·
                refine ⟨13312517401271168636146141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17750023201694891514861521 13312517401271168636146141)
                ·
                  refine ⟨4992194025476688238554803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13312517401271168636146141 4992194025476688238554803)
                  ·
                    refine ⟨7488291038215032357832205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4992194025476688238554803 7488291038215032357832205)
                    ·
                      refine ⟨2808109139330637134187077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7488291038215032357832205 2808109139330637134187077)
                      ·
                        rfl

theorem cell23_5468773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_5468773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5468773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5468773 prefixEnd_5468773 := by exact prefixLift 5468773
  have htrace : WordTrace (prefixWord ++ tailWord_5468773) baseStart_5468773 baseEnd_5468773 := by
    simpa [prefixWord, tailWord_5468773, baseEnd_5468773] using wordTrace_append hprefix tailTrace_5468773
  have hstable : (prefixWord ++ tailWord_5468773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5468773).length < 2 ^ (prefixWord ++ tailWord_5468773).sum := by decide
  have hdescent : baseEnd_5468773 < baseStart_5468773 := by decide
  rcases family_descends (prefixWord ++ tailWord_5468773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5468779 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 1, 8, 2]
def baseStart_5468779 : Nat := 118140960795 + 5468779 * 2 ^ 59
def prefixEnd_5468779 : Nat := 4983230072969 + 3 ^ 40 * 5468779 * 2
def baseEnd_5468779 : Nat := 2808112220214564110712049

theorem tailTrace_5468779 : CollatzResearch.WordTrace tailWord_5468779 prefixEnd_5468779 2808112220214564110712049 := by
  unfold tailWord_5468779
  simp only [CollatzResearch.WordTrace]
  refine ⟨199462756654555150939321391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132975171103036767292880927 199462756654555150939321391)
  ·
    refine ⟨299194134981832726408982087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199462756654555150939321391 299194134981832726408982087)
    ·
      refine ⟨448791202472749089613473131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299194134981832726408982087 448791202472749089613473131)
      ·
        refine ⟨673186803709123634420209697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 448791202472749089613473131 673186803709123634420209697)
        ·
          refine ⟨504890102781842725815157273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 673186803709123634420209697 504890102781842725815157273)
          ·
            refine ⟨378667577086382044361367955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 504890102781842725815157273 378667577086382044361367955)
            ·
              refine ⟨568001365629573066542051933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 378667577086382044361367955 568001365629573066542051933)
              ·
                refine ⟨213000512111089899953269475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 568001365629573066542051933 213000512111089899953269475)
                ·
                  refine ⟨319500768166634849929904213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 213000512111089899953269475 319500768166634849929904213)
                  ·
                    refine ⟨3744149626952752147616065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 319500768166634849929904213 3744149626952752147616065)
                    ·
                      refine ⟨2808112220214564110712049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3744149626952752147616065 2808112220214564110712049)
                      ·
                        rfl

theorem cell23_5468779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 8, 2].length) (baseStart_5468779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5468779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5468779 prefixEnd_5468779 := by exact prefixLift 5468779
  have htrace : WordTrace (prefixWord ++ tailWord_5468779) baseStart_5468779 baseEnd_5468779 := by
    simpa [prefixWord, tailWord_5468779, baseEnd_5468779] using wordTrace_append hprefix tailTrace_5468779
  have hstable : (prefixWord ++ tailWord_5468779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5468779).length < 2 ^ (prefixWord ++ tailWord_5468779).sum := by decide
  have hdescent : baseEnd_5468779 < baseStart_5468779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5468779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5468793 : List Nat := [1, 2, 1, 3, 3, 4, 2, 1, 1, 5]
def baseStart_5468793 : Nat := 118140960795 + 5468793 * 2 ^ 59
def prefixEnd_5468793 : Nat := 4983230072969 + 3 ^ 40 * 5468793 * 2
def baseEnd_5468793 : Nat := 936039802981242351978995

theorem tailTrace_5468793 : CollatzResearch.WordTrace tailWord_5468793 prefixEnd_5468793 936039802981242351978995 := by
  unfold tailWord_5468793
  simp only [CollatzResearch.WordTrace]
  refine ⟨199463267276504431330331033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132975511517669620886887355 199463267276504431330331033)
  ·
    refine ⟨149597450457378323497748275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199463267276504431330331033 149597450457378323497748275)
    ·
      refine ⟨224396175686067485246622413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149597450457378323497748275 224396175686067485246622413)
      ·
        refine ⟨84148565882275306967483405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 224396175686067485246622413 84148565882275306967483405)
        ·
          refine ⟨31555712205853240112806277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84148565882275306967483405 31555712205853240112806277)
          ·
            refine ⟨5916696038597482521151177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31555712205853240112806277 5916696038597482521151177)
            ·
              refine ⟨4437522028948111890863383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5916696038597482521151177 4437522028948111890863383)
              ·
                refine ⟨6656283043422167836295075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4437522028948111890863383 6656283043422167836295075)
                ·
                  refine ⟨9984424565133251754442613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6656283043422167836295075 9984424565133251754442613)
                  ·
                    refine ⟨936039802981242351978995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9984424565133251754442613 936039802981242351978995)
                    ·
                      rfl

theorem cell23_5468793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 1, 1, 5].length) (baseStart_5468793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5468793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5468793 prefixEnd_5468793 := by exact prefixLift 5468793
  have htrace : WordTrace (prefixWord ++ tailWord_5468793) baseStart_5468793 baseEnd_5468793 := by
    simpa [prefixWord, tailWord_5468793, baseEnd_5468793] using wordTrace_append hprefix tailTrace_5468793
  have hstable : (prefixWord ++ tailWord_5468793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5468793).length < 2 ^ (prefixWord ++ tailWord_5468793).sum := by decide
  have hdescent : baseEnd_5468793 < baseStart_5468793 := by decide
  rcases family_descends (prefixWord ++ tailWord_5468793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5468799 : List Nat := [1, 1, 2, 2, 1, 1, 1, 4, 5, 2, 3]
def baseStart_5468799 : Nat := 118140960795 + 5468799 * 2 ^ 59
def prefixEnd_5468799 : Nat := 4983230072969 + 3 ^ 40 * 5468799 * 2
def baseEnd_5468799 : Nat := 2808122489827654032461957

theorem tailTrace_5468799 : CollatzResearch.WordTrace tailWord_5468799 prefixEnd_5468799 2808122489827654032461957 := by
  unfold tailWord_5468799
  simp only [CollatzResearch.WordTrace]
  refine ⟨199463486114482694355049451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132975657409655129570032967 199463486114482694355049451)
  ·
    refine ⟨299195229171724041532574177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199463486114482694355049451 299195229171724041532574177)
    ·
      refine ⟨224396421878793031149430633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299195229171724041532574177 224396421878793031149430633)
      ·
        refine ⟨168297316409094773362072975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224396421878793031149430633 168297316409094773362072975)
        ·
          refine ⟨252445974613642160043109463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168297316409094773362072975 252445974613642160043109463)
          ·
            refine ⟨378668961920463240064664195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252445974613642160043109463 378668961920463240064664195)
            ·
              refine ⟨568003442880694860096996293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 378668961920463240064664195 568003442880694860096996293)
              ·
                refine ⟨106500645540130286268186805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 568003442880694860096996293 106500645540130286268186805)
                ·
                  refine ⟨9984435519387214337642513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 106500645540130286268186805 9984435519387214337642513)
                  ·
                    refine ⟨7488326639540410753231885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9984435519387214337642513 7488326639540410753231885)
                    ·
                      refine ⟨2808122489827654032461957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7488326639540410753231885 2808122489827654032461957)
                      ·
                        rfl

theorem cell23_5468799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 5, 2, 3].length) (baseStart_5468799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5468799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5468799 prefixEnd_5468799 := by exact prefixLift 5468799
  have htrace : WordTrace (prefixWord ++ tailWord_5468799) baseStart_5468799 baseEnd_5468799 := by
    simpa [prefixWord, tailWord_5468799, baseEnd_5468799] using wordTrace_append hprefix tailTrace_5468799
  have hstable : (prefixWord ++ tailWord_5468799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5468799).length < 2 ^ (prefixWord ++ tailWord_5468799).sum := by decide
  have hdescent : baseEnd_5468799 < baseStart_5468799 := by decide
  rcases family_descends (prefixWord ++ tailWord_5468799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5468823 : List Nat := [1, 1, 3, 3, 2, 1, 5, 1, 2, 4]
def baseStart_5468823 : Nat := 118140960795 + 5468823 * 2 ^ 59
def prefixEnd_5468823 : Nat := 4983230072969 + 3 ^ 40 * 5468823 * 2
def baseEnd_5468823 : Nat := 936044937787787312853949

theorem tailTrace_5468823 : CollatzResearch.WordTrace tailWord_5468823 prefixEnd_5468823 936044937787787312853949 := by
  unfold tailWord_5468823
  simp only [CollatzResearch.WordTrace]
  refine ⟨199464361466395746453923123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132976240977597164302615415 199464361466395746453923123)
  ·
    refine ⟨299196542199593619680884685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199464361466395746453923123 299196542199593619680884685)
    ·
      refine ⟨112198703324847607380331757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 299196542199593619680884685 112198703324847607380331757)
      ·
        refine ⟨42074513746817852767624409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112198703324847607380331757 42074513746817852767624409)
        ·
          refine ⟨31555885310113389575718307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42074513746817852767624409 31555885310113389575718307)
          ·
            refine ⟨47333827965170084363577461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31555885310113389575718307 47333827965170084363577461)
            ·
              refine ⟨4437546371734695409085387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47333827965170084363577461 4437546371734695409085387)
              ·
                refine ⟨6656319557602043113628081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4437546371734695409085387 6656319557602043113628081)
                ·
                  refine ⟨4992239668201532335221061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6656319557602043113628081 4992239668201532335221061)
                  ·
                    refine ⟨936044937787787312853949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4992239668201532335221061 936044937787787312853949)
                    ·
                      rfl

theorem cell23_5468823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 1, 2, 4].length) (baseStart_5468823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5468823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5468823 prefixEnd_5468823 := by exact prefixLift 5468823
  have htrace : WordTrace (prefixWord ++ tailWord_5468823) baseStart_5468823 baseEnd_5468823 := by
    simpa [prefixWord, tailWord_5468823, baseEnd_5468823] using wordTrace_append hprefix tailTrace_5468823
  have hstable : (prefixWord ++ tailWord_5468823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5468823).length < 2 ^ (prefixWord ++ tailWord_5468823).sum := by decide
  have hdescent : baseEnd_5468823 < baseStart_5468823 := by decide
  rcases family_descends (prefixWord ++ tailWord_5468823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5468830 : List Nat := [4, 3, 1, 1, 1, 1, 1, 4, 3, 2, 2]
def baseStart_5468830 : Nat := 118140960795 + 5468830 * 2 ^ 59
def prefixEnd_5468830 : Nat := 4983230072969 + 3 ^ 40 * 5468830 * 2
def baseEnd_5468830 : Nat := 2808138407727943411174315

theorem tailTrace_5468830 : CollatzResearch.WordTrace tailWord_5468830 prefixEnd_5468830 2808138407727943411174315 := by
  unfold tailWord_5468830
  simp only [CollatzResearch.WordTrace]
  refine ⟨24933077097171298331178493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132976411184913591099618629 24933077097171298331178493)
  ·
    refine ⟨9349903911439236874191935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24933077097171298331178493 9349903911439236874191935)
    ·
      refine ⟨14024855867158855311287903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9349903911439236874191935 14024855867158855311287903)
      ·
        refine ⟨21037283800738282966931855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14024855867158855311287903 21037283800738282966931855)
        ·
          refine ⟨31555925701107424450397783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21037283800738282966931855 31555925701107424450397783)
          ·
            refine ⟨47333888551661136675596675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31555925701107424450397783 47333888551661136675596675)
            ·
              refine ⟨71000832827491705013395013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47333888551661136675596675 71000832827491705013395013)
              ·
                refine ⟨13312656155154694690011565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71000832827491705013395013 13312656155154694690011565)
                ·
                  refine ⟨4992246058183010508754337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13312656155154694690011565 4992246058183010508754337)
                  ·
                    refine ⟨3744184543637257881565753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4992246058183010508754337 3744184543637257881565753)
                    ·
                      refine ⟨2808138407727943411174315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3744184543637257881565753 2808138407727943411174315)
                      ·
                        rfl

theorem cell23_5468830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_5468830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5468830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5468830 prefixEnd_5468830 := by exact prefixLift 5468830
  have htrace : WordTrace (prefixWord ++ tailWord_5468830) baseStart_5468830 baseEnd_5468830 := by
    simpa [prefixWord, tailWord_5468830, baseEnd_5468830] using wordTrace_append hprefix tailTrace_5468830
  have hstable : (prefixWord ++ tailWord_5468830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5468830).length < 2 ^ (prefixWord ++ tailWord_5468830).sum := by decide
  have hdescent : baseEnd_5468830 < baseStart_5468830 := by decide
  rcases family_descends (prefixWord ++ tailWord_5468830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5468847 : List Nat := [1, 1, 2, 1, 2, 7, 1, 3, 1, 2, 2]
def baseStart_5468847 : Nat := 118140960795 + 5468847 * 2 ^ 59
def prefixEnd_5468847 : Nat := 4983230072969 + 3 ^ 40 * 5468847 * 2
def baseEnd_5468847 : Nat := 2808147136899069844661737

theorem tailTrace_5468847 : CollatzResearch.WordTrace tailWord_5468847 prefixEnd_5468847 2808147136899069844661737 := by
  unfold tailWord_5468847
  simp only [CollatzResearch.WordTrace]
  refine ⟨199465236818308798552796795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132976824545539199035197863 199465236818308798552796795)
  ·
    refine ⟨299197855227463197829195193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199465236818308798552796795 299197855227463197829195193)
    ·
      refine ⟨224398391420597398371896395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299197855227463197829195193 224398391420597398371896395)
      ·
        refine ⟨336597587130896097557844593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224398391420597398371896395 336597587130896097557844593)
        ·
          refine ⟨252448190348172073168383445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 336597587130896097557844593 252448190348172073168383445)
          ·
            refine ⟨5916754461285282964883987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 252448190348172073168383445 5916754461285282964883987)
            ·
              refine ⟨8875131691927924447325981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5916754461285282964883987 8875131691927924447325981)
              ·
                refine ⟨3328174384472971667747243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8875131691927924447325981 3328174384472971667747243)
                ·
                  refine ⟨4992261576709457501620865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3328174384472971667747243 4992261576709457501620865)
                  ·
                    refine ⟨3744196182532093126215649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4992261576709457501620865 3744196182532093126215649)
                    ·
                      refine ⟨2808147136899069844661737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3744196182532093126215649 2808147136899069844661737)
                      ·
                        rfl

theorem cell23_5468847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 3, 1, 2, 2].length) (baseStart_5468847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5468847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5468847 prefixEnd_5468847 := by exact prefixLift 5468847
  have htrace : WordTrace (prefixWord ++ tailWord_5468847) baseStart_5468847 baseEnd_5468847 := by
    simpa [prefixWord, tailWord_5468847, baseEnd_5468847] using wordTrace_append hprefix tailTrace_5468847
  have hstable : (prefixWord ++ tailWord_5468847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5468847).length < 2 ^ (prefixWord ++ tailWord_5468847).sum := by decide
  have hdescent : baseEnd_5468847 < baseStart_5468847 := by decide
  rcases family_descends (prefixWord ++ tailWord_5468847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5468856 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 7, 3, 2]
def baseStart_5468856 : Nat := 118140960795 + 5468856 * 2 ^ 59
def prefixEnd_5468856 : Nat := 4983230072969 + 3 ^ 40 * 5468856 * 2
def baseEnd_5468856 : Nat := 2808151758224960309449195

theorem tailTrace_5468856 : CollatzResearch.WordTrace tailWord_5468856 prefixEnd_5468856 2808151758224960309449195 := by
  unfold tailWord_5468856
  simp only [CollatzResearch.WordTrace]
  refine ⟨99732782537638096544937211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132977043383517462059916281 99732782537638096544937211)
  ·
    refine ⟨149599173806457144817405817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99732782537638096544937211 149599173806457144817405817)
    ·
      refine ⟨112199380354842858613054363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149599173806457144817405817 112199380354842858613054363)
      ·
        refine ⟨168299070532264287919581545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112199380354842858613054363 168299070532264287919581545)
        ·
          refine ⟨126224302899198215939686159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168299070532264287919581545 126224302899198215939686159)
          ·
            refine ⟨189336454348797323909529239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126224302899198215939686159 189336454348797323909529239)
            ·
              refine ⟨284004681523195985864293859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189336454348797323909529239 284004681523195985864293859)
              ·
                refine ⟨426007022284793978796440789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 284004681523195985864293859 426007022284793978796440789)
                ·
                  refine ⟨9984539584799858878041581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 426007022284793978796440789 9984539584799858878041581)
                  ·
                    refine ⟨3744202344299947079265593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9984539584799858878041581 3744202344299947079265593)
                    ·
                      refine ⟨2808151758224960309449195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3744202344299947079265593 2808151758224960309449195)
                      ·
                        rfl

theorem cell23_5468856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 7, 3, 2].length) (baseStart_5468856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5468856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5468856 prefixEnd_5468856 := by exact prefixLift 5468856
  have htrace : WordTrace (prefixWord ++ tailWord_5468856) baseStart_5468856 baseEnd_5468856 := by
    simpa [prefixWord, tailWord_5468856, baseEnd_5468856] using wordTrace_append hprefix tailTrace_5468856
  have hstable : (prefixWord ++ tailWord_5468856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5468856).length < 2 ^ (prefixWord ++ tailWord_5468856).sum := by decide
  have hdescent : baseEnd_5468856 < baseStart_5468856 := by decide
  rcases family_descends (prefixWord ++ tailWord_5468856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5468870 : List Nat := [6, 1, 2, 1, 2, 1, 2, 8]
def baseStart_5468870 : Nat := 118140960795 + 5468870 * 2 ^ 59
def prefixEnd_5468870 : Nat := 4983230072969 + 3 ^ 40 * 5468870 * 2
def baseEnd_5468870 : Nat := 104005886924226787210153

theorem tailTrace_5468870 : CollatzResearch.WordTrace tailWord_5468870 prefixEnd_5468870 104005886924226787210153 := by
  unfold tailWord_5468870
  simp only [CollatzResearch.WordTrace]
  refine ⟨6233314865538296046277627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 132977383798150315653922709 6233314865538296046277627)
  ·
    refine ⟨9349972298307444069416441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6233314865538296046277627 9349972298307444069416441)
    ·
      refine ⟨7012479223730583052062331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9349972298307444069416441 7012479223730583052062331)
      ·
        refine ⟨10518718835595874578093497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7012479223730583052062331 10518718835595874578093497)
        ·
          refine ⟨7889039126696905933570123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10518718835595874578093497 7889039126696905933570123)
          ·
            refine ⟨11833558690045358900355185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7889039126696905933570123 11833558690045358900355185)
            ·
              refine ⟨8875169017534019175266389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11833558690045358900355185 8875169017534019175266389)
              ·
                refine ⟨104005886924226787210153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8875169017534019175266389 104005886924226787210153)
                ·
                  rfl

theorem cell23_5468870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 8].length) (baseStart_5468870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5468870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5468870 prefixEnd_5468870 := by exact prefixLift 5468870
  have htrace : WordTrace (prefixWord ++ tailWord_5468870) baseStart_5468870 baseEnd_5468870 := by
    simpa [prefixWord, tailWord_5468870, baseEnd_5468870] using wordTrace_append hprefix tailTrace_5468870
  have hstable : (prefixWord ++ tailWord_5468870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5468870).length < 2 ^ (prefixWord ++ tailWord_5468870).sum := by decide
  have hdescent : baseEnd_5468870 < baseStart_5468870 := by decide
  rcases family_descends (prefixWord ++ tailWord_5468870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5468889 : List Nat := [1, 2, 1, 2, 3, 2, 1, 1, 4, 1, 5]
def baseStart_5468889 : Nat := 118140960795 + 5468889 * 2 ^ 59
def prefixEnd_5468889 : Nat := 4983230072969 + 3 ^ 40 * 5468889 * 2
def baseEnd_5468889 : Nat := 2808168703086558680336543

theorem tailTrace_5468889 : CollatzResearch.WordTrace tailWord_5468889 prefixEnd_5468889 2808168703086558680336543 := by
  unfold tailWord_5468889
  simp only [CollatzResearch.WordTrace]
  refine ⟨199466768684156639725825721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132977845789437759817217147 199466768684156639725825721)
  ·
    refine ⟨149600076513117479794369291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199466768684156639725825721 149600076513117479794369291)
    ·
      refine ⟨224400114769676219691553937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149600076513117479794369291 224400114769676219691553937)
      ·
        refine ⟨168300086077257164768665453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224400114769676219691553937 168300086077257164768665453)
        ·
          refine ⟨63112532278971436788249545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168300086077257164768665453 63112532278971436788249545)
          ·
            refine ⟨47334399209228577591187159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63112532278971436788249545 47334399209228577591187159)
            ·
              refine ⟨71001598813842866386780739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47334399209228577591187159 71001598813842866386780739)
              ·
                refine ⟨106502398220764299580171109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71001598813842866386780739 106502398220764299580171109)
                ·
                  refine ⟨19969199666393306171282083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 106502398220764299580171109 19969199666393306171282083)
                  ·
                    refine ⟨29953799499589959256923125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19969199666393306171282083 29953799499589959256923125)
                    ·
                      refine ⟨2808168703086558680336543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29953799499589959256923125 2808168703086558680336543)
                      ·
                        rfl

theorem cell23_5468889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 1, 5].length) (baseStart_5468889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5468889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5468889 prefixEnd_5468889 := by exact prefixLift 5468889
  have htrace : WordTrace (prefixWord ++ tailWord_5468889) baseStart_5468889 baseEnd_5468889 := by
    simpa [prefixWord, tailWord_5468889, baseEnd_5468889] using wordTrace_append hprefix tailTrace_5468889
  have hstable : (prefixWord ++ tailWord_5468889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5468889).length < 2 ^ (prefixWord ++ tailWord_5468889).sum := by decide
  have hdescent : baseEnd_5468889 < baseStart_5468889 := by decide
  rcases family_descends (prefixWord ++ tailWord_5468889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5468920 : List Nat := [2, 1, 2, 1, 1, 2, 6, 2, 2, 2, 2]
def baseStart_5468920 : Nat := 118140960795 + 5468920 * 2 ^ 59
def prefixEnd_5468920 : Nat := 4983230072969 + 3 ^ 40 * 5468920 * 2
def baseEnd_5468920 : Nat := 2808184620986848059048901

theorem tailTrace_5468920 : CollatzResearch.WordTrace tailWord_5468920 prefixEnd_5468920 2808184620986848059048901 := by
  unfold tailWord_5468920
  simp only [CollatzResearch.WordTrace]
  refine ⟨99733949673522166010102107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132978599564696221346802809 99733949673522166010102107)
  ·
    refine ⟨149600924510283249015153161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99733949673522166010102107 149600924510283249015153161)
    ·
      refine ⟨112200693382712436761364871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149600924510283249015153161 112200693382712436761364871)
      ·
        refine ⟨168301040074068655142047307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112200693382712436761364871 168301040074068655142047307)
        ·
          refine ⟨252451560111102982713070961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168301040074068655142047307 252451560111102982713070961)
          ·
            refine ⟨189338670083327237034803221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 252451560111102982713070961 189338670083327237034803221)
            ·
              refine ⟨8875250160155964236006401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 189338670083327237034803221 8875250160155964236006401)
              ·
                refine ⟨6656437620116973177004801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8875250160155964236006401 6656437620116973177004801)
                ·
                  refine ⟨4992328215087729882753601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6656437620116973177004801 4992328215087729882753601)
                  ·
                    refine ⟨3744246161315797412065201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4992328215087729882753601 3744246161315797412065201)
                    ·
                      refine ⟨2808184620986848059048901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3744246161315797412065201 2808184620986848059048901)
                      ·
                        rfl

theorem cell23_5468920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 2, 2, 2, 2].length) (baseStart_5468920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5468920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5468920 prefixEnd_5468920 := by exact prefixLift 5468920
  have htrace : WordTrace (prefixWord ++ tailWord_5468920) baseStart_5468920 baseEnd_5468920 := by
    simpa [prefixWord, tailWord_5468920, baseEnd_5468920] using wordTrace_append hprefix tailTrace_5468920
  have hstable : (prefixWord ++ tailWord_5468920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5468920).length < 2 ^ (prefixWord ++ tailWord_5468920).sum := by decide
  have hdescent : baseEnd_5468920 < baseStart_5468920 := by decide
  rcases family_descends (prefixWord ++ tailWord_5468920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5468929 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 2, 1, 8]
def baseStart_5468929 : Nat := 118140960795 + 5468929 * 2 ^ 59
def prefixEnd_5468929 : Nat := 4983230072969 + 3 ^ 40 * 5468929 * 2
def baseEnd_5468929 : Nat := 2808189242312738523836359

theorem tailTrace_5468929 : CollatzResearch.WordTrace tailWord_5468929 prefixEnd_5468929 2808189242312738523836359 := by
  unfold tailWord_5468929
  simp only [CollatzResearch.WordTrace]
  refine ⟨199468227604011726557281841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132978818402674484371521227 199468227604011726557281841)
  ·
    refine ⟨149601170703008794917961381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199468227604011726557281841 149601170703008794917961381)
    ·
      refine ⟨28050219506814149047117759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149601170703008794917961381 28050219506814149047117759)
      ·
        refine ⟨42075329260221223570676639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28050219506814149047117759 42075329260221223570676639)
        ·
          refine ⟨63112993890331835356014959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42075329260221223570676639 63112993890331835356014959)
          ·
            refine ⟨94669490835497753034022439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63112993890331835356014959 94669490835497753034022439)
            ·
              refine ⟨142004236253246629551033659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94669490835497753034022439 142004236253246629551033659)
              ·
                refine ⟨213006354379869944326550489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142004236253246629551033659 213006354379869944326550489)
                ·
                  refine ⟨159754765784902458244912867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 213006354379869944326550489 159754765784902458244912867)
                  ·
                    refine ⟨239632148677353687367369301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 159754765784902458244912867 239632148677353687367369301)
                    ·
                      refine ⟨2808189242312738523836359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 239632148677353687367369301 2808189242312738523836359)
                      ·
                        rfl

theorem cell23_5468929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_5468929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5468929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5468929 prefixEnd_5468929 := by exact prefixLift 5468929
  have htrace : WordTrace (prefixWord ++ tailWord_5468929) baseStart_5468929 baseEnd_5468929 := by
    simpa [prefixWord, tailWord_5468929, baseEnd_5468929] using wordTrace_append hprefix tailTrace_5468929
  have hstable : (prefixWord ++ tailWord_5468929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5468929).length < 2 ^ (prefixWord ++ tailWord_5468929).sum := by decide
  have hdescent : baseEnd_5468929 < baseStart_5468929 := by decide
  rcases family_descends (prefixWord ++ tailWord_5468929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5468936 : List Nat := [2, 1, 3, 2, 2, 2, 1, 1, 1, 5, 3]
def baseStart_5468936 : Nat := 118140960795 + 5468936 * 2 ^ 59
def prefixEnd_5468936 : Nat := 4983230072969 + 3 ^ 40 * 5468936 * 2
def baseEnd_5468936 : Nat := 2808192836677319996448827

theorem tailTrace_5468936 : CollatzResearch.WordTrace tailWord_5468936 prefixEnd_5468936 2808192836677319996448827 := by
  unfold tailWord_5468936
  simp only [CollatzResearch.WordTrace]
  refine ⟨99734241457493183376393331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132978988609990911168524441 99734241457493183376393331)
  ·
    refine ⟨149601362186239775064589997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99734241457493183376393331 149601362186239775064589997)
    ·
      refine ⟨56100510819839915649221249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149601362186239775064589997 56100510819839915649221249)
      ·
        refine ⟨42075383114879936736915937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56100510819839915649221249 42075383114879936736915937)
        ·
          refine ⟨31556537336159952552686953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42075383114879936736915937 31556537336159952552686953)
          ·
            refine ⟨23667403002119964414515215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31556537336159952552686953 23667403002119964414515215)
            ·
              refine ⟨35501104503179946621772823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23667403002119964414515215 35501104503179946621772823)
              ·
                refine ⟨53251656754769919932659235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35501104503179946621772823 53251656754769919932659235)
                ·
                  refine ⟨79877485132154879898988853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53251656754769919932659235 79877485132154879898988853)
                  ·
                    refine ⟨7488514231139519990530205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 79877485132154879898988853 7488514231139519990530205)
                    ·
                      refine ⟨2808192836677319996448827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7488514231139519990530205 2808192836677319996448827)
                      ·
                        rfl

theorem cell23_5468936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_5468936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5468936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5468936 prefixEnd_5468936 := by exact prefixLift 5468936
  have htrace : WordTrace (prefixWord ++ tailWord_5468936) baseStart_5468936 baseEnd_5468936 := by
    simpa [prefixWord, tailWord_5468936, baseEnd_5468936] using wordTrace_append hprefix tailTrace_5468936
  have hstable : (prefixWord ++ tailWord_5468936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5468936).length < 2 ^ (prefixWord ++ tailWord_5468936).sum := by decide
  have hdescent : baseEnd_5468936 < baseStart_5468936 := by decide
  rcases family_descends (prefixWord ++ tailWord_5468936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5468939 : List Nat := [1, 1, 1, 1, 5, 1, 1, 4, 1, 7]
def baseStart_5468939 : Nat := 118140960795 + 5468939 * 2 ^ 59
def prefixEnd_5468939 : Nat := 4983230072969 + 3 ^ 40 * 5468939 * 2
def baseEnd_5468939 : Nat := 936064792373094494903771

theorem tailTrace_5468939 : CollatzResearch.WordTrace tailWord_5468939 prefixEnd_5468939 936064792373094494903771 := by
  unfold tailWord_5468939
  simp only [CollatzResearch.WordTrace]
  refine ⟨199468592333975498265145871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132979061555983665510097247 199468592333975498265145871)
  ·
    refine ⟨299202888500963247397718807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199468592333975498265145871 299202888500963247397718807)
    ·
      refine ⟨448804332751444871096578211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299202888500963247397718807 448804332751444871096578211)
      ·
        refine ⟨673206499127167306644867317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 448804332751444871096578211 673206499127167306644867317)
        ·
          refine ⟨63113109293171934997956311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 673206499127167306644867317 63113109293171934997956311)
          ·
            refine ⟨94669663939757902496934467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63113109293171934997956311 94669663939757902496934467)
            ·
              refine ⟨142004495909636853745401701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94669663939757902496934467 142004495909636853745401701)
              ·
                refine ⟨26625842983056910077262819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 142004495909636853745401701 26625842983056910077262819)
                ·
                  refine ⟨39938764474585365115894229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26625842983056910077262819 39938764474585365115894229)
                  ·
                    refine ⟨936064792373094494903771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39938764474585365115894229 936064792373094494903771)
                    ·
                      rfl

theorem cell23_5468939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 7].length) (baseStart_5468939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5468939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5468939 prefixEnd_5468939 := by exact prefixLift 5468939
  have htrace : WordTrace (prefixWord ++ tailWord_5468939) baseStart_5468939 baseEnd_5468939 := by
    simpa [prefixWord, tailWord_5468939, baseEnd_5468939] using wordTrace_append hprefix tailTrace_5468939
  have hstable : (prefixWord ++ tailWord_5468939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5468939).length < 2 ^ (prefixWord ++ tailWord_5468939).sum := by decide
  have hdescent : baseEnd_5468939 < baseStart_5468939 := by decide
  rcases family_descends (prefixWord ++ tailWord_5468939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5468956 : List Nat := [2, 2, 3, 1, 1, 4, 1, 1, 1, 7]
def baseStart_5468956 : Nat := 118140960795 + 5468956 * 2 ^ 59
def prefixEnd_5468956 : Nat := 4983230072969 + 3 ^ 40 * 5468956 * 2
def baseEnd_5468956 : Nat := 936067702096803306066245

theorem tailTrace_5468956 : CollatzResearch.WordTrace tailWord_5468956 prefixEnd_5468956 936067702096803306066245 := by
  unfold tailWord_5468956
  simp only [CollatzResearch.WordTrace]
  refine ⟨99734606187456955084257361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132979474916609273445676481 99734606187456955084257361)
  ·
    refine ⟨74800954640592716313193021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99734606187456955084257361 74800954640592716313193021)
    ·
      refine ⟨28050357990222268617447383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74800954640592716313193021 28050357990222268617447383)
      ·
        refine ⟨42075536985333402926171075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28050357990222268617447383 42075536985333402926171075)
        ·
          refine ⟨63113305478000104389256613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42075536985333402926171075 63113305478000104389256613)
          ·
            refine ⟨11833744777125019572985615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63113305478000104389256613 11833744777125019572985615)
            ·
              refine ⟨17750617165687529359478423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11833744777125019572985615 17750617165687529359478423)
              ·
                refine ⟨26625925748531294039217635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17750617165687529359478423 26625925748531294039217635)
                ·
                  refine ⟨39938888622796941058826453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26625925748531294039217635 39938888622796941058826453)
                  ·
                    refine ⟨936067702096803306066245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39938888622796941058826453 936067702096803306066245)
                    ·
                      rfl

theorem cell23_5468956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_5468956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5468956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5468956 prefixEnd_5468956 := by exact prefixLift 5468956
  have htrace : WordTrace (prefixWord ++ tailWord_5468956) baseStart_5468956 baseEnd_5468956 := by
    simpa [prefixWord, tailWord_5468956, baseEnd_5468956] using wordTrace_append hprefix tailTrace_5468956
  have hstable : (prefixWord ++ tailWord_5468956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5468956).length < 2 ^ (prefixWord ++ tailWord_5468956).sum := by decide
  have hdescent : baseEnd_5468956 < baseStart_5468956 := by decide
  rcases family_descends (prefixWord ++ tailWord_5468956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5468976 : List Nat := [2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 4]
def baseStart_5468976 : Nat := 118140960795 + 5468976 * 2 ^ 59
def prefixEnd_5468976 : Nat := 4983230072969 + 3 ^ 40 * 5468976 * 2
def baseEnd_5468976 : Nat := 2808213375903499839948643

theorem tailTrace_5468976 : CollatzResearch.WordTrace tailWord_5468976 prefixEnd_5468976 2808213375903499839948643 := by
  unfold tailWord_5468976
  simp only [CollatzResearch.WordTrace]
  refine ⟨99734970917420726792121391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132979961223227635722828521 99734970917420726792121391)
  ·
    refine ⟨149602456376131090188182087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99734970917420726792121391 149602456376131090188182087)
    ·
      refine ⟨224403684564196635282273131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149602456376131090188182087 224403684564196635282273131)
      ·
        refine ⟨336605526846294952923409697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224403684564196635282273131 336605526846294952923409697)
        ·
          refine ⟨252454145134721214692557273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 336605526846294952923409697 252454145134721214692557273)
          ·
            refine ⟨189340608851040911019417955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 252454145134721214692557273 189340608851040911019417955)
            ·
              refine ⟨284010913276561366529126933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189340608851040911019417955 284010913276561366529126933)
              ·
                refine ⟨13313011559838814056052825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 284010913276561366529126933 13313011559838814056052825)
                ·
                  refine ⟨9984758669879110542039619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13313011559838814056052825 9984758669879110542039619)
                  ·
                    refine ⟨14977138004818665813059429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9984758669879110542039619 14977138004818665813059429)
                    ·
                      refine ⟨2808213375903499839948643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14977138004818665813059429 2808213375903499839948643)
                      ·
                        rfl

theorem cell23_5468976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 4].length) (baseStart_5468976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5468976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5468976 prefixEnd_5468976 := by exact prefixLift 5468976
  have htrace : WordTrace (prefixWord ++ tailWord_5468976) baseStart_5468976 baseEnd_5468976 := by
    simpa [prefixWord, tailWord_5468976, baseEnd_5468976] using wordTrace_append hprefix tailTrace_5468976
  have hstable : (prefixWord ++ tailWord_5468976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5468976).length < 2 ^ (prefixWord ++ tailWord_5468976).sum := by decide
  have hdescent : baseEnd_5468976 < baseStart_5468976 := by decide
  rcases family_descends (prefixWord ++ tailWord_5468976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5469013 : List Nat := [1, 3, 2, 2, 2, 1, 2, 3, 2, 2, 3]
def baseStart_5469013 : Nat := 118140960795 + 5469013 * 2 ^ 59
def prefixEnd_5469013 : Nat := 4983230072969 + 3 ^ 40 * 5469013 * 2
def baseEnd_5469013 : Nat := 2808232374687716195185973

theorem tailTrace_5469013 : CollatzResearch.WordTrace tailWord_5469013 prefixEnd_5469013 2808232374687716195185973 := by
  unfold tailWord_5469013
  simp only [CollatzResearch.WordTrace]
  refine ⟨199471291335707408903339693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132980860890471605935559795 199471291335707408903339693)
  ·
    refine ⟨74801734250890278338752385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199471291335707408903339693 74801734250890278338752385)
    ·
      refine ⟨56101300688167708754064289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74801734250890278338752385 56101300688167708754064289)
      ·
        refine ⟨42075975516125781565548217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56101300688167708754064289 42075975516125781565548217)
        ·
          refine ⟨31556981637094336174161163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42075975516125781565548217 31556981637094336174161163)
          ·
            refine ⟨47335472455641504261241745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31556981637094336174161163 47335472455641504261241745)
            ·
              refine ⟨35501604341731128195931309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47335472455641504261241745 35501604341731128195931309)
              ·
                refine ⟨13313101628149173073474241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35501604341731128195931309 13313101628149173073474241)
                ·
                  refine ⟨9984826221111879805105681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13313101628149173073474241 9984826221111879805105681)
                  ·
                    refine ⟨7488619665833909853829261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9984826221111879805105681 7488619665833909853829261)
                    ·
                      refine ⟨2808232374687716195185973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7488619665833909853829261 2808232374687716195185973)
                      ·
                        rfl

theorem cell23_5469013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_5469013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5469013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5469013 prefixEnd_5469013 := by exact prefixLift 5469013
  have htrace : WordTrace (prefixWord ++ tailWord_5469013) baseStart_5469013 baseEnd_5469013 := by
    simpa [prefixWord, tailWord_5469013, baseEnd_5469013] using wordTrace_append hprefix tailTrace_5469013
  have hstable : (prefixWord ++ tailWord_5469013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5469013).length < 2 ^ (prefixWord ++ tailWord_5469013).sum := by decide
  have hdescent : baseEnd_5469013 < baseStart_5469013 := by decide
  rcases family_descends (prefixWord ++ tailWord_5469013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5469053 : List Nat := [1, 4, 1, 1, 2, 1, 2, 1, 3, 5, 2]
def baseStart_5469053 : Nat := 118140960795 + 5469053 * 2 ^ 59
def prefixEnd_5469053 : Nat := 4983230072969 + 3 ^ 40 * 5469053 * 2
def baseEnd_5469053 : Nat := 2808252913913896038685789

theorem tailTrace_5469053 : CollatzResearch.WordTrace tailWord_5469053 prefixEnd_5469053 2808252913913896038685789 := by
  unfold tailWord_5469053
  simp only [CollatzResearch.WordTrace]
  refine ⟨199472750255562495734795813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132981833503708330489863875 199472750255562495734795813)
  ·
    refine ⟨37401140672917967950274215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 199472750255562495734795813 37401140672917967950274215)
    ·
      refine ⟨56101711009376951925411323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37401140672917967950274215 56101711009376951925411323)
      ·
        refine ⟨84152566514065427888116985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56101711009376951925411323 84152566514065427888116985)
        ·
          refine ⟨63114424885549070916087739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84152566514065427888116985 63114424885549070916087739)
          ·
            refine ⟨94671637328323606374131609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63114424885549070916087739 94671637328323606374131609)
            ·
              refine ⟨71003727996242704780598707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94671637328323606374131609 71003727996242704780598707)
              ·
                refine ⟨106505591994364057170898061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71003727996242704780598707 106505591994364057170898061)
                ·
                  refine ⟨39939596997886521439086773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106505591994364057170898061 39939596997886521439086773)
                  ·
                    refine ⟨3744337218551861384914385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39939596997886521439086773 3744337218551861384914385)
                    ·
                      refine ⟨2808252913913896038685789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3744337218551861384914385 2808252913913896038685789)
                      ·
                        rfl

theorem cell23_5469053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 5, 2].length) (baseStart_5469053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5469053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5469053 prefixEnd_5469053 := by exact prefixLift 5469053
  have htrace : WordTrace (prefixWord ++ tailWord_5469053) baseStart_5469053 baseEnd_5469053 := by
    simpa [prefixWord, tailWord_5469053, baseEnd_5469053] using wordTrace_append hprefix tailTrace_5469053
  have hstable : (prefixWord ++ tailWord_5469053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5469053).length < 2 ^ (prefixWord ++ tailWord_5469053).sum := by decide
  have hdescent : baseEnd_5469053 < baseStart_5469053 := by decide
  rcases family_descends (prefixWord ++ tailWord_5469053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5469063 : List Nat := [1, 1, 4, 2, 3, 2, 1, 1, 3, 5]
def baseStart_5469063 : Nat := 118140960795 + 5469063 * 2 ^ 59
def prefixEnd_5469063 : Nat := 4983230072969 + 3 ^ 40 * 5469063 * 2
def baseEnd_5469063 : Nat := 936086016240146999853581

theorem tailTrace_5469063 : CollatzResearch.WordTrace tailWord_5469063 prefixEnd_5469063 936086016240146999853581 := by
  unfold tailWord_5469063
  simp only [CollatzResearch.WordTrace]
  refine ⟨199473114985526267442659843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132982076657017511628439895 199473114985526267442659843)
  ·
    refine ⟨299209672478289401163989765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199473114985526267442659843 299209672478289401163989765)
    ·
      refine ⟨56101813589679262718248081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 299209672478289401163989765 56101813589679262718248081)
      ·
        refine ⟨42076360192259447038686061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56101813589679262718248081 42076360192259447038686061)
        ·
          refine ⟨15778635072097292639507273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42076360192259447038686061 15778635072097292639507273)
          ·
            refine ⟨11833976304072969479630455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15778635072097292639507273 11833976304072969479630455)
            ·
              refine ⟨17750964456109454219445683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11833976304072969479630455 17750964456109454219445683)
              ·
                refine ⟨26626446684164181329168525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17750964456109454219445683 26626446684164181329168525)
                ·
                  refine ⟨9984917506561567998438197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26626446684164181329168525 9984917506561567998438197)
                  ·
                    refine ⟨936086016240146999853581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9984917506561567998438197 936086016240146999853581)
                    ·
                      rfl

theorem cell23_5469063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 3, 5].length) (baseStart_5469063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5469063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5469063 prefixEnd_5469063 := by exact prefixLift 5469063
  have htrace : WordTrace (prefixWord ++ tailWord_5469063) baseStart_5469063 baseEnd_5469063 := by
    simpa [prefixWord, tailWord_5469063, baseEnd_5469063] using wordTrace_append hprefix tailTrace_5469063
  have hstable : (prefixWord ++ tailWord_5469063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5469063).length < 2 ^ (prefixWord ++ tailWord_5469063).sum := by decide
  have hdescent : baseEnd_5469063 < baseStart_5469063 := by decide
  rcases family_descends (prefixWord ++ tailWord_5469063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5469113 : List Nat := [1, 2, 1, 4, 2, 2, 1, 3, 1, 2, 4]
def baseStart_5469113 : Nat := 118140960795 + 5469113 * 2 ^ 59
def prefixEnd_5469113 : Nat := 4983230072969 + 3 ^ 40 * 5469113 * 2
def baseEnd_5469113 : Nat := 2808283722753165803935513

theorem tailTrace_5469113 : CollatzResearch.WordTrace tailWord_5469113 prefixEnd_5469113 2808283722753165803935513 := by
  unfold tailWord_5469113
  simp only [CollatzResearch.WordTrace]
  refine ⟨199474938635345125981979993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132983292423563417321319995 199474938635345125981979993)
  ·
    refine ⟨149606203976508844486484995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199474938635345125981979993 149606203976508844486484995)
    ·
      refine ⟨224409305964763266729727493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149606203976508844486484995 224409305964763266729727493)
      ·
        refine ⟨42076744868393112511823905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 224409305964763266729727493 42076744868393112511823905)
        ·
          refine ⟨31557558651294834383867929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42076744868393112511823905 31557558651294834383867929)
          ·
            refine ⟨23668168988471125787900947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31557558651294834383867929 23668168988471125787900947)
            ·
              refine ⟨35502253482706688681851421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23668168988471125787900947 35502253482706688681851421)
              ·
                refine ⟨13313345056015008255694283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35502253482706688681851421 13313345056015008255694283)
                ·
                  refine ⟨19970017584022512383541425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13313345056015008255694283 19970017584022512383541425)
                  ·
                    refine ⟨14977513188016884287656069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19970017584022512383541425 14977513188016884287656069)
                    ·
                      refine ⟨2808283722753165803935513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14977513188016884287656069 2808283722753165803935513)
                      ·
                        rfl

theorem cell23_5469113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_5469113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5469113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5469113 prefixEnd_5469113 := by exact prefixLift 5469113
  have htrace : WordTrace (prefixWord ++ tailWord_5469113) baseStart_5469113 baseEnd_5469113 := by
    simpa [prefixWord, tailWord_5469113, baseEnd_5469113] using wordTrace_append hprefix tailTrace_5469113
  have hstable : (prefixWord ++ tailWord_5469113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5469113).length < 2 ^ (prefixWord ++ tailWord_5469113).sum := by decide
  have hdescent : baseEnd_5469113 < baseStart_5469113 := by decide
  rcases family_descends (prefixWord ++ tailWord_5469113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5469134 : List Nat := [4, 1, 1, 1, 2, 3, 1, 5, 1, 2, 2]
def baseStart_5469134 : Nat := 118140960795 + 5469134 * 2 ^ 59
def prefixEnd_5469134 : Nat := 4983230072969 + 3 ^ 40 * 5469134 * 2
def baseEnd_5469134 : Nat := 2808294505846910221772917

theorem tailTrace_5469134 : CollatzResearch.WordTrace tailWord_5469134 prefixEnd_5469134 2808294505846910221772917 := by
  unfold tailWord_5469134
  simp only [CollatzResearch.WordTrace]
  refine ⟨24934463071033630821061807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132983803045512697712329637 24934463071033630821061807)
  ·
    refine ⟨37401694606550446231592711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24934463071033630821061807 37401694606550446231592711)
    ·
      refine ⟨56102541909825669347389067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37401694606550446231592711 56102541909825669347389067)
      ·
        refine ⟨84153812864738504021083601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56102541909825669347389067 84153812864738504021083601)
        ·
          refine ⟨63115359648553878015812701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84153812864738504021083601 63115359648553878015812701)
          ·
            refine ⟨23668259868207704255929763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63115359648553878015812701 23668259868207704255929763)
            ·
              refine ⟨35502389802311556383894645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23668259868207704255929763 35502389802311556383894645)
              ·
                refine ⟨3328349043966708410990123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35502389802311556383894645 3328349043966708410990123)
                ·
                  refine ⟨4992523565950062616485185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3328349043966708410990123 4992523565950062616485185)
                  ·
                    refine ⟨3744392674462546962363889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4992523565950062616485185 3744392674462546962363889)
                    ·
                      refine ⟨2808294505846910221772917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3744392674462546962363889 2808294505846910221772917)
                      ·
                        rfl

theorem cell23_5469134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 5, 1, 2, 2].length) (baseStart_5469134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5469134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5469134 prefixEnd_5469134 := by exact prefixLift 5469134
  have htrace : WordTrace (prefixWord ++ tailWord_5469134) baseStart_5469134 baseEnd_5469134 := by
    simpa [prefixWord, tailWord_5469134, baseEnd_5469134] using wordTrace_append hprefix tailTrace_5469134
  have hstable : (prefixWord ++ tailWord_5469134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5469134).length < 2 ^ (prefixWord ++ tailWord_5469134).sum := by decide
  have hdescent : baseEnd_5469134 < baseStart_5469134 := by decide
  rcases family_descends (prefixWord ++ tailWord_5469134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5469160 : List Nat := [2, 1, 4, 1, 1, 1, 2, 1, 5, 3, 2]
def baseStart_5469160 : Nat := 118140960795 + 5469160 * 2 ^ 59
def prefixEnd_5469160 : Nat := 4983230072969 + 3 ^ 40 * 5469160 * 2
def baseEnd_5469160 : Nat := 2808307856343927120047797

theorem tailTrace_5469160 : CollatzResearch.WordTrace tailWord_5469160 prefixEnd_5469160 2808307856343927120047797 := by
  unfold tailWord_5469160
  simp only [CollatzResearch.WordTrace]
  refine ⟨99738326433087426504470467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132984435244116568672627289 99738326433087426504470467)
  ·
    refine ⟨149607489649631139756705701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99738326433087426504470467 149607489649631139756705701)
    ·
      refine ⟨28051404309305838704382319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149607489649631139756705701 28051404309305838704382319)
      ·
        refine ⟨42077106463958758056573479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28051404309305838704382319 42077106463958758056573479)
        ·
          refine ⟨63115659695938137084860219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42077106463958758056573479 63115659695938137084860219)
          ·
            refine ⟨94673489543907205627290329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63115659695938137084860219 94673489543907205627290329)
            ·
              refine ⟨71005117157930404220467747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94673489543907205627290329 71005117157930404220467747)
              ·
                refine ⟨106507675736895606330701621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71005117157930404220467747 106507675736895606330701621)
                ·
                  refine ⟨9985094600333963093503277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 106507675736895606330701621 9985094600333963093503277)
                  ·
                    refine ⟨3744410475125236160063729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9985094600333963093503277 3744410475125236160063729)
                    ·
                      refine ⟨2808307856343927120047797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3744410475125236160063729 2808307856343927120047797)
                      ·
                        rfl

theorem cell23_5469160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 5, 3, 2].length) (baseStart_5469160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5469160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5469160 prefixEnd_5469160 := by exact prefixLift 5469160
  have htrace : WordTrace (prefixWord ++ tailWord_5469160) baseStart_5469160 baseEnd_5469160 := by
    simpa [prefixWord, tailWord_5469160, baseEnd_5469160] using wordTrace_append hprefix tailTrace_5469160
  have hstable : (prefixWord ++ tailWord_5469160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5469160).length < 2 ^ (prefixWord ++ tailWord_5469160).sum := by decide
  have hdescent : baseEnd_5469160 < baseStart_5469160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5469160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5469177 : List Nat := [1, 2, 1, 3, 1, 3, 4, 2, 1, 3, 2]
def baseStart_5469177 : Nat := 118140960795 + 5469177 * 2 ^ 59
def prefixEnd_5469177 : Nat := 4983230072969 + 3 ^ 40 * 5469177 * 2
def baseEnd_5469177 : Nat := 2808316585515053553535219

theorem tailTrace_5469177 : CollatzResearch.WordTrace tailWord_5469177 prefixEnd_5469177 2808316585515053553535219 := by
  unfold tailWord_5469177
  simp only [CollatzResearch.WordTrace]
  refine ⟨199477272907113264912309785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132984848604742176608206523 199477272907113264912309785)
  ·
    refine ⟨149607954680334948684232339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199477272907113264912309785 149607954680334948684232339)
    ·
      refine ⟨224411932020502423026348509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149607954680334948684232339 224411932020502423026348509)
      ·
        refine ⟨84154474507688408634880691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 224411932020502423026348509 84154474507688408634880691)
        ·
          refine ⟨126231711761532612952321037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84154474507688408634880691 126231711761532612952321037)
          ·
            refine ⟨47336891910574729857120389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126231711761532612952321037 47336891910574729857120389)
            ·
              refine ⟨8875667233232761848210073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47336891910574729857120389 8875667233232761848210073)
              ·
                refine ⟨6656750424924571386157555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8875667233232761848210073 6656750424924571386157555)
                ·
                  refine ⟨9985125637386857079236333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6656750424924571386157555 9985125637386857079236333)
                  ·
                    refine ⟨3744422114020071404713625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9985125637386857079236333 3744422114020071404713625)
                    ·
                      refine ⟨2808316585515053553535219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3744422114020071404713625 2808316585515053553535219)
                      ·
                        rfl

theorem cell23_5469177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 2, 1, 3, 2].length) (baseStart_5469177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5469177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5469177 prefixEnd_5469177 := by exact prefixLift 5469177
  have htrace : WordTrace (prefixWord ++ tailWord_5469177) baseStart_5469177 baseEnd_5469177 := by
    simpa [prefixWord, tailWord_5469177, baseEnd_5469177] using wordTrace_append hprefix tailTrace_5469177
  have hstable : (prefixWord ++ tailWord_5469177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5469177).length < 2 ^ (prefixWord ++ tailWord_5469177).sum := by decide
  have hdescent : baseEnd_5469177 < baseStart_5469177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5469177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5469202 : List Nat := [3, 2, 5, 1, 1, 1, 3, 2, 1, 2, 2]
def baseStart_5469202 : Nat := 118140960795 + 5469202 * 2 ^ 59
def prefixEnd_5469202 : Nat := 4983230072969 + 3 ^ 40 * 5469202 * 2
def baseEnd_5469202 : Nat := 2808329422531415955722605

theorem tailTrace_5469202 : CollatzResearch.WordTrace tailWord_5469202 prefixEnd_5469202 2808329422531415955722605 := by
  unfold tailWord_5469202
  simp only [CollatzResearch.WordTrace]
  refine ⟨49869546183005673545492465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132985456488015129454646573 49869546183005673545492465)
  ·
    refine ⟨37402159637254255159119349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49869546183005673545492465 37402159637254255159119349)
    ·
      refine ⟨3506452465992586421167439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37402159637254255159119349 3506452465992586421167439)
      ·
        refine ⟨5259678698988879631751159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3506452465992586421167439 5259678698988879631751159)
        ·
          refine ⟨7889518048483319447626739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5259678698988879631751159 7889518048483319447626739)
          ·
            refine ⟨11834277072724979171440109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7889518048483319447626739 11834277072724979171440109)
            ·
              refine ⟨4437853902271867189290041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11834277072724979171440109 4437853902271867189290041)
              ·
                refine ⟨3328390426703900391967531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4437853902271867189290041 3328390426703900391967531)
                ·
                  refine ⟨4992585640055850587951297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3328390426703900391967531 4992585640055850587951297)
                  ·
                    refine ⟨3744439230041887940963473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4992585640055850587951297 3744439230041887940963473)
                    ·
                      refine ⟨2808329422531415955722605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3744439230041887940963473 2808329422531415955722605)
                      ·
                        rfl

theorem cell23_5469202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_5469202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5469202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5469202 prefixEnd_5469202 := by exact prefixLift 5469202
  have htrace : WordTrace (prefixWord ++ tailWord_5469202) baseStart_5469202 baseEnd_5469202 := by
    simpa [prefixWord, tailWord_5469202, baseEnd_5469202] using wordTrace_append hprefix tailTrace_5469202
  have hstable : (prefixWord ++ tailWord_5469202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5469202).length < 2 ^ (prefixWord ++ tailWord_5469202).sum := by decide
  have hdescent : baseEnd_5469202 < baseStart_5469202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5469202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5469253 : List Nat := [1, 3, 1, 1, 1, 3, 3, 2, 1, 2, 5]
def baseStart_5469253 : Nat := 118140960795 + 5469253 * 2 ^ 59
def prefixEnd_5469253 : Nat := 4983230072969 + 3 ^ 40 * 5469253 * 2
def baseEnd_5469253 : Nat := 2808355610044795256184869

theorem tailTrace_5469253 : CollatzResearch.WordTrace tailWord_5469253 prefixEnd_5469253 2808355610044795256184869 := by
  unfold tailWord_5469253
  simp only [CollatzResearch.WordTrace]
  refine ⟨199480044854837929892076413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132986696569891953261384275 199480044854837929892076413)
  ·
    refine ⟨74805016820564223709528655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199480044854837929892076413 74805016820564223709528655)
    ·
      refine ⟨112207525230846335564292983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74805016820564223709528655 112207525230846335564292983)
      ·
        refine ⟨168311287846269503346439475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112207525230846335564292983 168311287846269503346439475)
        ·
          refine ⟨252466931769404255019659213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168311287846269503346439475 252466931769404255019659213)
          ·
            refine ⟨94675099413526595632372205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 252466931769404255019659213 94675099413526595632372205)
            ·
              refine ⟨35503162280072473362139577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94675099413526595632372205 35503162280072473362139577)
              ·
                refine ⟨26627371710054355021604683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35503162280072473362139577 26627371710054355021604683)
                ·
                  refine ⟨39941057565081532532407025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26627371710054355021604683 39941057565081532532407025)
                  ·
                    refine ⟨29955793173811149399305269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39941057565081532532407025 29955793173811149399305269)
                    ·
                      refine ⟨2808355610044795256184869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29955793173811149399305269 2808355610044795256184869)
                      ·
                        rfl

theorem cell23_5469253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 2, 5].length) (baseStart_5469253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5469253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5469253 prefixEnd_5469253 := by exact prefixLift 5469253
  have htrace : WordTrace (prefixWord ++ tailWord_5469253) baseStart_5469253 baseEnd_5469253 := by
    simpa [prefixWord, tailWord_5469253, baseEnd_5469253] using wordTrace_append hprefix tailTrace_5469253
  have hstable : (prefixWord ++ tailWord_5469253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5469253).length < 2 ^ (prefixWord ++ tailWord_5469253).sum := by decide
  have hdescent : baseEnd_5469253 < baseStart_5469253 := by decide
  rcases family_descends (prefixWord ++ tailWord_5469253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5469303 : List Nat := [1, 1, 3, 1, 1, 4, 2, 2, 8]
def baseStart_5469303 : Nat := 118140960795 + 5469303 * 2 ^ 59
def prefixEnd_5469303 : Nat := 4983230072969 + 3 ^ 40 * 5469303 * 2
def baseEnd_5469303 : Nat := 312042364897502228951071

theorem tailTrace_5469303 : CollatzResearch.WordTrace tailWord_5469303 prefixEnd_5469303 312042364897502228951071 := by
  unfold tailWord_5469303
  simp only [CollatzResearch.WordTrace]
  refine ⟨199481868504656788431396563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132987912336437858954264375 199481868504656788431396563)
  ·
    refine ⟨299222802756985182647094845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199481868504656788431396563 299222802756985182647094845)
    ·
      refine ⟨112208551033869443492660567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 299222802756985182647094845 112208551033869443492660567)
      ·
        refine ⟨168312826550804165238990851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112208551033869443492660567 168312826550804165238990851)
        ·
          refine ⟨252469239826206247858486277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168312826550804165238990851 252469239826206247858486277)
          ·
            refine ⟨47337982467413671473466177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 252469239826206247858486277 47337982467413671473466177)
            ·
              refine ⟨35503486850560253605099633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47337982467413671473466177 35503486850560253605099633)
              ·
                refine ⟨26627615137920190203824725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35503486850560253605099633 26627615137920190203824725)
                ·
                  refine ⟨312042364897502228951071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26627615137920190203824725 312042364897502228951071)
                  ·
                    rfl

theorem cell23_5469303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 8].length) (baseStart_5469303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5469303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5469303 prefixEnd_5469303 := by exact prefixLift 5469303
  have htrace : WordTrace (prefixWord ++ tailWord_5469303) baseStart_5469303 baseEnd_5469303 := by
    simpa [prefixWord, tailWord_5469303, baseEnd_5469303] using wordTrace_append hprefix tailTrace_5469303
  have hstable : (prefixWord ++ tailWord_5469303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5469303).length < 2 ^ (prefixWord ++ tailWord_5469303).sum := by decide
  have hdescent : baseEnd_5469303 < baseStart_5469303 := by decide
  rcases family_descends (prefixWord ++ tailWord_5469303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5469333 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 2, 9]
def baseStart_5469333 : Nat := 118140960795 + 5469333 * 2 ^ 59
def prefixEnd_5469333 : Nat := 4983230072969 + 3 ^ 40 * 5469333 * 2
def baseEnd_5469333 : Nat := 936132229499051647728167

theorem tailTrace_5469333 : CollatzResearch.WordTrace tailWord_5469333 prefixEnd_5469333 936132229499051647728167 := by
  unfold tailWord_5469333
  simp only [CollatzResearch.WordTrace]
  refine ⟨199482962694548103554988653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132988641796365402369992435 199482962694548103554988653)
  ·
    refine ⟨74806111010455538833120745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199482962694548103554988653 74806111010455538833120745)
    ·
      refine ⟨56104583257841654124840559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74806111010455538833120745 56104583257841654124840559)
      ·
        refine ⟨84156874886762481187260839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56104583257841654124840559 84156874886762481187260839)
        ·
          refine ⟨126235312330143721780891259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84156874886762481187260839 126235312330143721780891259)
          ·
            refine ⟨189352968495215582671336889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126235312330143721780891259 189352968495215582671336889)
            ·
              refine ⟨142014726371411687003502667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189352968495215582671336889 142014726371411687003502667)
              ·
                refine ⟨213022089557117530505254001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142014726371411687003502667 213022089557117530505254001)
                ·
                  refine ⟨159766567167838147878940501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 213022089557117530505254001 159766567167838147878940501)
                  ·
                    refine ⟨936132229499051647728167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 159766567167838147878940501 936132229499051647728167)
                    ·
                      rfl

theorem cell23_5469333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 9].length) (baseStart_5469333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5469333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5469333 prefixEnd_5469333 := by exact prefixLift 5469333
  have htrace : WordTrace (prefixWord ++ tailWord_5469333) baseStart_5469333 baseEnd_5469333 := by
    simpa [prefixWord, tailWord_5469333, baseEnd_5469333] using wordTrace_append hprefix tailTrace_5469333
  have hstable : (prefixWord ++ tailWord_5469333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5469333).length < 2 ^ (prefixWord ++ tailWord_5469333).sum := by decide
  have hdescent : baseEnd_5469333 < baseStart_5469333 := by decide
  rcases family_descends (prefixWord ++ tailWord_5469333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5469370 : List Nat := [3, 1, 1, 1, 2, 2, 1, 2, 5, 1, 4]
def baseStart_5469370 : Nat := 118140960795 + 5469370 * 2 ^ 59
def prefixEnd_5469370 : Nat := 4983230072969 + 3 ^ 40 * 5469370 * 2
def baseEnd_5469370 : Nat := 2808415687281371298421831

theorem tailTrace_5469370 : CollatzResearch.WordTrace tailWord_5469370 prefixEnd_5469370 2808415687281371298421831 := by
  unfold tailWord_5469370
  simp only [CollatzResearch.WordTrace]
  refine ⟨49871078048853514718521391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132989541463609372582723709 49871078048853514718521391)
  ·
    refine ⟨74806617073280272077782087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49871078048853514718521391 74806617073280272077782087)
    ·
      refine ⟨112209925609920408116673131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74806617073280272077782087 112209925609920408116673131)
      ·
        refine ⟨168314888414880612175009697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112209925609920408116673131 168314888414880612175009697)
        ·
          refine ⟨126236166311160459131257273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168314888414880612175009697 126236166311160459131257273)
          ·
            refine ⟨94677124733370344348442955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126236166311160459131257273 94677124733370344348442955)
            ·
              refine ⟨142015687100055516522664433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94677124733370344348442955 142015687100055516522664433)
              ·
                refine ⟨106511765325041637391998325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142015687100055516522664433 106511765325041637391998325)
                ·
                  refine ⟨9985477999222653505499843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 106511765325041637391998325 9985477999222653505499843)
                  ·
                    refine ⟨14978216998833980258249765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9985477999222653505499843 14978216998833980258249765)
                    ·
                      refine ⟨2808415687281371298421831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14978216998833980258249765 2808415687281371298421831)
                      ·
                        rfl

theorem cell23_5469370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 5, 1, 4].length) (baseStart_5469370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5469370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5469370 prefixEnd_5469370 := by exact prefixLift 5469370
  have htrace : WordTrace (prefixWord ++ tailWord_5469370) baseStart_5469370 baseEnd_5469370 := by
    simpa [prefixWord, tailWord_5469370, baseEnd_5469370] using wordTrace_append hprefix tailTrace_5469370
  have hstable : (prefixWord ++ tailWord_5469370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5469370).length < 2 ^ (prefixWord ++ tailWord_5469370).sum := by decide
  have hdescent : baseEnd_5469370 < baseStart_5469370 := by decide
  rcases family_descends (prefixWord ++ tailWord_5469370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5469374 : List Nat := [4, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2]
def baseStart_5469374 : Nat := 118140960795 + 5469374 * 2 ^ 59
def prefixEnd_5469374 : Nat := 4983230072969 + 3 ^ 40 * 5469374 * 2
def baseEnd_5469374 : Nat := 2808417741203989282771813

theorem tailTrace_5469374 : CollatzResearch.WordTrace tailWord_5469374 prefixEnd_5469374 2808417741203989282771813 := by
  unfold tailWord_5469374
  simp only [CollatzResearch.WordTrace]
  refine ⟨24935557260924945944653897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132989638724933045038154117 24935557260924945944653897)
  ·
    refine ⟨18701667945693709458490423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24935557260924945944653897 18701667945693709458490423)
    ·
      refine ⟨28052501918540564187735635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18701667945693709458490423 28052501918540564187735635)
      ·
        refine ⟨42078752877810846281603453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28052501918540564187735635 42078752877810846281603453)
        ·
          refine ⟨15779532329179067355601295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42078752877810846281603453 15779532329179067355601295)
          ·
            refine ⟨23669298493768601033401943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15779532329179067355601295 23669298493768601033401943)
            ·
              refine ⟨35503947740652901550102915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23669298493768601033401943 35503947740652901550102915)
              ·
                refine ⟨53255921610979352325154373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35503947740652901550102915 53255921610979352325154373)
                ·
                  refine ⟨9985485302058628560966445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53255921610979352325154373 9985485302058628560966445)
                  ·
                    refine ⟨3744556988271985710362417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9985485302058628560966445 3744556988271985710362417)
                    ·
                      refine ⟨2808417741203989282771813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3744556988271985710362417 2808417741203989282771813)
                      ·
                        rfl

theorem cell23_5469374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2].length) (baseStart_5469374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5469374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5469374 prefixEnd_5469374 := by exact prefixLift 5469374
  have htrace : WordTrace (prefixWord ++ tailWord_5469374) baseStart_5469374 baseEnd_5469374 := by
    simpa [prefixWord, tailWord_5469374, baseEnd_5469374] using wordTrace_append hprefix tailTrace_5469374
  have hstable : (prefixWord ++ tailWord_5469374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5469374).length < 2 ^ (prefixWord ++ tailWord_5469374).sum := by decide
  have hdescent : baseEnd_5469374 < baseStart_5469374 := by decide
  rcases family_descends (prefixWord ++ tailWord_5469374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5469421 : List Nat := [1, 5, 1, 2, 2, 2, 3, 1, 1, 1, 4]
def baseStart_5469421 : Nat := 118140960795 + 5469421 * 2 ^ 59
def prefixEnd_5469421 : Nat := 4983230072969 + 3 ^ 40 * 5469421 * 2
def baseEnd_5469421 : Nat := 2808441874794750598884097

theorem tailTrace_5469421 : CollatzResearch.WordTrace tailWord_5469421 prefixEnd_5469421 2808441874794750598884097 := by
  unfold tailWord_5469421
  simp only [CollatzResearch.WordTrace]
  refine ⟨199486172318229294584192117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132990781545486196389461411 199486172318229294584192117)
  ·
    refine ⟨18701828654833996367268011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 199486172318229294584192117 18701828654833996367268011)
    ·
      refine ⟨28052742982250994550902017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18701828654833996367268011 28052742982250994550902017)
      ·
        refine ⟨21039557236688245913176513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28052742982250994550902017 21039557236688245913176513)
        ·
          refine ⟨15779667927516184434882385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21039557236688245913176513 15779667927516184434882385)
          ·
            refine ⟨11834750945637138326161789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15779667927516184434882385 11834750945637138326161789)
            ·
              refine ⟨4438031604613926872310671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11834750945637138326161789 4438031604613926872310671)
              ·
                refine ⟨6657047406920890308466007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4438031604613926872310671 6657047406920890308466007)
                ·
                  refine ⟨9985571110381335462699011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6657047406920890308466007 9985571110381335462699011)
                  ·
                    refine ⟨14978356665572003194048517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9985571110381335462699011 14978356665572003194048517)
                    ·
                      refine ⟨2808441874794750598884097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14978356665572003194048517 2808441874794750598884097)
                      ·
                        rfl

theorem cell23_5469421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_5469421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5469421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5469421 prefixEnd_5469421 := by exact prefixLift 5469421
  have htrace : WordTrace (prefixWord ++ tailWord_5469421) baseStart_5469421 baseEnd_5469421 := by
    simpa [prefixWord, tailWord_5469421, baseEnd_5469421] using wordTrace_append hprefix tailTrace_5469421
  have hstable : (prefixWord ++ tailWord_5469421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5469421).length < 2 ^ (prefixWord ++ tailWord_5469421).sum := by decide
  have hdescent : baseEnd_5469421 < baseStart_5469421 := by decide
  rcases family_descends (prefixWord ++ tailWord_5469421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5469450 : List Nat := [3, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5]
def baseStart_5469450 : Nat := 118140960795 + 5469450 * 2 ^ 59
def prefixEnd_5469450 : Nat := 4983230072969 + 3 ^ 40 * 5469450 * 2
def baseEnd_5469450 : Nat := 2808456765733730985421463

theorem tailTrace_5469450 : CollatzResearch.WordTrace tailWord_5469450 prefixEnd_5469450 2808456765733730985421463 := by
  unfold tailWord_5469450
  simp only [CollatzResearch.WordTrace]
  refine ⟨49871807508781058134249451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132991486690082821691331869 49871807508781058134249451)
  ·
    refine ⟨74807711263171587201374177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49871807508781058134249451 74807711263171587201374177)
    ·
      refine ⟨56105783447378690401030633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74807711263171587201374177 56105783447378690401030633)
      ·
        refine ⟨42079337585534017800772975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56105783447378690401030633 42079337585534017800772975)
        ·
          refine ⟨63119006378301026701159463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42079337585534017800772975 63119006378301026701159463)
          ·
            refine ⟨94678509567451540051739195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63119006378301026701159463 94678509567451540051739195)
            ·
              refine ⟨142017764351177310077608793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94678509567451540051739195 142017764351177310077608793)
              ·
                refine ⟨106513323263382982558206595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142017764351177310077608793 106513323263382982558206595)
                ·
                  refine ⟨159769984895074473837309893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106513323263382982558206595 159769984895074473837309893)
                  ·
                    refine ⟨29956872167826463844495605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 159769984895074473837309893 29956872167826463844495605)
                    ·
                      refine ⟨2808456765733730985421463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29956872167826463844495605 2808456765733730985421463)
                      ·
                        rfl

theorem cell23_5469450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_5469450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5469450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5469450 prefixEnd_5469450 := by exact prefixLift 5469450
  have htrace : WordTrace (prefixWord ++ tailWord_5469450) baseStart_5469450 baseEnd_5469450 := by
    simpa [prefixWord, tailWord_5469450, baseEnd_5469450] using wordTrace_append hprefix tailTrace_5469450
  have hstable : (prefixWord ++ tailWord_5469450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5469450).length < 2 ^ (prefixWord ++ tailWord_5469450).sum := by decide
  have hdescent : baseEnd_5469450 < baseStart_5469450 := by decide
  rcases family_descends (prefixWord ++ tailWord_5469450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5469454 : List Nat := [4, 1, 1, 2, 1, 4, 2, 1, 1, 3, 3]
def baseStart_5469454 : Nat := 118140960795 + 5469454 * 2 ^ 59
def prefixEnd_5469454 : Nat := 4983230072969 + 3 ^ 40 * 5469454 * 2
def baseEnd_5469454 : Nat := 2808458819656348969771445

theorem tailTrace_5469454 : CollatzResearch.WordTrace tailWord_5469454 prefixEnd_5469454 2808458819656348969771445 := by
  unfold tailWord_5469454
  simp only [CollatzResearch.WordTrace]
  refine ⟨24935921990888717652517927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132991583951406494146762277 24935921990888717652517927)
  ·
    refine ⟨37403882986333076478776891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24935921990888717652517927 37403882986333076478776891)
    ·
      refine ⟨56105824479499614718165337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37403882986333076478776891 56105824479499614718165337)
      ·
        refine ⟨42079368359624711038624003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56105824479499614718165337 42079368359624711038624003)
        ·
          refine ⟨63119052539437066557936005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42079368359624711038624003 63119052539437066557936005)
          ·
            refine ⟨11834822351144449979613001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63119052539437066557936005 11834822351144449979613001)
            ·
              refine ⟨8876116763358337484709751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11834822351144449979613001 8876116763358337484709751)
              ·
                refine ⟨13314175145037506227064627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8876116763358337484709751 13314175145037506227064627)
                ·
                  refine ⟨19971262717556259340596941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13314175145037506227064627 19971262717556259340596941)
                  ·
                    refine ⟨7489223519083597252723853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19971262717556259340596941 7489223519083597252723853)
                    ·
                      refine ⟨2808458819656348969771445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7489223519083597252723853 2808458819656348969771445)
                      ·
                        rfl

theorem cell23_5469454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_5469454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5469454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5469454 prefixEnd_5469454 := by exact prefixLift 5469454
  have htrace : WordTrace (prefixWord ++ tailWord_5469454) baseStart_5469454 baseEnd_5469454 := by
    simpa [prefixWord, tailWord_5469454, baseEnd_5469454] using wordTrace_append hprefix tailTrace_5469454
  have hstable : (prefixWord ++ tailWord_5469454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5469454).length < 2 ^ (prefixWord ++ tailWord_5469454).sum := by decide
  have hdescent : baseEnd_5469454 < baseStart_5469454 := by decide
  rcases family_descends (prefixWord ++ tailWord_5469454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5469464 : List Nat := [2, 1, 2, 3, 1, 3, 2, 1, 3, 3, 2]
def baseStart_5469464 : Nat := 118140960795 + 5469464 * 2 ^ 59
def prefixEnd_5469464 : Nat := 4983230072969 + 3 ^ 40 * 5469464 * 2
def baseEnd_5469464 : Nat := 2808463954462893930646399

theorem tailTrace_5469464 : CollatzResearch.WordTrace tailWord_5469464 prefixEnd_5469464 2808463954462893930646399 := by
  unfold tailWord_5469464
  simp only [CollatzResearch.WordTrace]
  refine ⟨99743870328536756464003723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132991827104715675285338297 99743870328536756464003723)
  ·
    refine ⟨149615805492805134696005585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99743870328536756464003723 149615805492805134696005585)
    ·
      refine ⟨112211854119603851022004189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149615805492805134696005585 112211854119603851022004189)
      ·
        refine ⟨42079445294851444133251571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112211854119603851022004189 42079445294851444133251571)
        ·
          refine ⟨63119167942277166199877357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42079445294851444133251571 63119167942277166199877357)
          ·
            refine ⟨23669687978353937324954009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63119167942277166199877357 23669687978353937324954009)
            ·
              refine ⟨17752265983765452993715507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23669687978353937324954009 17752265983765452993715507)
              ·
                refine ⟨26628398975648179490573261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17752265983765452993715507 26628398975648179490573261)
                ·
                  refine ⟨9985649615868067308964973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26628398975648179490573261 9985649615868067308964973)
                  ·
                    refine ⟨3744618605950525240861865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9985649615868067308964973 3744618605950525240861865)
                    ·
                      refine ⟨2808463954462893930646399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3744618605950525240861865 2808463954462893930646399)
                      ·
                        rfl

theorem cell23_5469464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 3, 3, 2].length) (baseStart_5469464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5469464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5469464 prefixEnd_5469464 := by exact prefixLift 5469464
  have htrace : WordTrace (prefixWord ++ tailWord_5469464) baseStart_5469464 baseEnd_5469464 := by
    simpa [prefixWord, tailWord_5469464, baseEnd_5469464] using wordTrace_append hprefix tailTrace_5469464
  have hstable : (prefixWord ++ tailWord_5469464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5469464).length < 2 ^ (prefixWord ++ tailWord_5469464).sum := by decide
  have hdescent : baseEnd_5469464 < baseStart_5469464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5469464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5469511 : List Nat := [1, 1, 4, 1, 2, 5, 1, 1, 1, 4, 2]
def baseStart_5469511 : Nat := 118140960795 + 5469511 * 2 ^ 59
def prefixEnd_5469511 : Nat := 4983230072969 + 3 ^ 40 * 5469511 * 2
def baseEnd_5469511 : Nat := 2808488088053655246758683

theorem tailTrace_5469511 : CollatzResearch.WordTrace tailWord_5469511 prefixEnd_5469511 2808488088053655246758683 := by
  unfold tailWord_5469511
  simp only [CollatzResearch.WordTrace]
  refine ⟨199489454887903239954968387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132992969925268826636645591 199489454887903239954968387)
  ·
    refine ⟨299234182331854859932452581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199489454887903239954968387 299234182331854859932452581)
    ·
      refine ⟨56106409187222786237334859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 299234182331854859932452581 56106409187222786237334859)
      ·
        refine ⟨84159613780834179356002289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56106409187222786237334859 84159613780834179356002289)
        ·
          refine ⟨63119710335625634517001717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84159613780834179356002289 63119710335625634517001717)
          ·
            refine ⟨5917472843964903235968911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63119710335625634517001717 5917472843964903235968911)
            ·
              refine ⟨8876209265947354853953367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5917472843964903235968911 8876209265947354853953367)
              ·
                refine ⟨13314313898921032280930051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8876209265947354853953367 13314313898921032280930051)
                ·
                  refine ⟨19971470848381548421395077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13314313898921032280930051 19971470848381548421395077)
                  ·
                    refine ⟨3744650784071540329011577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19971470848381548421395077 3744650784071540329011577)
                    ·
                      refine ⟨2808488088053655246758683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3744650784071540329011577 2808488088053655246758683)
                      ·
                        rfl

theorem cell23_5469511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 4, 2].length) (baseStart_5469511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5469511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5469511 prefixEnd_5469511 := by exact prefixLift 5469511
  have htrace : WordTrace (prefixWord ++ tailWord_5469511) baseStart_5469511 baseEnd_5469511 := by
    simpa [prefixWord, tailWord_5469511, baseEnd_5469511] using wordTrace_append hprefix tailTrace_5469511
  have hstable : (prefixWord ++ tailWord_5469511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5469511).length < 2 ^ (prefixWord ++ tailWord_5469511).sum := by decide
  have hdescent : baseEnd_5469511 < baseStart_5469511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5469511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5469554 : List Nat := [3, 2, 1, 2, 1, 2, 2, 1, 2, 5, 2]
def baseStart_5469554 : Nat := 118140960795 + 5469554 * 2 ^ 59
def prefixEnd_5469554 : Nat := 4983230072969 + 3 ^ 40 * 5469554 * 2
def baseEnd_5469554 : Nat := 2808510167721798578520985

theorem tailTrace_5469554 : CollatzResearch.WordTrace tailWord_5469554 prefixEnd_5469554 2808510167721798578520985 := by
  unfold tailWord_5469554
  simp only [CollatzResearch.WordTrace]
  refine ⟨49872755806686864574695929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132994015484498305532522477 49872755806686864574695929)
  ·
    refine ⟨37404566855015148431021947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49872755806686864574695929 37404566855015148431021947)
    ·
      refine ⟨56106850282522722646532921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37404566855015148431021947 56106850282522722646532921)
      ·
        refine ⟨42080137711892041984899691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56106850282522722646532921 42080137711892041984899691)
        ·
          refine ⟨63120206567838062977349537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42080137711892041984899691 63120206567838062977349537)
          ·
            refine ⟨47340154925878547233012153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63120206567838062977349537 47340154925878547233012153)
            ·
              refine ⟨35505116194408910424759115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47340154925878547233012153 35505116194408910424759115)
              ·
                refine ⟨53257674291613365637138673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35505116194408910424759115 53257674291613365637138673)
                ·
                  refine ⟨39943255718710024227854005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53257674291613365637138673 39943255718710024227854005)
                  ·
                    refine ⟨3744680223629064771361313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39943255718710024227854005 3744680223629064771361313)
                    ·
                      refine ⟨2808510167721798578520985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3744680223629064771361313 2808510167721798578520985)
                      ·
                        rfl

theorem cell23_5469554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 2, 5, 2].length) (baseStart_5469554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5469554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5469554 prefixEnd_5469554 := by exact prefixLift 5469554
  have htrace : WordTrace (prefixWord ++ tailWord_5469554) baseStart_5469554 baseEnd_5469554 := by
    simpa [prefixWord, tailWord_5469554, baseEnd_5469554] using wordTrace_append hprefix tailTrace_5469554
  have hstable : (prefixWord ++ tailWord_5469554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5469554).length < 2 ^ (prefixWord ++ tailWord_5469554).sum := by decide
  have hdescent : baseEnd_5469554 < baseStart_5469554 := by decide
  rcases family_descends (prefixWord ++ tailWord_5469554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5469704 : List Nat := [2, 1, 3, 2, 1, 1, 2, 4, 1, 2, 4]
def baseStart_5469704 : Nat := 118140960795 + 5469704 * 2 ^ 59
def prefixEnd_5469704 : Nat := 4983230072969 + 3 ^ 40 * 5469704 * 2
def baseEnd_5469704 : Nat := 2808587189819972991645295

theorem tailTrace_5469704 : CollatzResearch.WordTrace tailWord_5469704 prefixEnd_5469704 2808587189819972991645295 := by
  unfold tailWord_5469704
  simp only [CollatzResearch.WordTrace]
  refine ⟨99748247088102016958372083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132997662784136022611162777 99748247088102016958372083)
  ·
    refine ⟨149622370632153025437558125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99748247088102016958372083 149622370632153025437558125)
    ·
      refine ⟨56108388987057384539084297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149622370632153025437558125 56108388987057384539084297)
      ·
        refine ⟨42081291740293038404313223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56108388987057384539084297 42081291740293038404313223)
        ·
          refine ⟨63121937610439557606469835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42081291740293038404313223 63121937610439557606469835)
          ·
            refine ⟨94682906415659336409704753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63121937610439557606469835 94682906415659336409704753)
            ·
              refine ⟨71012179811744502307278565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94682906415659336409704753 71012179811744502307278565)
              ·
                refine ⟨13314783714702094182614731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71012179811744502307278565 13314783714702094182614731)
                ·
                  refine ⟨19972175572053141273922097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13314783714702094182614731 19972175572053141273922097)
                  ·
                    refine ⟨14979131679039855955441573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19972175572053141273922097 14979131679039855955441573)
                    ·
                      refine ⟨2808587189819972991645295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14979131679039855955441573 2808587189819972991645295)
                      ·
                        rfl

theorem cell23_5469704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_5469704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5469704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5469704 prefixEnd_5469704 := by exact prefixLift 5469704
  have htrace : WordTrace (prefixWord ++ tailWord_5469704) baseStart_5469704 baseEnd_5469704 := by
    simpa [prefixWord, tailWord_5469704, baseEnd_5469704] using wordTrace_append hprefix tailTrace_5469704
  have hstable : (prefixWord ++ tailWord_5469704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5469704).length < 2 ^ (prefixWord ++ tailWord_5469704).sum := by decide
  have hdescent : baseEnd_5469704 < baseStart_5469704 := by decide
  rcases family_descends (prefixWord ++ tailWord_5469704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5469774 : List Nat := [4, 1, 1, 1, 1, 2, 1, 4, 2, 6]
def baseStart_5469774 : Nat := 118140960795 + 5469774 * 2 ^ 59
def prefixEnd_5469774 : Nat := 4983230072969 + 3 ^ 40 * 5469774 * 2
def baseEnd_5469774 : Nat := 936207711155262572589991

theorem tailTrace_5469774 : CollatzResearch.WordTrace tailWord_5469774 prefixEnd_5469774 936207711155262572589991 := by
  unfold tailWord_5469774
  simp only [CollatzResearch.WordTrace]
  refine ⟨24937380910743804483974047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132999364857300290581194917 24937380910743804483974047)
  ·
    refine ⟨37406071366115706725961071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24937380910743804483974047 37406071366115706725961071)
    ·
      refine ⟨56109107049173560088941607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37406071366115706725961071 56109107049173560088941607)
      ·
        refine ⟨84163660573760340133412411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56109107049173560088941607 84163660573760340133412411)
        ·
          refine ⟨126245490860640510200118617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84163660573760340133412411 126245490860640510200118617)
          ·
            refine ⟨94684118145480382650088963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126245490860640510200118617 94684118145480382650088963)
            ·
              refine ⟨142026177218220573975133445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94684118145480382650088963 142026177218220573975133445)
              ·
                refine ⟨26629908228416357620337521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 142026177218220573975133445 26629908228416357620337521)
                ·
                  refine ⟨19972431171312268215253141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26629908228416357620337521 19972431171312268215253141)
                  ·
                    refine ⟨936207711155262572589991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19972431171312268215253141 936207711155262572589991)
                    ·
                      rfl

theorem cell23_5469774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 2, 6].length) (baseStart_5469774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5469774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5469774 prefixEnd_5469774 := by exact prefixLift 5469774
  have htrace : WordTrace (prefixWord ++ tailWord_5469774) baseStart_5469774 baseEnd_5469774 := by
    simpa [prefixWord, tailWord_5469774, baseEnd_5469774] using wordTrace_append hprefix tailTrace_5469774
  have hstable : (prefixWord ++ tailWord_5469774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5469774).length < 2 ^ (prefixWord ++ tailWord_5469774).sum := by decide
  have hdescent : baseEnd_5469774 < baseStart_5469774 := by decide
  rcases family_descends (prefixWord ++ tailWord_5469774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5469781 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 5, 4, 2]
def baseStart_5469781 : Nat := 118140960795 + 5469781 * 2 ^ 59
def prefixEnd_5469781 : Nat := 4983230072969 + 3 ^ 40 * 5469781 * 2
def baseEnd_5469781 : Nat := 2808626727830369190382441

theorem tailTrace_5469781 : CollatzResearch.WordTrace tailWord_5469781 prefixEnd_5469781 2808626727830369190382441 := by
  unfold tailWord_5469781
  simp only [CollatzResearch.WordTrace]
  refine ⟨199499302596925076067297197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132999535064616717378198131 199499302596925076067297197)
  ·
    refine ⟨74812238473846903525236449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199499302596925076067297197 74812238473846903525236449)
    ·
      refine ⟨56109178855385177643927337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74812238473846903525236449 56109178855385177643927337)
      ·
        refine ⟨42081884141538883232945503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56109178855385177643927337 42081884141538883232945503)
        ·
          refine ⟨63122826212308324849418255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42081884141538883232945503 63122826212308324849418255)
          ·
            refine ⟨94684239318462487274127383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63122826212308324849418255 94684239318462487274127383)
            ·
              refine ⟨142026358977693730911191075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94684239318462487274127383 142026358977693730911191075)
              ·
                refine ⟨213039538466540596366786613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142026358977693730911191075 213039538466540596366786613)
                ·
                  refine ⟨19972456731238180909386245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 213039538466540596366786613 19972456731238180909386245)
                  ·
                    refine ⟨3744835637107158920509921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19972456731238180909386245 3744835637107158920509921)
                    ·
                      refine ⟨2808626727830369190382441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3744835637107158920509921 2808626727830369190382441)
                      ·
                        rfl

theorem cell23_5469781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 4, 2].length) (baseStart_5469781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5469781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5469781 prefixEnd_5469781 := by exact prefixLift 5469781
  have htrace : WordTrace (prefixWord ++ tailWord_5469781) baseStart_5469781 baseEnd_5469781 := by
    simpa [prefixWord, tailWord_5469781, baseEnd_5469781] using wordTrace_append hprefix tailTrace_5469781
  have hstable : (prefixWord ++ tailWord_5469781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5469781).length < 2 ^ (prefixWord ++ tailWord_5469781).sum := by decide
  have hdescent : baseEnd_5469781 < baseStart_5469781 := by decide
  rcases family_descends (prefixWord ++ tailWord_5469781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5469782 : List Nat := [5, 2, 2, 2, 2, 1, 1, 8]
def baseStart_5469782 : Nat := 118140960795 + 5469782 * 2 ^ 59
def prefixEnd_5469782 : Nat := 4983230072969 + 3 ^ 40 * 5469782 * 2
def baseEnd_5469782 : Nat := 104023231159667543943331

theorem tailTrace_5469782 : CollatzResearch.WordTrace tailWord_5469782 prefixEnd_5469782 104023231159667543943331 := by
  unfold tailWord_5469782
  simp only [CollatzResearch.WordTrace]
  refine ⟨12468708691870090827380225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 132999559379947635492055733 12468708691870090827380225)
  ·
    refine ⟨9351531518902568120535169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12468708691870090827380225 9351531518902568120535169)
    ·
      refine ⟨7013648639176926090401377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9351531518902568120535169 7013648639176926090401377)
      ·
        refine ⟨5260236479382694567801033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7013648639176926090401377 5260236479382694567801033)
        ·
          refine ⟨3945177359537020925850775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5260236479382694567801033 3945177359537020925850775)
          ·
            refine ⟨5917766039305531388776163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3945177359537020925850775 5917766039305531388776163)
            ·
              refine ⟨8876649058958297083164245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5917766039305531388776163 8876649058958297083164245)
              ·
                refine ⟨104023231159667543943331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8876649058958297083164245 104023231159667543943331)
                ·
                  rfl

theorem cell23_5469782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 8].length) (baseStart_5469782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5469782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5469782 prefixEnd_5469782 := by exact prefixLift 5469782
  have htrace : WordTrace (prefixWord ++ tailWord_5469782) baseStart_5469782 baseEnd_5469782 := by
    simpa [prefixWord, tailWord_5469782, baseEnd_5469782] using wordTrace_append hprefix tailTrace_5469782
  have hstable : (prefixWord ++ tailWord_5469782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5469782).length < 2 ^ (prefixWord ++ tailWord_5469782).sum := by decide
  have hdescent : baseEnd_5469782 < baseStart_5469782 := by decide
  rcases family_descends (prefixWord ++ tailWord_5469782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5469831 : List Nat := [1, 1, 4, 2, 1, 3, 1, 2, 2, 3, 3]
def baseStart_5469831 : Nat := 118140960795 + 5469831 * 2 ^ 59
def prefixEnd_5469831 : Nat := 4983230072969 + 3 ^ 40 * 5469831 * 2
def baseEnd_5469831 : Nat := 2808652401863093994757211

theorem tailTrace_5469831 : CollatzResearch.WordTrace tailWord_5469831 prefixEnd_5469831 2808652401863093994757211 := by
  unfold tailWord_5469831
  simp only [CollatzResearch.WordTrace]
  refine ⟨199501126246743934606617347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133000750831162623071078231 199501126246743934606617347)
  ·
    refine ⟨299251689370115901909926021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199501126246743934606617347 299251689370115901909926021)
    ·
      refine ⟨56109691756896731608111129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 299251689370115901909926021 56109691756896731608111129)
      ·
        refine ⟨42082268817672548706083347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56109691756896731608111129 42082268817672548706083347)
        ·
          refine ⟨63123403226508823059125021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42082268817672548706083347 63123403226508823059125021)
          ·
            refine ⟨23671276209940808647171883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63123403226508823059125021 23671276209940808647171883)
            ·
              refine ⟨35506914314911212970757825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23671276209940808647171883 35506914314911212970757825)
              ·
                refine ⟨26630185736183409728068369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35506914314911212970757825 26630185736183409728068369)
                ·
                  refine ⟨19972639302137557296051277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26630185736183409728068369 19972639302137557296051277)
                  ·
                    refine ⟨7489739738301583986019229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19972639302137557296051277 7489739738301583986019229)
                    ·
                      refine ⟨2808652401863093994757211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7489739738301583986019229 2808652401863093994757211)
                      ·
                        rfl

theorem cell23_5469831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_5469831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5469831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5469831 prefixEnd_5469831 := by exact prefixLift 5469831
  have htrace : WordTrace (prefixWord ++ tailWord_5469831) baseStart_5469831 baseEnd_5469831 := by
    simpa [prefixWord, tailWord_5469831, baseEnd_5469831] using wordTrace_append hprefix tailTrace_5469831
  have hstable : (prefixWord ++ tailWord_5469831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5469831).length < 2 ^ (prefixWord ++ tailWord_5469831).sum := by decide
  have hdescent : baseEnd_5469831 < baseStart_5469831 := by decide
  rcases family_descends (prefixWord ++ tailWord_5469831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5469832 : List Nat := [2, 1, 3, 5, 1, 1, 1, 1, 4, 2, 2]
def baseStart_5469832 : Nat := 118140960795 + 5469832 * 2 ^ 59
def prefixEnd_5469832 : Nat := 4983230072969 + 3 ^ 40 * 5469832 * 2
def baseEnd_5469832 : Nat := 2808652915343748490844707

theorem tailTrace_5469832 : CollatzResearch.WordTrace tailWord_5469832 prefixEnd_5469832 2808652915343748490844707 := by
  unfold tailWord_5469832
  simp only [CollatzResearch.WordTrace]
  refine ⟨99750581359870155888701875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133000775146493541184935833 99750581359870155888701875)
  ·
    refine ⟨149625872039805233833052813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99750581359870155888701875 149625872039805233833052813)
    ·
      refine ⟨56109702014926962687394805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149625872039805233833052813 56109702014926962687394805)
      ·
        refine ⟨5260284563899402751943263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56109702014926962687394805 5260284563899402751943263)
        ·
          refine ⟨7890426845849104127914895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5260284563899402751943263 7890426845849104127914895)
          ·
            refine ⟨11835640268773656191872343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7890426845849104127914895 11835640268773656191872343)
            ·
              refine ⟨17753460403160484287808515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11835640268773656191872343 17753460403160484287808515)
              ·
                refine ⟨26630190604740726431712773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17753460403160484287808515 26630190604740726431712773)
                ·
                  refine ⟨4993160738388886205946145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26630190604740726431712773 4993160738388886205946145)
                  ·
                    refine ⟨3744870553791664654459609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4993160738388886205946145 3744870553791664654459609)
                    ·
                      refine ⟨2808652915343748490844707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3744870553791664654459609 2808652915343748490844707)
                      ·
                        rfl

theorem cell23_5469832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_5469832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5469832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5469832 prefixEnd_5469832 := by exact prefixLift 5469832
  have htrace : WordTrace (prefixWord ++ tailWord_5469832) baseStart_5469832 baseEnd_5469832 := by
    simpa [prefixWord, tailWord_5469832, baseEnd_5469832] using wordTrace_append hprefix tailTrace_5469832
  have hstable : (prefixWord ++ tailWord_5469832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5469832).length < 2 ^ (prefixWord ++ tailWord_5469832).sum := by decide
  have hdescent : baseEnd_5469832 < baseStart_5469832 := by decide
  rcases family_descends (prefixWord ++ tailWord_5469832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5469838 : List Nat := [4, 1, 1, 3, 1, 2, 2, 4, 5]
def baseStart_5469838 : Nat := 118140960795 + 5469838 * 2 ^ 59
def prefixEnd_5469838 : Nat := 4983230072969 + 3 ^ 40 * 5469838 * 2
def baseEnd_5469838 : Nat := 312072888469741718596631

theorem tailTrace_5469838 : CollatzResearch.WordTrace tailWord_5469838 prefixEnd_5469838 312072888469741718596631 := by
  unfold tailWord_5469838
  simp only [CollatzResearch.WordTrace]
  refine ⟨24937672694714821850265271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133000921038479049868081445 24937672694714821850265271)
  ·
    refine ⟨37406509042072232775397907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24937672694714821850265271 37406509042072232775397907)
    ·
      refine ⟨56109763563108349163096861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37406509042072232775397907 56109763563108349163096861)
      ·
        refine ⟨21041161336165630936161323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56109763563108349163096861 21041161336165630936161323)
        ·
          refine ⟨31561742004248446404241985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21041161336165630936161323 31561742004248446404241985)
          ·
            refine ⟨23671306503186334803181489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31561742004248446404241985 23671306503186334803181489)
            ·
              refine ⟨17753479877389751102386117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23671306503186334803181489 17753479877389751102386117)
              ·
                refine ⟨3328777477010578331697397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17753479877389751102386117 3328777477010578331697397)
                ·
                  refine ⟨312072888469741718596631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3328777477010578331697397 312072888469741718596631)
                  ·
                    rfl

theorem cell23_5469838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 4, 5].length) (baseStart_5469838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5469838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5469838 prefixEnd_5469838 := by exact prefixLift 5469838
  have htrace : WordTrace (prefixWord ++ tailWord_5469838) baseStart_5469838 baseEnd_5469838 := by
    simpa [prefixWord, tailWord_5469838, baseEnd_5469838] using wordTrace_append hprefix tailTrace_5469838
  have hstable : (prefixWord ++ tailWord_5469838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5469838).length < 2 ^ (prefixWord ++ tailWord_5469838).sum := by decide
  have hdescent : baseEnd_5469838 < baseStart_5469838 := by decide
  rcases family_descends (prefixWord ++ tailWord_5469838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5469841 : List Nat := [1, 2, 2, 1, 1, 1, 1, 5, 2, 5, 2]
def baseStart_5469841 : Nat := 118140960795 + 5469841 * 2 ^ 59
def prefixEnd_5469841 : Nat := 4983230072969 + 3 ^ 40 * 5469841 * 2
def baseEnd_5469841 : Nat := 2808657536669638955632165

theorem tailTrace_5469841 : CollatzResearch.WordTrace tailWord_5469841 prefixEnd_5469841 2808657536669638955632165 := by
  unfold tailWord_5469841
  simp only [CollatzResearch.WordTrace]
  refine ⟨199501490976707706314481377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133000993984471804209654251 199501490976707706314481377)
  ·
    refine ⟨149626118232530779735861033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199501490976707706314481377 149626118232530779735861033)
    ·
      refine ⟨112219588674398084801895775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149626118232530779735861033 112219588674398084801895775)
      ·
        refine ⟨168329383011597127202843663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112219588674398084801895775 168329383011597127202843663)
        ·
          refine ⟨252494074517395690804265495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168329383011597127202843663 252494074517395690804265495)
          ·
            refine ⟨378741111776093536206398243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252494074517395690804265495 378741111776093536206398243)
            ·
              refine ⟨568111667664140304309597365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 378741111776093536206398243 568111667664140304309597365)
              ·
                refine ⟨53260468843513153529024753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 568111667664140304309597365 53260468843513153529024753)
                ·
                  refine ⟨39945351632634865146768565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53260468843513153529024753 39945351632634865146768565)
                  ·
                    refine ⟨3744876715559518607509553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39945351632634865146768565 3744876715559518607509553)
                    ·
                      refine ⟨2808657536669638955632165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3744876715559518607509553 2808657536669638955632165)
                      ·
                        rfl

theorem cell23_5469841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 5, 2].length) (baseStart_5469841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5469841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5469841 prefixEnd_5469841 := by exact prefixLift 5469841
  have htrace : WordTrace (prefixWord ++ tailWord_5469841) baseStart_5469841 baseEnd_5469841 := by
    simpa [prefixWord, tailWord_5469841, baseEnd_5469841] using wordTrace_append hprefix tailTrace_5469841
  have hstable : (prefixWord ++ tailWord_5469841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5469841).length < 2 ^ (prefixWord ++ tailWord_5469841).sum := by decide
  have hdescent : baseEnd_5469841 < baseStart_5469841 := by decide
  rcases family_descends (prefixWord ++ tailWord_5469841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5469871 : List Nat := [1, 1, 2, 1, 2, 4, 2, 3, 2, 1, 4]
def baseStart_5469871 : Nat := 118140960795 + 5469871 * 2 ^ 59
def prefixEnd_5469871 : Nat := 4983230072969 + 3 ^ 40 * 5469871 * 2
def baseEnd_5469871 : Nat := 2808672941089273838257027

theorem tailTrace_5469871 : CollatzResearch.WordTrace tailWord_5469871 prefixEnd_5469871 2808672941089273838257027 := by
  unfold tailWord_5469871
  simp only [CollatzResearch.WordTrace]
  refine ⟨199502585166599021438073467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133001723444399347625382311 199502585166599021438073467)
  ·
    refine ⟨299253877749898532157110201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199502585166599021438073467 299253877749898532157110201)
    ·
      refine ⟨224440408312423899117832651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299253877749898532157110201 224440408312423899117832651)
      ·
        refine ⟨336660612468635848676748977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224440408312423899117832651 336660612468635848676748977)
        ·
          refine ⟨252495459351476886507561733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 336660612468635848676748977 252495459351476886507561733)
          ·
            refine ⟨47342898628401916220167825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 252495459351476886507561733 47342898628401916220167825)
            ·
              refine ⟨35507173971301437165125869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47342898628401916220167825 35507173971301437165125869)
              ·
                refine ⟨13315190239238038936922201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35507173971301437165125869 13315190239238038936922201)
                ·
                  refine ⟨9986392679428529202691651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13315190239238038936922201 9986392679428529202691651)
                  ·
                    refine ⟨14979589019142793804037477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9986392679428529202691651 14979589019142793804037477)
                    ·
                      refine ⟨2808672941089273838257027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14979589019142793804037477 2808672941089273838257027)
                      ·
                        rfl

theorem cell23_5469871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 2, 1, 4].length) (baseStart_5469871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5469871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5469871 prefixEnd_5469871 := by exact prefixLift 5469871
  have htrace : WordTrace (prefixWord ++ tailWord_5469871) baseStart_5469871 baseEnd_5469871 := by
    simpa [prefixWord, tailWord_5469871, baseEnd_5469871] using wordTrace_append hprefix tailTrace_5469871
  have hstable : (prefixWord ++ tailWord_5469871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5469871).length < 2 ^ (prefixWord ++ tailWord_5469871).sum := by decide
  have hdescent : baseEnd_5469871 < baseStart_5469871 := by decide
  rcases family_descends (prefixWord ++ tailWord_5469871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5469881 : List Nat := [1, 2, 1, 4, 1, 1, 2, 2, 5, 4]
def baseStart_5469881 : Nat := 118140960795 + 5469881 * 2 ^ 59
def prefixEnd_5469881 : Nat := 4983230072969 + 3 ^ 40 * 5469881 * 2
def baseEnd_5469881 : Nat := 936226025298606266377327

theorem tailTrace_5469881 : CollatzResearch.WordTrace tailWord_5469881 prefixEnd_5469881 936226025298606266377327 := by
  unfold tailWord_5469881
  simp only [CollatzResearch.WordTrace]
  refine ⟨199502949896562793145937497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133001966597708528763958331 199502949896562793145937497)
  ·
    refine ⟨149627212422422094859453123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199502949896562793145937497 149627212422422094859453123)
    ·
      refine ⟨224440818633633142289179685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149627212422422094859453123 224440818633633142289179685)
      ·
        refine ⟨42082653493806214179221191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 224440818633633142289179685 42082653493806214179221191)
        ·
          refine ⟨63123980240709321268831787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42082653493806214179221191 63123980240709321268831787)
          ·
            refine ⟨94685970361063981903247681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63123980240709321268831787 94685970361063981903247681)
            ·
              refine ⟨71014477770797986427435761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94685970361063981903247681 71014477770797986427435761)
              ·
                refine ⟨53260858328098489820576821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71014477770797986427435761 53260858328098489820576821)
                ·
                  refine ⟨4993205468259233420679077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53260858328098489820576821 4993205468259233420679077)
                  ·
                    refine ⟨936226025298606266377327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4993205468259233420679077 936226025298606266377327)
                    ·
                      rfl

theorem cell23_5469881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 5, 4].length) (baseStart_5469881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5469881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5469881 prefixEnd_5469881 := by exact prefixLift 5469881
  have htrace : WordTrace (prefixWord ++ tailWord_5469881) baseStart_5469881 baseEnd_5469881 := by
    simpa [prefixWord, tailWord_5469881, baseEnd_5469881] using wordTrace_append hprefix tailTrace_5469881
  have hstable : (prefixWord ++ tailWord_5469881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5469881).length < 2 ^ (prefixWord ++ tailWord_5469881).sum := by decide
  have hdescent : baseEnd_5469881 < baseStart_5469881 := by decide
  rcases family_descends (prefixWord ++ tailWord_5469881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5469911 : List Nat := [1, 1, 3, 2, 1, 3, 3, 3, 6]
def baseStart_5469911 : Nat := 118140960795 + 5469911 * 2 ^ 59
def prefixEnd_5469911 : Nat := 4983230072969 + 3 ^ 40 * 5469911 * 2
def baseEnd_5469911 : Nat := 312077053368383742417427

theorem tailTrace_5469911 : CollatzResearch.WordTrace tailWord_5469911 prefixEnd_5469911 312077053368383742417427 := by
  unfold tailWord_5469911
  simp only [CollatzResearch.WordTrace]
  refine ⟨199504044086454108269529587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133002696057636072179686391 199504044086454108269529587)
  ·
    refine ⟨299256066129681162404294381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199504044086454108269529587 299256066129681162404294381)
    ·
      refine ⟨112221024798630435901610393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 299256066129681162404294381 112221024798630435901610393)
      ·
        refine ⟨84165768598972826926207795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112221024798630435901610393 84165768598972826926207795)
        ·
          refine ⟨126248652898459240389311693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84165768598972826926207795 126248652898459240389311693)
          ·
            refine ⟨47343244836922215145991885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126248652898459240389311693 47343244836922215145991885)
            ·
              refine ⟨17753716813845830679746957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47343244836922215145991885 17753716813845830679746957)
              ·
                refine ⟨6657643805192186504905109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17753716813845830679746957 6657643805192186504905109)
                ·
                  refine ⟨312077053368383742417427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6657643805192186504905109 312077053368383742417427)
                  ·
                    rfl

theorem cell23_5469911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 3, 6].length) (baseStart_5469911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5469911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5469911 prefixEnd_5469911 := by exact prefixLift 5469911
  have htrace : WordTrace (prefixWord ++ tailWord_5469911) baseStart_5469911 baseEnd_5469911 := by
    simpa [prefixWord, tailWord_5469911, baseEnd_5469911] using wordTrace_append hprefix tailTrace_5469911
  have hstable : (prefixWord ++ tailWord_5469911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5469911).length < 2 ^ (prefixWord ++ tailWord_5469911).sum := by decide
  have hdescent : baseEnd_5469911 < baseStart_5469911 := by decide
  rcases family_descends (prefixWord ++ tailWord_5469911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5469978 : List Nat := [3, 1, 1, 3, 2, 2, 2, 1, 3, 1, 4]
def baseStart_5469978 : Nat := 118140960795 + 5469978 * 2 ^ 59
def prefixEnd_5469978 : Nat := 4983230072969 + 3 ^ 40 * 5469978 * 2
def baseEnd_5469978 : Nat := 2808727883519304919619035

theorem tailTrace_5469978 : CollatzResearch.WordTrace tailWord_5469978 prefixEnd_5469978 2808727883519304919619035 := by
  unfold tailWord_5469978
  simp only [CollatzResearch.WordTrace]
  refine ⟨49876621944302844678054647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133004325184807585808145725 49876621944302844678054647)
  ·
    refine ⟨74814932916454267017081971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49876621944302844678054647 74814932916454267017081971)
    ·
      refine ⟨112222399374681400525622957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74814932916454267017081971 112222399374681400525622957)
      ·
        refine ⟨42083399765505525197108609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112222399374681400525622957 42083399765505525197108609)
        ·
          refine ⟨31562549824129143897831457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42083399765505525197108609 31562549824129143897831457)
          ·
            refine ⟨23671912368096857923373593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31562549824129143897831457 23671912368096857923373593)
            ·
              refine ⟨17753934276072643442530195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23671912368096857923373593 17753934276072643442530195)
              ·
                refine ⟨26630901414108965163795293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17753934276072643442530195 26630901414108965163795293)
                ·
                  refine ⟨9986588030290861936423235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26630901414108965163795293 9986588030290861936423235)
                  ·
                    refine ⟨14979882045436292904634853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9986588030290861936423235 14979882045436292904634853)
                    ·
                      refine ⟨2808727883519304919619035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14979882045436292904634853 2808727883519304919619035)
                      ·
                        rfl

theorem cell23_5469978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_5469978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5469978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5469978 prefixEnd_5469978 := by exact prefixLift 5469978
  have htrace : WordTrace (prefixWord ++ tailWord_5469978) baseStart_5469978 baseEnd_5469978 := by
    simpa [prefixWord, tailWord_5469978, baseEnd_5469978] using wordTrace_append hprefix tailTrace_5469978
  have hstable : (prefixWord ++ tailWord_5469978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5469978).length < 2 ^ (prefixWord ++ tailWord_5469978).sum := by decide
  have hdescent : baseEnd_5469978 < baseStart_5469978 := by decide
  rcases family_descends (prefixWord ++ tailWord_5469978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5469988 : List Nat := [2, 3, 1, 3, 2, 1, 2, 2, 1, 6]
def baseStart_5469988 : Nat := 118140960795 + 5469988 * 2 ^ 59
def prefixEnd_5469988 : Nat := 4983230072969 + 3 ^ 40 * 5469988 * 2
def baseEnd_5469988 : Nat := 936244339441949960164663

theorem tailTrace_5469988 : CollatzResearch.WordTrace tailWord_5469988 prefixEnd_5469988 936244339441949960164663 := by
  unfold tailWord_5469988
  simp only [CollatzResearch.WordTrace]
  refine ⟨99753426253587575210041309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133004568338116766946721745 99753426253587575210041309)
  ·
    refine ⟨37407534845095340703765491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99753426253587575210041309 37407534845095340703765491)
    ·
      refine ⟨56111302267643011055648237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37407534845095340703765491 56111302267643011055648237)
      ·
        refine ⟨21041738350366129145868089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56111302267643011055648237 21041738350366129145868089)
        ·
          refine ⟨15781303762774596859401067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21041738350366129145868089 15781303762774596859401067)
          ·
            refine ⟨23671955644161895289101601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15781303762774596859401067 23671955644161895289101601)
            ·
              refine ⟨17753966733121421466826201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23671955644161895289101601 17753966733121421466826201)
              ·
                refine ⟨13315475049841066100119651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17753966733121421466826201 13315475049841066100119651)
                ·
                  refine ⟨19973212574761599150179477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13315475049841066100119651 19973212574761599150179477)
                  ·
                    refine ⟨936244339441949960164663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19973212574761599150179477 936244339441949960164663)
                    ·
                      rfl

theorem cell23_5469988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 1, 6].length) (baseStart_5469988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5469988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5469988 prefixEnd_5469988 := by exact prefixLift 5469988
  have htrace : WordTrace (prefixWord ++ tailWord_5469988) baseStart_5469988 baseEnd_5469988 := by
    simpa [prefixWord, tailWord_5469988, baseEnd_5469988] using wordTrace_append hprefix tailTrace_5469988
  have hstable : (prefixWord ++ tailWord_5469988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5469988).length < 2 ^ (prefixWord ++ tailWord_5469988).sum := by decide
  have hdescent : baseEnd_5469988 < baseStart_5469988 := by decide
  rcases family_descends (prefixWord ++ tailWord_5469988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5469992 : List Nat := [2, 1, 5, 1, 1, 4, 2, 1, 1, 5]
def baseStart_5469992 : Nat := 118140960795 + 5469992 * 2 ^ 59
def prefixEnd_5469992 : Nat := 4983230072969 + 3 ^ 40 * 5469992 * 2
def baseEnd_5469992 : Nat := 936245024082822621614657

theorem tailTrace_5469992 : CollatzResearch.WordTrace tailWord_5469992 prefixEnd_5469992 936245024082822621614657 := by
  unfold tailWord_5469992
  simp only [CollatzResearch.WordTrace]
  refine ⟨99753499199580329551614115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133004665599440439402152153 99753499199580329551614115)
  ·
    refine ⟨149630248799370494327421173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99753499199580329551614115 149630248799370494327421173)
    ·
      refine ⟨14027835824940983843195735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 149630248799370494327421173 14027835824940983843195735)
      ·
        refine ⟨21041753737411475764793603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14027835824940983843195735 21041753737411475764793603)
        ·
          refine ⟨31562630606117213647190405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21041753737411475764793603 31562630606117213647190405)
          ·
            refine ⟨5917993238646977558848201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31562630606117213647190405 5917993238646977558848201)
            ·
              refine ⟨4438494928985233169136151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5917993238646977558848201 4438494928985233169136151)
              ·
                refine ⟨6657742393477849753704227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4438494928985233169136151 6657742393477849753704227)
                ·
                  refine ⟨9986613590216774630556341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6657742393477849753704227 9986613590216774630556341)
                  ·
                    refine ⟨936245024082822621614657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9986613590216774630556341 936245024082822621614657)
                    ·
                      rfl

theorem cell23_5469992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_5469992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5469992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5469992 prefixEnd_5469992 := by exact prefixLift 5469992
  have htrace : WordTrace (prefixWord ++ tailWord_5469992) baseStart_5469992 baseEnd_5469992 := by
    simpa [prefixWord, tailWord_5469992, baseEnd_5469992] using wordTrace_append hprefix tailTrace_5469992
  have hstable : (prefixWord ++ tailWord_5469992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5469992).length < 2 ^ (prefixWord ++ tailWord_5469992).sum := by decide
  have hdescent : baseEnd_5469992 < baseStart_5469992 := by decide
  rcases family_descends (prefixWord ++ tailWord_5469992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5470001 : List Nat := [1, 2, 2, 3, 2, 3, 10]
def baseStart_5470001 : Nat := 118140960795 + 5470001 * 2 ^ 59
def prefixEnd_5470001 : Nat := 4983230072969 + 3 ^ 40 * 5470001 * 2
def baseEnd_5470001 : Nat := 34675798686103189254709

theorem tailTrace_5470001 : CollatzResearch.WordTrace tailWord_5470001 prefixEnd_5470001 34675798686103189254709 := by
  unfold tailWord_5470001
  simp only [CollatzResearch.WordTrace]
  refine ⟨199507326656128053640305857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133004884437418702426870571 199507326656128053640305857)
  ·
    refine ⟨149630494992096040230229393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199507326656128053640305857 149630494992096040230229393)
    ·
      refine ⟨112222871244072030172672045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149630494992096040230229393 112222871244072030172672045)
      ·
        refine ⟨42083576716527011314752017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112222871244072030172672045 42083576716527011314752017)
        ·
          refine ⟨31562682537395258486064013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42083576716527011314752017 31562682537395258486064013)
          ·
            refine ⟨11836005951523221932274005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31562682537395258486064013 11836005951523221932274005)
            ·
              refine ⟨34675798686103189254709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11836005951523221932274005 34675798686103189254709)
              ·
                rfl

theorem cell23_5470001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 10].length) (baseStart_5470001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5470001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5470001 prefixEnd_5470001 := by exact prefixLift 5470001
  have htrace : WordTrace (prefixWord ++ tailWord_5470001) baseStart_5470001 baseEnd_5470001 := by
    simpa [prefixWord, tailWord_5470001, baseEnd_5470001] using wordTrace_append hprefix tailTrace_5470001
  have hstable : (prefixWord ++ tailWord_5470001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5470001).length < 2 ^ (prefixWord ++ tailWord_5470001).sum := by decide
  have hdescent : baseEnd_5470001 < baseStart_5470001 := by decide
  rcases family_descends (prefixWord ++ tailWord_5470001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5470005 : List Nat := [1, 3, 3, 1, 4, 1, 1, 1, 4, 4]
def baseStart_5470005 : Nat := 118140960795 + 5470005 * 2 ^ 59
def prefixEnd_5470005 : Nat := 4983230072969 + 3 ^ 40 * 5470005 * 2
def baseEnd_5470005 : Nat := 936247249165658771327137

theorem tailTrace_5470005 : CollatzResearch.WordTrace tailWord_5470005 prefixEnd_5470005 936247249165658771327137 := by
  unfold tailWord_5470005
  simp only [CollatzResearch.WordTrace]
  refine ⟨199507472548113562323451469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133004981698742374882300979 199507472548113562323451469)
  ·
    refine ⟨74815302205542585871294301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199507472548113562323451469 74815302205542585871294301)
    ·
      refine ⟨28055738327078469701735363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74815302205542585871294301 28055738327078469701735363)
      ·
        refine ⟨42083607490617704552603045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28055738327078469701735363 42083607490617704552603045)
        ·
          refine ⟨7890676404490819603613071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42083607490617704552603045 7890676404490819603613071)
          ·
            refine ⟨11836014606736229405419607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7890676404490819603613071 11836014606736229405419607)
            ·
              refine ⟨17754021910104344108129411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11836014606736229405419607 17754021910104344108129411)
              ·
                refine ⟨26631032865156516162194117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17754021910104344108129411 26631032865156516162194117)
                ·
                  refine ⟨4993318662216846780411397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26631032865156516162194117 4993318662216846780411397)
                  ·
                    refine ⟨936247249165658771327137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4993318662216846780411397 936247249165658771327137)
                    ·
                      rfl

theorem cell23_5470005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_5470005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5470005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5470005 prefixEnd_5470005 := by exact prefixLift 5470005
  have htrace : WordTrace (prefixWord ++ tailWord_5470005) baseStart_5470005 baseEnd_5470005 := by
    simpa [prefixWord, tailWord_5470005, baseEnd_5470005] using wordTrace_append hprefix tailTrace_5470005
  have hstable : (prefixWord ++ tailWord_5470005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5470005).length < 2 ^ (prefixWord ++ tailWord_5470005).sum := by decide
  have hdescent : baseEnd_5470005 < baseStart_5470005 := by decide
  rcases family_descends (prefixWord ++ tailWord_5470005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5470022 : List Nat := [6, 1, 1, 2, 1, 1, 3, 1, 1, 6]
def baseStart_5470022 : Nat := 118140960795 + 5470022 * 2 ^ 59
def prefixEnd_5470022 : Nat := 4983230072969 + 3 ^ 40 * 5470022 * 2
def baseEnd_5470022 : Nat := 936250158889367582489611

theorem tailTrace_5470022 : CollatzResearch.WordTrace tailWord_5470022 prefixEnd_5470022 936250158889367582489611 := by
  unfold tailWord_5470022
  simp only [CollatzResearch.WordTrace]
  refine ⟨6234627893407874194588135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 133005395059367982817880213 6234627893407874194588135)
  ·
    refine ⟨9351941840111811291882203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6234627893407874194588135 9351941840111811291882203)
    ·
      refine ⟨14027912760167716937823305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9351941840111811291882203 14027912760167716937823305)
      ·
        refine ⟨10520934570125787703367479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14027912760167716937823305 10520934570125787703367479)
        ·
          refine ⟨15781401855188681555051219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10520934570125787703367479 15781401855188681555051219)
          ·
            refine ⟨23672102782783022332576829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15781401855188681555051219 23672102782783022332576829)
            ·
              refine ⟨8877038543543633374716311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23672102782783022332576829 8877038543543633374716311)
              ·
                refine ⟨13315557815315450062074467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8877038543543633374716311 13315557815315450062074467)
                ·
                  refine ⟨19973336722973175093111701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13315557815315450062074467 19973336722973175093111701)
                  ·
                    refine ⟨936250158889367582489611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19973336722973175093111701 936250158889367582489611)
                    ·
                      rfl

theorem cell23_5470022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_5470022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5470022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5470022 prefixEnd_5470022 := by exact prefixLift 5470022
  have htrace : WordTrace (prefixWord ++ tailWord_5470022) baseStart_5470022 baseEnd_5470022 := by
    simpa [prefixWord, tailWord_5470022, baseEnd_5470022] using wordTrace_append hprefix tailTrace_5470022
  have hstable : (prefixWord ++ tailWord_5470022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5470022).length < 2 ^ (prefixWord ++ tailWord_5470022).sum := by decide
  have hdescent : baseEnd_5470022 < baseStart_5470022 := by decide
  rcases family_descends (prefixWord ++ tailWord_5470022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5470029 : List Nat := [1, 6, 1, 2, 1, 1, 2, 2, 3, 2, 2]
def baseStart_5470029 : Nat := 118140960795 + 5470029 * 2 ^ 59
def prefixEnd_5470029 : Nat := 4983230072969 + 3 ^ 40 * 5470029 * 2
def baseEnd_5470029 : Nat := 2808754071032684220081301

theorem tailTrace_5470029 : CollatzResearch.WordTrace tailWord_5470029 prefixEnd_5470029 2808754071032684220081301 := by
  unfold tailWord_5470029
  simp only [CollatzResearch.WordTrace]
  refine ⟨199508347900026614422325141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133005565266684409614883427 199508347900026614422325141)
  ·
    refine ⟨9351953807813747551046491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 199508347900026614422325141 9351953807813747551046491)
    ·
      refine ⟨14027930711720621326569737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9351953807813747551046491 14027930711720621326569737)
      ·
        refine ⟨10520948033790465994927303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14027930711720621326569737 10520948033790465994927303)
        ·
          refine ⟨15781422050685698992390955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10520948033790465994927303 15781422050685698992390955)
          ·
            refine ⟨23672133076028548488586433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15781422050685698992390955 23672133076028548488586433)
            ·
              refine ⟨17754099807021411366439825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23672133076028548488586433 17754099807021411366439825)
              ·
                refine ⟨13315574855266058524829869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17754099807021411366439825 13315574855266058524829869)
                ·
                  refine ⟨4993340570724771946811201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13315574855266058524829869 4993340570724771946811201)
                  ·
                    refine ⟨3745005428043578960108401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4993340570724771946811201 3745005428043578960108401)
                    ·
                      refine ⟨2808754071032684220081301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3745005428043578960108401 2808754071032684220081301)
                      ·
                        rfl

theorem cell23_5470029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_5470029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5470029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5470029 prefixEnd_5470029 := by exact prefixLift 5470029
  have htrace : WordTrace (prefixWord ++ tailWord_5470029) baseStart_5470029 baseEnd_5470029 := by
    simpa [prefixWord, tailWord_5470029, baseEnd_5470029] using wordTrace_append hprefix tailTrace_5470029
  have hstable : (prefixWord ++ tailWord_5470029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5470029).length < 2 ^ (prefixWord ++ tailWord_5470029).sum := by decide
  have hdescent : baseEnd_5470029 < baseStart_5470029 := by decide
  rcases family_descends (prefixWord ++ tailWord_5470029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5470041 : List Nat := [1, 2, 1, 2, 2, 3, 1, 1, 1, 4, 5]
def baseStart_5470041 : Nat := 118140960795 + 5470041 * 2 ^ 59
def prefixEnd_5470041 : Nat := 4983230072969 + 3 ^ 40 * 5470041 * 2
def baseEnd_5470041 : Nat := 2808760232800538173131245

theorem tailTrace_5470041 : CollatzResearch.WordTrace tailWord_5470041 prefixEnd_5470041 2808760232800538173131245 := by
  unfold tailWord_5470041
  simp only [CollatzResearch.WordTrace]
  refine ⟨199508785575983140471761977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133005857050655426981174651 199508785575983140471761977)
  ·
    refine ⟨149631589181987355353821483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199508785575983140471761977 149631589181987355353821483)
    ·
      refine ⟨224447383772981033030732225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149631589181987355353821483 224447383772981033030732225)
      ·
        refine ⟨168335537829735774773049169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224447383772981033030732225 168335537829735774773049169)
        ·
          refine ⟨126251653372301831079786877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168335537829735774773049169 126251653372301831079786877)
          ·
            refine ⟨47344370014613186654920079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126251653372301831079786877 47344370014613186654920079)
            ·
              refine ⟨71016555021919779982380119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47344370014613186654920079 71016555021919779982380119)
              ·
                refine ⟨106524832532879669973570179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71016555021919779982380119 106524832532879669973570179)
                ·
                  refine ⟨159787248799319504960355269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106524832532879669973570179 159787248799319504960355269)
                  ·
                    refine ⟨29960109149872407180066613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 159787248799319504960355269 29960109149872407180066613)
                    ·
                      refine ⟨2808760232800538173131245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29960109149872407180066613 2808760232800538173131245)
                      ·
                        rfl

theorem cell23_5470041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 4, 5].length) (baseStart_5470041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5470041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5470041 prefixEnd_5470041 := by exact prefixLift 5470041
  have htrace : WordTrace (prefixWord ++ tailWord_5470041) baseStart_5470041 baseEnd_5470041 := by
    simpa [prefixWord, tailWord_5470041, baseEnd_5470041] using wordTrace_append hprefix tailTrace_5470041
  have hstable : (prefixWord ++ tailWord_5470041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5470041).length < 2 ^ (prefixWord ++ tailWord_5470041).sum := by decide
  have hdescent : baseEnd_5470041 < baseStart_5470041 := by decide
  rcases family_descends (prefixWord ++ tailWord_5470041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5470062 : List Nat := [4, 1, 2, 3, 1, 1, 2, 1, 4, 1, 3]
def baseStart_5470062 : Nat := 118140960795 + 5470062 * 2 ^ 59
def prefixEnd_5470062 : Nat := 4983230072969 + 3 ^ 40 * 5470062 * 2
def baseEnd_5470062 : Nat := 2808771015894282590968649

theorem tailTrace_5470062 : CollatzResearch.WordTrace tailWord_5470062 prefixEnd_5470062 2808771015894282590968649 := by
  unfold tailWord_5470062
  simp only [CollatzResearch.WordTrace]
  refine ⟨24938693938613382632284555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133006367672604707372184293 24938693938613382632284555)
  ·
    refine ⟨37408040907920073948426833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24938693938613382632284555 37408040907920073948426833)
    ·
      refine ⟨28056030680940055461320125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37408040907920073948426833 28056030680940055461320125)
      ·
        refine ⟨10521011505352520797995047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28056030680940055461320125 10521011505352520797995047)
        ·
          refine ⟨15781517258028781196992571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10521011505352520797995047 15781517258028781196992571)
          ·
            refine ⟨23672275887043171795488857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15781517258028781196992571 23672275887043171795488857)
            ·
              refine ⟨17754206915282378846616643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23672275887043171795488857 17754206915282378846616643)
              ·
                refine ⟨26631310372923568269924965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17754206915282378846616643 26631310372923568269924965)
                ·
                  refine ⟨4993370694923169050610931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26631310372923568269924965 4993370694923169050610931)
                  ·
                    refine ⟨7490056042384753575916397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4993370694923169050610931 7490056042384753575916397)
                    ·
                      refine ⟨2808771015894282590968649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7490056042384753575916397 2808771015894282590968649)
                      ·
                        rfl

theorem cell23_5470062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_5470062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5470062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5470062 prefixEnd_5470062 := by exact prefixLift 5470062
  have htrace : WordTrace (prefixWord ++ tailWord_5470062) baseStart_5470062 baseEnd_5470062 := by
    simpa [prefixWord, tailWord_5470062, baseEnd_5470062] using wordTrace_append hprefix tailTrace_5470062
  have hstable : (prefixWord ++ tailWord_5470062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5470062).length < 2 ^ (prefixWord ++ tailWord_5470062).sum := by decide
  have hdescent : baseEnd_5470062 < baseStart_5470062 := by decide
  rcases family_descends (prefixWord ++ tailWord_5470062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5470085 : List Nat := [1, 3, 1, 1, 3, 2, 2, 3, 1, 4, 2]
def baseStart_5470085 : Nat := 118140960795 + 5470085 * 2 ^ 59
def prefixEnd_5470085 : Nat := 4983230072969 + 3 ^ 40 * 5470085 * 2
def baseEnd_5470085 : Nat := 2808782825949336000981043

theorem tailTrace_5470085 : CollatzResearch.WordTrace tailWord_5470085 prefixEnd_5470085 2808782825949336000981043 := by
  unfold tailWord_5470085
  simp only [CollatzResearch.WordTrace]
  refine ⟨199510390387823735986363709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133006926925215823990909139 199510390387823735986363709)
  ·
    refine ⟨74816396395433900994886391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199510390387823735986363709 74816396395433900994886391)
    ·
      refine ⟨112224594593150851492329587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74816396395433900994886391 112224594593150851492329587)
      ·
        refine ⟨168336891889726277238494381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112224594593150851492329587 168336891889726277238494381)
        ·
          refine ⟨63126334458647353964435393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168336891889726277238494381 63126334458647353964435393)
          ·
            refine ⟨47344750843985515473326545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63126334458647353964435393 47344750843985515473326545)
            ·
              refine ⟨35508563132989136604994909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47344750843985515473326545 35508563132989136604994909)
              ·
                refine ⟨13315711174870926226873091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35508563132989136604994909 13315711174870926226873091)
                ·
                  refine ⟨19973566762306389340309637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13315711174870926226873091 19973566762306389340309637)
                  ·
                    refine ⟨3745043767932448001308057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19973566762306389340309637 3745043767932448001308057)
                    ·
                      refine ⟨2808782825949336000981043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3745043767932448001308057 2808782825949336000981043)
                      ·
                        rfl

theorem cell23_5470085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 4, 2].length) (baseStart_5470085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5470085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5470085 prefixEnd_5470085 := by exact prefixLift 5470085
  have htrace : WordTrace (prefixWord ++ tailWord_5470085) baseStart_5470085 baseEnd_5470085 := by
    simpa [prefixWord, tailWord_5470085, baseEnd_5470085] using wordTrace_append hprefix tailTrace_5470085
  have hstable : (prefixWord ++ tailWord_5470085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5470085).length < 2 ^ (prefixWord ++ tailWord_5470085).sum := by decide
  have hdescent : baseEnd_5470085 < baseStart_5470085 := by decide
  rcases family_descends (prefixWord ++ tailWord_5470085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5470091 : List Nat := [1, 1, 1, 1, 4, 2, 1, 3, 9]
def baseStart_5470091 : Nat := 118140960795 + 5470091 * 2 ^ 59
def prefixEnd_5470091 : Nat := 4983230072969 + 3 ^ 40 * 5470091 * 2
def baseEnd_5470091 : Nat := 312087322981473664167335

theorem tailTrace_5470091 : CollatzResearch.WordTrace tailWord_5470091 prefixEnd_5470091 312087322981473664167335 := by
  unfold tailWord_5470091
  simp only [CollatzResearch.WordTrace]
  refine ⟨199510609225801999011082127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133007072817201332674054751 199510609225801999011082127)
  ·
    refine ⟨299265913838702998516623191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199510609225801999011082127 299265913838702998516623191)
    ·
      refine ⟨448898870758054497774934787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299265913838702998516623191 448898870758054497774934787)
      ·
        refine ⟨673348306137081746662402181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 448898870758054497774934787 673348306137081746662402181)
        ·
          refine ⟨126252807400702827499200409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 673348306137081746662402181 126252807400702827499200409)
          ·
            refine ⟨94689605550527120624400307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126252807400702827499200409 94689605550527120624400307)
            ·
              refine ⟨142034408325790680936600461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94689605550527120624400307 142034408325790680936600461)
              ·
                refine ⟨53262903122171505351225173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 142034408325790680936600461 53262903122171505351225173)
                ·
                  refine ⟨312087322981473664167335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 53262903122171505351225173 312087322981473664167335)
                  ·
                    rfl

theorem cell23_5470091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 9].length) (baseStart_5470091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5470091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5470091 prefixEnd_5470091 := by exact prefixLift 5470091
  have htrace : WordTrace (prefixWord ++ tailWord_5470091) baseStart_5470091 baseEnd_5470091 := by
    simpa [prefixWord, tailWord_5470091, baseEnd_5470091] using wordTrace_append hprefix tailTrace_5470091
  have hstable : (prefixWord ++ tailWord_5470091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5470091).length < 2 ^ (prefixWord ++ tailWord_5470091).sum := by decide
  have hdescent : baseEnd_5470091 < baseStart_5470091 := by decide
  rcases family_descends (prefixWord ++ tailWord_5470091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5470119 : List Nat := [1, 1, 6, 1, 2, 1, 1, 4, 2, 2, 2]
def baseStart_5470119 : Nat := 118140960795 + 5470119 * 2 ^ 59
def prefixEnd_5470119 : Nat := 4983230072969 + 3 ^ 40 * 5470119 * 2
def baseEnd_5470119 : Nat := 2808800284291588867955887

theorem tailTrace_5470119 : CollatzResearch.WordTrace tailWord_5470119 prefixEnd_5470119 2808800284291588867955887 := by
  unfold tailWord_5470119
  simp only [CollatzResearch.WordTrace]
  refine ⟨199511630469700559793101411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133007753646467039862067607 199511630469700559793101411)
  ·
    refine ⟨299267445704550839689652117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199511630469700559793101411 299267445704550839689652117)
    ·
      refine ⟨14028161517400820610452443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 299267445704550839689652117 14028161517400820610452443)
      ·
        refine ⟨21042242276101230915678665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14028161517400820610452443 21042242276101230915678665)
        ·
          refine ⟨15781681707075923186758999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21042242276101230915678665 15781681707075923186758999)
          ·
            refine ⟨23672522560613884780138499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15781681707075923186758999 23672522560613884780138499)
            ·
              refine ⟨35508783840920827170207749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23672522560613884780138499 35508783840920827170207749)
              ·
                refine ⟨6657896970172655094413953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35508783840920827170207749 6657896970172655094413953)
                ·
                  refine ⟨4993422727629491320810465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6657896970172655094413953 4993422727629491320810465)
                  ·
                    refine ⟨3745067045722118490607849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4993422727629491320810465 3745067045722118490607849)
                    ·
                      refine ⟨2808800284291588867955887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3745067045722118490607849 2808800284291588867955887)
                      ·
                        rfl

theorem cell23_5470119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_5470119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5470119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5470119 prefixEnd_5470119 := by exact prefixLift 5470119
  have htrace : WordTrace (prefixWord ++ tailWord_5470119) baseStart_5470119 baseEnd_5470119 := by
    simpa [prefixWord, tailWord_5470119, baseEnd_5470119] using wordTrace_append hprefix tailTrace_5470119
  have hstable : (prefixWord ++ tailWord_5470119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5470119).length < 2 ^ (prefixWord ++ tailWord_5470119).sum := by decide
  have hdescent : baseEnd_5470119 < baseStart_5470119 := by decide
  rcases family_descends (prefixWord ++ tailWord_5470119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5470235 : List Nat := [1, 1, 1, 1, 1, 1, 3, 4, 3, 5, 2]
def baseStart_5470235 : Nat := 118140960795 + 5470235 * 2 ^ 59
def prefixEnd_5470235 : Nat := 4983230072969 + 3 ^ 40 * 5470235 * 2
def baseEnd_5470235 : Nat := 2808859848047510414105353

theorem tailTrace_5470235 : CollatzResearch.WordTrace tailWord_5470235 prefixEnd_5470235 2808859848047510414105353 := by
  unfold tailWord_5470235
  simp only [CollatzResearch.WordTrace]
  refine ⟨199515861337280311604324159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133010574224853541069549439 199515861337280311604324159)
  ·
    refine ⟨299273792005920467406486239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199515861337280311604324159 299273792005920467406486239)
    ·
      refine ⟨448910688008880701109729359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299273792005920467406486239 448910688008880701109729359)
      ·
        refine ⟨673366032013321051664594039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 448910688008880701109729359 673366032013321051664594039)
        ·
          refine ⟨1010049048019981577496891059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 673366032013321051664594039 1010049048019981577496891059)
          ·
            refine ⟨1515073572029972366245336589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1010049048019981577496891059 1515073572029972366245336589)
            ·
              refine ⟨568152589511239637342001221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1515073572029972366245336589 568152589511239637342001221)
              ·
                refine ⟨106528610533357432001625229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 568152589511239637342001221 106528610533357432001625229)
                ·
                  refine ⟨39948228950009037000609461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106528610533357432001625229 39948228950009037000609461)
                  ·
                    refine ⟨3745146464063347218807137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39948228950009037000609461 3745146464063347218807137)
                    ·
                      refine ⟨2808859848047510414105353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3745146464063347218807137 2808859848047510414105353)
                      ·
                        rfl

theorem cell23_5470235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 5, 2].length) (baseStart_5470235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5470235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5470235 prefixEnd_5470235 := by exact prefixLift 5470235
  have htrace : WordTrace (prefixWord ++ tailWord_5470235) baseStart_5470235 baseEnd_5470235 := by
    simpa [prefixWord, tailWord_5470235, baseEnd_5470235] using wordTrace_append hprefix tailTrace_5470235
  have hstable : (prefixWord ++ tailWord_5470235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5470235).length < 2 ^ (prefixWord ++ tailWord_5470235).sum := by decide
  have hdescent : baseEnd_5470235 < baseStart_5470235 := by decide
  rcases family_descends (prefixWord ++ tailWord_5470235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5470236 : List Nat := [2, 2, 3, 1, 3, 2, 3, 2, 1, 4]
def baseStart_5470236 : Nat := 118140960795 + 5470236 * 2 ^ 59
def prefixEnd_5470236 : Nat := 4983230072969 + 3 ^ 40 * 5470236 * 2
def baseEnd_5470236 : Nat := 936286787176054970064283

theorem tailTrace_5470236 : CollatzResearch.WordTrace tailWord_5470236 prefixEnd_5470236 936286787176054970064283 := by
  unfold tailWord_5470236
  simp only [CollatzResearch.WordTrace]
  refine ⟨99757948905138344387555281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133010598540184459183407041 99757948905138344387555281)
  ·
    refine ⟨74818461678853758290666461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99757948905138344387555281 74818461678853758290666461)
    ·
      refine ⟨28056923129570159358999923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74818461678853758290666461 28056923129570159358999923)
      ·
        refine ⟨42085384694355239038499885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28056923129570159358999923 42085384694355239038499885)
        ·
          refine ⟨15782019260383214639437457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42085384694355239038499885 15782019260383214639437457)
          ·
            refine ⟨11836514445287410979578093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15782019260383214639437457 11836514445287410979578093)
            ·
              refine ⟨4438692916982779117341785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11836514445287410979578093 4438692916982779117341785)
              ·
                refine ⟨3329019687737084338006339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4438692916982779117341785 3329019687737084338006339)
                ·
                  refine ⟨4993529531605626507009509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3329019687737084338006339 4993529531605626507009509)
                  ·
                    refine ⟨936286787176054970064283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4993529531605626507009509 936286787176054970064283)
                    ·
                      rfl

theorem cell23_5470236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_5470236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5470236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5470236 prefixEnd_5470236 := by exact prefixLift 5470236
  have htrace : WordTrace (prefixWord ++ tailWord_5470236) baseStart_5470236 baseEnd_5470236 := by
    simpa [prefixWord, tailWord_5470236, baseEnd_5470236] using wordTrace_append hprefix tailTrace_5470236
  have hstable : (prefixWord ++ tailWord_5470236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5470236).length < 2 ^ (prefixWord ++ tailWord_5470236).sum := by decide
  have hdescent : baseEnd_5470236 < baseStart_5470236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5470236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5470262 : List Nat := [5, 1, 2, 1, 1, 1, 3, 1, 3, 5]
def baseStart_5470262 : Nat := 118140960795 + 5470262 * 2 ^ 59
def prefixEnd_5470262 : Nat := 4983230072969 + 3 ^ 40 * 5470262 * 2
def baseEnd_5470262 : Nat := 936291237341727269489243

theorem tailTrace_5470262 : CollatzResearch.WordTrace tailWord_5470262 prefixEnd_5470262 936291237341727269489243 := by
  unfold tailWord_5470262
  simp only [CollatzResearch.WordTrace]
  refine ⟨12469802881761405950972315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 133011230738788330143704693 12469802881761405950972315)
  ·
    refine ⟨18704704322642108926458473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12469802881761405950972315 18704704322642108926458473)
    ·
      refine ⟨14028528241981581694843855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18704704322642108926458473 14028528241981581694843855)
      ·
        refine ⟨21042792362972372542265783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14028528241981581694843855 21042792362972372542265783)
        ·
          refine ⟨31564188544458558813398675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21042792362972372542265783 31564188544458558813398675)
          ·
            refine ⟨47346282816687838220098013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31564188544458558813398675 47346282816687838220098013)
            ·
              refine ⟨17754856056257939332536755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47346282816687838220098013 17754856056257939332536755)
              ·
                refine ⟨26632284084386908998805133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17754856056257939332536755 26632284084386908998805133)
                ·
                  refine ⟨9987106531645090874551925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26632284084386908998805133 9987106531645090874551925)
                  ·
                    refine ⟨936291237341727269489243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9987106531645090874551925 936291237341727269489243)
                    ·
                      rfl

theorem cell23_5470262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_5470262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5470262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5470262 prefixEnd_5470262 := by exact prefixLift 5470262
  have htrace : WordTrace (prefixWord ++ tailWord_5470262) baseStart_5470262 baseEnd_5470262 := by
    simpa [prefixWord, tailWord_5470262, baseEnd_5470262] using wordTrace_append hprefix tailTrace_5470262
  have hstable : (prefixWord ++ tailWord_5470262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5470262).length < 2 ^ (prefixWord ++ tailWord_5470262).sum := by decide
  have hdescent : baseEnd_5470262 < baseStart_5470262 := by decide
  rcases family_descends (prefixWord ++ tailWord_5470262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5470269 : List Nat := [1, 4, 1, 3, 1, 1, 4, 1, 2, 3, 2]
def baseStart_5470269 : Nat := 118140960795 + 5470269 * 2 ^ 59
def prefixEnd_5470269 : Nat := 4983230072969 + 3 ^ 40 * 5470269 * 2
def baseEnd_5470269 : Nat := 2808877306389763281080197

theorem tailTrace_5470269 : CollatzResearch.WordTrace tailWord_5470269 prefixEnd_5470269 2808877306389763281080197 := by
  unfold tailWord_5470269
  simp only [CollatzResearch.WordTrace]
  refine ⟨199517101419157135411061861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133011400946104756940707907 199517101419157135411061861)
  ·
    refine ⟨37409456516091962889574099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 199517101419157135411061861 37409456516091962889574099)
    ·
      refine ⟨56114184774137944334361149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37409456516091962889574099 56114184774137944334361149)
      ·
        refine ⟨21042819290301729125385431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56114184774137944334361149 21042819290301729125385431)
        ·
          refine ⟨31564228935452593688078147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21042819290301729125385431 31564228935452593688078147)
          ·
            refine ⟨47346343403178890532117221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31564228935452593688078147 47346343403178890532117221)
            ·
              refine ⟨8877439388096041974771979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47346343403178890532117221 8877439388096041974771979)
              ·
                refine ⟨13316159082144062962157969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8877439388096041974771979 13316159082144062962157969)
                ·
                  refine ⟨9987119311608047221618477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13316159082144062962157969 9987119311608047221618477)
                  ·
                    refine ⟨3745169741853017708106929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9987119311608047221618477 3745169741853017708106929)
                    ·
                      refine ⟨2808877306389763281080197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3745169741853017708106929 2808877306389763281080197)
                      ·
                        rfl

theorem cell23_5470269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_5470269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5470269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5470269 prefixEnd_5470269 := by exact prefixLift 5470269
  have htrace : WordTrace (prefixWord ++ tailWord_5470269) baseStart_5470269 baseEnd_5470269 := by
    simpa [prefixWord, tailWord_5470269, baseEnd_5470269] using wordTrace_append hprefix tailTrace_5470269
  have hstable : (prefixWord ++ tailWord_5470269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5470269).length < 2 ^ (prefixWord ++ tailWord_5470269).sum := by decide
  have hdescent : baseEnd_5470269 < baseStart_5470269 := by decide
  rcases family_descends (prefixWord ++ tailWord_5470269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5470275 : List Nat := [1, 1, 1, 3, 1, 2, 2, 4, 4, 4]
def baseStart_5470275 : Nat := 118140960795 + 5470275 * 2 ^ 59
def prefixEnd_5470275 : Nat := 4983230072969 + 3 ^ 40 * 5470275 * 2
def baseEnd_5470275 : Nat := 936293462424563419201723

theorem tailTrace_5470275 : CollatzResearch.WordTrace tailWord_5470275 prefixEnd_5470275 936293462424563419201723 := by
  unfold tailWord_5470275
  simp only [CollatzResearch.WordTrace]
  refine ⟨199517320257135398435780279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133011546838090265623853519 199517320257135398435780279)
  ·
    refine ⟨299275980385703097653670419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199517320257135398435780279 299275980385703097653670419)
    ·
      refine ⟨448913970578554646480505629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299275980385703097653670419 448913970578554646480505629)
      ·
        refine ⟨168342738966957992430189611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 448913970578554646480505629 168342738966957992430189611)
        ·
          refine ⟨252514108450436988645284417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168342738966957992430189611 252514108450436988645284417)
          ·
            refine ⟨189385581337827741483963313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 252514108450436988645284417 189385581337827741483963313)
            ·
              refine ⟨142039186003370806112972485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189385581337827741483963313 142039186003370806112972485)
              ·
                refine ⟨26632347375632026146182341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 142039186003370806112972485 26632347375632026146182341)
                ·
                  refine ⟨4993565132931004902409189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26632347375632026146182341 4993565132931004902409189)
                  ·
                    refine ⟨936293462424563419201723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4993565132931004902409189 936293462424563419201723)
                    ·
                      rfl

theorem cell23_5470275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 4, 4].length) (baseStart_5470275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5470275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5470275 prefixEnd_5470275 := by exact prefixLift 5470275
  have htrace : WordTrace (prefixWord ++ tailWord_5470275) baseStart_5470275 baseEnd_5470275 := by
    simpa [prefixWord, tailWord_5470275, baseEnd_5470275] using wordTrace_append hprefix tailTrace_5470275
  have hstable : (prefixWord ++ tailWord_5470275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5470275).length < 2 ^ (prefixWord ++ tailWord_5470275).sum := by decide
  have hdescent : baseEnd_5470275 < baseStart_5470275 := by decide
  rcases family_descends (prefixWord ++ tailWord_5470275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5470293 : List Nat := [1, 3, 2, 2, 1, 5, 2, 2, 1, 1, 3]
def baseStart_5470293 : Nat := 118140960795 + 5470293 * 2 ^ 59
def prefixEnd_5470293 : Nat := 4983230072969 + 3 ^ 40 * 5470293 * 2
def baseEnd_5470293 : Nat := 2808889629925471187180087

theorem tailTrace_5470293 : CollatzResearch.WordTrace tailWord_5470293 prefixEnd_5470293 2808889629925471187180087 := by
  unfold tailWord_5470293
  simp only [CollatzResearch.WordTrace]
  refine ⟨199517976771070187509935533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133011984514046791673290355 199517976771070187509935533)
  ·
    refine ⟨74819241289151320316225825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199517976771070187509935533 74819241289151320316225825)
    ·
      refine ⟨56114430966863490237169369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74819241289151320316225825 56114430966863490237169369)
      ·
        refine ⟨42085823225147617677877027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56114430966863490237169369 42085823225147617677877027)
        ·
          refine ⟨63128734837721426516815541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42085823225147617677877027 63128734837721426516815541)
          ·
            refine ⟨5918318891036383735951457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63128734837721426516815541 5918318891036383735951457)
            ·
              refine ⟨4438739168277287801963593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5918318891036383735951457 4438739168277287801963593)
              ·
                refine ⟨3329054376207965851472695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4438739168277287801963593 3329054376207965851472695)
                ·
                  refine ⟨4993581564311948777209043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3329054376207965851472695 4993581564311948777209043)
                  ·
                    refine ⟨7490372346467923165813565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4993581564311948777209043 7490372346467923165813565)
                    ·
                      refine ⟨2808889629925471187180087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7490372346467923165813565 2808889629925471187180087)
                      ·
                        rfl

theorem cell23_5470293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 2, 1, 1, 3].length) (baseStart_5470293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5470293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5470293 prefixEnd_5470293 := by exact prefixLift 5470293
  have htrace : WordTrace (prefixWord ++ tailWord_5470293) baseStart_5470293 baseEnd_5470293 := by
    simpa [prefixWord, tailWord_5470293, baseEnd_5470293] using wordTrace_append hprefix tailTrace_5470293
  have hstable : (prefixWord ++ tailWord_5470293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5470293).length < 2 ^ (prefixWord ++ tailWord_5470293).sum := by decide
  have hdescent : baseEnd_5470293 < baseStart_5470293 := by decide
  rcases family_descends (prefixWord ++ tailWord_5470293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5470322 : List Nat := [3, 2, 1, 2, 2, 3, 3, 7]
def baseStart_5470322 : Nat := 118140960795 + 5470322 * 2 ^ 59
def prefixEnd_5470322 : Nat := 4983230072969 + 3 ^ 40 * 5470322 * 2
def baseEnd_5470322 : Nat := 104033500772757465693239

theorem tailTrace_5470322 : CollatzResearch.WordTrace tailWord_5470322 prefixEnd_5470322 104033500772757465693239 := by
  unfold tailWord_5470322
  simp only [CollatzResearch.WordTrace]
  refine ⟨49879758621991281365685305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133012689658643416975160813 49879758621991281365685305)
  ·
    refine ⟨37409818966493461024263979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49879758621991281365685305 37409818966493461024263979)
    ·
      refine ⟨56114728449740191536395969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37409818966493461024263979 56114728449740191536395969)
      ·
        refine ⟨42086046337305143652296977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56114728449740191536395969 42086046337305143652296977)
        ·
          refine ⟨31564534752978857739222733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42086046337305143652296977 31564534752978857739222733)
          ·
            refine ⟨11836700532367071652208525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31564534752978857739222733 11836700532367071652208525)
            ·
              refine ⟨4438762699637651869578197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11836700532367071652208525 4438762699637651869578197)
              ·
                refine ⟨104033500772757465693239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4438762699637651869578197 104033500772757465693239)
                ·
                  rfl

theorem cell23_5470322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 7].length) (baseStart_5470322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5470322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5470322 prefixEnd_5470322 := by exact prefixLift 5470322
  have htrace : WordTrace (prefixWord ++ tailWord_5470322) baseStart_5470322 baseEnd_5470322 := by
    simpa [prefixWord, tailWord_5470322, baseEnd_5470322] using wordTrace_append hprefix tailTrace_5470322
  have hstable : (prefixWord ++ tailWord_5470322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5470322).length < 2 ^ (prefixWord ++ tailWord_5470322).sum := by decide
  have hdescent : baseEnd_5470322 < baseStart_5470322 := by decide
  rcases family_descends (prefixWord ++ tailWord_5470322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5470332 : List Nat := [2, 2, 2, 1, 1, 4, 2, 2, 1, 3, 3]
def baseStart_5470332 : Nat := 118140960795 + 5470332 * 2 ^ 59
def prefixEnd_5470332 : Nat := 4983230072969 + 3 ^ 40 * 5470332 * 2
def baseEnd_5470332 : Nat := 2808909655670996534592407

theorem tailTrace_5470332 : CollatzResearch.WordTrace tailWord_5470332 prefixEnd_5470332 2808909655670996534592407 := by
  unfold tailWord_5470332
  simp only [CollatzResearch.WordTrace]
  refine ⟨99759699608964448585302625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133012932811952598113736833 99759699608964448585302625)
  ·
    refine ⟨74819774706723336438976969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99759699608964448585302625 74819774706723336438976969)
    ·
      refine ⟨56114831030042502329232727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74819774706723336438976969 56114831030042502329232727)
      ·
        refine ⟨84172246545063753493849091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56114831030042502329232727 84172246545063753493849091)
        ·
          refine ⟨126258369817595630240773637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84172246545063753493849091 126258369817595630240773637)
          ·
            refine ⟨23673444340799180670145057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126258369817595630240773637 23673444340799180670145057)
            ·
              refine ⟨17755083255599385502608793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23673444340799180670145057 17755083255599385502608793)
              ·
                refine ⟨13316312441699539126956595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17755083255599385502608793 13316312441699539126956595)
                ·
                  refine ⟨19974468662549308690434893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13316312441699539126956595 19974468662549308690434893)
                  ·
                    refine ⟨7490425748455990758913085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19974468662549308690434893 7490425748455990758913085)
                    ·
                      refine ⟨2808909655670996534592407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7490425748455990758913085 2808909655670996534592407)
                      ·
                        rfl

theorem cell23_5470332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 1, 3, 3].length) (baseStart_5470332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5470332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5470332 prefixEnd_5470332 := by exact prefixLift 5470332
  have htrace : WordTrace (prefixWord ++ tailWord_5470332) baseStart_5470332 baseEnd_5470332 := by
    simpa [prefixWord, tailWord_5470332, baseEnd_5470332] using wordTrace_append hprefix tailTrace_5470332
  have hstable : (prefixWord ++ tailWord_5470332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5470332).length < 2 ^ (prefixWord ++ tailWord_5470332).sum := by decide
  have hdescent : baseEnd_5470332 < baseStart_5470332 := by decide
  rcases family_descends (prefixWord ++ tailWord_5470332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5470333 : List Nat := [1, 4, 1, 1, 3, 3, 2, 3, 1, 2, 2]
def baseStart_5470333 : Nat := 118140960795 + 5470333 * 2 ^ 59
def prefixEnd_5470333 : Nat := 4983230072969 + 3 ^ 40 * 5470333 * 2
def baseEnd_5470333 : Nat := 2808910169151651030679903

theorem tailTrace_5470333 : CollatzResearch.WordTrace tailWord_5470333 prefixEnd_5470333 2808910169151651030679903 := by
  unfold tailWord_5470333
  simp only [CollatzResearch.WordTrace]
  refine ⟨199519435690925274341391653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133012957127283516227594435 199519435690925274341391653)
  ·
    refine ⟨37409894192048488939010935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 199519435690925274341391653 37409894192048488939010935)
    ·
      refine ⟨56114841288072733408516403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37409894192048488939010935 56114841288072733408516403)
      ·
        refine ⟨84172261932109100112774605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56114841288072733408516403 84172261932109100112774605)
        ·
          refine ⟨31564598224540912542290477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84172261932109100112774605 31564598224540912542290477)
          ·
            refine ⟨11836724334202842203358929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31564598224540912542290477 11836724334202842203358929)
            ·
              refine ⟨8877543250652131652519197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11836724334202842203358929 8877543250652131652519197)
              ·
                refine ⟨3329078718994549369694699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8877543250652131652519197 3329078718994549369694699)
                ·
                  refine ⟨4993618078491824054542049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3329078718994549369694699 4993618078491824054542049)
                  ·
                    refine ⟨3745213558868868040906537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4993618078491824054542049 3745213558868868040906537)
                    ·
                      refine ⟨2808910169151651030679903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3745213558868868040906537 2808910169151651030679903)
                      ·
                        rfl

theorem cell23_5470333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 3, 1, 2, 2].length) (baseStart_5470333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5470333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5470333 prefixEnd_5470333 := by exact prefixLift 5470333
  have htrace : WordTrace (prefixWord ++ tailWord_5470333) baseStart_5470333 baseEnd_5470333 := by
    simpa [prefixWord, tailWord_5470333, baseEnd_5470333] using wordTrace_append hprefix tailTrace_5470333
  have hstable : (prefixWord ++ tailWord_5470333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5470333).length < 2 ^ (prefixWord ++ tailWord_5470333).sum := by decide
  have hdescent : baseEnd_5470333 < baseStart_5470333 := by decide
  rcases family_descends (prefixWord ++ tailWord_5470333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5470425 : List Nat := [1, 2, 1, 2, 3, 1, 2, 1, 3, 7]
def baseStart_5470425 : Nat := 118140960795 + 5470425 * 2 ^ 59
def prefixEnd_5470425 : Nat := 4983230072969 + 3 ^ 40 * 5470425 * 2
def baseEnd_5470425 : Nat := 936319136457288223576493

theorem tailTrace_5470425 : CollatzResearch.WordTrace tailWord_5470425 prefixEnd_5470425 936319136457288223576493 := by
  unfold tailWord_5470425
  simp only [CollatzResearch.WordTrace]
  refine ⟨199522791206591974053740729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133015194137727982702493819 199522791206591974053740729)
  ·
    refine ⟨149642093404943980540305547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199522791206591974053740729 149642093404943980540305547)
    ·
      refine ⟨224463140107415970810458321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149642093404943980540305547 224463140107415970810458321)
      ·
        refine ⟨168347355080561978107843741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224463140107415970810458321 168347355080561978107843741)
        ·
          refine ⟨63130258155210741790441403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168347355080561978107843741 63130258155210741790441403)
          ·
            refine ⟨94695387232816112685662105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63130258155210741790441403 94695387232816112685662105)
            ·
              refine ⟨71021540424612084514246579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94695387232816112685662105 71021540424612084514246579)
              ·
                refine ⟨106532310636918126771369869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71021540424612084514246579 106532310636918126771369869)
                ·
                  refine ⟨39949616488844297539263701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106532310636918126771369869 39949616488844297539263701)
                  ·
                    refine ⟨936319136457288223576493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39949616488844297539263701 936319136457288223576493)
                    ·
                      rfl

theorem cell23_5470425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 7].length) (baseStart_5470425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5470425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5470425 prefixEnd_5470425 := by exact prefixLift 5470425
  have htrace : WordTrace (prefixWord ++ tailWord_5470425) baseStart_5470425 baseEnd_5470425 := by
    simpa [prefixWord, tailWord_5470425, baseEnd_5470425] using wordTrace_append hprefix tailTrace_5470425
  have hstable : (prefixWord ++ tailWord_5470425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5470425).length < 2 ^ (prefixWord ++ tailWord_5470425).sum := by decide
  have hdescent : baseEnd_5470425 < baseStart_5470425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5470425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5470466 : List Nat := [3, 4, 1, 1, 2, 1, 1, 1, 2, 5, 2]
def baseStart_5470466 : Nat := 118140960795 + 5470466 * 2 ^ 59
def prefixEnd_5470466 : Nat := 4983230072969 + 3 ^ 40 * 5470466 * 2
def baseEnd_5470466 : Nat := 2808978462078699010316791

theorem tailTrace_5470466 : CollatzResearch.WordTrace tailWord_5470466 prefixEnd_5470466 2808978462078699010316791 := by
  unfold tailWord_5470466
  simp only [CollatzResearch.WordTrace]
  refine ⟨49881071649860859513995813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133016191066295625370655501 49881071649860859513995813)
  ·
    refine ⟨9352700934348911158874215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49881071649860859513995813 9352700934348911158874215)
    ·
      refine ⟨14029051401523366738311323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9352700934348911158874215 14029051401523366738311323)
      ·
        refine ⟨21043577102285050107466985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14029051401523366738311323 21043577102285050107466985)
        ·
          refine ⟨15782682826713787580600239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21043577102285050107466985 15782682826713787580600239)
          ·
            refine ⟨23674024240070681370900359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15782682826713787580600239 23674024240070681370900359)
            ·
              refine ⟨35511036360106022056350539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23674024240070681370900359 35511036360106022056350539)
              ·
                refine ⟨53266554540159033084525809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35511036360106022056350539 53266554540159033084525809)
                ·
                  refine ⟨39949915905119274813394357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53266554540159033084525809 39949915905119274813394357)
                  ·
                    refine ⟨3745304616104932013755721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39949915905119274813394357 3745304616104932013755721)
                    ·
                      refine ⟨2808978462078699010316791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3745304616104932013755721 2808978462078699010316791)
                      ·
                        rfl

theorem cell23_5470466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_5470466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5470466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5470466 prefixEnd_5470466 := by exact prefixLift 5470466
  have htrace : WordTrace (prefixWord ++ tailWord_5470466) baseStart_5470466 baseEnd_5470466 := by
    simpa [prefixWord, tailWord_5470466, baseEnd_5470466] using wordTrace_append hprefix tailTrace_5470466
  have hstable : (prefixWord ++ tailWord_5470466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5470466).length < 2 ^ (prefixWord ++ tailWord_5470466).sum := by decide
  have hdescent : baseEnd_5470466 < baseStart_5470466 := by decide
  rcases family_descends (prefixWord ++ tailWord_5470466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5470493 : List Nat := [1, 4, 2, 3, 3, 1, 1, 1, 2, 5]
def baseStart_5470493 : Nat := 118140960795 + 5470493 * 2 ^ 59
def prefixEnd_5470493 : Nat := 4983230072969 + 3 ^ 40 * 5470493 * 2
def baseEnd_5470493 : Nat := 936330775352123468226389

theorem tailTrace_5470493 : CollatzResearch.WordTrace tailWord_5470493 prefixEnd_5470493 936330775352123468226389 := by
  unfold tailWord_5470493
  simp only [CollatzResearch.WordTrace]
  refine ⟨199525271370345621667216133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133016847580230414444810755 199525271370345621667216133)
  ·
    refine ⟨37410988381939804062603025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 199525271370345621667216133 37410988381939804062603025)
    ·
      refine ⟨28058241286454853046952269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37410988381939804062603025 28058241286454853046952269)
      ·
        refine ⟨10521840482420569892607101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28058241286454853046952269 10521840482420569892607101)
        ·
          refine ⟨3945690180907713709727663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10521840482420569892607101 3945690180907713709727663)
          ·
            refine ⟨5918535271361570564591495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3945690180907713709727663 5918535271361570564591495)
            ·
              refine ⟨8877802907042355846887243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5918535271361570564591495 8877802907042355846887243)
              ·
                refine ⟨13316704360563533770330865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8877802907042355846887243 13316704360563533770330865)
                ·
                  refine ⟨9987528270422650327748149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13316704360563533770330865 9987528270422650327748149)
                  ·
                    refine ⟨936330775352123468226389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9987528270422650327748149 936330775352123468226389)
                    ·
                      rfl

theorem cell23_5470493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_5470493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5470493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5470493 prefixEnd_5470493 := by exact prefixLift 5470493
  have htrace : WordTrace (prefixWord ++ tailWord_5470493) baseStart_5470493 baseEnd_5470493 := by
    simpa [prefixWord, tailWord_5470493, baseEnd_5470493] using wordTrace_append hprefix tailTrace_5470493
  have hstable : (prefixWord ++ tailWord_5470493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5470493).length < 2 ^ (prefixWord ++ tailWord_5470493).sum := by decide
  have hdescent : baseEnd_5470493 < baseStart_5470493 := by decide
  rcases family_descends (prefixWord ++ tailWord_5470493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5470496 : List Nat := [2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 4]
def baseStart_5470496 : Nat := 118140960795 + 5470496 * 2 ^ 59
def prefixEnd_5470496 : Nat := 4983230072969 + 3 ^ 40 * 5470496 * 2
def baseEnd_5470496 : Nat := 2808993866498333892941653

theorem tailTrace_5470496 : CollatzResearch.WordTrace tailWord_5470496 prefixEnd_5470496 2808993866498333892941653 := by
  unfold tailWord_5470496
  simp only [CollatzResearch.WordTrace]
  refine ⟨99762690394667376589787671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133016920526223168786383561 99762690394667376589787671)
  ·
    refine ⟨149644035592001064884681507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99762690394667376589787671 149644035592001064884681507)
    ·
      refine ⟨224466053388001597327022261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149644035592001064884681507 224466053388001597327022261)
      ·
        refine ⟨21043692505125149749408337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 224466053388001597327022261 21043692505125149749408337)
        ·
          refine ⟨15782769378843862312056253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21043692505125149749408337 15782769378843862312056253)
          ·
            refine ⟨5918538517066448367021095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15782769378843862312056253 5918538517066448367021095)
            ·
              refine ⟨8877807775599672550531643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5918538517066448367021095 8877807775599672550531643)
              ·
                refine ⟨13316711663399508825797465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8877807775599672550531643 13316711663399508825797465)
                ·
                  refine ⟨9987533747549631619348099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13316711663399508825797465 9987533747549631619348099)
                  ·
                    refine ⟨14981300621324447429022149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9987533747549631619348099 14981300621324447429022149)
                    ·
                      refine ⟨2808993866498333892941653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14981300621324447429022149 2808993866498333892941653)
                      ·
                        rfl

theorem cell23_5470496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_5470496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5470496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5470496 prefixEnd_5470496 := by exact prefixLift 5470496
  have htrace : WordTrace (prefixWord ++ tailWord_5470496) baseStart_5470496 baseEnd_5470496 := by
    simpa [prefixWord, tailWord_5470496, baseEnd_5470496] using wordTrace_append hprefix tailTrace_5470496
  have hstable : (prefixWord ++ tailWord_5470496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5470496).length < 2 ^ (prefixWord ++ tailWord_5470496).sum := by decide
  have hdescent : baseEnd_5470496 < baseStart_5470496 := by decide
  rcases family_descends (prefixWord ++ tailWord_5470496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5470522 : List Nat := [3, 1, 1, 1, 4, 2, 1, 1, 1, 2, 6]
def baseStart_5470522 : Nat := 118140960795 + 5470522 * 2 ^ 59
def prefixEnd_5470522 : Nat := 4983230072969 + 3 ^ 40 * 5470522 * 2
def baseEnd_5470522 : Nat := 2809007216995350791216533

theorem tailTrace_5470522 : CollatzResearch.WordTrace tailWord_5470522 prefixEnd_5470522 2809007216995350791216533 := by
  unfold tailWord_5470522
  simp only [CollatzResearch.WordTrace]
  refine ⟨49881582271810139905005455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133017552724827039746681213 49881582271810139905005455)
  ·
    refine ⟨74822373407715209857508183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49881582271810139905005455 74822373407715209857508183)
    ·
      refine ⟨112233560111572814786262275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74822373407715209857508183 112233560111572814786262275)
      ·
        refine ⟨168350340167359222179393413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112233560111572814786262275 168350340167359222179393413)
        ·
          refine ⟨31565688781379854158636265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 168350340167359222179393413 31565688781379854158636265)
          ·
            refine ⟨23674266586034890618977199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31565688781379854158636265 23674266586034890618977199)
            ·
              refine ⟨35511399879052335928465799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23674266586034890618977199 35511399879052335928465799)
              ·
                refine ⟨53267099818578503892698699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35511399879052335928465799 53267099818578503892698699)
                ·
                  refine ⟨79900649727867755839048049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53267099818578503892698699 79900649727867755839048049)
                  ·
                    refine ⟨59925487295900816879286037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 79900649727867755839048049 59925487295900816879286037)
                    ·
                      refine ⟨2809007216995350791216533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59925487295900816879286037 2809007216995350791216533)
                      ·
                        rfl

theorem cell23_5470522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 1, 2, 6].length) (baseStart_5470522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5470522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5470522 prefixEnd_5470522 := by exact prefixLift 5470522
  have htrace : WordTrace (prefixWord ++ tailWord_5470522) baseStart_5470522 baseEnd_5470522 := by
    simpa [prefixWord, tailWord_5470522, baseEnd_5470522] using wordTrace_append hprefix tailTrace_5470522
  have hstable : (prefixWord ++ tailWord_5470522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5470522).length < 2 ^ (prefixWord ++ tailWord_5470522).sum := by decide
  have hdescent : baseEnd_5470522 < baseStart_5470522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5470522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5470539 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 6, 3, 2]
def baseStart_5470539 : Nat := 118140960795 + 5470539 * 2 ^ 59
def prefixEnd_5470539 : Nat := 4983230072969 + 3 ^ 40 * 5470539 * 2
def baseEnd_5470539 : Nat := 2809015946166477224703955

theorem tailTrace_5470539 : CollatzResearch.WordTrace tailWord_5470539 prefixEnd_5470539 2809015946166477224703955 := by
  unfold tailWord_5470539
  simp only [CollatzResearch.WordTrace]
  refine ⟨199526949128178971523390671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133017966085452647682260447 199526949128178971523390671)
  ·
    refine ⟨299290423692268457285086007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199526949128178971523390671 299290423692268457285086007)
    ·
      refine ⟨448935635538402685927629011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299290423692268457285086007 448935635538402685927629011)
      ·
        refine ⟨673403453307604028891443517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 448935635538402685927629011 673403453307604028891443517)
        ·
          refine ⟨252526294990351510834291319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 673403453307604028891443517 252526294990351510834291319)
          ·
            refine ⟨378789442485527266251436979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252526294990351510834291319 378789442485527266251436979)
            ·
              refine ⟨568184163728290899377155469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 378789442485527266251436979 568184163728290899377155469)
              ·
                refine ⟨213069061398109087266433301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 568184163728290899377155469 213069061398109087266433301)
                ·
                  refine ⟨9987612253036363465614061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 213069061398109087266433301 9987612253036363465614061)
                  ·
                    refine ⟨3745354594888636299605273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9987612253036363465614061 3745354594888636299605273)
                    ·
                      refine ⟨2809015946166477224703955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3745354594888636299605273 2809015946166477224703955)
                      ·
                        rfl

theorem cell23_5470539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 6, 3, 2].length) (baseStart_5470539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5470539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5470539 prefixEnd_5470539 := by exact prefixLift 5470539
  have htrace : WordTrace (prefixWord ++ tailWord_5470539) baseStart_5470539 baseEnd_5470539 := by
    simpa [prefixWord, tailWord_5470539, baseEnd_5470539] using wordTrace_append hprefix tailTrace_5470539
  have hstable : (prefixWord ++ tailWord_5470539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5470539).length < 2 ^ (prefixWord ++ tailWord_5470539).sum := by decide
  have hdescent : baseEnd_5470539 < baseStart_5470539 := by decide
  rcases family_descends (prefixWord ++ tailWord_5470539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5470546 : List Nat := [3, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3]
def baseStart_5470546 : Nat := 118140960795 + 5470546 * 2 ^ 59
def prefixEnd_5470546 : Nat := 4983230072969 + 3 ^ 40 * 5470546 * 2
def baseEnd_5470546 : Nat := 2809019540531058697316423

theorem tailTrace_5470546 : CollatzResearch.WordTrace tailWord_5470546 prefixEnd_5470546 2809019540531058697316423 := by
  unfold tailWord_5470546
  simp only [CollatzResearch.WordTrace]
  refine ⟨49881801109788402929723873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133018136292769074479263661 49881801109788402929723873)
  ·
    refine ⟨37411350832341302197292905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49881801109788402929723873 37411350832341302197292905)
    ·
      refine ⟨28058513124255976647969679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37411350832341302197292905 28058513124255976647969679)
      ·
        refine ⟨42087769686383964971954519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28058513124255976647969679 42087769686383964971954519)
        ·
          refine ⟨63131654529575947457931779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42087769686383964971954519 63131654529575947457931779)
          ·
            refine ⟨94697481794363921186897669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63131654529575947457931779 94697481794363921186897669)
            ·
              refine ⟨17755777836443235222543313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94697481794363921186897669 17755777836443235222543313)
              ·
                refine ⟨13316833377332426416907485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17755777836443235222543313 13316833377332426416907485)
                ·
                  refine ⟨4993812516499659906340307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13316833377332426416907485 4993812516499659906340307)
                  ·
                    refine ⟨7490718774749489859510461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4993812516499659906340307 7490718774749489859510461)
                    ·
                      refine ⟨2809019540531058697316423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7490718774749489859510461 2809019540531058697316423)
                      ·
                        rfl

theorem cell23_5470546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_5470546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5470546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5470546 prefixEnd_5470546 := by exact prefixLift 5470546
  have htrace : WordTrace (prefixWord ++ tailWord_5470546) baseStart_5470546 baseEnd_5470546 := by
    simpa [prefixWord, tailWord_5470546, baseEnd_5470546] using wordTrace_append hprefix tailTrace_5470546
  have hstable : (prefixWord ++ tailWord_5470546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5470546).length < 2 ^ (prefixWord ++ tailWord_5470546).sum := by decide
  have hdescent : baseEnd_5470546 < baseStart_5470546 := by decide
  rcases family_descends (prefixWord ++ tailWord_5470546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5470569 : List Nat := [1, 2, 1, 1, 1, 3, 3, 5, 1, 1, 4]
def baseStart_5470569 : Nat := 118140960795 + 5470569 * 2 ^ 59
def prefixEnd_5470569 : Nat := 4983230072969 + 3 ^ 40 * 5470569 * 2
def baseEnd_5470569 : Nat := 2809031350586112107328817

theorem tailTrace_5470569 : CollatzResearch.WordTrace tailWord_5470569 prefixEnd_5470569 2809031350586112107328817 := by
  unfold tailWord_5470569
  simp only [CollatzResearch.WordTrace]
  refine ⟨199528043318070286646982761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133018695545380191097988507 199528043318070286646982761)
  ·
    refine ⟨149646032488552714985237071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199528043318070286646982761 149646032488552714985237071)
    ·
      refine ⟨224469048732829072477855607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149646032488552714985237071 224469048732829072477855607)
      ·
        refine ⟨336703573099243608716783411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224469048732829072477855607 336703573099243608716783411)
        ·
          refine ⟨505055359648865413075175117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 336703573099243608716783411 505055359648865413075175117)
          ·
            refine ⟨189395759868324529903190669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 505055359648865413075175117 189395759868324529903190669)
            ·
              refine ⟨71023409950621698713696501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 189395759868324529903190669 71023409950621698713696501)
              ·
                refine ⟨6658444682870784254409047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71023409950621698713696501 6658444682870784254409047)
                ·
                  refine ⟨9987667024306176381613571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6658444682870784254409047 9987667024306176381613571)
                  ·
                    refine ⟨14981500536459264572420357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9987667024306176381613571 14981500536459264572420357)
                    ·
                      refine ⟨2809031350586112107328817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14981500536459264572420357 2809031350586112107328817)
                      ·
                        rfl

theorem cell23_5470569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 5, 1, 1, 4].length) (baseStart_5470569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5470569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5470569 prefixEnd_5470569 := by exact prefixLift 5470569
  have htrace : WordTrace (prefixWord ++ tailWord_5470569) baseStart_5470569 baseEnd_5470569 := by
    simpa [prefixWord, tailWord_5470569, baseEnd_5470569] using wordTrace_append hprefix tailTrace_5470569
  have hstable : (prefixWord ++ tailWord_5470569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5470569).length < 2 ^ (prefixWord ++ tailWord_5470569).sum := by decide
  have hdescent : baseEnd_5470569 < baseStart_5470569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5470569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5470589 : List Nat := [1, 4, 1, 1, 2, 3, 2, 2, 1, 1, 5]
def baseStart_5470589 : Nat := 118140960795 + 5470589 * 2 ^ 59
def prefixEnd_5470589 : Nat := 4983230072969 + 3 ^ 40 * 5470589 * 2
def baseEnd_5470589 : Nat := 2809041620199202029078725

theorem tailTrace_5470589 : CollatzResearch.WordTrace tailWord_5470589 prefixEnd_5470589 2809041620199202029078725 := by
  unfold tailWord_5470589
  simp only [CollatzResearch.WordTrace]
  refine ⟨199528772777997830062710821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133019181851998553375140547 199528772777997830062710821)
  ·
    refine ⟨37411644895874593136758279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 199528772777997830062710821 37411644895874593136758279)
    ·
      refine ⟨56117467343811889705137419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37411644895874593136758279 56117467343811889705137419)
      ·
        refine ⟨84176201015717834557706129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56117467343811889705137419 84176201015717834557706129)
        ·
          refine ⟨63132150761788375918279597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84176201015717834557706129 63132150761788375918279597)
          ·
            refine ⟨23674556535670640969354849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63132150761788375918279597 23674556535670640969354849)
            ·
              refine ⟨17755917401752980727016137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23674556535670640969354849 17755917401752980727016137)
              ·
                refine ⟨13316938051314735545262103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17755917401752980727016137 13316938051314735545262103)
                ·
                  refine ⟨19975407076972103317893155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13316938051314735545262103 19975407076972103317893155)
                  ·
                    refine ⟨29963110615458154976839733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19975407076972103317893155 29963110615458154976839733)
                    ·
                      refine ⟨2809041620199202029078725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29963110615458154976839733 2809041620199202029078725)
                      ·
                        rfl

theorem cell23_5470589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_5470589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5470589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5470589 prefixEnd_5470589 := by exact prefixLift 5470589
  have htrace : WordTrace (prefixWord ++ tailWord_5470589) baseStart_5470589 baseEnd_5470589 := by
    simpa [prefixWord, tailWord_5470589, baseEnd_5470589] using wordTrace_append hprefix tailTrace_5470589
  have hstable : (prefixWord ++ tailWord_5470589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5470589).length < 2 ^ (prefixWord ++ tailWord_5470589).sum := by decide
  have hdescent : baseEnd_5470589 < baseStart_5470589 := by decide
  rcases family_descends (prefixWord ++ tailWord_5470589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5470596 : List Nat := [2, 3, 2, 1, 1, 2, 3, 3, 2, 4]
def baseStart_5470596 : Nat := 118140960795 + 5470596 * 2 ^ 59
def prefixEnd_5470596 : Nat := 4983230072969 + 3 ^ 40 * 5470596 * 2
def baseEnd_5470596 : Nat := 936348404854594500563731

theorem tailTrace_5470596 : CollatzResearch.WordTrace tailWord_5470596 prefixEnd_5470596 936348404854594500563731 := by
  unfold tailWord_5470596
  simp only [CollatzResearch.WordTrace]
  refine ⟨99764514044486235129107821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133019352059314980172143761 99764514044486235129107821)
  ·
    refine ⟨37411692766682338173415433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99764514044486235129107821 37411692766682338173415433)
    ·
      refine ⟨28058769575011753630061575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37411692766682338173415433 28058769575011753630061575)
      ·
        refine ⟨42088154362517630445092363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28058769575011753630061575 42088154362517630445092363)
        ·
          refine ⟨63132231543776445667638545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42088154362517630445092363 63132231543776445667638545)
          ·
            refine ⟨47349173657832334250728909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63132231543776445667638545 47349173657832334250728909)
            ·
              refine ⟨17755940121687125344023341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47349173657832334250728909 17755940121687125344023341)
              ·
                refine ⟨6658477545632672004008753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17755940121687125344023341 6658477545632672004008753)
                ·
                  refine ⟨4993858159224504003006565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6658477545632672004008753 4993858159224504003006565)
                  ·
                    refine ⟨936348404854594500563731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4993858159224504003006565 936348404854594500563731)
                    ·
                      rfl

theorem cell23_5470596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_5470596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5470596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5470596 prefixEnd_5470596 := by exact prefixLift 5470596
  have htrace : WordTrace (prefixWord ++ tailWord_5470596) baseStart_5470596 baseEnd_5470596 := by
    simpa [prefixWord, tailWord_5470596, baseEnd_5470596] using wordTrace_append hprefix tailTrace_5470596
  have hstable : (prefixWord ++ tailWord_5470596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5470596).length < 2 ^ (prefixWord ++ tailWord_5470596).sum := by decide
  have hdescent : baseEnd_5470596 < baseStart_5470596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5470596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5470599 : List Nat := [1, 1, 4, 2, 2, 1, 2, 3, 1, 2, 4]
def baseStart_5470599 : Nat := 118140960795 + 5470599 * 2 ^ 59
def prefixEnd_5470599 : Nat := 4983230072969 + 3 ^ 40 * 5470599 * 2
def baseEnd_5470599 : Nat := 2809046755005746989953679

theorem tailTrace_5470599 : CollatzResearch.WordTrace tailWord_5470599 prefixEnd_5470599 2809046755005746989953679 := by
  unfold tailWord_5470599
  simp only [CollatzResearch.WordTrace]
  refine ⟨199529137507961601770574851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133019425005307734513716567 199529137507961601770574851)
  ·
    refine ⟨299293706261942402655862277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199529137507961601770574851 299293706261942402655862277)
    ·
      refine ⟨56117569924114200497974177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 299293706261942402655862277 56117569924114200497974177)
      ·
        refine ⟨42088177443085650373480633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56117569924114200497974177 42088177443085650373480633)
        ·
          refine ⟨31566133082314237780110475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42088177443085650373480633 31566133082314237780110475)
          ·
            refine ⟨47349199623471356670165713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31566133082314237780110475 47349199623471356670165713)
            ·
              refine ⟨35511899717603517502624285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47349199623471356670165713 35511899717603517502624285)
              ·
                refine ⟨13316962394101319063484107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35511899717603517502624285 13316962394101319063484107)
                ·
                  refine ⟨19975443591151978595226161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13316962394101319063484107 19975443591151978595226161)
                  ·
                    refine ⟨14981582693363983946419621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19975443591151978595226161 14981582693363983946419621)
                    ·
                      refine ⟨2809046755005746989953679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14981582693363983946419621 2809046755005746989953679)
                      ·
                        rfl

theorem cell23_5470599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_5470599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5470599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5470599 prefixEnd_5470599 := by exact prefixLift 5470599
  have htrace : WordTrace (prefixWord ++ tailWord_5470599) baseStart_5470599 baseEnd_5470599 := by
    simpa [prefixWord, tailWord_5470599, baseEnd_5470599] using wordTrace_append hprefix tailTrace_5470599
  have hstable : (prefixWord ++ tailWord_5470599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5470599).length < 2 ^ (prefixWord ++ tailWord_5470599).sum := by decide
  have hdescent : baseEnd_5470599 < baseStart_5470599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5470599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5470616 : List Nat := [2, 1, 2, 5, 1, 2, 1, 2, 1, 2, 4]
def baseStart_5470616 : Nat := 118140960795 + 5470616 * 2 ^ 59
def prefixEnd_5470616 : Nat := 4983230072969 + 3 ^ 40 * 5470616 * 2
def baseEnd_5470616 : Nat := 2809055484176873423441101

theorem tailTrace_5470616 : CollatzResearch.WordTrace tailWord_5470616 prefixEnd_5470616 2809055484176873423441101 := by
  unfold tailWord_5470616
  simp only [CollatzResearch.WordTrace]
  refine ⟨99764878774450006836971851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133019838365933342449295801 99764878774450006836971851)
  ·
    refine ⟨149647318161675010255457777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99764878774450006836971851 149647318161675010255457777)
    ·
      refine ⟨112235488621256257691593333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149647318161675010255457777 112235488621256257691593333)
      ·
        refine ⟨10522077058242774158586875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 112235488621256257691593333 10522077058242774158586875)
        ·
          refine ⟨15783115587364161237880313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10522077058242774158586875 15783115587364161237880313)
          ·
            refine ⟨11837336690523120928410235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15783115587364161237880313 11837336690523120928410235)
            ·
              refine ⟨17756005035784681392615353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11837336690523120928410235 17756005035784681392615353)
              ·
                refine ⟨13317003776838511044461515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17756005035784681392615353 13317003776838511044461515)
                ·
                  refine ⟨19975505665257766566692273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13317003776838511044461515 19975505665257766566692273)
                  ·
                    refine ⟨14981629248943324925019205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19975505665257766566692273 14981629248943324925019205)
                    ·
                      refine ⟨2809055484176873423441101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14981629248943324925019205 2809055484176873423441101)
                      ·
                        rfl

theorem cell23_5470616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_5470616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5470616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5470616 prefixEnd_5470616 := by exact prefixLift 5470616
  have htrace : WordTrace (prefixWord ++ tailWord_5470616) baseStart_5470616 baseEnd_5470616 := by
    simpa [prefixWord, tailWord_5470616, baseEnd_5470616] using wordTrace_append hprefix tailTrace_5470616
  have hstable : (prefixWord ++ tailWord_5470616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5470616).length < 2 ^ (prefixWord ++ tailWord_5470616).sum := by decide
  have hdescent : baseEnd_5470616 < baseStart_5470616 := by decide
  rcases family_descends (prefixWord ++ tailWord_5470616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5470623 : List Nat := [1, 1, 2, 5, 1, 1, 5, 1, 1, 2, 3]
def baseStart_5470623 : Nat := 118140960795 + 5470623 * 2 ^ 59
def prefixEnd_5470623 : Nat := 4983230072969 + 3 ^ 40 * 5470623 * 2
def baseEnd_5470623 : Nat := 2809059078541454896053569

theorem tailTrace_5470623 : CollatzResearch.WordTrace tailWord_5470623 prefixEnd_5470623 2809059078541454896053569 := by
  unfold tailWord_5470623
  simp only [CollatzResearch.WordTrace]
  refine ⟨199530012859874653869448523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133020008573249769246299015 199530012859874653869448523)
  ·
    refine ⟨299295019289811980804172785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199530012859874653869448523 299295019289811980804172785)
    ·
      refine ⟨224471264467358985603129589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299295019289811980804172785 224471264467358985603129589)
      ·
        refine ⟨21044181043814904900293399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 224471264467358985603129589 21044181043814904900293399)
        ·
          refine ⟨31566271565722357350440099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21044181043814904900293399 31566271565722357350440099)
          ·
            refine ⟨47349407348583536025660149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31566271565722357350440099 47349407348583536025660149)
            ·
              refine ⟨4439006938929706502405639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47349407348583536025660149 4439006938929706502405639)
              ·
                refine ⟨6658510408394559753608459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4439006938929706502405639 6658510408394559753608459)
                ·
                  refine ⟨9987765612591839630412689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6658510408394559753608459 9987765612591839630412689)
                  ·
                    refine ⟨7490824209443879722809517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9987765612591839630412689 7490824209443879722809517)
                    ·
                      refine ⟨2809059078541454896053569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7490824209443879722809517 2809059078541454896053569)
                      ·
                        rfl

theorem cell23_5470623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_5470623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5470623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5470623 prefixEnd_5470623 := by exact prefixLift 5470623
  have htrace : WordTrace (prefixWord ++ tailWord_5470623) baseStart_5470623 baseEnd_5470623 := by
    simpa [prefixWord, tailWord_5470623, baseEnd_5470623] using wordTrace_append hprefix tailTrace_5470623
  have hstable : (prefixWord ++ tailWord_5470623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5470623).length < 2 ^ (prefixWord ++ tailWord_5470623).sum := by decide
  have hdescent : baseEnd_5470623 < baseStart_5470623 := by decide
  rcases family_descends (prefixWord ++ tailWord_5470623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5470653 : List Nat := [1, 4, 1, 2, 2, 2, 2, 3, 2, 1, 3]
def baseStart_5470653 : Nat := 118140960795 + 5470653 * 2 ^ 59
def prefixEnd_5470653 : Nat := 4983230072969 + 3 ^ 40 * 5470653 * 2
def baseEnd_5470653 : Nat := 2809074482961089778678431

theorem tailTrace_5470653 : CollatzResearch.WordTrace tailWord_5470653 prefixEnd_5470653 2809074482961089778678431 := by
  unfold tailWord_5470653
  simp only [CollatzResearch.WordTrace]
  refine ⟨199531107049765968993040613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133020738033177312662027075 199531107049765968993040613)
  ·
    refine ⟨37412082571831119186195115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 199531107049765968993040613 37412082571831119186195115)
    ·
      refine ⟨56118123857746678779292673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37412082571831119186195115 56118123857746678779292673)
      ·
        refine ⟨42088592893310009084469505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56118123857746678779292673 42088592893310009084469505)
        ·
          refine ⟨31566444669982506813352129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42088592893310009084469505 31566444669982506813352129)
          ·
            refine ⟨23674833502486880110014097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31566444669982506813352129 23674833502486880110014097)
            ·
              refine ⟨17756125126865160082510573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23674833502486880110014097 17756125126865160082510573)
              ·
                refine ⟨6658546922574435030941465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17756125126865160082510573 6658546922574435030941465)
                ·
                  refine ⟨4993910191930826273206099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6658546922574435030941465 4993910191930826273206099)
                  ·
                    refine ⟨7490865287896239409809149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4993910191930826273206099 7490865287896239409809149)
                    ·
                      refine ⟨2809074482961089778678431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7490865287896239409809149 2809074482961089778678431)
                      ·
                        rfl

theorem cell23_5470653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_5470653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5470653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5470653 prefixEnd_5470653 := by exact prefixLift 5470653
  have htrace : WordTrace (prefixWord ++ tailWord_5470653) baseStart_5470653 baseEnd_5470653 := by
    simpa [prefixWord, tailWord_5470653, baseEnd_5470653] using wordTrace_append hprefix tailTrace_5470653
  have hstable : (prefixWord ++ tailWord_5470653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5470653).length < 2 ^ (prefixWord ++ tailWord_5470653).sum := by decide
  have hdescent : baseEnd_5470653 < baseStart_5470653 := by decide
  rcases family_descends (prefixWord ++ tailWord_5470653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5470674 : List Nat := [3, 2, 2, 4, 2, 1, 2, 1, 1, 2, 3]
def baseStart_5470674 : Nat := 118140960795 + 5470674 * 2 ^ 59
def prefixEnd_5470674 : Nat := 4983230072969 + 3 ^ 40 * 5470674 * 2
def baseEnd_5470674 : Nat := 2809085266054834196515835

theorem tailTrace_5470674 : CollatzResearch.WordTrace tailWord_5470674 prefixEnd_5470674 2809085266054834196515835 := by
  unfold tailWord_5470674
  simp only [CollatzResearch.WordTrace]
  refine ⟨49882968245672472394888769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133021248655126593053036717 49882968245672472394888769)
  ·
    refine ⟨37412226184254354296166577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49882968245672472394888769 37412226184254354296166577)
    ·
      refine ⟨28059169638190765722124933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37412226184254354296166577 28059169638190765722124933)
      ·
        refine ⟨5261094307160768572898425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28059169638190765722124933 5261094307160768572898425)
        ·
          refine ⟨3945820730370576429673819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5261094307160768572898425 3945820730370576429673819)
          ·
            refine ⟨5918731095555864644510729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3945820730370576429673819 5918731095555864644510729)
            ·
              refine ⟨4439048321666898483383047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5918731095555864644510729 4439048321666898483383047)
              ·
                refine ⟨6658572482500347725074571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4439048321666898483383047 6658572482500347725074571)
                ·
                  refine ⟨9987858723750521587611857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6658572482500347725074571 9987858723750521587611857)
                  ·
                    refine ⟨7490894042812891190708893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9987858723750521587611857 7490894042812891190708893)
                    ·
                      refine ⟨2809085266054834196515835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7490894042812891190708893 2809085266054834196515835)
                      ·
                        rfl

theorem cell23_5470674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_5470674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5470674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5470674 prefixEnd_5470674 := by exact prefixLift 5470674
  have htrace : WordTrace (prefixWord ++ tailWord_5470674) baseStart_5470674 baseEnd_5470674 := by
    simpa [prefixWord, tailWord_5470674, baseEnd_5470674] using wordTrace_append hprefix tailTrace_5470674
  have hstable : (prefixWord ++ tailWord_5470674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5470674).length < 2 ^ (prefixWord ++ tailWord_5470674).sum := by decide
  have hdescent : baseEnd_5470674 < baseStart_5470674 := by decide
  rcases family_descends (prefixWord ++ tailWord_5470674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5470689 : List Nat := [1, 2, 3, 1, 2, 2, 1, 1, 4, 2, 4]
def baseStart_5470689 : Nat := 118140960795 + 5470689 * 2 ^ 59
def prefixEnd_5470689 : Nat := 4983230072969 + 3 ^ 40 * 5470689 * 2
def baseEnd_5470689 : Nat := 2809092968264651637828265

theorem tailTrace_5470689 : CollatzResearch.WordTrace tailWord_5470689 prefixEnd_5470689 2809092968264651637828265 := by
  unfold tailWord_5470689
  simp only [CollatzResearch.WordTrace]
  refine ⟨199532420077635547141351121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133021613385090364760900747 199532420077635547141351121)
  ·
    refine ⟨149649315058226660356013341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199532420077635547141351121 149649315058226660356013341)
    ·
      refine ⟨56118493146834997633505003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149649315058226660356013341 56118493146834997633505003)
      ·
        refine ⟨84177739720252496450257505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56118493146834997633505003 84177739720252496450257505)
        ·
          refine ⟨63133304790189372337693129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84177739720252496450257505 63133304790189372337693129)
          ·
            refine ⟨47349978592642029253269847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63133304790189372337693129 47349978592642029253269847)
            ·
              refine ⟨71024967888963043879904771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47349978592642029253269847 71024967888963043879904771)
              ·
                refine ⟨106537451833444565819857157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71024967888963043879904771 106537451833444565819857157)
                ·
                  refine ⟨19975772218770856091223217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 106537451833444565819857157 19975772218770856091223217)
                  ·
                    refine ⟨14981829164078142068417413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19975772218770856091223217 14981829164078142068417413)
                    ·
                      refine ⟨2809092968264651637828265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14981829164078142068417413 2809092968264651637828265)
                      ·
                        rfl

theorem cell23_5470689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_5470689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5470689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5470689 prefixEnd_5470689 := by exact prefixLift 5470689
  have htrace : WordTrace (prefixWord ++ tailWord_5470689) baseStart_5470689 baseEnd_5470689 := by
    simpa [prefixWord, tailWord_5470689, baseEnd_5470689] using wordTrace_append hprefix tailTrace_5470689
  have hstable : (prefixWord ++ tailWord_5470689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5470689).length < 2 ^ (prefixWord ++ tailWord_5470689).sum := by decide
  have hdescent : baseEnd_5470689 < baseStart_5470689 := by decide
  rcases family_descends (prefixWord ++ tailWord_5470689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5470699 : List Nat := [1, 1, 1, 1, 2, 3, 6, 1, 7]
def baseStart_5470699 : Nat := 118140960795 + 5470699 * 2 ^ 59
def prefixEnd_5470699 : Nat := 4983230072969 + 3 ^ 40 * 5470699 * 2
def baseEnd_5470699 : Nat := 312122011452355177633691

theorem tailTrace_5470699 : CollatzResearch.WordTrace tailWord_5470699 prefixEnd_5470699 312122011452355177633691 := by
  unfold tailWord_5470699
  simp only [CollatzResearch.WordTrace]
  refine ⟨199532784807599318849215151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133021856538399545899476767 199532784807599318849215151)
  ·
    refine ⟨299299177211398978273822727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199532784807599318849215151 299299177211398978273822727)
    ·
      refine ⟨448948765817098467410734091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299299177211398978273822727 448948765817098467410734091)
      ·
        refine ⟨673423148725647701116101137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 448948765817098467410734091 673423148725647701116101137)
        ·
          refine ⟨505067361544235775837075853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 673423148725647701116101137 505067361544235775837075853)
          ·
            refine ⟨189400260579088415938903445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 505067361544235775837075853 189400260579088415938903445)
            ·
              refine ⟨8878137214644769497136099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 189400260579088415938903445 8878137214644769497136099)
              ·
                refine ⟨13317205821967154245704149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8878137214644769497136099 13317205821967154245704149)
                ·
                  refine ⟨312122011452355177633691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13317205821967154245704149 312122011452355177633691)
                  ·
                    rfl

theorem cell23_5470699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 7].length) (baseStart_5470699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5470699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5470699 prefixEnd_5470699 := by exact prefixLift 5470699
  have htrace : WordTrace (prefixWord ++ tailWord_5470699) baseStart_5470699 baseEnd_5470699 := by
    simpa [prefixWord, tailWord_5470699, baseEnd_5470699] using wordTrace_append hprefix tailTrace_5470699
  have hstable : (prefixWord ++ tailWord_5470699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5470699).length < 2 ^ (prefixWord ++ tailWord_5470699).sum := by decide
  have hdescent : baseEnd_5470699 < baseStart_5470699 := by decide
  rcases family_descends (prefixWord ++ tailWord_5470699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5470739 : List Nat := [1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 5]
def baseStart_5470739 : Nat := 118140960795 + 5470739 * 2 ^ 59
def prefixEnd_5470739 : Nat := 4983230072969 + 3 ^ 40 * 5470739 * 2
def baseEnd_5470739 : Nat := 2809118642297376442203035

theorem tailTrace_5470739 : CollatzResearch.WordTrace tailWord_5470739 prefixEnd_5470739 2809118642297376442203035 := by
  unfold tailWord_5470739
  simp only [CollatzResearch.WordTrace]
  refine ⟨199534243727454405680671271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133022829151636270453780847 199534243727454405680671271)
  ·
    refine ⟨299301365591181608521006907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199534243727454405680671271 299301365591181608521006907)
    ·
      refine ⟨448952048386772412781510361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299301365591181608521006907 448952048386772412781510361)
      ·
        refine ⟨336714036290079309586132771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 448952048386772412781510361 336714036290079309586132771)
        ·
          refine ⟨505071054435118964379199157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 336714036290079309586132771 505071054435118964379199157)
          ·
            refine ⟨47350411353292402910549921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 505071054435118964379199157 47350411353292402910549921)
            ·
              refine ⟨35512808514969302182912441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47350411353292402910549921 35512808514969302182912441)
              ·
                refine ⟨26634606386226976637184331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35512808514969302182912441 26634606386226976637184331)
                ·
                  refine ⟨39951909579340464955776497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26634606386226976637184331 39951909579340464955776497)
                  ·
                    refine ⟨29963932184505348716832373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39951909579340464955776497 29963932184505348716832373)
                    ·
                      refine ⟨2809118642297376442203035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29963932184505348716832373 2809118642297376442203035)
                      ·
                        rfl

theorem cell23_5470739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 5].length) (baseStart_5470739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5470739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5470739 prefixEnd_5470739 := by exact prefixLift 5470739
  have htrace : WordTrace (prefixWord ++ tailWord_5470739) baseStart_5470739 baseEnd_5470739 := by
    simpa [prefixWord, tailWord_5470739, baseEnd_5470739] using wordTrace_append hprefix tailTrace_5470739
  have hstable : (prefixWord ++ tailWord_5470739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5470739).length < 2 ^ (prefixWord ++ tailWord_5470739).sum := by decide
  have hdescent : baseEnd_5470739 < baseStart_5470739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5470739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5470776 : List Nat := [2, 1, 2, 1, 4, 1, 2, 1, 5, 4]
def baseStart_5470776 : Nat := 118140960795 + 5470776 * 2 ^ 59
def prefixEnd_5470776 : Nat := 4983230072969 + 3 ^ 40 * 5470776 * 2
def baseEnd_5470776 : Nat := 936379213693864265813455

theorem tailTrace_5470776 : CollatzResearch.WordTrace tailWord_5470776 prefixEnd_5470776 936379213693864265813455 := by
  unfold tailWord_5470776
  simp only [CollatzResearch.WordTrace]
  refine ⟨99767796614160180499884091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133023728818880240666512121 99767796614160180499884091)
  ·
    refine ⟨149651694921240270749826137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99767796614160180499884091 149651694921240270749826137)
    ·
      refine ⟨112238771190930203062369603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149651694921240270749826137 112238771190930203062369603)
      ·
        refine ⟨168358156786395304593554405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112238771190930203062369603 168358156786395304593554405)
        ·
          refine ⟨31567154397449119611291451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 168358156786395304593554405 31567154397449119611291451)
          ·
            refine ⟨47350731596173679416937177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31567154397449119611291451 47350731596173679416937177)
            ·
              refine ⟨35513048697130259562702883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47350731596173679416937177 35513048697130259562702883)
              ·
                refine ⟨53269573045695389344054325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35513048697130259562702883 53269573045695389344054325)
                ·
                  refine ⟨4994022473033942751005093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53269573045695389344054325 4994022473033942751005093)
                  ·
                    refine ⟨936379213693864265813455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4994022473033942751005093 936379213693864265813455)
                    ·
                      rfl

theorem cell23_5470776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 5, 4].length) (baseStart_5470776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5470776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5470776 prefixEnd_5470776 := by exact prefixLift 5470776
  have htrace : WordTrace (prefixWord ++ tailWord_5470776) baseStart_5470776 baseEnd_5470776 := by
    simpa [prefixWord, tailWord_5470776, baseEnd_5470776] using wordTrace_append hprefix tailTrace_5470776
  have hstable : (prefixWord ++ tailWord_5470776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5470776).length < 2 ^ (prefixWord ++ tailWord_5470776).sum := by decide
  have hdescent : baseEnd_5470776 < baseStart_5470776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5470776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5470837 : List Nat := [1, 3, 4, 2, 2, 2, 1, 1, 2, 2, 3]
def baseStart_5470837 : Nat := 118140960795 + 5470837 * 2 ^ 59
def prefixEnd_5470837 : Nat := 4983230072969 + 3 ^ 40 * 5470837 * 2
def baseEnd_5470837 : Nat := 2809168963401517058777585

theorem tailTrace_5470837 : CollatzResearch.WordTrace tailWord_5470837 prefixEnd_5470837 2809168963401517058777585 := by
  unfold tailWord_5470837
  simp only [CollatzResearch.WordTrace]
  refine ⟨199537818081099368417738765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133025212054066245611825843 199537818081099368417738765)
  ·
    refine ⟨74826681780412263156652037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199537818081099368417738765 74826681780412263156652037)
    ·
      refine ⟨14030002833827299341872257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74826681780412263156652037 14030002833827299341872257)
      ·
        refine ⟨10522502125370474506404193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14030002833827299341872257 10522502125370474506404193)
        ·
          refine ⟨7891876594027855879803145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10522502125370474506404193 7891876594027855879803145)
          ·
            refine ⟨5918907445520891909852359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7891876594027855879803145 5918907445520891909852359)
            ·
              refine ⟨8878361168281337864778539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5918907445520891909852359 8878361168281337864778539)
              ·
                refine ⟨13317541752422006797167809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8878361168281337864778539 13317541752422006797167809)
                ·
                  refine ⟨9988156314316505097875857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13317541752422006797167809 9988156314316505097875857)
                  ·
                    refine ⟨7491117235737378823406893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9988156314316505097875857 7491117235737378823406893)
                    ·
                      refine ⟨2809168963401517058777585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7491117235737378823406893 2809168963401517058777585)
                      ·
                        rfl

theorem cell23_5470837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_5470837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5470837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5470837 prefixEnd_5470837 := by exact prefixLift 5470837
  have htrace : WordTrace (prefixWord ++ tailWord_5470837) baseStart_5470837 baseEnd_5470837 := by
    simpa [prefixWord, tailWord_5470837, baseEnd_5470837] using wordTrace_append hprefix tailTrace_5470837
  have hstable : (prefixWord ++ tailWord_5470837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5470837).length < 2 ^ (prefixWord ++ tailWord_5470837).sum := by decide
  have hdescent : baseEnd_5470837 < baseStart_5470837 := by decide
  rcases family_descends (prefixWord ++ tailWord_5470837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5470843 : List Nat := [1, 1, 1, 1, 1, 4, 2, 5, 2, 3, 2]
def baseStart_5470843 : Nat := 118140960795 + 5470843 * 2 ^ 59
def prefixEnd_5470843 : Nat := 4983230072969 + 3 ^ 40 * 5470843 * 2
def baseEnd_5470843 : Nat := 2809172044285444035302557

theorem tailTrace_5470843 : CollatzResearch.WordTrace tailWord_5470843 prefixEnd_5470843 2809172044285444035302557 := by
  unfold tailWord_5470843
  simp only [CollatzResearch.WordTrace]
  refine ⟨199538036919077631442457183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133025357946051754294971455 199538036919077631442457183)
  ·
    refine ⟨299307055378616447163685775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199538036919077631442457183 299307055378616447163685775)
    ·
      refine ⟨448960583067924670745528663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299307055378616447163685775 448960583067924670745528663)
      ·
        refine ⟨673440874601887006118292995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 448960583067924670745528663 673440874601887006118292995)
        ·
          refine ⟨1010161311902830509177439493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 673440874601887006118292995 1010161311902830509177439493)
          ·
            refine ⟨189405245981780720470769905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1010161311902830509177439493 189405245981780720470769905)
            ·
              refine ⟨142053934486335540353077429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189405245981780720470769905 142053934486335540353077429)
              ·
                refine ⟨13317556358093956908101009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 142053934486335540353077429 13317556358093956908101009)
                ·
                  refine ⟨9988167268570467681075757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13317556358093956908101009 9988167268570467681075757)
                  ·
                    refine ⟨3745562725713925380403409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9988167268570467681075757 3745562725713925380403409)
                    ·
                      refine ⟨2809172044285444035302557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3745562725713925380403409 2809172044285444035302557)
                      ·
                        rfl

theorem cell23_5470843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 2, 3, 2].length) (baseStart_5470843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5470843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5470843 prefixEnd_5470843 := by exact prefixLift 5470843
  have htrace : WordTrace (prefixWord ++ tailWord_5470843) baseStart_5470843 baseEnd_5470843 := by
    simpa [prefixWord, tailWord_5470843, baseEnd_5470843] using wordTrace_append hprefix tailTrace_5470843
  have hstable : (prefixWord ++ tailWord_5470843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5470843).length < 2 ^ (prefixWord ++ tailWord_5470843).sum := by decide
  have hdescent : baseEnd_5470843 < baseStart_5470843 := by decide
  rcases family_descends (prefixWord ++ tailWord_5470843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5470853 : List Nat := [1, 3, 1, 1, 4, 3, 1, 3, 1, 5]
def baseStart_5470853 : Nat := 118140960795 + 5470853 * 2 ^ 59
def prefixEnd_5470853 : Nat := 4983230072969 + 3 ^ 40 * 5470853 * 2
def baseEnd_5470853 : Nat := 936392393030662998725837

theorem tailTrace_5470853 : CollatzResearch.WordTrace tailWord_5470853 prefixEnd_5470853 936392393030662998725837 := by
  unfold tailWord_5470853
  simp only [CollatzResearch.WordTrace]
  refine ⟨199538401649041403150321213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133025601099360935433547475 199538401649041403150321213)
  ·
    refine ⟨74826900618390526181370455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199538401649041403150321213 74826900618390526181370455)
    ·
      refine ⟨112240350927585789272055683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74826900618390526181370455 112240350927585789272055683)
      ·
        refine ⟨168360526391378683908083525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112240350927585789272055683 168360526391378683908083525)
        ·
          refine ⟨31567598698383503232765661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 168360526391378683908083525 31567598698383503232765661)
          ·
            refine ⟨11837849511893813712287123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31567598698383503232765661 11837849511893813712287123)
            ·
              refine ⟨17756774267840720568430685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11837849511893813712287123 17756774267840720568430685)
              ·
                refine ⟨6658790350440270213161507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17756774267840720568430685 6658790350440270213161507)
                ·
                  refine ⟨9988185525660405319742261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6658790350440270213161507 9988185525660405319742261)
                  ·
                    refine ⟨936392393030662998725837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9988185525660405319742261 936392393030662998725837)
                    ·
                      rfl

theorem cell23_5470853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 3, 1, 5].length) (baseStart_5470853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5470853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5470853 prefixEnd_5470853 := by exact prefixLift 5470853
  have htrace : WordTrace (prefixWord ++ tailWord_5470853) baseStart_5470853 baseEnd_5470853 := by
    simpa [prefixWord, tailWord_5470853, baseEnd_5470853] using wordTrace_append hprefix tailTrace_5470853
  have hstable : (prefixWord ++ tailWord_5470853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5470853).length < 2 ^ (prefixWord ++ tailWord_5470853).sum := by decide
  have hdescent : baseEnd_5470853 < baseStart_5470853 := by decide
  rcases family_descends (prefixWord ++ tailWord_5470853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5470887 : List Nat := [1, 1, 6, 3, 1, 1, 2, 2, 1, 5]
def baseStart_5470887 : Nat := 118140960795 + 5470887 * 2 ^ 59
def prefixEnd_5470887 : Nat := 4983230072969 + 3 ^ 40 * 5470887 * 2
def baseEnd_5470887 : Nat := 936398212478080621050785

theorem tailTrace_5470887 : CollatzResearch.WordTrace tailWord_5470887 prefixEnd_5470887 936398212478080621050785 := by
  unfold tailWord_5470887
  simp only [CollatzResearch.WordTrace]
  refine ⟨199539641730918226957058915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133026427820612151304705943 199539641730918226957058915)
  ·
    refine ⟨299309462596377340435588373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199539641730918226957058915 299309462596377340435588373)
    ·
      refine ⟨14030131059205187832918205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 299309462596377340435588373 14030131059205187832918205)
      ·
        refine ⟨5261299147201945437344327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14030131059205187832918205 5261299147201945437344327)
        ·
          refine ⟨7891948720802918156016491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5261299147201945437344327 7891948720802918156016491)
          ·
            refine ⟨11837923081204377234024737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7891948720802918156016491 11837923081204377234024737)
            ·
              refine ⟨8878442310903282925518553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11837923081204377234024737 8878442310903282925518553)
              ·
                refine ⟨6658831733177462194138915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8878442310903282925518553 6658831733177462194138915)
                ·
                  refine ⟨9988247599766193291208373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6658831733177462194138915 9988247599766193291208373)
                  ·
                    refine ⟨936398212478080621050785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9988247599766193291208373 936398212478080621050785)
                    ·
                      rfl

theorem cell23_5470887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_5470887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5470887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5470887 prefixEnd_5470887 := by exact prefixLift 5470887
  have htrace : WordTrace (prefixWord ++ tailWord_5470887) baseStart_5470887 baseEnd_5470887 := by
    simpa [prefixWord, tailWord_5470887, baseEnd_5470887] using wordTrace_append hprefix tailTrace_5470887
  have hstable : (prefixWord ++ tailWord_5470887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5470887).length < 2 ^ (prefixWord ++ tailWord_5470887).sum := by decide
  have hdescent : baseEnd_5470887 < baseStart_5470887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5470887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5470910 : List Nat := [4, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3]
def baseStart_5470910 : Nat := 118140960795 + 5470910 * 2 ^ 59
def prefixEnd_5470910 : Nat := 4983230072969 + 3 ^ 40 * 5470910 * 2
def baseEnd_5470910 : Nat := 2809206447489295273164749

theorem tailTrace_5470910 : CollatzResearch.WordTrace tailWord_5470910 prefixEnd_5470910 2809206447489295273164749 := by
  unfold tailWord_5470910
  simp only [CollatzResearch.WordTrace]
  refine ⟨24942560076229362735643273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133026987073223267923430789 24942560076229362735643273)
  ·
    refine ⟨18706920057172022051732455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24942560076229362735643273 18706920057172022051732455)
    ·
      refine ⟨28060380085758033077598683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18706920057172022051732455 28060380085758033077598683)
      ·
        refine ⟨42090570128637049616398025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28060380085758033077598683 42090570128637049616398025)
        ·
          refine ⟨31567927596477787212298519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42090570128637049616398025 31567927596477787212298519)
          ·
            refine ⟨47351891394716680818447779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31567927596477787212298519 47351891394716680818447779)
            ·
              refine ⟨71027837092075021227671669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47351891394716680818447779 71027837092075021227671669)
              ·
                refine ⟨6658859727382033240094219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71027837092075021227671669 6658859727382033240094219)
                ·
                  refine ⟨9988289591073049860141329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6658859727382033240094219 9988289591073049860141329)
                  ·
                    refine ⟨7491217193304787395105997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9988289591073049860141329 7491217193304787395105997)
                    ·
                      refine ⟨2809206447489295273164749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7491217193304787395105997 2809206447489295273164749)
                      ·
                        rfl

theorem cell23_5470910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_5470910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5470910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5470910 prefixEnd_5470910 := by exact prefixLift 5470910
  have htrace : WordTrace (prefixWord ++ tailWord_5470910) baseStart_5470910 baseEnd_5470910 := by
    simpa [prefixWord, tailWord_5470910, baseEnd_5470910] using wordTrace_append hprefix tailTrace_5470910
  have hstable : (prefixWord ++ tailWord_5470910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5470910).length < 2 ^ (prefixWord ++ tailWord_5470910).sum := by decide
  have hdescent : baseEnd_5470910 < baseStart_5470910 := by decide
  rcases family_descends (prefixWord ++ tailWord_5470910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5470918 : List Nat := [6, 1, 2, 1, 3, 1, 1, 1, 3, 1, 3]
def baseStart_5470918 : Nat := 118140960795 + 5470918 * 2 ^ 59
def prefixEnd_5470918 : Nat := 4983230072969 + 3 ^ 40 * 5470918 * 2
def baseEnd_5470918 : Nat := 2809210555334531241864713

theorem tailTrace_5470918 : CollatzResearch.WordTrace tailWord_5470918 prefixEnd_5470918 2809210555334531241864713 := by
  unfold tailWord_5470918
  simp only [CollatzResearch.WordTrace]
  refine ⟨6235649137306434976607419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 133027181595870612834291605 6235649137306434976607419)
  ·
    refine ⟨9353473705959652464911129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6235649137306434976607419 9353473705959652464911129)
    ·
      refine ⟨7015105279469739348683347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9353473705959652464911129 7015105279469739348683347)
      ·
        refine ⟨10522657919204609023025021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7015105279469739348683347 10522657919204609023025021)
        ·
          refine ⟨3945996719701728383634383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10522657919204609023025021 3945996719701728383634383)
          ·
            refine ⟨5918995079552592575451575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3945996719701728383634383 5918995079552592575451575)
            ·
              refine ⟨8878492619328888863177363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5918995079552592575451575 8878492619328888863177363)
              ·
                refine ⟨13317738928993333294766045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8878492619328888863177363 13317738928993333294766045)
                ·
                  refine ⟨4994152098372499985537267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13317738928993333294766045 4994152098372499985537267)
                  ·
                    refine ⟨7491228147558749978305901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4994152098372499985537267 7491228147558749978305901)
                    ·
                      refine ⟨2809210555334531241864713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7491228147558749978305901 2809210555334531241864713)
                      ·
                        rfl

theorem cell23_5470918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_5470918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5470918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5470918 prefixEnd_5470918 := by exact prefixLift 5470918
  have htrace : WordTrace (prefixWord ++ tailWord_5470918) baseStart_5470918 baseEnd_5470918 := by
    simpa [prefixWord, tailWord_5470918, baseEnd_5470918] using wordTrace_append hprefix tailTrace_5470918
  have hstable : (prefixWord ++ tailWord_5470918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5470918).length < 2 ^ (prefixWord ++ tailWord_5470918).sum := by decide
  have hdescent : baseEnd_5470918 < baseStart_5470918 := by decide
  rcases family_descends (prefixWord ++ tailWord_5470918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5470924 : List Nat := [2, 2, 1, 5, 1, 3, 1, 1, 3, 2, 2]
def baseStart_5470924 : Nat := 118140960795 + 5470924 * 2 ^ 59
def prefixEnd_5470924 : Nat := 4983230072969 + 3 ^ 40 * 5470924 * 2
def baseEnd_5470924 : Nat := 2809213636218458218389685

theorem tailTrace_5470924 : CollatzResearch.WordTrace tailWord_5470924 prefixEnd_5470924 2809213636218458218389685 := by
  unfold tailWord_5470924
  simp only [CollatzResearch.WordTrace]
  refine ⟨99770495615892091138077913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133027327487856121517437217 99770495615892091138077913)
  ·
    refine ⟨74827871711919068353558435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99770495615892091138077913 74827871711919068353558435)
    ·
      refine ⟨112241807567878602530337653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74827871711919068353558435 112241807567878602530337653)
      ·
        refine ⟨10522669459488618987219155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 112241807567878602530337653 10522669459488618987219155)
        ·
          refine ⟨15784004189232928480828733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10522669459488618987219155 15784004189232928480828733)
          ·
            refine ⟨5919001570962348180310775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15784004189232928480828733 5919001570962348180310775)
            ·
              refine ⟨8878502356443522270466163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5919001570962348180310775 8878502356443522270466163)
              ·
                refine ⟨13317753534665283405699245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8878502356443522270466163 13317753534665283405699245)
                ·
                  refine ⟨4994157575499481277137217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13317753534665283405699245 4994157575499481277137217)
                  ·
                    refine ⟨3745618181624610957852913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4994157575499481277137217 3745618181624610957852913)
                    ·
                      refine ⟨2809213636218458218389685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3745618181624610957852913 2809213636218458218389685)
                      ·
                        rfl

theorem cell23_5470924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_5470924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5470924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5470924 prefixEnd_5470924 := by exact prefixLift 5470924
  have htrace : WordTrace (prefixWord ++ tailWord_5470924) baseStart_5470924 baseEnd_5470924 := by
    simpa [prefixWord, tailWord_5470924, baseEnd_5470924] using wordTrace_append hprefix tailTrace_5470924
  have hstable : (prefixWord ++ tailWord_5470924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5470924).length < 2 ^ (prefixWord ++ tailWord_5470924).sum := by decide
  have hdescent : baseEnd_5470924 < baseStart_5470924 := by decide
  rcases family_descends (prefixWord ++ tailWord_5470924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5470956 : List Nat := [2, 2, 1, 1, 2, 2, 1, 2, 4, 6]
def baseStart_5470956 : Nat := 118140960795 + 5470956 * 2 ^ 59
def prefixEnd_5470956 : Nat := 4983230072969 + 3 ^ 40 * 5470956 * 2
def baseEnd_5470956 : Nat := 936410022533134031063179

theorem tailTrace_5470956 : CollatzResearch.WordTrace tailWord_5470956 prefixEnd_5470956 936410022533134031063179 := by
  unfold tailWord_5470956
  simp only [CollatzResearch.WordTrace]
  refine ⟨99771079183834125870660361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133028105578445501160880481 99771079183834125870660361)
  ·
    refine ⟨74828309387875594402995271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99771079183834125870660361 74828309387875594402995271)
    ·
      refine ⟨112242464081813391604492907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74828309387875594402995271 112242464081813391604492907)
      ·
        refine ⟨168363696122720087406739361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112242464081813391604492907 168363696122720087406739361)
        ·
          refine ⟨126272772092040065555054521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168363696122720087406739361 126272772092040065555054521)
          ·
            refine ⟨94704579069030049166290891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126272772092040065555054521 94704579069030049166290891)
            ·
              refine ⟨142056868603545073749436337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94704579069030049166290891 142056868603545073749436337)
              ·
                refine ⟨106542651452658805312077253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142056868603545073749436337 106542651452658805312077253)
                ·
                  refine ⟨19976747147373525996014485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 106542651452658805312077253 19976747147373525996014485)
                  ·
                    refine ⟨936410022533134031063179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19976747147373525996014485 936410022533134031063179)
                    ·
                      rfl

theorem cell23_5470956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 6].length) (baseStart_5470956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5470956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5470956 prefixEnd_5470956 := by exact prefixLift 5470956
  have htrace : WordTrace (prefixWord ++ tailWord_5470956) baseStart_5470956 baseEnd_5470956 := by
    simpa [prefixWord, tailWord_5470956, baseEnd_5470956] using wordTrace_append hprefix tailTrace_5470956
  have hstable : (prefixWord ++ tailWord_5470956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5470956).length < 2 ^ (prefixWord ++ tailWord_5470956).sum := by decide
  have hdescent : baseEnd_5470956 < baseStart_5470956 := by decide
  rcases family_descends (prefixWord ++ tailWord_5470956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5470974 : List Nat := [4, 2, 2, 1, 2, 2, 2, 2, 2, 1, 3]
def baseStart_5470974 : Nat := 118140960795 + 5470974 * 2 ^ 59
def prefixEnd_5470974 : Nat := 4983230072969 + 3 ^ 40 * 5470974 * 2
def baseEnd_5470974 : Nat := 2809239310251183022764455

theorem tailTrace_5470974 : CollatzResearch.WordTrace tailWord_5470974 prefixEnd_5470974 2809239310251183022764455 := by
  unfold tailWord_5470974
  simp only [CollatzResearch.WordTrace]
  refine ⟨24942851860200380101934497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133028543254402027210317317 24942851860200380101934497)
  ·
    refine ⟨18707138895150285076450873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24942851860200380101934497 18707138895150285076450873)
    ·
      refine ⟨14030354171362713807338155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18707138895150285076450873 14030354171362713807338155)
      ·
        refine ⟨21045531257044070711007233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14030354171362713807338155 21045531257044070711007233)
        ·
          refine ⟨15784148442783053033255425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21045531257044070711007233 15784148442783053033255425)
          ·
            refine ⟨11838111332087289774941569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15784148442783053033255425 11838111332087289774941569)
            ·
              refine ⟨8878583499065467331206177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11838111332087289774941569 8878583499065467331206177)
              ·
                refine ⟨6658937624299100498404633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8878583499065467331206177 6658937624299100498404633)
                ·
                  refine ⟨4994203218224325373803475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6658937624299100498404633 4994203218224325373803475)
                  ·
                    refine ⟨7491304827336488060705213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4994203218224325373803475 7491304827336488060705213)
                    ·
                      refine ⟨2809239310251183022764455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7491304827336488060705213 2809239310251183022764455)
                      ·
                        rfl

theorem cell23_5470974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_5470974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5470974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5470974 prefixEnd_5470974 := by exact prefixLift 5470974
  have htrace : WordTrace (prefixWord ++ tailWord_5470974) baseStart_5470974 baseEnd_5470974 := by
    simpa [prefixWord, tailWord_5470974, baseEnd_5470974] using wordTrace_append hprefix tailTrace_5470974
  have hstable : (prefixWord ++ tailWord_5470974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5470974).length < 2 ^ (prefixWord ++ tailWord_5470974).sum := by decide
  have hdescent : baseEnd_5470974 < baseStart_5470974 := by decide
  rcases family_descends (prefixWord ++ tailWord_5470974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5470980 : List Nat := [2, 3, 2, 2, 1, 1, 1, 2, 3, 4, 2]
def baseStart_5470980 : Nat := 118140960795 + 5470980 * 2 ^ 59
def prefixEnd_5470980 : Nat := 4983230072969 + 3 ^ 40 * 5470980 * 2
def baseEnd_5470980 : Nat := 2809242391135109999289427

theorem tailTrace_5470980 : CollatzResearch.WordTrace tailWord_5470980 prefixEnd_5470980 2809242391135109999289427 := by
  unfold tailWord_5470980
  simp only [CollatzResearch.WordTrace]
  refine ⟨99771516859790651920097197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133028689146387535893462929 99771516859790651920097197)
  ·
    refine ⟨37414318822421494470036449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99771516859790651920097197 37414318822421494470036449)
    ·
      refine ⟨28060739116816120852527337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37414318822421494470036449 28060739116816120852527337)
      ·
        refine ⟨21045554337612090639395503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28060739116816120852527337 21045554337612090639395503)
        ·
          refine ⟨31568331506418135959093255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21045554337612090639395503 31568331506418135959093255)
          ·
            refine ⟨47352497259627203938639883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31568331506418135959093255 47352497259627203938639883)
            ·
              refine ⟨71028745889440805907959825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47352497259627203938639883 71028745889440805907959825)
              ·
                refine ⟨53271559417080604430969869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71028745889440805907959825 53271559417080604430969869)
                ·
                  refine ⟨19976834781405226661613701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53271559417080604430969869 19976834781405226661613701)
                  ·
                    refine ⟨3745656521513479999052569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19976834781405226661613701 3745656521513479999052569)
                    ·
                      refine ⟨2809242391135109999289427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3745656521513479999052569 2809242391135109999289427)
                      ·
                        rfl

theorem cell23_5470980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_5470980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5470980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5470980 prefixEnd_5470980 := by exact prefixLift 5470980
  have htrace : WordTrace (prefixWord ++ tailWord_5470980) baseStart_5470980 baseEnd_5470980 := by
    simpa [prefixWord, tailWord_5470980, baseEnd_5470980] using wordTrace_append hprefix tailTrace_5470980
  have hstable : (prefixWord ++ tailWord_5470980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5470980).length < 2 ^ (prefixWord ++ tailWord_5470980).sum := by decide
  have hdescent : baseEnd_5470980 < baseStart_5470980 := by decide
  rcases family_descends (prefixWord ++ tailWord_5470980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5470997 : List Nat := [1, 3, 2, 1, 2, 2, 1, 5, 2, 2, 2]
def baseStart_5470997 : Nat := 118140960795 + 5470997 * 2 ^ 59
def prefixEnd_5470997 : Nat := 4983230072969 + 3 ^ 40 * 5470997 * 2
def baseEnd_5470997 : Nat := 2809251120306236432776849

theorem tailTrace_5470997 : CollatzResearch.WordTrace tailWord_5470997 prefixEnd_5470997 2809251120306236432776849 := by
  unfold tailWord_5470997
  simp only [CollatzResearch.WordTrace]
  refine ⟨199543653760519715743563245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133029102507013143829042163 199543653760519715743563245)
  ·
    refine ⟨74828870160194893403836217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199543653760519715743563245 74828870160194893403836217)
    ·
      refine ⟨56121652620146170052877163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74828870160194893403836217 56121652620146170052877163)
      ·
        refine ⟨84182478930219255079315745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56121652620146170052877163 84182478930219255079315745)
        ·
          refine ⟨63136859197664441309486809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84182478930219255079315745 63136859197664441309486809)
          ·
            refine ⟨47352644398248330982115107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63136859197664441309486809 47352644398248330982115107)
            ·
              refine ⟨71028966597372496473172661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47352644398248330982115107 71028966597372496473172661)
              ·
                refine ⟨6658965618503671544359937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71028966597372496473172661 6658965618503671544359937)
                ·
                  refine ⟨4994224213877753658269953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6658965618503671544359937 4994224213877753658269953)
                  ·
                    refine ⟨3745668160408315243702465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4994224213877753658269953 3745668160408315243702465)
                    ·
                      refine ⟨2809251120306236432776849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3745668160408315243702465 2809251120306236432776849)
                      ·
                        rfl

theorem cell23_5470997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 5, 2, 2, 2].length) (baseStart_5470997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5470997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5470997 prefixEnd_5470997 := by exact prefixLift 5470997
  have htrace : WordTrace (prefixWord ++ tailWord_5470997) baseStart_5470997 baseEnd_5470997 := by
    simpa [prefixWord, tailWord_5470997, baseEnd_5470997] using wordTrace_append hprefix tailTrace_5470997
  have hstable : (prefixWord ++ tailWord_5470997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5470997).length < 2 ^ (prefixWord ++ tailWord_5470997).sum := by decide
  have hdescent : baseEnd_5470997 < baseStart_5470997 := by decide
  rcases family_descends (prefixWord ++ tailWord_5470997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471013 : List Nat := [1, 3, 1, 2, 3, 1, 1, 2, 1, 5, 3]
def baseStart_5471013 : Nat := 118140960795 + 5471013 * 2 ^ 59
def prefixEnd_5471013 : Nat := 4983230072969 + 3 ^ 40 * 5471013 * 2
def baseEnd_5471013 : Nat := 2809259335996708370176775

theorem tailTrace_5471013 : CollatzResearch.WordTrace tailWord_5471013 prefixEnd_5471013 2809259335996708370176775 := by
  unfold tailWord_5471013
  simp only [CollatzResearch.WordTrace]
  refine ⟨199544237328461750476145693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133029491552307833650763795 199544237328461750476145693)
  ·
    refine ⟨74829088998173156428554635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199544237328461750476145693 74829088998173156428554635)
    ·
      refine ⟨112243633497259734642831953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74829088998173156428554635 112243633497259734642831953)
      ·
        refine ⟨84182725122944800982123965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112243633497259734642831953 84182725122944800982123965)
        ·
          refine ⟨31568521921104300368296487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84182725122944800982123965 31568521921104300368296487)
          ·
            refine ⟨47352782881656450552444731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31568521921104300368296487 47352782881656450552444731)
            ·
              refine ⟨71029174322484675828667097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47352782881656450552444731 71029174322484675828667097)
              ·
                refine ⟨53271880741863506871500323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71029174322484675828667097 53271880741863506871500323)
                ·
                  refine ⟨79907821112795260307250485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53271880741863506871500323 79907821112795260307250485)
                  ·
                    refine ⟨7491358229324555653804733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 79907821112795260307250485 7491358229324555653804733)
                    ·
                      refine ⟨2809259335996708370176775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7491358229324555653804733 2809259335996708370176775)
                      ·
                        rfl

theorem cell23_5471013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 5, 3].length) (baseStart_5471013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471013 prefixEnd_5471013 := by exact prefixLift 5471013
  have htrace : WordTrace (prefixWord ++ tailWord_5471013) baseStart_5471013 baseEnd_5471013 := by
    simpa [prefixWord, tailWord_5471013, baseEnd_5471013] using wordTrace_append hprefix tailTrace_5471013
  have hstable : (prefixWord ++ tailWord_5471013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471013).length < 2 ^ (prefixWord ++ tailWord_5471013).sum := by decide
  have hdescent : baseEnd_5471013 < baseStart_5471013 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471018 : List Nat := [3, 1, 4, 3, 1, 2, 2, 1, 1, 3, 2]
def baseStart_5471018 : Nat := 118140960795 + 5471018 * 2 ^ 59
def prefixEnd_5471018 : Nat := 4983230072969 + 3 ^ 40 * 5471018 * 2
def baseEnd_5471018 : Nat := 2809261903399980850614253

theorem tailTrace_5471018 : CollatzResearch.WordTrace tailWord_5471018 prefixEnd_5471018 2809261903399980850614253 := by
  unfold tailWord_5471018
  simp only [CollatzResearch.WordTrace]
  refine ⟨49886104923360909082519427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133029613128962424220051805 49886104923360909082519427)
  ·
    refine ⟨74829157385041363623779141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49886104923360909082519427 74829157385041363623779141)
    ·
      refine ⟨14030467009695255679458589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74829157385041363623779141 14030467009695255679458589)
      ·
        refine ⟨5261425128635720879796971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14030467009695255679458589 5261425128635720879796971)
        ·
          refine ⟨7892137692953581319695457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5261425128635720879796971 7892137692953581319695457)
          ·
            refine ⟨5919103269715185989771593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7892137692953581319695457 5919103269715185989771593)
            ·
              refine ⟨4439327452286389492328695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5919103269715185989771593 4439327452286389492328695)
              ·
                refine ⟨6658991178429584238493043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4439327452286389492328695 6658991178429584238493043)
                ·
                  refine ⟨9988486767644376357739565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6658991178429584238493043 9988486767644376357739565)
                  ·
                    refine ⟨3745682537866641134152337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9988486767644376357739565 3745682537866641134152337)
                    ·
                      refine ⟨2809261903399980850614253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3745682537866641134152337 2809261903399980850614253)
                      ·
                        rfl

theorem cell23_5471018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_5471018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471018 prefixEnd_5471018 := by exact prefixLift 5471018
  have htrace : WordTrace (prefixWord ++ tailWord_5471018) baseStart_5471018 baseEnd_5471018 := by
    simpa [prefixWord, tailWord_5471018, baseEnd_5471018] using wordTrace_append hprefix tailTrace_5471018
  have hstable : (prefixWord ++ tailWord_5471018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471018).length < 2 ^ (prefixWord ++ tailWord_5471018).sum := by decide
  have hdescent : baseEnd_5471018 < baseStart_5471018 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471020 : List Nat := [2, 2, 1, 1, 1, 4, 4, 3, 5]
def baseStart_5471020 : Nat := 118140960795 + 5471020 * 2 ^ 59
def prefixEnd_5471020 : Nat := 4983230072969 + 3 ^ 40 * 5471020 * 2
def baseEnd_5471020 : Nat := 312140325595698871421027

theorem tailTrace_5471020 : CollatzResearch.WordTrace tailWord_5471020 prefixEnd_5471020 312140325595698871421027 := by
  unfold tailWord_5471020
  simp only [CollatzResearch.WordTrace]
  refine ⟨99772246319718195335825257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133029661759624260447767009 99772246319718195335825257)
  ·
    refine ⟨74829184739788646501868943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99772246319718195335825257 74829184739788646501868943)
    ·
      refine ⟨112243777109682969752803415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74829184739788646501868943 112243777109682969752803415)
      ·
        refine ⟨168365665664524454629205123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112243777109682969752803415 168365665664524454629205123)
        ·
          refine ⟨252548498496786681943807685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168365665664524454629205123 252548498496786681943807685)
          ·
            refine ⟨47352843468147502864463941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 252548498496786681943807685 47352843468147502864463941)
            ·
              refine ⟨8878658150277656787086989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47352843468147502864463941 8878658150277656787086989)
              ·
                refine ⟨3329496806354121295157621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8878658150277656787086989 3329496806354121295157621)
                ·
                  refine ⟨312140325595698871421027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3329496806354121295157621 312140325595698871421027)
                  ·
                    rfl

theorem cell23_5471020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 3, 5].length) (baseStart_5471020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471020 prefixEnd_5471020 := by exact prefixLift 5471020
  have htrace : WordTrace (prefixWord ++ tailWord_5471020) baseStart_5471020 baseEnd_5471020 := by
    simpa [prefixWord, tailWord_5471020, baseEnd_5471020] using wordTrace_append hprefix tailTrace_5471020
  have hstable : (prefixWord ++ tailWord_5471020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471020).length < 2 ^ (prefixWord ++ tailWord_5471020).sum := by decide
  have hdescent : baseEnd_5471020 < baseStart_5471020 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471090 : List Nat := [3, 2, 1, 2, 1, 1, 3, 1, 4, 2, 3]
def baseStart_5471090 : Nat := 118140960795 + 5471090 * 2 ^ 59
def prefixEnd_5471090 : Nat := 4983230072969 + 3 ^ 40 * 5471090 * 2
def baseEnd_5471090 : Nat := 2809298874007104568913921

theorem tailTrace_5471090 : CollatzResearch.WordTrace tailWord_5471090 prefixEnd_5471090 2809298874007104568913921 := by
  unfold tailWord_5471090
  simp only [CollatzResearch.WordTrace]
  refine ⟨49886761437295698156674681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133031363832788528417799149 49886761437295698156674681)
  ·
    refine ⟨37415071077971773617506011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49886761437295698156674681 37415071077971773617506011)
    ·
      refine ⟨56122606616957660426259017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37415071077971773617506011 56122606616957660426259017)
      ·
        refine ⟨42091954962718245319694263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56122606616957660426259017 42091954962718245319694263)
        ·
          refine ⟨63137932444077367979541395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42091954962718245319694263 63137932444077367979541395)
          ·
            refine ⟨94706898666116051969312093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63137932444077367979541395 94706898666116051969312093)
            ·
              refine ⟨35515086999793519488492035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94706898666116051969312093 35515086999793519488492035)
              ·
                refine ⟨53272630499690279232738053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35515086999793519488492035 53272630499690279232738053)
                ·
                  refine ⟨9988618218691927356138385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53272630499690279232738053 9988618218691927356138385)
                  ·
                    refine ⟨7491463664018945517103789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9988618218691927356138385 7491463664018945517103789)
                    ·
                      refine ⟨2809298874007104568913921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7491463664018945517103789 2809298874007104568913921)
                      ·
                        rfl

theorem cell23_5471090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_5471090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471090 prefixEnd_5471090 := by exact prefixLift 5471090
  have htrace : WordTrace (prefixWord ++ tailWord_5471090) baseStart_5471090 baseEnd_5471090 := by
    simpa [prefixWord, tailWord_5471090, baseEnd_5471090] using wordTrace_append hprefix tailTrace_5471090
  have hstable : (prefixWord ++ tailWord_5471090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471090).length < 2 ^ (prefixWord ++ tailWord_5471090).sum := by decide
  have hdescent : baseEnd_5471090 < baseStart_5471090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471097 : List Nat := [1, 2, 1, 3, 2, 5, 1, 1, 3, 4]
def baseStart_5471097 : Nat := 118140960795 + 5471097 * 2 ^ 59
def prefixEnd_5471097 : Nat := 4983230072969 + 3 ^ 40 * 5471097 * 2
def baseEnd_5471097 : Nat := 936434156123895347175463

theorem tailTrace_5471097 : CollatzResearch.WordTrace tailWord_5471097 prefixEnd_5471097 936434156123895347175463 := by
  unfold tailWord_5471097
  simp only [CollatzResearch.WordTrace]
  refine ⟨199547301060157432822203545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133031534040104955214802363 199547301060157432822203545)
  ·
    refine ⟨149660475795118074616652659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199547301060157432822203545 149660475795118074616652659)
    ·
      refine ⟨224490713692677111924978989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149660475795118074616652659 224490713692677111924978989)
      ·
        refine ⟨84184017634753916971867121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 224490713692677111924978989 84184017634753916971867121)
        ·
          refine ⟨63138013226065437728900341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84184017634753916971867121 63138013226065437728900341)
          ·
            refine ⟨5919188739943634787084407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63138013226065437728900341 5919188739943634787084407)
            ·
              refine ⟨8878783109915452180626611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5919188739943634787084407 8878783109915452180626611)
              ·
                refine ⟨13318174664873178270939917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8878783109915452180626611 13318174664873178270939917)
                ·
                  refine ⟨4994315499327441851602469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13318174664873178270939917 4994315499327441851602469)
                  ·
                    refine ⟨936434156123895347175463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4994315499327441851602469 936434156123895347175463)
                    ·
                      rfl

theorem cell23_5471097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 3, 4].length) (baseStart_5471097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471097 prefixEnd_5471097 := by exact prefixLift 5471097
  have htrace : WordTrace (prefixWord ++ tailWord_5471097) baseStart_5471097 baseEnd_5471097 := by
    simpa [prefixWord, tailWord_5471097, baseEnd_5471097] using wordTrace_append hprefix tailTrace_5471097
  have hstable : (prefixWord ++ tailWord_5471097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471097).length < 2 ^ (prefixWord ++ tailWord_5471097).sum := by decide
  have hdescent : baseEnd_5471097 < baseStart_5471097 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471160 : List Nat := [2, 1, 2, 1, 2, 4, 1, 2, 3, 1, 4]
def baseStart_5471160 : Nat := 118140960795 + 5471160 * 2 ^ 59
def prefixEnd_5471160 : Nat := 4983230072969 + 3 ^ 40 * 5471160 * 2
def baseEnd_5471160 : Nat := 2809334817652919295038599

theorem tailTrace_5471160 : CollatzResearch.WordTrace tailWord_5471160 prefixEnd_5471160 2809334817652919295038599 := by
  unfold tailWord_5471160
  simp only [CollatzResearch.WordTrace]
  refine ⟨99774799429464597290873467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133033065905952796387831289 99774799429464597290873467)
  ·
    refine ⟨149662199144196895936310201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99774799429464597290873467 149662199144196895936310201)
    ·
      refine ⟨112246649358147671952232651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149662199144196895936310201 112246649358147671952232651)
      ·
        refine ⟨168369974037221507928348977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112246649358147671952232651 168369974037221507928348977)
        ·
          refine ⟨126277480527916130946261733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168369974037221507928348977 126277480527916130946261733)
          ·
            refine ⟨23677027598984274552424075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126277480527916130946261733 23677027598984274552424075)
            ·
              refine ⟨35515541398476411828636113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23677027598984274552424075 35515541398476411828636113)
              ·
                refine ⟨26636656048857308871477085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35515541398476411828636113 26636656048857308871477085)
                ·
                  refine ⟨9988746018321490826803907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26636656048857308871477085 9988746018321490826803907)
                  ·
                    refine ⟨14983119027482236240205861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9988746018321490826803907 14983119027482236240205861)
                    ·
                      refine ⟨2809334817652919295038599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14983119027482236240205861 2809334817652919295038599)
                      ·
                        rfl

theorem cell23_5471160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 3, 1, 4].length) (baseStart_5471160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471160 prefixEnd_5471160 := by exact prefixLift 5471160
  have htrace : WordTrace (prefixWord ++ tailWord_5471160) baseStart_5471160 baseEnd_5471160 := by
    simpa [prefixWord, tailWord_5471160, baseEnd_5471160] using wordTrace_append hprefix tailTrace_5471160
  have hstable : (prefixWord ++ tailWord_5471160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471160).length < 2 ^ (prefixWord ++ tailWord_5471160).sum := by decide
  have hdescent : baseEnd_5471160 < baseStart_5471160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471173 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 5, 1, 6]
def baseStart_5471173 : Nat := 118140960795 + 5471173 * 2 ^ 59
def prefixEnd_5471173 : Nat := 4983230072969 + 3 ^ 40 * 5471173 * 2
def baseEnd_5471173 : Nat := 2809341492901427744176039

theorem tailTrace_5471173 : CollatzResearch.WordTrace tailWord_5471173 prefixEnd_5471173 2809341492901427744176039 := by
  unfold tailWord_5471173
  simp only [CollatzResearch.WordTrace]
  refine ⟨199550073007882097801970173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133033382005254731867980115 199550073007882097801970173)
  ·
    refine ⟨74831277377955786675738815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199550073007882097801970173 74831277377955786675738815)
    ·
      refine ⟨112246916066933680013608223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74831277377955786675738815 112246916066933680013608223)
      ·
        refine ⟨168370374100400520020412335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112246916066933680013608223 168370374100400520020412335)
        ·
          refine ⟨252555561150600780030618503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168370374100400520020412335 252555561150600780030618503)
          ·
            refine ⟨378833341725901170045927755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252555561150600780030618503 378833341725901170045927755)
            ·
              refine ⟨568250012588851755068891633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 378833341725901170045927755 568250012588851755068891633)
              ·
                refine ⟨426187509441638816301668725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 568250012588851755068891633 426187509441638816301668725)
                ·
                  refine ⟨39955079010153639028281443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 426187509441638816301668725 39955079010153639028281443)
                  ·
                    refine ⟨59932618515230458542422165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39955079010153639028281443 59932618515230458542422165)
                    ·
                      refine ⟨2809341492901427744176039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59932618515230458542422165 2809341492901427744176039)
                      ·
                        rfl

theorem cell23_5471173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 1, 6].length) (baseStart_5471173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471173 prefixEnd_5471173 := by exact prefixLift 5471173
  have htrace : WordTrace (prefixWord ++ tailWord_5471173) baseStart_5471173 baseEnd_5471173 := by
    simpa [prefixWord, tailWord_5471173, baseEnd_5471173] using wordTrace_append hprefix tailTrace_5471173
  have hstable : (prefixWord ++ tailWord_5471173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471173).length < 2 ^ (prefixWord ++ tailWord_5471173).sum := by decide
  have hdescent : baseEnd_5471173 < baseStart_5471173 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471194 : List Nat := [3, 1, 1, 2, 4, 1, 4, 1, 1, 1, 4]
def baseStart_5471194 : Nat := 118140960795 + 5471194 * 2 ^ 59
def prefixEnd_5471194 : Nat := 4983230072969 + 3 ^ 40 * 5471194 * 2
def baseEnd_5471194 : Nat := 2809352275995172162013443

theorem tailTrace_5471194 : CollatzResearch.WordTrace tailWord_5471194 prefixEnd_5471194 2809352275995172162013443 := by
  unfold tailWord_5471194
  simp only [CollatzResearch.WordTrace]
  refine ⟨49887709735201504597121159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133033892627204012258989757 49887709735201504597121159)
  ·
    refine ⟨74831564602802256895681739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49887709735201504597121159 74831564602802256895681739)
    ·
      refine ⟨112247346904203385343522609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74831564602802256895681739 112247346904203385343522609)
      ·
        refine ⟨84185510178152539007641957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112247346904203385343522609 84185510178152539007641957)
        ·
          refine ⟨15784783158403601063932867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84185510178152539007641957 15784783158403601063932867)
          ·
            refine ⟨23677174737605401595899301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15784783158403601063932867 23677174737605401595899301)
            ·
              refine ⟨4439470263301012799231119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23677174737605401595899301 4439470263301012799231119)
              ·
                refine ⟨6659205394951519198846679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4439470263301012799231119 6659205394951519198846679)
                ·
                  refine ⟨9988808092427278798270019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6659205394951519198846679 9988808092427278798270019)
                  ·
                    refine ⟨14983212138640918197405029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9988808092427278798270019 14983212138640918197405029)
                    ·
                      refine ⟨2809352275995172162013443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14983212138640918197405029 2809352275995172162013443)
                      ·
                        rfl

theorem cell23_5471194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 1, 1, 1, 4].length) (baseStart_5471194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471194 prefixEnd_5471194 := by exact prefixLift 5471194
  have htrace : WordTrace (prefixWord ++ tailWord_5471194) baseStart_5471194 baseEnd_5471194 := by
    simpa [prefixWord, tailWord_5471194, baseEnd_5471194] using wordTrace_append hprefix tailTrace_5471194
  have hstable : (prefixWord ++ tailWord_5471194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471194).length < 2 ^ (prefixWord ++ tailWord_5471194).sum := by decide
  have hdescent : baseEnd_5471194 < baseStart_5471194 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471221 : List Nat := [1, 3, 5, 2, 1, 2, 1, 1, 1, 6]
def baseStart_5471221 : Nat := 118140960795 + 5471221 * 2 ^ 59
def prefixEnd_5471221 : Nat := 4983230072969 + 3 ^ 40 * 5471221 * 2
def baseEnd_5471221 : Nat := 936455379990947852125273

theorem tailTrace_5471221 : CollatzResearch.WordTrace tailWord_5471221 prefixEnd_5471221 936455379990947852125273 := by
  unfold tailWord_5471221
  simp only [CollatzResearch.WordTrace]
  refine ⟨199551823711708201999717517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133034549141138801333145011 199551823711708201999717517)
  ·
    refine ⟨74831933891890575749894069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199551823711708201999717517 74831933891890575749894069)
    ·
      refine ⟨7015493802364741476552569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 74831933891890575749894069 7015493802364741476552569)
      ·
        refine ⟨5261620351773556107414427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7015493802364741476552569 5261620351773556107414427)
        ·
          refine ⟨7892430527660334161121641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5261620351773556107414427 7892430527660334161121641)
          ·
            refine ⟨5919322895745250620841231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7892430527660334161121641 5919322895745250620841231)
            ·
              refine ⟨8878984343617875931261847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5919322895745250620841231 8878984343617875931261847)
              ·
                refine ⟨13318476515426813896892771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8878984343617875931261847 13318476515426813896892771)
                ·
                  refine ⟨19977714773140220845339157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13318476515426813896892771 19977714773140220845339157)
                  ·
                    refine ⟨936455379990947852125273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19977714773140220845339157 936455379990947852125273)
                    ·
                      rfl

theorem cell23_5471221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_5471221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471221 prefixEnd_5471221 := by exact prefixLift 5471221
  have htrace : WordTrace (prefixWord ++ tailWord_5471221) baseStart_5471221 baseEnd_5471221 := by
    simpa [prefixWord, tailWord_5471221, baseEnd_5471221] using wordTrace_append hprefix tailTrace_5471221
  have hstable : (prefixWord ++ tailWord_5471221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471221).length < 2 ^ (prefixWord ++ tailWord_5471221).sum := by decide
  have hdescent : baseEnd_5471221 < baseStart_5471221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471234 : List Nat := [3, 4, 1, 3, 1, 1, 1, 9]
def baseStart_5471234 : Nat := 118140960795 + 5471234 * 2 ^ 59
def prefixEnd_5471234 : Nat := 4983230072969 + 3 ^ 40 * 5471234 * 2
def baseEnd_5471234 : Nat := 104050845008198222426417

theorem tailTrace_5471234 : CollatzResearch.WordTrace tailWord_5471234 prefixEnd_5471234 104050845008198222426417 := by
  unfold tailWord_5471234
  simp only [CollatzResearch.WordTrace]
  refine ⟨49888074465165276304985189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133034865240440736813293837 49888074465165276304985189)
  ·
    refine ⟨9354013962218489307184723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49888074465165276304985189 9354013962218489307184723)
    ·
      refine ⟨14031020943327733960777085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9354013962218489307184723 14031020943327733960777085)
      ·
        refine ⟨5261632853747900235291407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14031020943327733960777085 5261632853747900235291407)
        ·
          refine ⟨7892449280621850352937111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5261632853747900235291407 7892449280621850352937111)
          ·
            refine ⟨11838673920932775529405667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7892449280621850352937111 11838673920932775529405667)
            ·
              refine ⟨17758010881399163294108501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11838673920932775529405667 17758010881399163294108501)
              ·
                refine ⟨104050845008198222426417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17758010881399163294108501 104050845008198222426417)
                ·
                  rfl

theorem cell23_5471234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 9].length) (baseStart_5471234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471234 prefixEnd_5471234 := by exact prefixLift 5471234
  have htrace : WordTrace (prefixWord ++ tailWord_5471234) baseStart_5471234 baseEnd_5471234 := by
    simpa [prefixWord, tailWord_5471234, baseEnd_5471234] using wordTrace_append hprefix tailTrace_5471234
  have hstable : (prefixWord ++ tailWord_5471234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471234).length < 2 ^ (prefixWord ++ tailWord_5471234).sum := by decide
  have hdescent : baseEnd_5471234 < baseStart_5471234 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471240 : List Nat := [2, 1, 3, 2, 1, 3, 1, 1, 2, 2, 5]
def baseStart_5471240 : Nat := 118140960795 + 5471240 * 2 ^ 59
def prefixEnd_5471240 : Nat := 4983230072969 + 3 ^ 40 * 5471240 * 2
def baseEnd_5471240 : Nat := 2809375896105278982038231

theorem tailTrace_5471240 : CollatzResearch.WordTrace tailWord_5471240 prefixEnd_5471240 2809375896105278982038231 := by
  unfold tailWord_5471240
  simp only [CollatzResearch.WordTrace]
  refine ⟨99776258349319684122329587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133035011132426245496439449 99776258349319684122329587)
  ·
    refine ⟨149664387523979526183494381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99776258349319684122329587 149664387523979526183494381)
    ·
      refine ⟨56124145321492322318810393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149664387523979526183494381 56124145321492322318810393)
      ·
        refine ⟨42093108991119241739107795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56124145321492322318810393 42093108991119241739107795)
        ·
          refine ⟨63139663486678862608661693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42093108991119241739107795 63139663486678862608661693)
          ·
            refine ⟨23677373807504573478248135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63139663486678862608661693 23677373807504573478248135)
            ·
              refine ⟨35516060711256860217372203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23677373807504573478248135 35516060711256860217372203)
              ·
                refine ⟨53274091066885290326058305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35516060711256860217372203 53274091066885290326058305)
                ·
                  refine ⟨39955568300163967744543729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53274091066885290326058305 39955568300163967744543729)
                  ·
                    refine ⟨29966676225122975808407797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39955568300163967744543729 29966676225122975808407797)
                    ·
                      refine ⟨2809375896105278982038231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29966676225122975808407797 2809375896105278982038231)
                      ·
                        rfl

theorem cell23_5471240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_5471240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471240 prefixEnd_5471240 := by exact prefixLift 5471240
  have htrace : WordTrace (prefixWord ++ tailWord_5471240) baseStart_5471240 baseEnd_5471240 := by
    simpa [prefixWord, tailWord_5471240, baseEnd_5471240] using wordTrace_append hprefix tailTrace_5471240
  have hstable : (prefixWord ++ tailWord_5471240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471240).length < 2 ^ (prefixWord ++ tailWord_5471240).sum := by decide
  have hdescent : baseEnd_5471240 < baseStart_5471240 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471280 : List Nat := [2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 4]
def baseStart_5471280 : Nat := 118140960795 + 5471280 * 2 ^ 59
def prefixEnd_5471280 : Nat := 4983230072969 + 3 ^ 40 * 5471280 * 2
def baseEnd_5471280 : Nat := 2809396435331458825538047

theorem tailTrace_5471280 : CollatzResearch.WordTrace tailWord_5471280 prefixEnd_5471280 2809396435331458825538047 := by
  unfold tailWord_5471280
  simp only [CollatzResearch.WordTrace]
  refine ⟨99776987809247227538057647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133035983745662970050743529 99776987809247227538057647)
  ·
    refine ⟨149665481713870841307086471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99776987809247227538057647 149665481713870841307086471)
    ·
      refine ⟨224498222570806261960629707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149665481713870841307086471 224498222570806261960629707)
      ·
        refine ⟨336747333856209392940944561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224498222570806261960629707 336747333856209392940944561)
        ·
          refine ⟨252560500392157044705708421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 336747333856209392940944561 252560500392157044705708421)
          ·
            refine ⟨47355093823529445882320329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 252560500392157044705708421 47355093823529445882320329)
            ·
              refine ⟨35516320367647084411740247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47355093823529445882320329 35516320367647084411740247)
              ·
                refine ⟨53274480551470626617610371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35516320367647084411740247 53274480551470626617610371)
                ·
                  refine ⟨79911720827205939926415557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53274480551470626617610371 79911720827205939926415557)
                  ·
                    refine ⟨14983447655101113736202917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 79911720827205939926415557 14983447655101113736202917)
                    ·
                      refine ⟨2809396435331458825538047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14983447655101113736202917 2809396435331458825538047)
                      ·
                        rfl

theorem cell23_5471280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 4].length) (baseStart_5471280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471280 prefixEnd_5471280 := by exact prefixLift 5471280
  have htrace : WordTrace (prefixWord ++ tailWord_5471280) baseStart_5471280 baseEnd_5471280 := by
    simpa [prefixWord, tailWord_5471280, baseEnd_5471280] using wordTrace_append hprefix tailTrace_5471280
  have hstable : (prefixWord ++ tailWord_5471280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471280).length < 2 ^ (prefixWord ++ tailWord_5471280).sum := by decide
  have hdescent : baseEnd_5471280 < baseStart_5471280 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471290 : List Nat := [3, 1, 1, 1, 3, 1, 2, 4, 7]
def baseStart_5471290 : Nat := 118140960795 + 5471290 * 2 ^ 59
def prefixEnd_5471290 : Nat := 4983230072969 + 3 ^ 40 * 5471290 * 2
def baseEnd_5471290 : Nat := 312155730015333754045889

theorem tailTrace_5471290 : CollatzResearch.WordTrace tailWord_5471290 prefixEnd_5471290 312155730015333754045889 := by
  unfold tailWord_5471290
  simp only [CollatzResearch.WordTrace]
  refine ⟨49888585087114556695994831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133036226898972151189319549 49888585087114556695994831)
  ·
    refine ⟨74832877630671835043992247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49888585087114556695994831 74832877630671835043992247)
    ·
      refine ⟨112249316446007752565988371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74832877630671835043992247 112249316446007752565988371)
      ·
        refine ⟨168373974669011628848982557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112249316446007752565988371 168373974669011628848982557)
        ·
          refine ⟨63140240500879360818368459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168373974669011628848982557 63140240500879360818368459)
          ·
            refine ⟨94710360751319041227552689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63140240500879360818368459 94710360751319041227552689)
            ·
              refine ⟨71032770563489280920664517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94710360751319041227552689 71032770563489280920664517)
              ·
                refine ⟨13318644480654240172624597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71032770563489280920664517 13318644480654240172624597)
                ·
                  refine ⟨312155730015333754045889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13318644480654240172624597 312155730015333754045889)
                  ·
                    rfl

theorem cell23_5471290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 7].length) (baseStart_5471290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471290 prefixEnd_5471290 := by exact prefixLift 5471290
  have htrace : WordTrace (prefixWord ++ tailWord_5471290) baseStart_5471290 baseEnd_5471290 := by
    simpa [prefixWord, tailWord_5471290, baseEnd_5471290] using wordTrace_append hprefix tailTrace_5471290
  have hstable : (prefixWord ++ tailWord_5471290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471290).length < 2 ^ (prefixWord ++ tailWord_5471290).sum := by decide
  have hdescent : baseEnd_5471290 < baseStart_5471290 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471317 : List Nat := [1, 3, 2, 2, 1, 2, 2, 2, 2, 3, 3]
def baseStart_5471317 : Nat := 118140960795 + 5471317 * 2 ^ 59
def prefixEnd_5471317 : Nat := 4983230072969 + 3 ^ 40 * 5471317 * 2
def baseEnd_5471317 : Nat := 2809415434115675180775377

theorem tailTrace_5471317 : CollatzResearch.WordTrace tailWord_5471317 prefixEnd_5471317 2809415434115675180775377 := by
  unfold tailWord_5471317
  simp only [CollatzResearch.WordTrace]
  refine ⟨199555325119360410395212205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133036883412906940263474803 199555325119360410395212205)
  ·
    refine ⟨74833246919760153898204577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199555325119360410395212205 74833246919760153898204577)
    ·
      refine ⟨56124935189820115423653433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74833246919760153898204577 56124935189820115423653433)
      ·
        refine ⟨42093701392365086567740075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56124935189820115423653433 42093701392365086567740075)
        ·
          refine ⟨63140552088547629851610113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42093701392365086567740075 63140552088547629851610113)
          ·
            refine ⟨47355414066410722388707585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63140552088547629851610113 47355414066410722388707585)
            ·
              refine ⟨35516560549808041791530689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47355414066410722388707585 35516560549808041791530689)
              ·
                refine ⟨26637420412356031343648017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35516560549808041791530689 26637420412356031343648017)
                ·
                  refine ⟨19978065309267023507736013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26637420412356031343648017 19978065309267023507736013)
                  ·
                    refine ⟨7491774490975133815401005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19978065309267023507736013 7491774490975133815401005)
                    ·
                      refine ⟨2809415434115675180775377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7491774490975133815401005 2809415434115675180775377)
                      ·
                        rfl

theorem cell23_5471317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_5471317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471317 prefixEnd_5471317 := by exact prefixLift 5471317
  have htrace : WordTrace (prefixWord ++ tailWord_5471317) baseStart_5471317 baseEnd_5471317 := by
    simpa [prefixWord, tailWord_5471317, baseEnd_5471317] using wordTrace_append hprefix tailTrace_5471317
  have hstable : (prefixWord ++ tailWord_5471317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471317).length < 2 ^ (prefixWord ++ tailWord_5471317).sum := by decide
  have hdescent : baseEnd_5471317 < baseStart_5471317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471324 : List Nat := [2, 2, 4, 1, 1, 1, 3, 4, 5]
def baseStart_5471324 : Nat := 118140960795 + 5471324 * 2 ^ 59
def prefixEnd_5471324 : Nat := 4983230072969 + 3 ^ 40 * 5471324 * 2
def baseEnd_5471324 : Nat := 312157669831139628154205

theorem tailTrace_5471324 : CollatzResearch.WordTrace tailWord_5471324 prefixEnd_5471324 312157669831139628154205 := by
  unfold tailWord_5471324
  simp only [CollatzResearch.WordTrace]
  refine ⟨99777790215167525295358513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133037053620223367060478017 99777790215167525295358513)
  ·
    refine ⟨74833342661375643971518885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99777790215167525295358513 74833342661375643971518885)
    ·
      refine ⟨14031251749007933244659791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74833342661375643971518885 14031251749007933244659791)
      ·
        refine ⟨21046877623511899866989687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14031251749007933244659791 21046877623511899866989687)
        ·
          refine ⟨31570316435267849800484531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21046877623511899866989687 31570316435267849800484531)
          ·
            refine ⟨47355474652901774700726797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31570316435267849800484531 47355474652901774700726797)
            ·
              refine ⟨17758302994838165512772549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47355474652901774700726797 17758302994838165512772549)
              ·
                refine ⟨3329681811532156033644853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17758302994838165512772549 3329681811532156033644853)
                ·
                  refine ⟨312157669831139628154205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3329681811532156033644853 312157669831139628154205)
                  ·
                    rfl

theorem cell23_5471324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 4, 5].length) (baseStart_5471324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471324 prefixEnd_5471324 := by exact prefixLift 5471324
  have htrace : WordTrace (prefixWord ++ tailWord_5471324) baseStart_5471324 baseEnd_5471324 := by
    simpa [prefixWord, tailWord_5471324, baseEnd_5471324] using wordTrace_append hprefix tailTrace_5471324
  have hstable : (prefixWord ++ tailWord_5471324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471324).length < 2 ^ (prefixWord ++ tailWord_5471324).sum := by decide
  have hdescent : baseEnd_5471324 < baseStart_5471324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471327 : List Nat := [1, 1, 2, 3, 1, 1, 3, 1, 1, 7, 2]
def baseStart_5471327 : Nat := 118140960795 + 5471327 * 2 ^ 59
def prefixEnd_5471327 : Nat := 4983230072969 + 3 ^ 40 * 5471327 * 2
def baseEnd_5471327 : Nat := 2809420568922220141650331

theorem tailTrace_5471327 : CollatzResearch.WordTrace tailWord_5471327 prefixEnd_5471327 2809420568922220141650331 := by
  unfold tailWord_5471327
  simp only [CollatzResearch.WordTrace]
  refine ⟨199555689849324182103076235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133037126566216121402050823 199555689849324182103076235)
  ·
    refine ⟨299333534773986273154614353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199555689849324182103076235 299333534773986273154614353)
    ·
      refine ⟨224500151080489704865960765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299333534773986273154614353 224500151080489704865960765)
      ·
        refine ⟨84187556655183639324735287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 224500151080489704865960765 84187556655183639324735287)
        ·
          refine ⟨126281334982775458987102931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84187556655183639324735287 126281334982775458987102931)
          ·
            refine ⟨189422002474163188480654397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126281334982775458987102931 189422002474163188480654397)
            ·
              refine ⟨71033250927811195680245399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 189422002474163188480654397 71033250927811195680245399)
              ·
                refine ⟨106549876391716793520368099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71033250927811195680245399 106549876391716793520368099)
                ·
                  refine ⟨159824814587575190280552149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106549876391716793520368099 159824814587575190280552149)
                  ·
                    refine ⟨3745894091896293522200441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 159824814587575190280552149 3745894091896293522200441)
                    ·
                      refine ⟨2809420568922220141650331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3745894091896293522200441 2809420568922220141650331)
                      ·
                        rfl

theorem cell23_5471327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 7, 2].length) (baseStart_5471327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471327 prefixEnd_5471327 := by exact prefixLift 5471327
  have htrace : WordTrace (prefixWord ++ tailWord_5471327) baseStart_5471327 baseEnd_5471327 := by
    simpa [prefixWord, tailWord_5471327, baseEnd_5471327] using wordTrace_append hprefix tailTrace_5471327
  have hstable : (prefixWord ++ tailWord_5471327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471327).length < 2 ^ (prefixWord ++ tailWord_5471327).sum := by decide
  have hdescent : baseEnd_5471327 < baseStart_5471327 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471357 : List Nat := [1, 4, 1, 1, 3, 1, 3, 1, 1, 3, 4]
def baseStart_5471357 : Nat := 118140960795 + 5471357 * 2 ^ 59
def prefixEnd_5471357 : Nat := 4983230072969 + 3 ^ 40 * 5471357 * 2
def baseEnd_5471357 : Nat := 2809435973341855024275193

theorem tailTrace_5471357 : CollatzResearch.WordTrace tailWord_5471357 prefixEnd_5471357 2809435973341855024275193 := by
  unfold tailWord_5471357
  simp only [CollatzResearch.WordTrace]
  refine ⟨199556784039215497226668325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133037856026143664817778883 199556784039215497226668325)
  ·
    refine ⟨37416897007352905730000311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 199556784039215497226668325 37416897007352905730000311)
    ·
      refine ⟨56125345511029358595000467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37416897007352905730000311 56125345511029358595000467)
      ·
        refine ⟨84188018266544037892500701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56125345511029358595000467 84188018266544037892500701)
        ·
          refine ⟨31570506849954014209687763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84188018266544037892500701 31570506849954014209687763)
          ·
            refine ⟨47355760274931021314531645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31570506849954014209687763 47355760274931021314531645)
            ·
              refine ⟨17758410103099132992949367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47355760274931021314531645 17758410103099132992949367)
              ·
                refine ⟨26637615154648699489424051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17758410103099132992949367 26637615154648699489424051)
                ·
                  refine ⟨39956422731973049234136077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26637615154648699489424051 39956422731973049234136077)
                  ·
                    refine ⟨14983658524489893462801029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39956422731973049234136077 14983658524489893462801029)
                    ·
                      refine ⟨2809435973341855024275193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14983658524489893462801029 2809435973341855024275193)
                      ·
                        rfl

theorem cell23_5471357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_5471357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471357 prefixEnd_5471357 := by exact prefixLift 5471357
  have htrace : WordTrace (prefixWord ++ tailWord_5471357) baseStart_5471357 baseEnd_5471357 := by
    simpa [prefixWord, tailWord_5471357, baseEnd_5471357] using wordTrace_append hprefix tailTrace_5471357
  have hstable : (prefixWord ++ tailWord_5471357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471357).length < 2 ^ (prefixWord ++ tailWord_5471357).sum := by decide
  have hdescent : baseEnd_5471357 < baseStart_5471357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471367 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 7, 4]
def baseStart_5471367 : Nat := 118140960795 + 5471367 * 2 ^ 59
def prefixEnd_5471367 : Nat := 4983230072969 + 3 ^ 40 * 5471367 * 2
def baseEnd_5471367 : Nat := 936480369382799995050049

theorem tailTrace_5471367 : CollatzResearch.WordTrace tailWord_5471367 prefixEnd_5471367 936480369382799995050049 := by
  unfold tailWord_5471367
  simp only [CollatzResearch.WordTrace]
  refine ⟨199557148769179268934532355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133038099179452845956354903 199557148769179268934532355)
  ·
    refine ⟨299335723153768903401798533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199557148769179268934532355 299335723153768903401798533)
    ·
      refine ⟨56125448091331669387837225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 299335723153768903401798533 56125448091331669387837225)
      ·
        refine ⟨42094086068498752040877919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56125448091331669387837225 42094086068498752040877919)
        ·
          refine ⟨63141129102748128061316879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42094086068498752040877919 63141129102748128061316879)
          ·
            refine ⟨94711693654122192091975319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63141129102748128061316879 94711693654122192091975319)
            ·
              refine ⟨142067540481183288137962979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94711693654122192091975319 142067540481183288137962979)
              ·
                refine ⟨213101310721774932206944469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142067540481183288137962979 213101310721774932206944469)
                ·
                  refine ⟨4994561970041599973600261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 213101310721774932206944469 4994561970041599973600261)
                  ·
                    refine ⟨936480369382799995050049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4994561970041599973600261 936480369382799995050049)
                    ·
                      rfl

theorem cell23_5471367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 7, 4].length) (baseStart_5471367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471367 prefixEnd_5471367 := by exact prefixLift 5471367
  have htrace : WordTrace (prefixWord ++ tailWord_5471367) baseStart_5471367 baseEnd_5471367 := by
    simpa [prefixWord, tailWord_5471367, baseEnd_5471367] using wordTrace_append hprefix tailTrace_5471367
  have hstable : (prefixWord ++ tailWord_5471367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471367).length < 2 ^ (prefixWord ++ tailWord_5471367).sum := by decide
  have hdescent : baseEnd_5471367 < baseStart_5471367 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471384 : List Nat := [2, 1, 2, 4, 2, 1, 1, 3, 3, 4]
def baseStart_5471384 : Nat := 118140960795 + 5471384 * 2 ^ 59
def prefixEnd_5471384 : Nat := 4983230072969 + 3 ^ 40 * 5471384 * 2
def baseEnd_5471384 : Nat := 936483279106508806212523

theorem tailTrace_5471384 : CollatzResearch.WordTrace tailWord_5471384 prefixEnd_5471384 936483279106508806212523 := by
  unfold tailWord_5471384
  simp only [CollatzResearch.WordTrace]
  refine ⟨99778884405058840418950603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133038512540078453891934137 99778884405058840418950603)
  ·
    refine ⟨149668326607588260628425905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99778884405058840418950603 149668326607588260628425905)
    ·
      refine ⟨112251244955691195471319429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149668326607588260628425905 112251244955691195471319429)
      ·
        refine ⟨21047108429192099150872393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112251244955691195471319429 21047108429192099150872393)
        ·
          refine ⟨15785331321894074363154295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21047108429192099150872393 15785331321894074363154295)
          ·
            refine ⟨23677996982841111544731443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15785331321894074363154295 23677996982841111544731443)
            ·
              refine ⟨35516995474261667317097165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23677996982841111544731443 35516995474261667317097165)
              ·
                refine ⟨13318873302848125243911437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35516995474261667317097165 13318873302848125243911437)
                ·
                  refine ⟨4994577488568046966466789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13318873302848125243911437 4994577488568046966466789)
                  ·
                    refine ⟨936483279106508806212523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4994577488568046966466789 936483279106508806212523)
                    ·
                      rfl

theorem cell23_5471384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 3, 4].length) (baseStart_5471384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471384 prefixEnd_5471384 := by exact prefixLift 5471384
  have htrace : WordTrace (prefixWord ++ tailWord_5471384) baseStart_5471384 baseEnd_5471384 := by
    simpa [prefixWord, tailWord_5471384, baseEnd_5471384] using wordTrace_append hprefix tailTrace_5471384
  have hstable : (prefixWord ++ tailWord_5471384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471384).length < 2 ^ (prefixWord ++ tailWord_5471384).sum := by decide
  have hdescent : baseEnd_5471384 < baseStart_5471384 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471448 : List Nat := [2, 1, 2, 2, 6, 1, 2, 1, 6]
def baseStart_5471448 : Nat := 118140960795 + 5471448 * 2 ^ 59
def prefixEnd_5471448 : Nat := 4983230072969 + 3 ^ 40 * 5471448 * 2
def baseEnd_5471448 : Nat := 312164744453490463137475

theorem tailTrace_5471448 : CollatzResearch.WordTrace tailWord_5471448 prefixEnd_5471448 312164744453490463137475 := by
  unfold tailWord_5471448
  simp only [CollatzResearch.WordTrace]
  refine ⟨99780051540942909884115499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133040068721257213178820665 99780051540942909884115499)
  ·
    refine ⟨149670077311414364826173249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99780051540942909884115499 149670077311414364826173249)
    ·
      refine ⟨112252557983560773619629937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149670077311414364826173249 112252557983560773619629937)
      ·
        refine ⟨84189418487670580214722453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112252557983560773619629937 84189418487670580214722453)
        ·
          refine ⟨3946378991609558447565115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 84189418487670580214722453 3946378991609558447565115)
          ·
            refine ⟨5919568487414337671347673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3946378991609558447565115 5919568487414337671347673)
            ·
              refine ⟨4439676365560753253510755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5919568487414337671347673 4439676365560753253510755)
              ·
                refine ⟨6659514548341129880266133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4439676365560753253510755 6659514548341129880266133)
                ·
                  refine ⟨312164744453490463137475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6659514548341129880266133 312164744453490463137475)
                  ·
                    rfl

theorem cell23_5471448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 1, 6].length) (baseStart_5471448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471448 prefixEnd_5471448 := by exact prefixLift 5471448
  have htrace : WordTrace (prefixWord ++ tailWord_5471448) baseStart_5471448 baseEnd_5471448 := by
    simpa [prefixWord, tailWord_5471448, baseEnd_5471448] using wordTrace_append hprefix tailTrace_5471448
  have hstable : (prefixWord ++ tailWord_5471448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471448).length < 2 ^ (prefixWord ++ tailWord_5471448).sum := by decide
  have hdescent : baseEnd_5471448 < baseStart_5471448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471464 : List Nat := [2, 1, 4, 1, 2, 1, 3, 1, 3, 1, 4]
def baseStart_5471464 : Nat := 118140960795 + 5471464 * 2 ^ 59
def prefixEnd_5471464 : Nat := 4983230072969 + 3 ^ 40 * 5471464 * 2
def baseEnd_5471464 : Nat := 2809490915771886105637201

theorem tailTrace_5471464 : CollatzResearch.WordTrace tailWord_5471464 prefixEnd_5471464 2809490915771886105637201 := by
  unfold tailWord_5471464
  simp only [CollatzResearch.WordTrace]
  refine ⟨99780343324913927250406723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133040457766551903000542297 99780343324913927250406723)
  ·
    refine ⟨149670514987370890875610085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99780343324913927250406723 149670514987370890875610085)
    ·
      refine ⟨28063221560132042039176891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149670514987370890875610085 28063221560132042039176891)
      ·
        refine ⟨42094832340198063058765337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28063221560132042039176891 42094832340198063058765337)
        ·
          refine ⟨31571124255148547294074003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42094832340198063058765337 31571124255148547294074003)
          ·
            refine ⟨47356686382722820941111005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31571124255148547294074003 47356686382722820941111005)
            ·
              refine ⟨17758757393521057852916627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47356686382722820941111005 17758757393521057852916627)
              ·
                refine ⟨26638136090281586779374941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17758757393521057852916627 26638136090281586779374941)
                ·
                  refine ⟨9989301033855595042265603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26638136090281586779374941 9989301033855595042265603)
                  ·
                    refine ⟨14983951550783392563398405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9989301033855595042265603 14983951550783392563398405)
                    ·
                      refine ⟨2809490915771886105637201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14983951550783392563398405 2809490915771886105637201)
                      ·
                        rfl

theorem cell23_5471464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_5471464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471464 prefixEnd_5471464 := by exact prefixLift 5471464
  have htrace : WordTrace (prefixWord ++ tailWord_5471464) baseStart_5471464 baseEnd_5471464 := by
    simpa [prefixWord, tailWord_5471464, baseEnd_5471464] using wordTrace_append hprefix tailTrace_5471464
  have hstable : (prefixWord ++ tailWord_5471464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471464).length < 2 ^ (prefixWord ++ tailWord_5471464).sum := by decide
  have hdescent : baseEnd_5471464 < baseStart_5471464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471481 : List Nat := [1, 2, 1, 3, 1, 1, 7, 1, 1, 1, 4]
def baseStart_5471481 : Nat := 118140960795 + 5471481 * 2 ^ 59
def prefixEnd_5471481 : Nat := 4983230072969 + 3 ^ 40 * 5471481 * 2
def baseEnd_5471481 : Nat := 2809499644943012539124623

theorem tailTrace_5471481 : CollatzResearch.WordTrace tailWord_5471481 prefixEnd_5471481 2809499644943012539124623 := by
  unfold tailWord_5471481
  simp only [CollatzResearch.WordTrace]
  refine ⟨199561306690766266404182297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133040871127177510936121531 199561306690766266404182297)
  ·
    refine ⟨149670980018074699803136723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199561306690766266404182297 149670980018074699803136723)
    ·
      refine ⟨224506470027112049704705085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149670980018074699803136723 224506470027112049704705085)
      ·
        refine ⟨84189926260167018639264407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 224506470027112049704705085 84189926260167018639264407)
        ·
          refine ⟨126284889390250527958896611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84189926260167018639264407 126284889390250527958896611)
          ·
            refine ⟨189427334085375791938344917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126284889390250527958896611 189427334085375791938344917)
            ·
              refine ⟨4439703142625995123554959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 189427334085375791938344917 4439703142625995123554959)
              ·
                refine ⟨6659554713938992685332439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4439703142625995123554959 6659554713938992685332439)
                ·
                  refine ⟨9989332070908489027998659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6659554713938992685332439 9989332070908489027998659)
                  ·
                    refine ⟨14983998106362733541997989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9989332070908489027998659 14983998106362733541997989)
                    ·
                      refine ⟨2809499644943012539124623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14983998106362733541997989 2809499644943012539124623)
                      ·
                        rfl

theorem cell23_5471481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 1, 1, 1, 4].length) (baseStart_5471481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471481 prefixEnd_5471481 := by exact prefixLift 5471481
  have htrace : WordTrace (prefixWord ++ tailWord_5471481) baseStart_5471481 baseEnd_5471481 := by
    simpa [prefixWord, tailWord_5471481, baseEnd_5471481] using wordTrace_append hprefix tailTrace_5471481
  have hstable : (prefixWord ++ tailWord_5471481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471481).length < 2 ^ (prefixWord ++ tailWord_5471481).sum := by decide
  have hdescent : baseEnd_5471481 < baseStart_5471481 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471491 : List Nat := [1, 1, 1, 3, 2, 5, 2, 2, 2, 4]
def baseStart_5471491 : Nat := 118140960795 + 5471491 * 2 ^ 59
def prefixEnd_5471491 : Nat := 4983230072969 + 3 ^ 40 * 5471491 * 2
def baseEnd_5471491 : Nat := 936501593249852499999859

theorem tailTrace_5471491 : CollatzResearch.WordTrace tailWord_5471491 prefixEnd_5471491 936501593249852499999859 := by
  unfold tailWord_5471491
  simp only [CollatzResearch.WordTrace]
  refine ⟨199561671420730038112046327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133041114280486692074697551 199561671420730038112046327)
  ·
    refine ⟨299342507131095057168069491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199561671420730038112046327 299342507131095057168069491)
    ·
      refine ⟨449013760696642585752104237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299342507131095057168069491 449013760696642585752104237)
      ·
        refine ⟨168380160261240969657039089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 449013760696642585752104237 168380160261240969657039089)
        ·
          refine ⟨126285120195930727242779317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168380160261240969657039089 126285120195930727242779317)
          ·
            refine ⟨11839230018368505679010561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 126285120195930727242779317 11839230018368505679010561)
            ·
              refine ⟨8879422513776379259257921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11839230018368505679010561 8879422513776379259257921)
              ·
                refine ⟨6659566885332284444443441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8879422513776379259257921 6659566885332284444443441)
                ·
                  refine ⟨4994675163999213333332581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6659566885332284444443441 4994675163999213333332581)
                  ·
                    refine ⟨936501593249852499999859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4994675163999213333332581 936501593249852499999859)
                    ·
                      rfl

theorem cell23_5471491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 2, 2, 4].length) (baseStart_5471491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471491 prefixEnd_5471491 := by exact prefixLift 5471491
  have htrace : WordTrace (prefixWord ++ tailWord_5471491) baseStart_5471491 baseEnd_5471491 := by
    simpa [prefixWord, tailWord_5471491, baseEnd_5471491] using wordTrace_append hprefix tailTrace_5471491
  have hstable : (prefixWord ++ tailWord_5471491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471491).length < 2 ^ (prefixWord ++ tailWord_5471491).sum := by decide
  have hdescent : baseEnd_5471491 < baseStart_5471491 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471492 : List Nat := [2, 3, 2, 2, 2, 3, 2, 2, 1, 1, 3]
def baseStart_5471492 : Nat := 118140960795 + 5471492 * 2 ^ 59
def prefixEnd_5471492 : Nat := 4983230072969 + 3 ^ 40 * 5471492 * 2
def baseEnd_5471492 : Nat := 2809505293230211996087073

theorem tailTrace_5471492 : CollatzResearch.WordTrace tailWord_5471492 prefixEnd_5471492 2809505293230211996087073 := by
  unfold tailWord_5471492
  simp only [CollatzResearch.WordTrace]
  refine ⟨99780853946863207641416365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133041138595817610188555153 99780853946863207641416365)
  ·
    refine ⟨37417820230073702865531137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99780853946863207641416365 37417820230073702865531137)
    ·
      refine ⟨28063365172555277149148353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37417820230073702865531137 28063365172555277149148353)
      ·
        refine ⟨21047523879416457861861265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28063365172555277149148353 21047523879416457861861265)
        ·
          refine ⟨15785642909562343396395949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21047523879416457861861265 15785642909562343396395949)
          ·
            refine ⟨5919616091085878773648481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15785642909562343396395949 5919616091085878773648481)
            ·
              refine ⟨4439712068314409080236361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5919616091085878773648481 4439712068314409080236361)
              ·
                refine ⟨3329784051235806810177271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4439712068314409080236361 3329784051235806810177271)
                ·
                  refine ⟨4994676076853710215265907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3329784051235806810177271 4994676076853710215265907)
                  ·
                    refine ⟨7492014115280565322898861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4994676076853710215265907 7492014115280565322898861)
                    ·
                      refine ⟨2809505293230211996087073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7492014115280565322898861 2809505293230211996087073)
                      ·
                        rfl

theorem cell23_5471492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_5471492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471492 prefixEnd_5471492 := by exact prefixLift 5471492
  have htrace : WordTrace (prefixWord ++ tailWord_5471492) baseStart_5471492 baseEnd_5471492 := by
    simpa [prefixWord, tailWord_5471492, baseEnd_5471492] using wordTrace_append hprefix tailTrace_5471492
  have hstable : (prefixWord ++ tailWord_5471492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471492).length < 2 ^ (prefixWord ++ tailWord_5471492).sum := by decide
  have hdescent : baseEnd_5471492 < baseStart_5471492 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471542 : List Nat := [5, 1, 2, 3, 1, 2, 1, 2, 2, 4]
def baseStart_5471542 : Nat := 118140960795 + 5471542 * 2 ^ 59
def prefixEnd_5471542 : Nat := 4983230072969 + 3 ^ 40 * 5471542 * 2
def baseEnd_5471542 : Nat := 936510322420978933487281

theorem tailTrace_5471542 : CollatzResearch.WordTrace tailWord_5471542 prefixEnd_5471542 936510322420978933487281 := by
  unfold tailWord_5471542
  simp only [CollatzResearch.WordTrace]
  refine ⟨12472720721471579613884555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 133042354362363515881435253 12472720721471579613884555)
  ·
    refine ⟨18709081082207369420826833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12472720721471579613884555 18709081082207369420826833)
    ·
      refine ⟨14031810811655527065620125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18709081082207369420826833 14031810811655527065620125)
      ·
        refine ⟨5261929054370822649607547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14031810811655527065620125 5261929054370822649607547)
        ·
          refine ⟨7892893581556233974411321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5261929054370822649607547 7892893581556233974411321)
          ·
            refine ⟨5919670186167175480808491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7892893581556233974411321 5919670186167175480808491)
            ·
              refine ⟨8879505279250763221212737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5919670186167175480808491 8879505279250763221212737)
              ·
                refine ⟨6659628959438072415909553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8879505279250763221212737 6659628959438072415909553)
                ·
                  refine ⟨4994721719578554311932165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6659628959438072415909553 4994721719578554311932165)
                  ·
                    refine ⟨936510322420978933487281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4994721719578554311932165 936510322420978933487281)
                    ·
                      rfl

theorem cell23_5471542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_5471542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471542 prefixEnd_5471542 := by exact prefixLift 5471542
  have htrace : WordTrace (prefixWord ++ tailWord_5471542) baseStart_5471542 baseEnd_5471542 := by
    simpa [prefixWord, tailWord_5471542, baseEnd_5471542] using wordTrace_append hprefix tailTrace_5471542
  have hstable : (prefixWord ++ tailWord_5471542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471542).length < 2 ^ (prefixWord ++ tailWord_5471542).sum := by decide
  have hdescent : baseEnd_5471542 < baseStart_5471542 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471548 : List Nat := [2, 2, 2, 2, 1, 3, 3, 2, 2, 1, 3]
def baseStart_5471548 : Nat := 118140960795 + 5471548 * 2 ^ 59
def prefixEnd_5471548 : Nat := 4983230072969 + 3 ^ 40 * 5471548 * 2
def baseEnd_5471548 : Nat := 2809534048146863776986815

theorem tailTrace_5471548 : CollatzResearch.WordTrace tailWord_5471548 prefixEnd_5471548 2809534048146863776986815 := by
  unfold tailWord_5471548
  simp only [CollatzResearch.WordTrace]
  refine ⟨99781875190761768423435649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133042500254349024564580865 99781875190761768423435649)
  ·
    refine ⟨74836406393071326317576737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99781875190761768423435649 74836406393071326317576737)
    ·
      refine ⟨56127304794803494738182553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74836406393071326317576737 56127304794803494738182553)
      ·
        refine ⟨42095478596102621053636915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56127304794803494738182553 42095478596102621053636915)
        ·
          refine ⟨63143217894153931580455373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42095478596102621053636915 63143217894153931580455373)
          ·
            refine ⟨23678706710307724342670765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63143217894153931580455373 23678706710307724342670765)
            ·
              refine ⟨8879515016365396628501537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23678706710307724342670765 8879515016365396628501537)
              ·
                refine ⟨6659636262274047471376153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8879515016365396628501537 6659636262274047471376153)
                ·
                  refine ⟨4994727196705535603532115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6659636262274047471376153 4994727196705535603532115)
                  ·
                    refine ⟨7492090795058303405298173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4994727196705535603532115 7492090795058303405298173)
                    ·
                      refine ⟨2809534048146863776986815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7492090795058303405298173 2809534048146863776986815)
                      ·
                        rfl

theorem cell23_5471548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_5471548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471548 prefixEnd_5471548 := by exact prefixLift 5471548
  have htrace : WordTrace (prefixWord ++ tailWord_5471548) baseStart_5471548 baseEnd_5471548 := by
    simpa [prefixWord, tailWord_5471548, baseEnd_5471548] using wordTrace_append hprefix tailTrace_5471548
  have hstable : (prefixWord ++ tailWord_5471548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471548).length < 2 ^ (prefixWord ++ tailWord_5471548).sum := by decide
  have hdescent : baseEnd_5471548 < baseStart_5471548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471564 : List Nat := [2, 2, 1, 3, 2, 2, 2, 1, 2, 6]
def baseStart_5471564 : Nat := 118140960795 + 5471564 * 2 ^ 59
def prefixEnd_5471564 : Nat := 4983230072969 + 3 ^ 40 * 5471564 * 2
def baseEnd_5471564 : Nat := 936514087945778571462247

theorem tailTrace_5471564 : CollatzResearch.WordTrace tailWord_5471564 prefixEnd_5471564 936514087945778571462247 := by
  unfold tailWord_5471564
  simp only [CollatzResearch.WordTrace]
  refine ⟨99782166974732785789726873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133042889299643714386302497 99782166974732785789726873)
  ·
    refine ⟨74836625231049589342295155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99782166974732785789726873 74836625231049589342295155)
    ·
      refine ⟨112254937846574384013442733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74836625231049589342295155 112254937846574384013442733)
      ·
        refine ⟨42095601692465394005041025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112254937846574384013442733 42095601692465394005041025)
        ·
          refine ⟨31571701269349045503780769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42095601692465394005041025 31571701269349045503780769)
          ·
            refine ⟨23678775952011784127835577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31571701269349045503780769 23678775952011784127835577)
            ·
              refine ⟨17759081964008838095876683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23678775952011784127835577 17759081964008838095876683)
              ·
                refine ⟨26638622946013257143815025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17759081964008838095876683 26638622946013257143815025)
                ·
                  refine ⟨19978967209509942857861269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26638622946013257143815025 19978967209509942857861269)
                  ·
                    refine ⟨936514087945778571462247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19978967209509942857861269 936514087945778571462247)
                    ·
                      rfl

theorem cell23_5471564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 2, 6].length) (baseStart_5471564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471564 prefixEnd_5471564 := by exact prefixLift 5471564
  have htrace : WordTrace (prefixWord ++ tailWord_5471564) baseStart_5471564 baseEnd_5471564 := by
    simpa [prefixWord, tailWord_5471564, baseEnd_5471564] using wordTrace_append hprefix tailTrace_5471564
  have hstable : (prefixWord ++ tailWord_5471564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471564).length < 2 ^ (prefixWord ++ tailWord_5471564).sum := by decide
  have hdescent : baseEnd_5471564 < baseStart_5471564 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471588 : List Nat := [2, 3, 1, 1, 3, 2, 1, 2, 4, 2, 2]
def baseStart_5471588 : Nat := 118140960795 + 5471588 * 2 ^ 59
def prefixEnd_5471588 : Nat := 4983230072969 + 3 ^ 40 * 5471588 * 2
def baseEnd_5471588 : Nat := 2809554587373043620486631

theorem tailTrace_5471588 : CollatzResearch.WordTrace tailWord_5471588 prefixEnd_5471588 2809554587373043620486631 := by
  unfold tailWord_5471588
  simp only [CollatzResearch.WordTrace]
  refine ⟨99782604650689311839163709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133043472867585749118884945 99782604650689311839163709)
  ·
    refine ⟨37418476744008491939686391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99782604650689311839163709 37418476744008491939686391)
    ·
      refine ⟨56127715116012737909529587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37418476744008491939686391 56127715116012737909529587)
      ·
        refine ⟨84191572674019106864294381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56127715116012737909529587 84191572674019106864294381)
        ·
          refine ⟨31571839752757165074110393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84191572674019106864294381 31571839752757165074110393)
          ·
            refine ⟨23678879814567873805582795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31571839752757165074110393 23678879814567873805582795)
            ·
              refine ⟨35518319721851810708374193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23678879814567873805582795 35518319721851810708374193)
              ·
                refine ⟨26638739791388858031280645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35518319721851810708374193 26638739791388858031280645)
                ·
                  refine ⟨4994763710885410880865121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26638739791388858031280645 4994763710885410880865121)
                  ·
                    refine ⟨3746072783164058160648841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4994763710885410880865121 3746072783164058160648841)
                    ·
                      refine ⟨2809554587373043620486631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3746072783164058160648841 2809554587373043620486631)
                      ·
                        rfl

theorem cell23_5471588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 4, 2, 2].length) (baseStart_5471588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471588 prefixEnd_5471588 := by exact prefixLift 5471588
  have htrace : WordTrace (prefixWord ++ tailWord_5471588) baseStart_5471588 baseEnd_5471588 := by
    simpa [prefixWord, tailWord_5471588, baseEnd_5471588] using wordTrace_append hprefix tailTrace_5471588
  have hstable : (prefixWord ++ tailWord_5471588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471588).length < 2 ^ (prefixWord ++ tailWord_5471588).sum := by decide
  have hdescent : baseEnd_5471588 < baseStart_5471588 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471591 : List Nat := [1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 5]
def baseStart_5471591 : Nat := 118140960795 + 5471591 * 2 ^ 59
def prefixEnd_5471591 : Nat := 4983230072969 + 3 ^ 40 * 5471591 * 2
def baseEnd_5471591 : Nat := 2809556127815007108749117

theorem tailTrace_5471591 : CollatzResearch.WordTrace tailWord_5471591 prefixEnd_5471591 2809556127815007108749117 := by
  unfold tailWord_5471591
  simp only [CollatzResearch.WordTrace]
  refine ⟨199565318720367755190686627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133043545813578503460457751 199565318720367755190686627)
  ·
    refine ⟨299347978080551632786029941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199565318720367755190686627 299347978080551632786029941)
    ·
      refine ⟨28063872945051715573690307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 299347978080551632786029941 28063872945051715573690307)
      ·
        refine ⟨42095809417577573360535461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28063872945051715573690307 42095809417577573360535461)
        ·
          refine ⟨7892964265795795005100399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42095809417577573360535461 7892964265795795005100399)
          ·
            refine ⟨11839446398693692507650599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7892964265795795005100399 11839446398693692507650599)
            ·
              refine ⟨17759169598040538761475899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11839446398693692507650599 17759169598040538761475899)
              ·
                refine ⟨26638754397060808142213849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17759169598040538761475899 26638754397060808142213849)
                ·
                  refine ⟨19979065797795606106660387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26638754397060808142213849 19979065797795606106660387)
                  ·
                    refine ⟨29968598696693409159990581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19979065797795606106660387 29968598696693409159990581)
                    ·
                      refine ⟨2809556127815007108749117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29968598696693409159990581 2809556127815007108749117)
                      ·
                        rfl

theorem cell23_5471591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_5471591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471591 prefixEnd_5471591 := by exact prefixLift 5471591
  have htrace : WordTrace (prefixWord ++ tailWord_5471591) baseStart_5471591 baseEnd_5471591 := by
    simpa [prefixWord, tailWord_5471591, baseEnd_5471591] using wordTrace_append hprefix tailTrace_5471591
  have hstable : (prefixWord ++ tailWord_5471591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471591).length < 2 ^ (prefixWord ++ tailWord_5471591).sum := by decide
  have hdescent : baseEnd_5471591 < baseStart_5471591 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471641 : List Nat := [1, 2, 1, 2, 1, 6, 2, 1, 2, 5]
def baseStart_5471641 : Nat := 118140960795 + 5471641 * 2 ^ 59
def prefixEnd_5471641 : Nat := 4983230072969 + 3 ^ 40 * 5471641 * 2
def baseEnd_5471641 : Nat := 936527267282577304374629

theorem tailTrace_5471641 : CollatzResearch.WordTrace tailWord_5471641 prefixEnd_5471641 936527267282577304374629 := by
  unfold tailWord_5471641
  simp only [CollatzResearch.WordTrace]
  refine ⟨199567142370186613730006777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133044761580124409153337851 199567142370186613730006777)
  ·
    refine ⟨149675356777639960297505083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199567142370186613730006777 149675356777639960297505083)
    ·
      refine ⟨224513035166459940446257625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149675356777639960297505083 224513035166459940446257625)
      ·
        refine ⟨168384776374844955334693219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224513035166459940446257625 168384776374844955334693219)
        ·
          refine ⟨252577164562267433002039829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168384776374844955334693219 252577164562267433002039829)
          ·
            refine ⟨11839554588856285921970617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 252577164562267433002039829 11839554588856285921970617)
            ·
              refine ⟨8879665941642214441477963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11839554588856285921970617 8879665941642214441477963)
              ·
                refine ⟨13319498912463321662216945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8879665941642214441477963 13319498912463321662216945)
                ·
                  refine ⟨9989624184347491246662709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13319498912463321662216945 9989624184347491246662709)
                  ·
                    refine ⟨936527267282577304374629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9989624184347491246662709 936527267282577304374629)
                    ·
                      rfl

theorem cell23_5471641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 2, 5].length) (baseStart_5471641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471641 prefixEnd_5471641 := by exact prefixLift 5471641
  have htrace : WordTrace (prefixWord ++ tailWord_5471641) baseStart_5471641 baseEnd_5471641 := by
    simpa [prefixWord, tailWord_5471641, baseEnd_5471641] using wordTrace_append hprefix tailTrace_5471641
  have hstable : (prefixWord ++ tailWord_5471641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471641).length < 2 ^ (prefixWord ++ tailWord_5471641).sum := by decide
  have hdescent : baseEnd_5471641 < baseStart_5471641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471671 : List Nat := [1, 1, 3, 1, 3, 2, 2, 3, 3, 4]
def baseStart_5471671 : Nat := 118140960795 + 5471671 * 2 ^ 59
def prefixEnd_5471671 : Nat := 4983230072969 + 3 ^ 40 * 5471671 * 2
def baseEnd_5471671 : Nat := 936532402089122265249583

theorem tailTrace_5471671 : CollatzResearch.WordTrace tailWord_5471671 prefixEnd_5471671 936532402089122265249583 := by
  unfold tailWord_5471671
  simp only [CollatzResearch.WordTrace]
  refine ⟨199568236560077928853598867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133045491040051952569065911 199568236560077928853598867)
  ·
    refine ⟨299352354840116893280398301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199568236560077928853598867 299352354840116893280398301)
    ·
      refine ⟨112257133065043834980149363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 299352354840116893280398301 112257133065043834980149363)
      ·
        refine ⟨168385699597565752470224045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112257133065043834980149363 168385699597565752470224045)
        ·
          refine ⟨63144637349087157176334017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168385699597565752470224045 63144637349087157176334017)
          ·
            refine ⟨47358478011815367882250513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63144637349087157176334017 47358478011815367882250513)
            ·
              refine ⟨35518858508861525911687885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47358478011815367882250513 35518858508861525911687885)
              ·
                refine ⟨13319571940823072216882957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35518858508861525911687885 13319571940823072216882957)
                ·
                  refine ⟨4994839477808652081331109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13319571940823072216882957 4994839477808652081331109)
                  ·
                    refine ⟨936532402089122265249583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4994839477808652081331109 936532402089122265249583)
                    ·
                      rfl

theorem cell23_5471671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 3, 4].length) (baseStart_5471671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471671 prefixEnd_5471671 := by exact prefixLift 5471671
  have htrace : WordTrace (prefixWord ++ tailWord_5471671) baseStart_5471671 baseEnd_5471671 := by
    simpa [prefixWord, tailWord_5471671, baseEnd_5471671] using wordTrace_append hprefix tailTrace_5471671
  have hstable : (prefixWord ++ tailWord_5471671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471671).length < 2 ^ (prefixWord ++ tailWord_5471671).sum := by decide
  have hdescent : baseEnd_5471671 < baseStart_5471671 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471674 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 4, 4, 4]
def baseStart_5471674 : Nat := 118140960795 + 5471674 * 2 ^ 59
def prefixEnd_5471674 : Nat := 4983230072969 + 3 ^ 40 * 5471674 * 2
def baseEnd_5471674 : Nat := 2809598746709330284011235

theorem tailTrace_5471674 : CollatzResearch.WordTrace tailWord_5471674 prefixEnd_5471674 2809598746709330284011235 := by
  unfold tailWord_5471674
  simp only [CollatzResearch.WordTrace]
  refine ⟨49892086494766765091489519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133045563986044706910638717 49892086494766765091489519)
  ·
    refine ⟨74838129742150147637234279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49892086494766765091489519 74838129742150147637234279)
    ·
      refine ⟨112257194613225221455851419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74838129742150147637234279 112257194613225221455851419)
      ·
        refine ⟨168385791919837832183777129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112257194613225221455851419 168385791919837832183777129)
        ·
          refine ⟨126289343939878374137832847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168385791919837832183777129 126289343939878374137832847)
          ·
            refine ⟨189434015909817561206749271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126289343939878374137832847 189434015909817561206749271)
            ·
              refine ⟨284151023864726341810123907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189434015909817561206749271 284151023864726341810123907)
              ·
                refine ⟨426226535797089512715185861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 284151023864726341810123907 426226535797089512715185861)
                ·
                  refine ⟨79917475461954283634097349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 426226535797089512715185861 79917475461954283634097349)
                  ·
                    refine ⟨14984526649116428181393253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 79917475461954283634097349 14984526649116428181393253)
                    ·
                      refine ⟨2809598746709330284011235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14984526649116428181393253 2809598746709330284011235)
                      ·
                        rfl

theorem cell23_5471674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 4, 4, 4].length) (baseStart_5471674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471674 prefixEnd_5471674 := by exact prefixLift 5471674
  have htrace : WordTrace (prefixWord ++ tailWord_5471674) baseStart_5471674 baseEnd_5471674 := by
    simpa [prefixWord, tailWord_5471674, baseEnd_5471674] using wordTrace_append hprefix tailTrace_5471674
  have hstable : (prefixWord ++ tailWord_5471674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471674).length < 2 ^ (prefixWord ++ tailWord_5471674).sum := by decide
  have hdescent : baseEnd_5471674 < baseStart_5471674 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471705 : List Nat := [1, 2, 1, 2, 4, 3, 2, 3, 1, 4]
def baseStart_5471705 : Nat := 118140960795 + 5471705 * 2 ^ 59
def prefixEnd_5471705 : Nat := 4983230072969 + 3 ^ 40 * 5471705 * 2
def baseEnd_5471705 : Nat := 936538221536539887574531

theorem tailTrace_5471705 : CollatzResearch.WordTrace tailWord_5471705 prefixEnd_5471705 936538221536539887574531 := by
  unfold tailWord_5471705
  simp only [CollatzResearch.WordTrace]
  refine ⟨199569476641954752660336569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133046317761303168440224379 199569476641954752660336569)
  ·
    refine ⟨149677107481466064495252427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199569476641954752660336569 149677107481466064495252427)
    ·
      refine ⟨224515661222199096742878641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149677107481466064495252427 224515661222199096742878641)
      ·
        refine ⟨168386745916649322557158981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224515661222199096742878641 168386745916649322557158981)
        ·
          refine ⟨31572514859371747979467309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 168386745916649322557158981 31572514859371747979467309)
          ·
            refine ⟨11839693072264405492300241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31572514859371747979467309 11839693072264405492300241)
            ·
              refine ⟨8879769804198304119225181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11839693072264405492300241 8879769804198304119225181)
              ·
                refine ⟨3329913676574364044709443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8879769804198304119225181 3329913676574364044709443)
                ·
                  refine ⟨4994870514861546067064165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3329913676574364044709443 4994870514861546067064165)
                  ·
                    refine ⟨936538221536539887574531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4994870514861546067064165 936538221536539887574531)
                    ·
                      rfl

theorem cell23_5471705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 3, 1, 4].length) (baseStart_5471705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471705 prefixEnd_5471705 := by exact prefixLift 5471705
  have htrace : WordTrace (prefixWord ++ tailWord_5471705) baseStart_5471705 baseEnd_5471705 := by
    simpa [prefixWord, tailWord_5471705, baseEnd_5471705] using wordTrace_append hprefix tailTrace_5471705
  have hstable : (prefixWord ++ tailWord_5471705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471705).length < 2 ^ (prefixWord ++ tailWord_5471705).sum := by decide
  have hdescent : baseEnd_5471705 < baseStart_5471705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471724 : List Nat := [2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 7]
def baseStart_5471724 : Nat := 118140960795 + 5471724 * 2 ^ 59
def prefixEnd_5471724 : Nat := 4983230072969 + 3 ^ 40 * 5471724 * 2
def baseEnd_5471724 : Nat := 2809624420742055088386005

theorem tailTrace_5471724 : CollatzResearch.WordTrace tailWord_5471724 prefixEnd_5471724 2809624420742055088386005 := by
  unfold tailWord_5471724
  simp only [CollatzResearch.WordTrace]
  refine ⟨99785084814442959452639113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133046779752590612603518817 99785084814442959452639113)
  ·
    refine ⟨74838813610832219589479335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99785084814442959452639113 74838813610832219589479335)
    ·
      refine ⟨112258220416248329384219003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74838813610832219589479335 112258220416248329384219003)
      ·
        refine ⟨168387330624372494076328505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112258220416248329384219003 168387330624372494076328505)
        ·
          refine ⟨126290497968279370557246379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168387330624372494076328505 126290497968279370557246379)
          ·
            refine ⟨189435746952419055835869569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126290497968279370557246379 189435746952419055835869569)
            ·
              refine ⟨142076810214314291876902177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189435746952419055835869569 142076810214314291876902177)
              ·
                refine ⟨106557607660735718907676633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142076810214314291876902177 106557607660735718907676633)
                ·
                  refine ⟨79918205745551789180757475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106557607660735718907676633 79918205745551789180757475)
                  ·
                    refine ⟨119877308618327683771136213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 79918205745551789180757475 119877308618327683771136213)
                    ·
                      refine ⟨2809624420742055088386005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 119877308618327683771136213 2809624420742055088386005)
                      ·
                        rfl

theorem cell23_5471724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 7].length) (baseStart_5471724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471724 prefixEnd_5471724 := by exact prefixLift 5471724
  have htrace : WordTrace (prefixWord ++ tailWord_5471724) baseStart_5471724 baseEnd_5471724 := by
    simpa [prefixWord, tailWord_5471724, baseEnd_5471724] using wordTrace_append hprefix tailTrace_5471724
  have hstable : (prefixWord ++ tailWord_5471724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471724).length < 2 ^ (prefixWord ++ tailWord_5471724).sum := by decide
  have hdescent : baseEnd_5471724 < baseStart_5471724 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471728 : List Nat := [2, 1, 1, 1, 3, 4, 1, 3, 3, 1, 3]
def baseStart_5471728 : Nat := 118140960795 + 5471728 * 2 ^ 59
def prefixEnd_5471728 : Nat := 4983230072969 + 3 ^ 40 * 5471728 * 2
def baseEnd_5471728 : Nat := 2809626474664673072735987

theorem tailTrace_5471728 : CollatzResearch.WordTrace tailWord_5471728 prefixEnd_5471728 2809626474664673072735987 := by
  unfold tailWord_5471728
  simp only [CollatzResearch.WordTrace]
  refine ⟨99785157760435713794211919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133046877013914285058949225 99785157760435713794211919)
  ·
    refine ⟨149677736640653570691317879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99785157760435713794211919 149677736640653570691317879)
    ·
      refine ⟨224516604960980356036976819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149677736640653570691317879 224516604960980356036976819)
      ·
        refine ⟨336774907441470534055465229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224516604960980356036976819 336774907441470534055465229)
        ·
          refine ⟨126290590290551450270799461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 336774907441470534055465229 126290590290551450270799461)
          ·
            refine ⟨23679485679478396925774899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126290590290551450270799461 23679485679478396925774899)
            ·
              refine ⟨35519228519217595388662349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23679485679478396925774899 35519228519217595388662349)
              ·
                refine ⟨13319710694706598270748381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35519228519217595388662349 13319710694706598270748381)
                ·
                  refine ⟨4994891510514974351530643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13319710694706598270748381 4994891510514974351530643)
                  ·
                    refine ⟨7492337265772461527295965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4994891510514974351530643 7492337265772461527295965)
                    ·
                      refine ⟨2809626474664673072735987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7492337265772461527295965 2809626474664673072735987)
                      ·
                        rfl

theorem cell23_5471728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 3, 1, 3].length) (baseStart_5471728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471728 prefixEnd_5471728 := by exact prefixLift 5471728
  have htrace : WordTrace (prefixWord ++ tailWord_5471728) baseStart_5471728 baseEnd_5471728 := by
    simpa [prefixWord, tailWord_5471728, baseEnd_5471728] using wordTrace_append hprefix tailTrace_5471728
  have hstable : (prefixWord ++ tailWord_5471728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471728).length < 2 ^ (prefixWord ++ tailWord_5471728).sum := by decide
  have hdescent : baseEnd_5471728 < baseStart_5471728 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471761 : List Nat := [1, 2, 2, 1, 1, 2, 3, 1, 6, 4]
def baseStart_5471761 : Nat := 118140960795 + 5471761 * 2 ^ 59
def prefixEnd_5471761 : Nat := 4983230072969 + 3 ^ 40 * 5471761 * 2
def baseEnd_5471761 : Nat := 936547806508757147874445

theorem tailTrace_5471761 : CollatzResearch.WordTrace tailWord_5471761 prefixEnd_5471761 936547806508757147874445 := by
  unfold tailWord_5471761
  simp only [CollatzResearch.WordTrace]
  refine ⟨199571519129751874224375137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133047679419834582816250091 199571519129751874224375137)
  ·
    refine ⟨149678639347313905668281353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199571519129751874224375137 149678639347313905668281353)
    ·
      refine ⟨112258979510485429251211015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149678639347313905668281353 112258979510485429251211015)
      ·
        refine ⟨168388469265728143876816523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112258979510485429251211015 168388469265728143876816523)
        ·
          refine ⟨252582703898592215815224785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168388469265728143876816523 252582703898592215815224785)
          ·
            refine ⟨189437027923944161861418589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 252582703898592215815224785 189437027923944161861418589)
            ·
              refine ⟨71038885471479060698031971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 189437027923944161861418589 71038885471479060698031971)
              ·
                refine ⟨106558328207218591047047957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71038885471479060698031971 106558328207218591047047957)
                ·
                  refine ⟨4994921634713371455330373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 106558328207218591047047957 4994921634713371455330373)
                  ·
                    refine ⟨936547806508757147874445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4994921634713371455330373 936547806508757147874445)
                    ·
                      rfl

theorem cell23_5471761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 6, 4].length) (baseStart_5471761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471761 prefixEnd_5471761 := by exact prefixLift 5471761
  have htrace : WordTrace (prefixWord ++ tailWord_5471761) baseStart_5471761 baseEnd_5471761 := by
    simpa [prefixWord, tailWord_5471761, baseEnd_5471761] using wordTrace_append hprefix tailTrace_5471761
  have hstable : (prefixWord ++ tailWord_5471761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471761).length < 2 ^ (prefixWord ++ tailWord_5471761).sum := by decide
  have hdescent : baseEnd_5471761 < baseStart_5471761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471778 : List Nat := [3, 3, 1, 1, 1, 1, 4, 1, 4, 4]
def baseStart_5471778 : Nat := 118140960795 + 5471778 * 2 ^ 59
def prefixEnd_5471778 : Nat := 4983230072969 + 3 ^ 40 * 5471778 * 2
def baseEnd_5471778 : Nat := 936550716232465959036919

theorem tailTrace_5471778 : CollatzResearch.WordTrace tailWord_5471778 prefixEnd_5471778 936550716232465959036919 := by
  unfold tailWord_5471778
  simp only [CollatzResearch.WordTrace]
  refine ⟨49893034792672571531935997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133048092780460190751829325 49893034792672571531935997)
  ·
    refine ⟨18709888047252214324475999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49893034792672571531935997 18709888047252214324475999)
    ·
      refine ⟨28064832070878321486713999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18709888047252214324475999 28064832070878321486713999)
      ·
        refine ⟨42097248106317482230070999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28064832070878321486713999 42097248106317482230070999)
        ·
          refine ⟨63145872159476223345106499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42097248106317482230070999 63145872159476223345106499)
          ·
            refine ⟨94718808239214335017659749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63145872159476223345106499 94718808239214335017659749)
            ·
              refine ⟨17759776544852687815811203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94718808239214335017659749 17759776544852687815811203)
              ·
                refine ⟨26639664817279031723716805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17759776544852687815811203 26639664817279031723716805)
                ·
                  refine ⟨4994937153239818448196901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26639664817279031723716805 4994937153239818448196901)
                  ·
                    refine ⟨936550716232465959036919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4994937153239818448196901 936550716232465959036919)
                    ·
                      rfl

theorem cell23_5471778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_5471778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471778 prefixEnd_5471778 := by exact prefixLift 5471778
  have htrace : WordTrace (prefixWord ++ tailWord_5471778) baseStart_5471778 baseEnd_5471778 := by
    simpa [prefixWord, tailWord_5471778, baseEnd_5471778] using wordTrace_append hprefix tailTrace_5471778
  have hstable : (prefixWord ++ tailWord_5471778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471778).length < 2 ^ (prefixWord ++ tailWord_5471778).sum := by decide
  have hdescent : baseEnd_5471778 < baseStart_5471778 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471779 : List Nat := [1, 1, 1, 4, 5, 1, 3, 2, 1, 1, 3]
def baseStart_5471779 : Nat := 118140960795 + 5471779 * 2 ^ 59
def prefixEnd_5471779 : Nat := 4983230072969 + 3 ^ 40 * 5471779 * 2
def baseEnd_5471779 : Nat := 2809652662178052373198253

theorem tailTrace_5471779 : CollatzResearch.WordTrace tailWord_5471779 prefixEnd_5471779 2809652662178052373198253 := by
  unfold tailWord_5471779
  simp only [CollatzResearch.WordTrace]
  refine ⟨199572175643686663298530391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133048117095791108865686927 199572175643686663298530391)
  ·
    refine ⟨299358263465529994947795587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199572175643686663298530391 299358263465529994947795587)
    ·
      refine ⟨449037395198294992421693381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299358263465529994947795587 449037395198294992421693381)
      ·
        refine ⟨84194511599680311079067509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 449037395198294992421693381 84194511599680311079067509)
        ·
          refine ⟨7893235462470029163662579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 84194511599680311079067509 7893235462470029163662579)
          ·
            refine ⟨11839853193705043745493869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7893235462470029163662579 11839853193705043745493869)
            ·
              refine ⟨4439944947639391404560201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11839853193705043745493869 4439944947639391404560201)
              ·
                refine ⟨3329958710729543553420151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4439944947639391404560201 3329958710729543553420151)
                ·
                  refine ⟨4994938066094315330130227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3329958710729543553420151 4994938066094315330130227)
                  ·
                    refine ⟨7492407099141472995195341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4994938066094315330130227 7492407099141472995195341)
                    ·
                      refine ⟨2809652662178052373198253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7492407099141472995195341 2809652662178052373198253)
                      ·
                        rfl

theorem cell23_5471779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 2, 1, 1, 3].length) (baseStart_5471779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471779 prefixEnd_5471779 := by exact prefixLift 5471779
  have htrace : WordTrace (prefixWord ++ tailWord_5471779) baseStart_5471779 baseEnd_5471779 := by
    simpa [prefixWord, tailWord_5471779, baseEnd_5471779] using wordTrace_append hprefix tailTrace_5471779
  have hstable : (prefixWord ++ tailWord_5471779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471779).length < 2 ^ (prefixWord ++ tailWord_5471779).sum := by decide
  have hdescent : baseEnd_5471779 < baseStart_5471779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471795 : List Nat := [1, 1, 1, 2, 4, 3, 4, 1, 2, 4]
def baseStart_5471795 : Nat := 118140960795 + 5471795 * 2 ^ 59
def prefixEnd_5471795 : Nat := 4983230072969 + 3 ^ 40 * 5471795 * 2
def baseEnd_5471795 : Nat := 936553625956174770199393

theorem tailTrace_5471795 : CollatzResearch.WordTrace tailWord_5471795 prefixEnd_5471795 936553625956174770199393 := by
  unfold tailWord_5471795
  simp only [CollatzResearch.WordTrace]
  refine ⟨199572759211628698031112839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133048506141085798687408559 199572759211628698031112839)
  ·
    refine ⟨299359138817443047046669259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199572759211628698031112839 299359138817443047046669259)
    ·
      refine ⟨449038708226164570570003889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299359138817443047046669259 449038708226164570570003889)
      ·
        refine ⟨336779031169623427927502917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 449038708226164570570003889 336779031169623427927502917)
        ·
          refine ⟨63146068344304392736406797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 336779031169623427927502917 63146068344304392736406797)
          ·
            refine ⟨23679775629114147276152549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63146068344304392736406797 23679775629114147276152549)
            ·
              refine ⟨4439957930458902614278603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23679775629114147276152549 4439957930458902614278603)
              ·
                refine ⟨6659936895688353921417905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4439957930458902614278603 6659936895688353921417905)
                ·
                  refine ⟨4994952671766265441063429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6659936895688353921417905 4994952671766265441063429)
                  ·
                    refine ⟨936553625956174770199393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4994952671766265441063429 936553625956174770199393)
                    ·
                      rfl

theorem cell23_5471795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 1, 2, 4].length) (baseStart_5471795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471795 prefixEnd_5471795 := by exact prefixLift 5471795
  have htrace : WordTrace (prefixWord ++ tailWord_5471795) baseStart_5471795 baseEnd_5471795 := by
    simpa [prefixWord, tailWord_5471795, baseEnd_5471795] using wordTrace_append hprefix tailTrace_5471795
  have hstable : (prefixWord ++ tailWord_5471795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471795).length < 2 ^ (prefixWord ++ tailWord_5471795).sum := by decide
  have hdescent : baseEnd_5471795 < baseStart_5471795 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471805 : List Nat := [1, 4, 1, 3, 3, 1, 1, 1, 3, 2, 3]
def baseStart_5471805 : Nat := 118140960795 + 5471805 * 2 ^ 59
def prefixEnd_5471805 : Nat := 4983230072969 + 3 ^ 40 * 5471805 * 2
def baseEnd_5471805 : Nat := 2809666012675069271473133

theorem tailTrace_5471805 : CollatzResearch.WordTrace tailWord_5471805 prefixEnd_5471805 2809666012675069271473133 := by
  unfold tailWord_5471805
  simp only [CollatzResearch.WordTrace]
  refine ⟨199573123941592469738976869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133048749294394979825984579 199573123941592469738976869)
  ·
    refine ⟨37419960739048588076058163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 199573123941592469738976869 37419960739048588076058163)
    ·
      refine ⟨56129941108572882114087245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37419960739048588076058163 56129941108572882114087245)
      ·
        refine ⟨21048727915714830792782717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56129941108572882114087245 21048727915714830792782717)
        ·
          refine ⟨7893272968393061547293519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21048727915714830792782717 7893272968393061547293519)
          ·
            refine ⟨11839909452589592320940279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7893272968393061547293519 11839909452589592320940279)
            ·
              refine ⟨17759864178884388481410419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11839909452589592320940279 17759864178884388481410419)
              ·
                refine ⟨26639796268326582722115629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17759864178884388481410419 26639796268326582722115629)
                ·
                  refine ⟨9989923600622468520793361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26639796268326582722115629 9989923600622468520793361)
                  ·
                    refine ⟨7492442700466851390595021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9989923600622468520793361 7492442700466851390595021)
                    ·
                      refine ⟨2809666012675069271473133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7492442700466851390595021 2809666012675069271473133)
                      ·
                        rfl

theorem cell23_5471805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_5471805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471805 prefixEnd_5471805 := by exact prefixLift 5471805
  have htrace : WordTrace (prefixWord ++ tailWord_5471805) baseStart_5471805 baseEnd_5471805 := by
    simpa [prefixWord, tailWord_5471805, baseEnd_5471805] using wordTrace_append hprefix tailTrace_5471805
  have hstable : (prefixWord ++ tailWord_5471805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471805).length < 2 ^ (prefixWord ++ tailWord_5471805).sum := by decide
  have hdescent : baseEnd_5471805 < baseStart_5471805 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471818 : List Nat := [3, 1, 2, 1, 1, 3, 3, 2, 1, 3, 3]
def baseStart_5471818 : Nat := 118140960795 + 5471818 * 2 ^ 59
def prefixEnd_5471818 : Nat := 4983230072969 + 3 ^ 40 * 5471818 * 2
def baseEnd_5471818 : Nat := 2809672687923577720610573

theorem tailTrace_5471818 : CollatzResearch.WordTrace tailWord_5471818 prefixEnd_5471818 2809672687923577720610573 := by
  unfold tailWord_5471818
  simp only [CollatzResearch.WordTrace]
  refine ⟨49893399522636343239800027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133049065393696915306133405 49893399522636343239800027)
  ·
    refine ⟨74840099283954514859700041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49893399522636343239800027 74840099283954514859700041)
    ·
      refine ⟨56130074462965886144775031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74840099283954514859700041 56130074462965886144775031)
      ·
        refine ⟨84195111694448829217162547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56130074462965886144775031 84195111694448829217162547)
        ·
          refine ⟨126292667541673243825743821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84195111694448829217162547 126292667541673243825743821)
          ·
            refine ⟨47359750328127466434653933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126292667541673243825743821 47359750328127466434653933)
            ·
              refine ⟨17759906373047799912995225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47359750328127466434653933 17759906373047799912995225)
              ·
                refine ⟨13319929779785849934746419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17759906373047799912995225 13319929779785849934746419)
                ·
                  refine ⟨19979894669678774902119629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13319929779785849934746419 19979894669678774902119629)
                  ·
                    refine ⟨7492460501129540588294861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19979894669678774902119629 7492460501129540588294861)
                    ·
                      refine ⟨2809672687923577720610573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7492460501129540588294861 2809672687923577720610573)
                      ·
                        rfl

theorem cell23_5471818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 1, 3, 3].length) (baseStart_5471818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471818 prefixEnd_5471818 := by exact prefixLift 5471818
  have htrace : WordTrace (prefixWord ++ tailWord_5471818) baseStart_5471818 baseEnd_5471818 := by
    simpa [prefixWord, tailWord_5471818, baseEnd_5471818] using wordTrace_append hprefix tailTrace_5471818
  have hstable : (prefixWord ++ tailWord_5471818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471818).length < 2 ^ (prefixWord ++ tailWord_5471818).sum := by decide
  have hdescent : baseEnd_5471818 < baseStart_5471818 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471830 : List Nat := [5, 2, 2, 2, 1, 2, 2, 2, 1, 1, 3]
def baseStart_5471830 : Nat := 118140960795 + 5471830 * 2 ^ 59
def prefixEnd_5471830 : Nat := 4983230072969 + 3 ^ 40 * 5471830 * 2
def baseEnd_5471830 : Nat := 2809678849691431673660519

theorem tailTrace_5471830 : CollatzResearch.WordTrace tailWord_5471830 prefixEnd_5471830 2809678849691431673660519 := by
  unfold tailWord_5471830
  simp only [CollatzResearch.WordTrace]
  refine ⟨12473377235406368688039809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 133049357177667932672424629 12473377235406368688039809)
  ·
    refine ⟨9355032926554776516029857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12473377235406368688039809 9355032926554776516029857)
    ·
      refine ⟨7016274694916082387022393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9355032926554776516029857 7016274694916082387022393)
      ·
        refine ⟨5262206021187061790266795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7016274694916082387022393 5262206021187061790266795)
        ·
          refine ⟨7893309031780592685400193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5262206021187061790266795 7893309031780592685400193)
          ·
            refine ⟨5919981773835444514050145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7893309031780592685400193 5919981773835444514050145)
            ·
              refine ⟨4439986330376583385537609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5919981773835444514050145 4439986330376583385537609)
              ·
                refine ⟨3329989747782437539153207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4439986330376583385537609 3329989747782437539153207)
                ·
                  refine ⟨4994984621673656308729811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3329989747782437539153207 4994984621673656308729811)
                  ·
                    refine ⟨7492476932510484463094717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4994984621673656308729811 7492476932510484463094717)
                    ·
                      refine ⟨2809678849691431673660519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7492476932510484463094717 2809678849691431673660519)
                      ·
                        rfl

theorem cell23_5471830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_5471830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471830 prefixEnd_5471830 := by exact prefixLift 5471830
  have htrace : WordTrace (prefixWord ++ tailWord_5471830) baseStart_5471830 baseEnd_5471830 := by
    simpa [prefixWord, tailWord_5471830, baseEnd_5471830] using wordTrace_append hprefix tailTrace_5471830
  have hstable : (prefixWord ++ tailWord_5471830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471830).length < 2 ^ (prefixWord ++ tailWord_5471830).sum := by decide
  have hdescent : baseEnd_5471830 < baseStart_5471830 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471836 : List Nat := [2, 2, 4, 1, 2, 1, 4, 2, 1, 2, 2]
def baseStart_5471836 : Nat := 118140960795 + 5471836 * 2 ^ 59
def prefixEnd_5471836 : Nat := 4983230072969 + 3 ^ 40 * 5471836 * 2
def baseEnd_5471836 : Nat := 2809681930575358650185491

theorem tailTrace_5471836 : CollatzResearch.WordTrace tailWord_5471836 prefixEnd_5471836 2809681930575358650185491 := by
  unfold tailWord_5471836
  simp only [CollatzResearch.WordTrace]
  refine ⟨99787127302240081016677681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133049503069653441355570241 99787127302240081016677681)
  ·
    refine ⟨74840345476680060762508261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99787127302240081016677681 74840345476680060762508261)
    ·
      refine ⟨14032564776877511392970299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74840345476680060762508261 14032564776877511392970299)
      ·
        refine ⟨21048847165316267089455449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14032564776877511392970299 21048847165316267089455449)
        ·
          refine ⟨15786635373987200317091587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21048847165316267089455449 15786635373987200317091587)
          ·
            refine ⟨23679953060980800475637381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15786635373987200317091587 23679953060980800475637381)
            ·
              refine ⟨4439991198933900089182009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23679953060980800475637381 4439991198933900089182009)
              ·
                refine ⟨3329993399200425066886507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4439991198933900089182009 3329993399200425066886507)
                ·
                  refine ⟨4994990098800637600329761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3329993399200425066886507 4994990098800637600329761)
                  ·
                    refine ⟨3746242574100478200247321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4994990098800637600329761 3746242574100478200247321)
                    ·
                      refine ⟨2809681930575358650185491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3746242574100478200247321 2809681930575358650185491)
                      ·
                        rfl

theorem cell23_5471836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_5471836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471836 prefixEnd_5471836 := by exact prefixLift 5471836
  have htrace : WordTrace (prefixWord ++ tailWord_5471836) baseStart_5471836 baseEnd_5471836 := by
    simpa [prefixWord, tailWord_5471836, baseEnd_5471836] using wordTrace_append hprefix tailTrace_5471836
  have hstable : (prefixWord ++ tailWord_5471836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471836).length < 2 ^ (prefixWord ++ tailWord_5471836).sum := by decide
  have hdescent : baseEnd_5471836 < baseStart_5471836 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471841 : List Nat := [1, 2, 3, 1, 1, 3, 1, 1, 1, 5, 4]
def baseStart_5471841 : Nat := 118140960795 + 5471841 * 2 ^ 59
def prefixEnd_5471841 : Nat := 4983230072969 + 3 ^ 40 * 5471841 * 2
def baseEnd_5471841 : Nat := 2809684497978631130622967

theorem tailTrace_5471841 : CollatzResearch.WordTrace tailWord_5471841 prefixEnd_5471841 2809684497978631130622967 := by
  unfold tailWord_5471841
  simp only [CollatzResearch.WordTrace]
  refine ⟨199574436969462047887287377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133049624646308031924858251 199574436969462047887287377)
  ·
    refine ⟨149680827727096535915465533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199574436969462047887287377 149680827727096535915465533)
    ·
      refine ⟨56130310397661200968299575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149680827727096535915465533 56130310397661200968299575)
      ·
        refine ⟨84195465596491801452449363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56130310397661200968299575 84195465596491801452449363)
        ·
          refine ⟨126293198394737702178674045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84195465596491801452449363 126293198394737702178674045)
          ·
            refine ⟨47359949398026638317002767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126293198394737702178674045 47359949398026638317002767)
            ·
              refine ⟨71039924097039957475504151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47359949398026638317002767 71039924097039957475504151)
              ·
                refine ⟨106559886145559936213256227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71039924097039957475504151 106559886145559936213256227)
                ·
                  refine ⟨159839829218339904319884341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106559886145559936213256227 159839829218339904319884341)
                  ·
                    refine ⟨14984983989219366029989157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 159839829218339904319884341 14984983989219366029989157)
                    ·
                      refine ⟨2809684497978631130622967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14984983989219366029989157 2809684497978631130622967)
                      ·
                        rfl

theorem cell23_5471841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_5471841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471841 prefixEnd_5471841 := by exact prefixLift 5471841
  have htrace : WordTrace (prefixWord ++ tailWord_5471841) baseStart_5471841 baseEnd_5471841 := by
    simpa [prefixWord, tailWord_5471841, baseEnd_5471841] using wordTrace_append hprefix tailTrace_5471841
  have hstable : (prefixWord ++ tailWord_5471841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471841).length < 2 ^ (prefixWord ++ tailWord_5471841).sum := by decide
  have hdescent : baseEnd_5471841 < baseStart_5471841 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471845 : List Nat := [1, 3, 1, 3, 3, 1, 1, 2, 3, 3, 2]
def baseStart_5471845 : Nat := 118140960795 + 5471845 * 2 ^ 59
def prefixEnd_5471845 : Nat := 4983230072969 + 3 ^ 40 * 5471845 * 2
def baseEnd_5471845 : Nat := 2809686551901249114972949

theorem tailTrace_5471845 : CollatzResearch.WordTrace tailWord_5471845 prefixEnd_5471845 2809686551901249114972949 := by
  unfold tailWord_5471845
  simp only [CollatzResearch.WordTrace]
  refine ⟨199574582861447556570432989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133049721907631704380288659 199574582861447556570432989)
  ·
    refine ⟨74840468573042833713912371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199574582861447556570432989 74840468573042833713912371)
    ·
      refine ⟨112260702859564250570868557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74840468573042833713912371 112260702859564250570868557)
      ·
        refine ⟨42097763572336593964075709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112260702859564250570868557 42097763572336593964075709)
        ·
          refine ⟨15786661339626222736528391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42097763572336593964075709 15786661339626222736528391)
          ·
            refine ⟨23679992009439334104792587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15786661339626222736528391 23679992009439334104792587)
            ·
              refine ⟨35519988014159001157188881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23679992009439334104792587 35519988014159001157188881)
              ·
                refine ⟨26639991010619250867891661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35519988014159001157188881 26639991010619250867891661)
                ·
                  refine ⟨9989996628982219075459373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26639991010619250867891661 9989996628982219075459373)
                  ·
                    refine ⟨3746248735868332153297265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9989996628982219075459373 3746248735868332153297265)
                    ·
                      refine ⟨2809686551901249114972949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3746248735868332153297265 2809686551901249114972949)
                      ·
                        rfl

theorem cell23_5471845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 3, 3, 2].length) (baseStart_5471845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471845 prefixEnd_5471845 := by exact prefixLift 5471845
  have htrace : WordTrace (prefixWord ++ tailWord_5471845) baseStart_5471845 baseEnd_5471845 := by
    simpa [prefixWord, tailWord_5471845, baseEnd_5471845] using wordTrace_append hprefix tailTrace_5471845
  have hstable : (prefixWord ++ tailWord_5471845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471845).length < 2 ^ (prefixWord ++ tailWord_5471845).sum := by decide
  have hdescent : baseEnd_5471845 < baseStart_5471845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471862 : List Nat := [5, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2]
def baseStart_5471862 : Nat := 118140960795 + 5471862 * 2 ^ 59
def prefixEnd_5471862 : Nat := 4983230072969 + 3 ^ 40 * 5471862 * 2
def baseEnd_5471862 : Nat := 2809695281072375548460371

theorem tailTrace_5471862 : CollatzResearch.WordTrace tailWord_5471862 prefixEnd_5471862 2809695281072375548460371 := by
  unfold tailWord_5471862
  simp only [CollatzResearch.WordTrace]
  refine ⟨12473450181399123029612615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 133050135268257312315867893 12473450181399123029612615)
  ·
    refine ⟨18710175272098684544418923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12473450181399123029612615 18710175272098684544418923)
    ·
      refine ⟨28065262908148026816628385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18710175272098684544418923 28065262908148026816628385)
      ·
        refine ⟨21048947181111020112471289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28065262908148026816628385 21048947181111020112471289)
        ·
          refine ⟨15786710385833265084353467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21048947181111020112471289 15786710385833265084353467)
          ·
            refine ⟨23680065578749897626530201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15786710385833265084353467 23680065578749897626530201)
            ·
              refine ⟨17760049184062423219897651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23680065578749897626530201 17760049184062423219897651)
              ·
                refine ⟨26640073776093634829846477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17760049184062423219897651 26640073776093634829846477)
                ·
                  refine ⟨9990027666035113061192429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26640073776093634829846477 9990027666035113061192429)
                  ·
                    refine ⟨3746260374763167397947161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9990027666035113061192429 3746260374763167397947161)
                    ·
                      refine ⟨2809695281072375548460371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3746260374763167397947161 2809695281072375548460371)
                      ·
                        rfl

theorem cell23_5471862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_5471862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471862 prefixEnd_5471862 := by exact prefixLift 5471862
  have htrace : WordTrace (prefixWord ++ tailWord_5471862) baseStart_5471862 baseEnd_5471862 := by
    simpa [prefixWord, tailWord_5471862, baseEnd_5471862] using wordTrace_append hprefix tailTrace_5471862
  have hstable : (prefixWord ++ tailWord_5471862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471862).length < 2 ^ (prefixWord ++ tailWord_5471862).sum := by decide
  have hdescent : baseEnd_5471862 < baseStart_5471862 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471875 : List Nat := [1, 1, 1, 3, 3, 1, 1, 4, 4, 2, 2]
def baseStart_5471875 : Nat := 118140960795 + 5471875 * 2 ^ 59
def prefixEnd_5471875 : Nat := 4983230072969 + 3 ^ 40 * 5471875 * 2
def baseEnd_5471875 : Nat := 2809701956320883997597811

theorem tailTrace_5471875 : CollatzResearch.WordTrace tailWord_5471875 prefixEnd_5471875 2809701956320883997597811 := by
  unfold tailWord_5471875
  simp only [CollatzResearch.WordTrace]
  refine ⟨199575677051338871694025079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133050451367559247796016719 199575677051338871694025079)
  ·
    refine ⟨299363515577008307541037619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199575677051338871694025079 299363515577008307541037619)
    ·
      refine ⟨449045273365512461311556429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299363515577008307541037619 449045273365512461311556429)
      ·
        refine ⟨168391977512067172991833661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 449045273365512461311556429 168391977512067172991833661)
        ·
          refine ⟨63146991567025189871937623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168391977512067172991833661 63146991567025189871937623)
          ·
            refine ⟨94720487350537784807906435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63146991567025189871937623 94720487350537784807906435)
            ·
              refine ⟨142080731025806677211859653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94720487350537784807906435 142080731025806677211859653)
              ·
                refine ⟨26640137067338751977223685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 142080731025806677211859653 26640137067338751977223685)
                ·
                  refine ⟨4995025700126015995729441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26640137067338751977223685 4995025700126015995729441)
                  ·
                    refine ⟨3746269275094511996797081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4995025700126015995729441 3746269275094511996797081)
                    ·
                      refine ⟨2809701956320883997597811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3746269275094511996797081 2809701956320883997597811)
                      ·
                        rfl

theorem cell23_5471875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 4, 2, 2].length) (baseStart_5471875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471875 prefixEnd_5471875 := by exact prefixLift 5471875
  have htrace : WordTrace (prefixWord ++ tailWord_5471875) baseStart_5471875 baseEnd_5471875 := by
    simpa [prefixWord, tailWord_5471875, baseEnd_5471875] using wordTrace_append hprefix tailTrace_5471875
  have hstable : (prefixWord ++ tailWord_5471875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471875).length < 2 ^ (prefixWord ++ tailWord_5471875).sum := by decide
  have hdescent : baseEnd_5471875 < baseStart_5471875 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471879 : List Nat := [1, 1, 4, 2, 1, 5, 2, 1, 1, 3, 2]
def baseStart_5471879 : Nat := 118140960795 + 5471879 * 2 ^ 59
def prefixEnd_5471879 : Nat := 4983230072969 + 3 ^ 40 * 5471879 * 2
def baseEnd_5471879 : Nat := 2809704010243501981947793

theorem tailTrace_5471879 : CollatzResearch.WordTrace tailWord_5471879 prefixEnd_5471879 2809704010243501981947793 := by
  unfold tailWord_5471879
  simp only [CollatzResearch.WordTrace]
  refine ⟨199575822943324380377170691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133050548628882920251447127 199575822943324380377170691)
  ·
    refine ⟨299363734414986570565756037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199575822943324380377170691 299363734414986570565756037)
    ·
      refine ⟨56130700202809981981079257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 299363734414986570565756037 56130700202809981981079257)
      ·
        refine ⟨42098025152107486485809443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56130700202809981981079257 42098025152107486485809443)
        ·
          refine ⟨63147037728161229728714165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42098025152107486485809443 63147037728161229728714165)
          ·
            refine ⟨5920034787015115287066953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63147037728161229728714165 5920034787015115287066953)
            ·
              refine ⟨4440026090261336465300215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5920034787015115287066953 4440026090261336465300215)
              ·
                refine ⟨6660039135392004697950323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4440026090261336465300215 6660039135392004697950323)
                ·
                  refine ⟨9990058703088007046925485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6660039135392004697950323 9990058703088007046925485)
                  ·
                    refine ⟨3746272013658002642597057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9990058703088007046925485 3746272013658002642597057)
                    ·
                      refine ⟨2809704010243501981947793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3746272013658002642597057 2809704010243501981947793)
                      ·
                        rfl

theorem cell23_5471879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 1, 1, 3, 2].length) (baseStart_5471879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471879 prefixEnd_5471879 := by exact prefixLift 5471879
  have htrace : WordTrace (prefixWord ++ tailWord_5471879) baseStart_5471879 baseEnd_5471879 := by
    simpa [prefixWord, tailWord_5471879, baseEnd_5471879] using wordTrace_append hprefix tailTrace_5471879
  have hstable : (prefixWord ++ tailWord_5471879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471879).length < 2 ^ (prefixWord ++ tailWord_5471879).sum := by decide
  have hdescent : baseEnd_5471879 < baseStart_5471879 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471932 : List Nat := [2, 2, 2, 3, 1, 4, 1, 3, 5]
def baseStart_5471932 : Nat := 118140960795 + 5471932 * 2 ^ 59
def prefixEnd_5471932 : Nat := 4983230072969 + 3 ^ 40 * 5471932 * 2
def baseEnd_5471932 : Nat := 312192358302021141620561

theorem tailTrace_5471932 : CollatzResearch.WordTrace tailWord_5471932 prefixEnd_5471932 312192358302021141620561 := by
  unfold tailWord_5471932
  simp only [CollatzResearch.WordTrace]
  refine ⟨99788878006066185214425025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133051837341421580285900033 99788878006066185214425025)
  ·
    refine ⟨74841658504549638910818769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99788878006066185214425025 74841658504549638910818769)
    ·
      refine ⟨56131243878412229183114077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74841658504549638910818769 56131243878412229183114077)
      ·
        refine ⟨21049216454404585943667779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56131243878412229183114077 21049216454404585943667779)
        ·
          refine ⟨31573824681606878915501669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21049216454404585943667779 31573824681606878915501669)
          ·
            refine ⟨5920092127801289796656563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31573824681606878915501669 5920092127801289796656563)
            ·
              refine ⟨8880138191701934694984845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5920092127801289796656563 8880138191701934694984845)
              ·
                refine ⟨3330051821888225510619317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8880138191701934694984845 3330051821888225510619317)
                ·
                  refine ⟨312192358302021141620561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3330051821888225510619317 312192358302021141620561)
                  ·
                    rfl

theorem cell23_5471932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 3, 5].length) (baseStart_5471932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471932 prefixEnd_5471932 := by exact prefixLift 5471932
  have htrace : WordTrace (prefixWord ++ tailWord_5471932) baseStart_5471932 baseEnd_5471932 := by
    simpa [prefixWord, tailWord_5471932, baseEnd_5471932] using wordTrace_append hprefix tailTrace_5471932
  have hstable : (prefixWord ++ tailWord_5471932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471932).length < 2 ^ (prefixWord ++ tailWord_5471932).sum := by decide
  have hdescent : baseEnd_5471932 < baseStart_5471932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471941 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 1, 10]
def baseStart_5471941 : Nat := 118140960795 + 5471941 * 2 ^ 59
def prefixEnd_5471941 : Nat := 4983230072969 + 3 ^ 40 * 5471941 * 2
def baseEnd_5471941 : Nat := 936578615348026913124169

theorem tailTrace_5471941 : CollatzResearch.WordTrace tailWord_5471941 prefixEnd_5471941 936578615348026913124169 := by
  unfold tailWord_5471941
  simp only [CollatzResearch.WordTrace]
  refine ⟨199578084269099764965927677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133052056179399843310618451 199578084269099764965927677)
  ·
    refine ⟨74841781600912411862222879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199578084269099764965927677 74841781600912411862222879)
    ·
      refine ⟨112262672401368617793334319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74841781600912411862222879 112262672401368617793334319)
      ·
        refine ⟨168394008602052926690001479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112262672401368617793334319 168394008602052926690001479)
        ·
          refine ⟨252591012903079390035002219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168394008602052926690001479 252591012903079390035002219)
          ·
            refine ⟨378886519354619085052503329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252591012903079390035002219 378886519354619085052503329)
            ·
              refine ⟨284164889515964313789377497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 378886519354619085052503329 284164889515964313789377497)
              ·
                refine ⟨213123667136973235342033123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 284164889515964313789377497 213123667136973235342033123)
                ·
                  refine ⟨319685500705459853013049685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 213123667136973235342033123 319685500705459853013049685)
                  ·
                    refine ⟨936578615348026913124169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 319685500705459853013049685 936578615348026913124169)
                    ·
                      rfl

theorem cell23_5471941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 10].length) (baseStart_5471941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471941 prefixEnd_5471941 := by exact prefixLift 5471941
  have htrace : WordTrace (prefixWord ++ tailWord_5471941) baseStart_5471941 baseEnd_5471941 := by
    simpa [prefixWord, tailWord_5471941, baseEnd_5471941] using wordTrace_append hprefix tailTrace_5471941
  have hstable : (prefixWord ++ tailWord_5471941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471941).length < 2 ^ (prefixWord ++ tailWord_5471941).sum := by decide
  have hdescent : baseEnd_5471941 < baseStart_5471941 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471968 : List Nat := [2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 3]
def baseStart_5471968 : Nat := 118140960795 + 5471968 * 2 ^ 59
def prefixEnd_5471968 : Nat := 4983230072969 + 3 ^ 40 * 5471968 * 2
def baseEnd_5471968 : Nat := 2809749710021752133734883

theorem tailTrace_5471968 : CollatzResearch.WordTrace tailWord_5471968 prefixEnd_5471968 2809749710021752133734883 := by
  unfold tailWord_5471968
  simp only [CollatzResearch.WordTrace]
  refine ⟨99789534520000974288580279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133052712693334632384773705 99789534520000974288580279)
  ·
    refine ⟨149684301780001461432870419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99789534520000974288580279 149684301780001461432870419)
    ·
      refine ⟨224526452670002192149305629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149684301780001461432870419 224526452670002192149305629)
      ·
        refine ⟨84197419751250822055989611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 224526452670002192149305629 84197419751250822055989611)
        ·
          refine ⟨126296129626876233083984417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84197419751250822055989611 126296129626876233083984417)
          ·
            refine ⟨94722097220157174812988313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126296129626876233083984417 94722097220157174812988313)
            ·
              refine ⟨71041572915117881109741235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94722097220157174812988313 71041572915117881109741235)
              ·
                refine ⟨106562359372676821664611853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71041572915117881109741235 106562359372676821664611853)
                ·
                  refine ⟨39960884764753808124229445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106562359372676821664611853 39960884764753808124229445)
                  ·
                    refine ⟨7492665893391339023293021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39960884764753808124229445 7492665893391339023293021)
                    ·
                      refine ⟨2809749710021752133734883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7492665893391339023293021 2809749710021752133734883)
                      ·
                        rfl

theorem cell23_5471968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 3].length) (baseStart_5471968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471968 prefixEnd_5471968 := by exact prefixLift 5471968
  have htrace : WordTrace (prefixWord ++ tailWord_5471968) baseStart_5471968 baseEnd_5471968 := by
    simpa [prefixWord, tailWord_5471968, baseEnd_5471968] using wordTrace_append hprefix tailTrace_5471968
  have hstable : (prefixWord ++ tailWord_5471968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471968).length < 2 ^ (prefixWord ++ tailWord_5471968).sum := by decide
  have hdescent : baseEnd_5471968 < baseStart_5471968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471978 : List Nat := [3, 1, 3, 1, 1, 1, 2, 1, 2, 4, 4]
def baseStart_5471978 : Nat := 118140960795 + 5471978 * 2 ^ 59
def prefixEnd_5471978 : Nat := 4983230072969 + 3 ^ 40 * 5471978 * 2
def baseEnd_5471978 : Nat := 2809754844828297094609837

theorem tailTrace_5471978 : CollatzResearch.WordTrace tailWord_5471978 prefixEnd_5471978 2809754844828297094609837 := by
  unfold tailWord_5471978
  simp only [CollatzResearch.WordTrace]
  refine ⟨49894858442491430071256147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133052955846643813523349725 49894858442491430071256147)
  ·
    refine ⟨74842287663737145106884221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49894858442491430071256147 74842287663737145106884221)
    ·
      refine ⟨28065857873901429415081583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74842287663737145106884221 28065857873901429415081583)
      ·
        refine ⟨42098786810852144122622375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28065857873901429415081583 42098786810852144122622375)
        ·
          refine ⟨63148180216278216183933563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42098786810852144122622375 63148180216278216183933563)
          ·
            refine ⟨94722270324417324275900345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63148180216278216183933563 94722270324417324275900345)
            ·
              refine ⟨71041702743312993206925259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94722270324417324275900345 71041702743312993206925259)
              ·
                refine ⟨106562554114969489810387889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71041702743312993206925259 106562554114969489810387889)
                ·
                  refine ⟨79921915586227117357790917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106562554114969489810387889 79921915586227117357790917)
                  ·
                    refine ⟨14985359172417584504585797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 79921915586227117357790917 14985359172417584504585797)
                    ·
                      refine ⟨2809754844828297094609837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14985359172417584504585797 2809754844828297094609837)
                      ·
                        rfl

theorem cell23_5471978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_5471978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471978 prefixEnd_5471978 := by exact prefixLift 5471978
  have htrace : WordTrace (prefixWord ++ tailWord_5471978) baseStart_5471978 baseEnd_5471978 := by
    simpa [prefixWord, tailWord_5471978, baseEnd_5471978] using wordTrace_append hprefix tailTrace_5471978
  have hstable : (prefixWord ++ tailWord_5471978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471978).length < 2 ^ (prefixWord ++ tailWord_5471978).sum := by decide
  have hdescent : baseEnd_5471978 < baseStart_5471978 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5471985 : List Nat := [1, 2, 2, 2, 2, 3, 1, 3, 2, 2, 3]
def baseStart_5471985 : Nat := 118140960795 + 5471985 * 2 ^ 59
def prefixEnd_5471985 : Nat := 4983230072969 + 3 ^ 40 * 5471985 * 2
def baseEnd_5471985 : Nat := 2809758439192878567222305

theorem tailTrace_5471985 : CollatzResearch.WordTrace tailWord_5471985 prefixEnd_5471985 2809758439192878567222305 := by
  unfold tailWord_5471985
  simp only [CollatzResearch.WordTrace]
  refine ⟨199579689080940360480529409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133053126053960240320352939 199579689080940360480529409)
  ·
    refine ⟨149684766810705270360397057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199579689080940360480529409 149684766810705270360397057)
    ·
      refine ⟨112263575108028952770297793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149684766810705270360397057 112263575108028952770297793)
      ·
        refine ⟨84197681331021714577723345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112263575108028952770297793 84197681331021714577723345)
        ·
          refine ⟨63148260998266285933292509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84197681331021714577723345 63148260998266285933292509)
          ·
            refine ⟨23680597874349857224984691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63148260998266285933292509 23680597874349857224984691)
            ·
              refine ⟨35520896811524785837477037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23680597874349857224984691 35520896811524785837477037)
              ·
                refine ⟨13320336304321794689053889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35520896811524785837477037 13320336304321794689053889)
                ·
                  refine ⟨9990252228241346016790417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13320336304321794689053889 9990252228241346016790417)
                  ·
                    refine ⟨7492689171181009512592813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9990252228241346016790417 7492689171181009512592813)
                    ·
                      refine ⟨2809758439192878567222305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7492689171181009512592813 2809758439192878567222305)
                      ·
                        rfl

theorem cell23_5471985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 2, 2, 3].length) (baseStart_5471985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5471985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5471985 prefixEnd_5471985 := by exact prefixLift 5471985
  have htrace : WordTrace (prefixWord ++ tailWord_5471985) baseStart_5471985 baseEnd_5471985 := by
    simpa [prefixWord, tailWord_5471985, baseEnd_5471985] using wordTrace_append hprefix tailTrace_5471985
  have hstable : (prefixWord ++ tailWord_5471985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5471985).length < 2 ^ (prefixWord ++ tailWord_5471985).sum := by decide
  have hdescent : baseEnd_5471985 < baseStart_5471985 := by decide
  rcases family_descends (prefixWord ++ tailWord_5471985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5472002 : List Nat := [3, 4, 1, 1, 1, 1, 1, 4, 2, 2, 3]
def baseStart_5472002 : Nat := 118140960795 + 5472002 * 2 ^ 59
def prefixEnd_5472002 : Nat := 4983230072969 + 3 ^ 40 * 5472002 * 2
def baseEnd_5472002 : Nat := 2809767168364005000709727

theorem tailTrace_5472002 : CollatzResearch.WordTrace tailWord_5472002 prefixEnd_5472002 2809767168364005000709727 := by
  unfold tailWord_5472002
  simp only [CollatzResearch.WordTrace]
  refine ⟨49895077280469693095974565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133053539414585848255932173 49895077280469693095974565)
  ·
    refine ⟨9355326990088067455495231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49895077280469693095974565 9355326990088067455495231)
    ·
      refine ⟨14032990485132101183242847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9355326990088067455495231 14032990485132101183242847)
      ·
        refine ⟨21049485727698151774864271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14032990485132101183242847 21049485727698151774864271)
        ·
          refine ⟨31574228591547227662296407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21049485727698151774864271 31574228591547227662296407)
          ·
            refine ⟨47361342887320841493444611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31574228591547227662296407 47361342887320841493444611)
            ·
              refine ⟨71042014330981262240166917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47361342887320841493444611 71042014330981262240166917)
              ·
                refine ⟨13320377687058986670031297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71042014330981262240166917 13320377687058986670031297)
                ·
                  refine ⟨9990283265294240002523473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13320377687058986670031297 9990283265294240002523473)
                  ·
                    refine ⟨7492712448970680001892605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9990283265294240002523473 7492712448970680001892605)
                    ·
                      refine ⟨2809767168364005000709727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7492712448970680001892605 2809767168364005000709727)
                      ·
                        rfl

theorem cell23_5472002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_5472002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5472002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5472002 prefixEnd_5472002 := by exact prefixLift 5472002
  have htrace : WordTrace (prefixWord ++ tailWord_5472002) baseStart_5472002 baseEnd_5472002 := by
    simpa [prefixWord, tailWord_5472002, baseEnd_5472002] using wordTrace_append hprefix tailTrace_5472002
  have hstable : (prefixWord ++ tailWord_5472002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5472002).length < 2 ^ (prefixWord ++ tailWord_5472002).sum := by decide
  have hdescent : baseEnd_5472002 < baseStart_5472002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5472002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5472008 : List Nat := [2, 1, 3, 2, 2, 1, 2, 1, 1, 2, 6]
def baseStart_5472008 : Nat := 118140960795 + 5472008 * 2 ^ 59
def prefixEnd_5472008 : Nat := 4983230072969 + 3 ^ 40 * 5472008 * 2
def baseEnd_5472008 : Nat := 2809770249247931977234699

theorem tailTrace_5472008 : CollatzResearch.WordTrace tailWord_5472008 prefixEnd_5472008 2809770249247931977234699 := by
  unfold tailWord_5472008
  simp only [CollatzResearch.WordTrace]
  refine ⟨99790263979928517704308339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133053685306571356939077785 99790263979928517704308339)
  ·
    refine ⟨149685395969892776556462509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99790263979928517704308339 149685395969892776556462509)
    ·
      refine ⟨56132023488709791208673441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149685395969892776556462509 56132023488709791208673441)
      ·
        refine ⟨42099017616532343406505081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56132023488709791208673441 42099017616532343406505081)
        ·
          refine ⟨31574263212399257554878811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42099017616532343406505081 31574263212399257554878811)
          ·
            refine ⟨47361394818598886332318217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31574263212399257554878811 47361394818598886332318217)
            ·
              refine ⟨35521046113949164749238663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47361394818598886332318217 35521046113949164749238663)
              ·
                refine ⟨53281569170923747123857995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35521046113949164749238663 53281569170923747123857995)
                ·
                  refine ⟨79922353756385620685786993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53281569170923747123857995 79922353756385620685786993)
                  ·
                    refine ⟨59941765317289215514340245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 79922353756385620685786993 59941765317289215514340245)
                    ·
                      refine ⟨2809770249247931977234699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59941765317289215514340245 2809770249247931977234699)
                      ·
                        rfl

theorem cell23_5472008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_5472008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5472008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5472008 prefixEnd_5472008 := by exact prefixLift 5472008
  have htrace : WordTrace (prefixWord ++ tailWord_5472008) baseStart_5472008 baseEnd_5472008 := by
    simpa [prefixWord, tailWord_5472008, baseEnd_5472008] using wordTrace_append hprefix tailTrace_5472008
  have hstable : (prefixWord ++ tailWord_5472008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5472008).length < 2 ^ (prefixWord ++ tailWord_5472008).sum := by decide
  have hdescent : baseEnd_5472008 < baseStart_5472008 := by decide
  rcases family_descends (prefixWord ++ tailWord_5472008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5472028 : List Nat := [2, 2, 3, 1, 1, 2, 1, 1, 2, 1, 7]
def baseStart_5472028 : Nat := 118140960795 + 5472028 * 2 ^ 59
def prefixEnd_5472028 : Nat := 4983230072969 + 3 ^ 40 * 5472028 * 2
def baseEnd_5472028 : Nat := 2809780518861021898984607

theorem tailTrace_5472028 : CollatzResearch.WordTrace tailWord_5472028 prefixEnd_5472028 2809780518861021898984607 := by
  unfold tailWord_5472028
  simp only [CollatzResearch.WordTrace]
  refine ⟨99790628709892289412172369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133054171613189719216229825 99790628709892289412172369)
  ·
    refine ⟨74842971532419217059129277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99790628709892289412172369 74842971532419217059129277)
    ·
      refine ⟨28066114324657206397173479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74842971532419217059129277 28066114324657206397173479)
      ·
        refine ⟨42099171486985809595760219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28066114324657206397173479 42099171486985809595760219)
        ·
          refine ⟨63148757230478714393640329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42099171486985809595760219 63148757230478714393640329)
          ·
            refine ⟨47361567922859035795230247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63148757230478714393640329 47361567922859035795230247)
            ·
              refine ⟨71042351884288553692845371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47361567922859035795230247 71042351884288553692845371)
              ·
                refine ⟨106563527826432830539268057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71042351884288553692845371 106563527826432830539268057)
                ·
                  refine ⟨79922645869824622904451043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106563527826432830539268057 79922645869824622904451043)
                  ·
                    refine ⟨119883968804736934356676565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 79922645869824622904451043 119883968804736934356676565)
                    ·
                      refine ⟨2809780518861021898984607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 119883968804736934356676565 2809780518861021898984607)
                      ·
                        rfl

theorem cell23_5472028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_5472028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5472028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5472028 prefixEnd_5472028 := by exact prefixLift 5472028
  have htrace : WordTrace (prefixWord ++ tailWord_5472028) baseStart_5472028 baseEnd_5472028 := by
    simpa [prefixWord, tailWord_5472028, baseEnd_5472028] using wordTrace_append hprefix tailTrace_5472028
  have hstable : (prefixWord ++ tailWord_5472028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5472028).length < 2 ^ (prefixWord ++ tailWord_5472028).sum := by decide
  have hdescent : baseEnd_5472028 < baseStart_5472028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5472028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5472032 : List Nat := [2, 1, 1, 5, 1, 1, 3, 2, 3, 1, 3]
def baseStart_5472032 : Nat := 118140960795 + 5472032 * 2 ^ 59
def prefixEnd_5472032 : Nat := 4983230072969 + 3 ^ 40 * 5472032 * 2
def baseEnd_5472032 : Nat := 2809782572783639883334589

theorem tailTrace_5472032 : CollatzResearch.WordTrace tailWord_5472032 prefixEnd_5472032 2809782572783639883334589 := by
  unfold tailWord_5472032
  simp only [CollatzResearch.WordTrace]
  refine ⟨99790701655885043753745175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133054268874513391671660233 99790701655885043753745175)
  ·
    refine ⟨149686052483827565630617763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99790701655885043753745175 149686052483827565630617763)
    ·
      refine ⟨224529078725741348445926645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149686052483827565630617763 224529078725741348445926645)
      ·
        refine ⟨21049601130538251416805623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 224529078725741348445926645 21049601130538251416805623)
        ·
          refine ⟨31574401695807377125208435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21049601130538251416805623 31574401695807377125208435)
          ·
            refine ⟨47361602543711065687812653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31574401695807377125208435 47361602543711065687812653)
            ·
              refine ⟨17760600953891649632929745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47361602543711065687812653 17760600953891649632929745)
              ·
                refine ⟨13320450715418737224697309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17760600953891649632929745 13320450715418737224697309)
                ·
                  refine ⟨4995169018282026459261491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13320450715418737224697309 4995169018282026459261491)
                  ·
                    refine ⟨7492753527423039688892237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4995169018282026459261491 7492753527423039688892237)
                    ·
                      refine ⟨2809782572783639883334589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7492753527423039688892237 2809782572783639883334589)
                      ·
                        rfl

theorem cell23_5472032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_5472032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5472032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5472032 prefixEnd_5472032 := by exact prefixLift 5472032
  have htrace : WordTrace (prefixWord ++ tailWord_5472032) baseStart_5472032 baseEnd_5472032 := by
    simpa [prefixWord, tailWord_5472032, baseEnd_5472032] using wordTrace_append hprefix tailTrace_5472032
  have hstable : (prefixWord ++ tailWord_5472032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5472032).length < 2 ^ (prefixWord ++ tailWord_5472032).sum := by decide
  have hdescent : baseEnd_5472032 < baseStart_5472032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5472032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5472049 : List Nat := [1, 2, 2, 3, 2, 2, 1, 5, 1, 1, 3]
def baseStart_5472049 : Nat := 118140960795 + 5472049 * 2 ^ 59
def prefixEnd_5472049 : Nat := 4983230072969 + 3 ^ 40 * 5472049 * 2
def baseEnd_5472049 : Nat := 2809791301954766316822011

theorem tailTrace_5472049 : CollatzResearch.WordTrace tailWord_5472049 prefixEnd_5472049 2809791301954766316822011 := by
  unfold tailWord_5472049
  simp only [CollatzResearch.WordTrace]
  refine ⟨199582023352708499410859201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133054682235138999607239467 199582023352708499410859201)
  ·
    refine ⟨149686517514531374558144401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199582023352708499410859201 149686517514531374558144401)
    ·
      refine ⟨112264888135898530918608301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149686517514531374558144401 112264888135898530918608301)
      ·
        refine ⟨42099333050961949094478113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112264888135898530918608301 42099333050961949094478113)
        ·
          refine ⟨31574499788221461820858585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42099333050961949094478113 31574499788221461820858585)
          ·
            refine ⟨23680874841166096365643939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31574499788221461820858585 23680874841166096365643939)
            ·
              refine ⟨35521312261749144548465909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23680874841166096365643939 35521312261749144548465909)
              ·
                refine ⟨3330123024538982301418679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35521312261749144548465909 3330123024538982301418679)
                ·
                  refine ⟨4995184536808473452128019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3330123024538982301418679 4995184536808473452128019)
                  ·
                    refine ⟨7492776805212710178192029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4995184536808473452128019 7492776805212710178192029)
                    ·
                      refine ⟨2809791301954766316822011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7492776805212710178192029 2809791301954766316822011)
                      ·
                        rfl

theorem cell23_5472049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 5, 1, 1, 3].length) (baseStart_5472049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5472049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5472049 prefixEnd_5472049 := by exact prefixLift 5472049
  have htrace : WordTrace (prefixWord ++ tailWord_5472049) baseStart_5472049 baseEnd_5472049 := by
    simpa [prefixWord, tailWord_5472049, baseEnd_5472049] using wordTrace_append hprefix tailTrace_5472049
  have hstable : (prefixWord ++ tailWord_5472049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5472049).length < 2 ^ (prefixWord ++ tailWord_5472049).sum := by decide
  have hdescent : baseEnd_5472049 < baseStart_5472049 := by decide
  rcases family_descends (prefixWord ++ tailWord_5472049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5472082 : List Nat := [3, 2, 2, 1, 1, 5, 1, 1, 1, 6]
def baseStart_5472082 : Nat := 118140960795 + 5472082 * 2 ^ 59
def prefixEnd_5472082 : Nat := 4983230072969 + 3 ^ 40 * 5472082 * 2
def baseEnd_5472082 : Nat := 936602748938788229236453

theorem tailTrace_5472082 : CollatzResearch.WordTrace tailWord_5472082 prefixEnd_5472082 936602748938788229236453 := by
  unfold tailWord_5472082
  simp only [CollatzResearch.WordTrace]
  refine ⟨49895806740397236511702625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133055484641059297364540333 49895806740397236511702625)
  ·
    refine ⟨37421855055297927383776969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49895806740397236511702625 37421855055297927383776969)
    ·
      refine ⟨28066391291473445537832727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37421855055297927383776969 28066391291473445537832727)
      ·
        refine ⟨42099586937210168306749091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28066391291473445537832727 42099586937210168306749091)
        ·
          refine ⟨63149380405815252460123637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42099586937210168306749091 63149380405815252460123637)
          ·
            refine ⟨5920254413045179918136591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63149380405815252460123637 5920254413045179918136591)
            ·
              refine ⟨8880381619567769877204887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5920254413045179918136591 8880381619567769877204887)
              ·
                refine ⟨13320572429351654815807331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8880381619567769877204887 13320572429351654815807331)
                ·
                  refine ⟨19980858644027482223710997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13320572429351654815807331 19980858644027482223710997)
                  ·
                    refine ⟨936602748938788229236453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19980858644027482223710997 936602748938788229236453)
                    ·
                      rfl

theorem cell23_5472082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_5472082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5472082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5472082 prefixEnd_5472082 := by exact prefixLift 5472082
  have htrace : WordTrace (prefixWord ++ tailWord_5472082) baseStart_5472082 baseEnd_5472082 := by
    simpa [prefixWord, tailWord_5472082, baseEnd_5472082] using wordTrace_append hprefix tailTrace_5472082
  have hstable : (prefixWord ++ tailWord_5472082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5472082).length < 2 ^ (prefixWord ++ tailWord_5472082).sum := by decide
  have hdescent : baseEnd_5472082 < baseStart_5472082 := by decide
  rcases family_descends (prefixWord ++ tailWord_5472082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5472085 : List Nat := [1, 3, 2, 2, 2, 3, 1, 1, 1, 1, 6]
def baseStart_5472085 : Nat := 118140960795 + 5472085 * 2 ^ 59
def prefixEnd_5472085 : Nat := 4983230072969 + 3 ^ 40 * 5472085 * 2
def baseEnd_5472085 : Nat := 2809809787258328175971845

theorem tailTrace_5472085 : CollatzResearch.WordTrace tailWord_5472085 prefixEnd_5472085 2809809787258328175971845 := by
  unfold tailWord_5472085
  simp only [CollatzResearch.WordTrace]
  refine ⟨199583336380578077559169709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133055557587052051706113139 199583336380578077559169709)
  ·
    refine ⟨74843751142716779084688641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199583336380578077559169709 74843751142716779084688641)
    ·
      refine ⟨56132813357037584313516481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74843751142716779084688641 56132813357037584313516481)
      ·
        refine ⟨42099610017778188235137361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56132813357037584313516481 42099610017778188235137361)
        ·
          refine ⟨31574707513333641176353021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42099610017778188235137361 31574707513333641176353021)
          ·
            refine ⟨11840515317500115441132383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31574707513333641176353021 11840515317500115441132383)
            ·
              refine ⟨17760772976250173161698575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11840515317500115441132383 17760772976250173161698575)
              ·
                refine ⟨26641159464375259742547863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17760772976250173161698575 26641159464375259742547863)
                ·
                  refine ⟨39961739196562889613821795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26641159464375259742547863 39961739196562889613821795)
                  ·
                    refine ⟨59942608794844334420732693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39961739196562889613821795 59942608794844334420732693)
                    ·
                      refine ⟨2809809787258328175971845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59942608794844334420732693 2809809787258328175971845)
                      ·
                        rfl

theorem cell23_5472085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_5472085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5472085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5472085 prefixEnd_5472085 := by exact prefixLift 5472085
  have htrace : WordTrace (prefixWord ++ tailWord_5472085) baseStart_5472085 baseEnd_5472085 := by
    simpa [prefixWord, tailWord_5472085, baseEnd_5472085] using wordTrace_append hprefix tailTrace_5472085
  have hstable : (prefixWord ++ tailWord_5472085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5472085).length < 2 ^ (prefixWord ++ tailWord_5472085).sum := by decide
  have hdescent : baseEnd_5472085 < baseStart_5472085 := by decide
  rcases family_descends (prefixWord ++ tailWord_5472085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5472095 : List Nat := [1, 1, 2, 3, 1, 4, 4, 7]
def baseStart_5472095 : Nat := 118140960795 + 5472095 * 2 ^ 59
def prefixEnd_5472095 : Nat := 4983230072969 + 3 ^ 40 * 5472095 * 2
def baseEnd_5472095 : Nat := 104067219335736042105437

theorem tailTrace_5472095 : CollatzResearch.WordTrace tailWord_5472095 prefixEnd_5472095 104067219335736042105437 := by
  unfold tailWord_5472095
  simp only [CollatzResearch.WordTrace]
  refine ⟨199583701110541849267033739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133055800740361232844689159 199583701110541849267033739)
  ·
    refine ⟨299375551665812773900550609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199583701110541849267033739 299375551665812773900550609)
    ·
      refine ⟨224531663749359580425412957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299375551665812773900550609 224531663749359580425412957)
      ·
        refine ⟨84199373906009842659529859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 224531663749359580425412957 84199373906009842659529859)
        ·
          refine ⟨126299060859014763989294789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84199373906009842659529859 126299060859014763989294789)
          ·
            refine ⟨23681073911065268247992773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126299060859014763989294789 23681073911065268247992773)
            ·
              refine ⟨4440201358324737796498645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23681073911065268247992773 4440201358324737796498645)
              ·
                refine ⟨104067219335736042105437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4440201358324737796498645 104067219335736042105437)
                ·
                  rfl

theorem cell23_5472095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 7].length) (baseStart_5472095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5472095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5472095 prefixEnd_5472095 := by exact prefixLift 5472095
  have htrace : WordTrace (prefixWord ++ tailWord_5472095) baseStart_5472095 baseEnd_5472095 := by
    simpa [prefixWord, tailWord_5472095, baseEnd_5472095] using wordTrace_append hprefix tailTrace_5472095
  have hstable : (prefixWord ++ tailWord_5472095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5472095).length < 2 ^ (prefixWord ++ tailWord_5472095).sum := by decide
  have hdescent : baseEnd_5472095 < baseStart_5472095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5472095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5472105 : List Nat := [1, 2, 1, 1, 1, 3, 1, 6, 1, 3, 3]
def baseStart_5472105 : Nat := 118140960795 + 5472105 * 2 ^ 59
def prefixEnd_5472105 : Nat := 4983230072969 + 3 ^ 40 * 5472105 * 2
def baseEnd_5472105 : Nat := 2809820056871418097721753

theorem tailTrace_5472105 : CollatzResearch.WordTrace tailWord_5472105 prefixEnd_5472105 2809820056871418097721753 := by
  unfold tailWord_5472105
  simp only [CollatzResearch.WordTrace]
  refine ⟨199584065840505620974897769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133056043893670413983265179 199584065840505620974897769)
  ·
    refine ⟨149688049380379215731173327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199584065840505620974897769 149688049380379215731173327)
    ·
      refine ⟨224532074070568823596759991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149688049380379215731173327 224532074070568823596759991)
      ·
        refine ⟨336798111105853235395139987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224532074070568823596759991 336798111105853235395139987)
        ·
          refine ⟨505197166658779853092709981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 336798111105853235395139987 505197166658779853092709981)
          ·
            refine ⟨189448937497042444909766243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 505197166658779853092709981 189448937497042444909766243)
            ·
              refine ⟨284173406245563667364649365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189448937497042444909766243 284173406245563667364649365)
              ·
                refine ⟨13320628417760796907717939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 284173406245563667364649365 13320628417760796907717939)
                ·
                  refine ⟨19980942626641195361576909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13320628417760796907717939 19980942626641195361576909)
                  ·
                    refine ⟨7492853484990448260591341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19980942626641195361576909 7492853484990448260591341)
                    ·
                      refine ⟨2809820056871418097721753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7492853484990448260591341 2809820056871418097721753)
                      ·
                        rfl

theorem cell23_5472105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 3, 3].length) (baseStart_5472105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5472105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5472105 prefixEnd_5472105 := by exact prefixLift 5472105
  have htrace : WordTrace (prefixWord ++ tailWord_5472105) baseStart_5472105 baseEnd_5472105 := by
    simpa [prefixWord, tailWord_5472105, baseEnd_5472105] using wordTrace_append hprefix tailTrace_5472105
  have hstable : (prefixWord ++ tailWord_5472105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5472105).length < 2 ^ (prefixWord ++ tailWord_5472105).sum := by decide
  have hdescent : baseEnd_5472105 < baseStart_5472105 := by decide
  rcases family_descends (prefixWord ++ tailWord_5472105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5472122 : List Nat := [3, 1, 1, 1, 1, 1, 6, 1, 4, 1, 3]
def baseStart_5472122 : Nat := 118140960795 + 5472122 * 2 ^ 59
def prefixEnd_5472122 : Nat := 4983230072969 + 3 ^ 40 * 5472122 * 2
def baseEnd_5472122 : Nat := 2809828786042544531209175

theorem tailTrace_5472122 : CollatzResearch.WordTrace tailWord_5472122 prefixEnd_5472122 2809828786042544531209175 := by
  unfold tailWord_5472122
  simp only [CollatzResearch.WordTrace]
  refine ⟨49896171470361008219566655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133056457254296021918844413 49896171470361008219566655)
  ·
    refine ⟨74844257205541512329349983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49896171470361008219566655 74844257205541512329349983)
    ·
      refine ⟨112266385808312268494024975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74844257205541512329349983 112266385808312268494024975)
      ·
        refine ⟨168399578712468402741037463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112266385808312268494024975 168399578712468402741037463)
        ·
          refine ⟨252599368068702604111556195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168399578712468402741037463 252599368068702604111556195)
          ·
            refine ⟨378899052103053906167334293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252599368068702604111556195 378899052103053906167334293)
            ·
              refine ⟨17760893067330651851593795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 378899052103053906167334293 17760893067330651851593795)
              ·
                refine ⟨26641339600995977777390693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17760893067330651851593795 26641339600995977777390693)
                ·
                  refine ⟨4995251175186745833260755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26641339600995977777390693 4995251175186745833260755)
                  ·
                    refine ⟨7492876762780118749891133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4995251175186745833260755 7492876762780118749891133)
                    ·
                      refine ⟨2809828786042544531209175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7492876762780118749891133 2809828786042544531209175)
                      ·
                        rfl

theorem cell23_5472122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 4, 1, 3].length) (baseStart_5472122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5472122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5472122 prefixEnd_5472122 := by exact prefixLift 5472122
  have htrace : WordTrace (prefixWord ++ tailWord_5472122) baseStart_5472122 baseEnd_5472122 := by
    simpa [prefixWord, tailWord_5472122, baseEnd_5472122] using wordTrace_append hprefix tailTrace_5472122
  have hstable : (prefixWord ++ tailWord_5472122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5472122).length < 2 ^ (prefixWord ++ tailWord_5472122).sum := by decide
  have hdescent : baseEnd_5472122 < baseStart_5472122 := by decide
  rcases family_descends (prefixWord ++ tailWord_5472122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5472165 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 4, 4, 3]
def baseStart_5472165 : Nat := 118140960795 + 5472165 * 2 ^ 59
def prefixEnd_5472165 : Nat := 4983230072969 + 3 ^ 40 * 5472165 * 2
def baseEnd_5472165 : Nat := 2809850865710687862971477

theorem tailTrace_5472165 : CollatzResearch.WordTrace tailWord_5472165 prefixEnd_5472165 2809850865710687862971477 := by
  unfold tailWord_5472165
  simp only [CollatzResearch.WordTrace]
  refine ⟨199586254220288251222081949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133057502813525500814721299 199586254220288251222081949)
  ·
    refine ⟨74844845332608094208280731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199586254220288251222081949 74844845332608094208280731)
    ·
      refine ⟨112267267998912141312421097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74844845332608094208280731 112267267998912141312421097)
      ·
        refine ⟨84200450999184105984315823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112267267998912141312421097 84200450999184105984315823)
        ·
          refine ⟨126300676498776158976473735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84200450999184105984315823 126300676498776158976473735)
          ·
            refine ⟨189451014748164238464710603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126300676498776158976473735 189451014748164238464710603)
            ·
              refine ⟨284176522122246357697065905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189451014748164238464710603 284176522122246357697065905)
              ·
                refine ⟨213132391591684768272799429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 284176522122246357697065905 213132391591684768272799429)
                ·
                  refine ⟨39962323423440894051149893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 213132391591684768272799429 39962323423440894051149893)
                  ·
                    refine ⟨7492935641895167634590605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39962323423440894051149893 7492935641895167634590605)
                    ·
                      refine ⟨2809850865710687862971477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7492935641895167634590605 2809850865710687862971477)
                      ·
                        rfl

theorem cell23_5472165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 4, 3].length) (baseStart_5472165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5472165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5472165 prefixEnd_5472165 := by exact prefixLift 5472165
  have htrace : WordTrace (prefixWord ++ tailWord_5472165) baseStart_5472165 baseEnd_5472165 := by
    simpa [prefixWord, tailWord_5472165, baseEnd_5472165] using wordTrace_append hprefix tailTrace_5472165
  have hstable : (prefixWord ++ tailWord_5472165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5472165).length < 2 ^ (prefixWord ++ tailWord_5472165).sum := by decide
  have hdescent : baseEnd_5472165 < baseStart_5472165 := by decide
  rcases family_descends (prefixWord ++ tailWord_5472165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5472175 : List Nat := [1, 1, 2, 1, 2, 2, 4, 2, 2, 2, 4]
def baseStart_5472175 : Nat := 118140960795 + 5472175 * 2 ^ 59
def prefixEnd_5472175 : Nat := 4983230072969 + 3 ^ 40 * 5472175 * 2
def baseEnd_5472175 : Nat := 2809856000517232823846431

theorem tailTrace_5472175 : CollatzResearch.WordTrace tailWord_5472175 prefixEnd_5472175 2809856000517232823846431 := by
  unfold tailWord_5472175
  simp only [CollatzResearch.WordTrace]
  refine ⟨199586618950252022929945979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133057745966834681953297319 199586618950252022929945979)
  ·
    refine ⟨299379928425378034394918969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199586618950252022929945979 299379928425378034394918969)
    ·
      refine ⟨224534946319033525796189227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299379928425378034394918969 224534946319033525796189227)
      ·
        refine ⟨336802419478550288694283841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224534946319033525796189227 336802419478550288694283841)
        ·
          refine ⟨252601814608912716520712881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 336802419478550288694283841 252601814608912716520712881)
          ·
            refine ⟨189451360956684537390534661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 252601814608912716520712881 189451360956684537390534661)
            ·
              refine ⟨35522130179378350760725249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 189451360956684537390534661 35522130179378350760725249)
              ·
                refine ⟨26641597634533763070543937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35522130179378350760725249 26641597634533763070543937)
                ·
                  refine ⟨19981198225900322302907953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26641597634533763070543937 19981198225900322302907953)
                  ·
                    refine ⟨14985898669425241727180965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19981198225900322302907953 14985898669425241727180965)
                    ·
                      refine ⟨2809856000517232823846431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14985898669425241727180965 2809856000517232823846431)
                      ·
                        rfl

theorem cell23_5472175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 2, 4].length) (baseStart_5472175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5472175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5472175 prefixEnd_5472175 := by exact prefixLift 5472175
  have htrace : WordTrace (prefixWord ++ tailWord_5472175) baseStart_5472175 baseEnd_5472175 := by
    simpa [prefixWord, tailWord_5472175, baseEnd_5472175] using wordTrace_append hprefix tailTrace_5472175
  have hstable : (prefixWord ++ tailWord_5472175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5472175).length < 2 ^ (prefixWord ++ tailWord_5472175).sum := by decide
  have hdescent : baseEnd_5472175 < baseStart_5472175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5472175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5472185 : List Nat := [1, 2, 1, 4, 2, 1, 2, 3, 7]
def baseStart_5472185 : Nat := 118140960795 + 5472185 * 2 ^ 59
def prefixEnd_5472185 : Nat := 4983230072969 + 3 ^ 40 * 5472185 * 2
def baseEnd_5472185 : Nat := 312206792813753087191265

theorem tailTrace_5472185 : CollatzResearch.WordTrace tailWord_5472185 prefixEnd_5472185 312206792813753087191265 := by
  unfold tailWord_5472185
  simp only [CollatzResearch.WordTrace]
  refine ⟨199586983680215794637810009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133057989120143863091873339 199586983680215794637810009)
  ·
    refine ⟨149690237760161845978357507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199586983680215794637810009 149690237760161845978357507)
    ·
      refine ⟨224535356640242768967536261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149690237760161845978357507 224535356640242768967536261)
      ·
        refine ⟨42100379370045519181413049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 224535356640242768967536261 42100379370045519181413049)
        ·
          refine ⟨31575284527534139386059787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42100379370045519181413049 31575284527534139386059787)
          ·
            refine ⟨47362926791301209079089681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31575284527534139386059787 47362926791301209079089681)
            ·
              refine ⟨35522195093475906809317261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47362926791301209079089681 35522195093475906809317261)
              ·
                refine ⟨13320823160053465053493973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35522195093475906809317261 13320823160053465053493973)
                ·
                  refine ⟨312206792813753087191265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13320823160053465053493973 312206792813753087191265)
                  ·
                    rfl

theorem cell23_5472185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 7].length) (baseStart_5472185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5472185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5472185 prefixEnd_5472185 := by exact prefixLift 5472185
  have htrace : WordTrace (prefixWord ++ tailWord_5472185) baseStart_5472185 baseEnd_5472185 := by
    simpa [prefixWord, tailWord_5472185, baseEnd_5472185] using wordTrace_append hprefix tailTrace_5472185
  have hstable : (prefixWord ++ tailWord_5472185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5472185).length < 2 ^ (prefixWord ++ tailWord_5472185).sum := by decide
  have hdescent : baseEnd_5472185 < baseStart_5472185 := by decide
  rcases family_descends (prefixWord ++ tailWord_5472185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5472212 : List Nat := [2, 4, 1, 2, 1, 1, 1, 2, 1, 5, 3]
def baseStart_5472212 : Nat := 118140960795 + 5472212 * 2 ^ 59
def prefixEnd_5472212 : Nat := 4983230072969 + 3 ^ 40 * 5472212 * 2
def baseEnd_5472212 : Nat := 2809874999301449179083761

theorem tailTrace_5472212 : CollatzResearch.WordTrace tailWord_5472212 prefixEnd_5472212 2809874999301449179083761 := by
  unfold tailWord_5472212
  simp only [CollatzResearch.WordTrace]
  refine ⟨99793984225558989124521445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133058645634078652166028593 99793984225558989124521445)
  ·
    refine ⟨18711372042292310460847771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99793984225558989124521445 18711372042292310460847771)
    ·
      refine ⟨28067058063438465691271657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18711372042292310460847771 28067058063438465691271657)
      ·
        refine ⟨21050293547578849268453743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28067058063438465691271657 21050293547578849268453743)
        ·
          refine ⟨31575440321368273902680615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21050293547578849268453743 31575440321368273902680615)
          ·
            refine ⟨47363160482052410854020923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31575440321368273902680615 47363160482052410854020923)
            ·
              refine ⟨71044740723078616281031385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47363160482052410854020923 71044740723078616281031385)
              ·
                refine ⟨53283555542308962210773539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71044740723078616281031385 53283555542308962210773539)
                ·
                  refine ⟨79925333313463443316160309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53283555542308962210773539 79925333313463443316160309)
                  ·
                    refine ⟨7492999998137197810890029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 79925333313463443316160309 7492999998137197810890029)
                    ·
                      refine ⟨2809874999301449179083761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7492999998137197810890029 2809874999301449179083761)
                      ·
                        rfl

theorem cell23_5472212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_5472212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5472212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5472212 prefixEnd_5472212 := by exact prefixLift 5472212
  have htrace : WordTrace (prefixWord ++ tailWord_5472212) baseStart_5472212 baseEnd_5472212 := by
    simpa [prefixWord, tailWord_5472212, baseEnd_5472212] using wordTrace_append hprefix tailTrace_5472212
  have hstable : (prefixWord ++ tailWord_5472212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5472212).length < 2 ^ (prefixWord ++ tailWord_5472212).sum := by decide
  have hdescent : baseEnd_5472212 < baseStart_5472212 := by decide
  rcases family_descends (prefixWord ++ tailWord_5472212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5472215 : List Nat := [1, 1, 3, 2, 1, 1, 5, 1, 1, 7]
def baseStart_5472215 : Nat := 118140960795 + 5472215 * 2 ^ 59
def prefixEnd_5472215 : Nat := 4983230072969 + 3 ^ 40 * 5472215 * 2
def baseEnd_5472215 : Nat := 936625513247804222448749

theorem tailTrace_5472215 : CollatzResearch.WordTrace tailWord_5472215 prefixEnd_5472215 936625513247804222448749 := by
  unfold tailWord_5472215
  simp only [CollatzResearch.WordTrace]
  refine ⟨199588077870107109761402099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133058718580071406507601399 199588077870107109761402099)
  ·
    refine ⟨299382116805160664642103149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199588077870107109761402099 299382116805160664642103149)
    ·
      refine ⟨112268293801935249240788681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 299382116805160664642103149 112268293801935249240788681)
      ·
        refine ⟨84201220351451436930591511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112268293801935249240788681 84201220351451436930591511)
        ·
          refine ⟨126301830527177155395887267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84201220351451436930591511 126301830527177155395887267)
          ·
            refine ⟨189452745790765733093830901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126301830527177155395887267 189452745790765733093830901)
            ·
              refine ⟨17761194917884287477546647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 189452745790765733093830901 17761194917884287477546647)
              ·
                refine ⟨26641792376826431216319971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17761194917884287477546647 26641792376826431216319971)
                ·
                  refine ⟨39962688565239646824479957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26641792376826431216319971 39962688565239646824479957)
                  ·
                    refine ⟨936625513247804222448749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39962688565239646824479957 936625513247804222448749)
                    ·
                      rfl

theorem cell23_5472215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 7].length) (baseStart_5472215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5472215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5472215 prefixEnd_5472215 := by exact prefixLift 5472215
  have htrace : WordTrace (prefixWord ++ tailWord_5472215) baseStart_5472215 baseEnd_5472215 := by
    simpa [prefixWord, tailWord_5472215, baseEnd_5472215] using wordTrace_append hprefix tailTrace_5472215
  have hstable : (prefixWord ++ tailWord_5472215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5472215).length < 2 ^ (prefixWord ++ tailWord_5472215).sum := by decide
  have hdescent : baseEnd_5472215 < baseStart_5472215 := by decide
  rcases family_descends (prefixWord ++ tailWord_5472215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5472225 : List Nat := [1, 2, 3, 1, 2, 1, 2, 1, 3, 2, 5]
def baseStart_5472225 : Nat := 118140960795 + 5472225 * 2 ^ 59
def prefixEnd_5472225 : Nat := 4983230072969 + 3 ^ 40 * 5472225 * 2
def baseEnd_5472225 : Nat := 2809881674549957628221201

theorem tailTrace_5472225 : CollatzResearch.WordTrace tailWord_5472225 prefixEnd_5472225 2809881674549957628221201 := by
  unfold tailWord_5472225
  simp only [CollatzResearch.WordTrace]
  refine ⟨199588442600070881469266129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133058961733380587646177419 199588442600070881469266129)
  ·
    refine ⟨149691331950053161101949597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199588442600070881469266129 149691331950053161101949597)
    ·
      refine ⟨56134249481269935413231099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149691331950053161101949597 56134249481269935413231099)
      ·
        refine ⟨84201374221904903119846649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56134249481269935413231099 84201374221904903119846649)
        ·
          refine ⟨63151030666428677339884987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84201374221904903119846649 63151030666428677339884987)
          ·
            refine ⟨94726545999643016009827481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63151030666428677339884987 94726545999643016009827481)
            ·
              refine ⟨71044909499732262007370611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94726545999643016009827481 71044909499732262007370611)
              ·
                refine ⟨106567364249598393011055917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71044909499732262007370611 106567364249598393011055917)
                ·
                  refine ⟨39962761593599397379145969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106567364249598393011055917 39962761593599397379145969)
                  ·
                    refine ⟨29972071195199548034359477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39962761593599397379145969 29972071195199548034359477)
                    ·
                      refine ⟨2809881674549957628221201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29972071195199548034359477 2809881674549957628221201)
                      ·
                        rfl

theorem cell23_5472225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_5472225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5472225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5472225 prefixEnd_5472225 := by exact prefixLift 5472225
  have htrace : WordTrace (prefixWord ++ tailWord_5472225) baseStart_5472225 baseEnd_5472225 := by
    simpa [prefixWord, tailWord_5472225, baseEnd_5472225] using wordTrace_append hprefix tailTrace_5472225
  have hstable : (prefixWord ++ tailWord_5472225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5472225).length < 2 ^ (prefixWord ++ tailWord_5472225).sum := by decide
  have hdescent : baseEnd_5472225 < baseStart_5472225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5472225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5472275 : List Nat := [1, 1, 1, 2, 1, 4, 3, 2, 8]
def baseStart_5472275 : Nat := 118140960795 + 5472275 * 2 ^ 59
def prefixEnd_5472275 : Nat := 4983230072969 + 3 ^ 40 * 5472275 * 2
def baseEnd_5472275 : Nat := 312211927620298048066219

theorem tailTrace_5472275 : CollatzResearch.WordTrace tailWord_5472275 prefixEnd_5472275 312211927620298048066219 := by
  unfold tailWord_5472275
  simp only [CollatzResearch.WordTrace]
  refine ⟨199590266249889740008586279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133060177499926493339057519 199590266249889740008586279)
  ·
    refine ⟨299385399374834610012879419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199590266249889740008586279 299385399374834610012879419)
    ·
      refine ⟨449078099062251915019319129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299385399374834610012879419 449078099062251915019319129)
      ·
        refine ⟨336808574296688936264489347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 449078099062251915019319129 336808574296688936264489347)
        ·
          refine ⟨505212861445033404396734021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 336808574296688936264489347 505212861445033404396734021)
          ·
            refine ⟨94727411520943763324387629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 505212861445033404396734021 94727411520943763324387629)
            ·
              refine ⟨35522779320353911246645361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94727411520943763324387629 35522779320353911246645361)
              ·
                refine ⟨26642084490265433434984021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35522779320353911246645361 26642084490265433434984021)
                ·
                  refine ⟨312211927620298048066219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26642084490265433434984021 312211927620298048066219)
                  ·
                    rfl

theorem cell23_5472275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 8].length) (baseStart_5472275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5472275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5472275 prefixEnd_5472275 := by exact prefixLift 5472275
  have htrace : WordTrace (prefixWord ++ tailWord_5472275) baseStart_5472275 baseEnd_5472275 := by
    simpa [prefixWord, tailWord_5472275, baseEnd_5472275] using wordTrace_append hprefix tailTrace_5472275
  have hstable : (prefixWord ++ tailWord_5472275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5472275).length < 2 ^ (prefixWord ++ tailWord_5472275).sum := by decide
  have hdescent : baseEnd_5472275 < baseStart_5472275 := by decide
  rcases family_descends (prefixWord ++ tailWord_5472275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5472309 : List Nat := [1, 3, 3, 1, 1, 1, 6, 1, 6]
def baseStart_5472309 : Nat := 118140960795 + 5472309 * 2 ^ 59
def prefixEnd_5472309 : Nat := 4983230072969 + 3 ^ 40 * 5472309 * 2
def baseEnd_5472309 : Nat := 312213867436103922174535

theorem tailTrace_5472309 : CollatzResearch.WordTrace tailWord_5472309 prefixEnd_5472309 312213867436103922174535 := by
  unfold tailWord_5472309
  simp only [CollatzResearch.WordTrace]
  refine ⟨199591506331766563815323981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133061004221177709210215987 199591506331766563815323981)
  ·
    refine ⟨74846814874412461430746493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199591506331766563815323981 74846814874412461430746493)
    ·
      refine ⟨28067555577904673036529935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74846814874412461430746493 28067555577904673036529935)
      ·
        refine ⟨42101333366857009554794903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28067555577904673036529935 42101333366857009554794903)
        ·
          refine ⟨63152000050285514332192355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42101333366857009554794903 63152000050285514332192355)
          ·
            refine ⟨94728000075428271498288533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63152000050285514332192355 94728000075428271498288533)
            ·
              refine ⟨4440375003535700226482275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 94728000075428271498288533 4440375003535700226482275)
              ·
                refine ⟨6660562505303550339723413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4440375003535700226482275 6660562505303550339723413)
                ·
                  refine ⟨312213867436103922174535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6660562505303550339723413 312213867436103922174535)
                  ·
                    rfl

theorem cell23_5472309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 1, 6].length) (baseStart_5472309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5472309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5472309 prefixEnd_5472309 := by exact prefixLift 5472309
  have htrace : WordTrace (prefixWord ++ tailWord_5472309) baseStart_5472309 baseEnd_5472309 := by
    simpa [prefixWord, tailWord_5472309, baseEnd_5472309] using wordTrace_append hprefix tailTrace_5472309
  have hstable : (prefixWord ++ tailWord_5472309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5472309).length < 2 ^ (prefixWord ++ tailWord_5472309).sum := by decide
  have hdescent : baseEnd_5472309 < baseStart_5472309 := by decide
  rcases family_descends (prefixWord ++ tailWord_5472309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5472315 : List Nat := [1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 7]
def baseStart_5472315 : Nat := 118140960795 + 5472315 * 2 ^ 59
def prefixEnd_5472315 : Nat := 4983230072969 + 3 ^ 40 * 5472315 * 2
def baseEnd_5472315 : Nat := 2809927887808862276095787

theorem tailTrace_5472315 : CollatzResearch.WordTrace tailWord_5472315 prefixEnd_5472315 2809927887808862276095787 := by
  unfold tailWord_5472315
  simp only [CollatzResearch.WordTrace]
  refine ⟨199591725169744826840042399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133061150113163217893361599 199591725169744826840042399)
  ·
    refine ⟨299387587754617240260063599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199591725169744826840042399 299387587754617240260063599)
    ·
      refine ⟨449081381631925860390095399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299387587754617240260063599 449081381631925860390095399)
      ·
        refine ⟨673622072447888790585143099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 449081381631925860390095399 673622072447888790585143099)
        ·
          refine ⟨1010433108671833185877714649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 673622072447888790585143099 1010433108671833185877714649)
          ·
            refine ⟨757824831503874889408285987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1010433108671833185877714649 757824831503874889408285987)
            ·
              refine ⟨1136737247255812334112428981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 757824831503874889408285987 1136737247255812334112428981)
              ·
                refine ⟨106569116930232406323040217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1136737247255812334112428981 106569116930232406323040217)
                ·
                  refine ⟨79926837697674304742280163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106569116930232406323040217 79926837697674304742280163)
                  ·
                    refine ⟨119890256546511457113420245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 79926837697674304742280163 119890256546511457113420245)
                    ·
                      refine ⟨2809927887808862276095787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 119890256546511457113420245 2809927887808862276095787)
                      ·
                        rfl

theorem cell23_5472315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 7].length) (baseStart_5472315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5472315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5472315 prefixEnd_5472315 := by exact prefixLift 5472315
  have htrace : WordTrace (prefixWord ++ tailWord_5472315) baseStart_5472315 baseEnd_5472315 := by
    simpa [prefixWord, tailWord_5472315, baseEnd_5472315] using wordTrace_append hprefix tailTrace_5472315
  have hstable : (prefixWord ++ tailWord_5472315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5472315).length < 2 ^ (prefixWord ++ tailWord_5472315).sum := by decide
  have hdescent : baseEnd_5472315 < baseStart_5472315 := by decide
  rcases family_descends (prefixWord ++ tailWord_5472315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5472319 : List Nat := [1, 1, 2, 2, 3, 1, 2, 4, 3, 1, 3]
def baseStart_5472319 : Nat := 118140960795 + 5472319 * 2 ^ 59
def prefixEnd_5472319 : Nat := 4983230072969 + 3 ^ 40 * 5472319 * 2
def baseEnd_5472319 : Nat := 2809929941731480260445769

theorem tailTrace_5472319 : CollatzResearch.WordTrace tailWord_5472319 prefixEnd_5472319 2809929941731480260445769 := by
  unfold tailWord_5472319
  simp only [CollatzResearch.WordTrace]
  refine ⟨199591871061730335523188011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133061247374486890348792007 199591871061730335523188011)
  ·
    refine ⟨299387806592595503284782017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199591871061730335523188011 299387806592595503284782017)
    ·
      refine ⟨224540854944446627463586513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299387806592595503284782017 224540854944446627463586513)
      ·
        refine ⟨168405641208334970597689885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224540854944446627463586513 168405641208334970597689885)
        ·
          refine ⟨63152115453125613974133707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168405641208334970597689885 63152115453125613974133707)
          ·
            refine ⟨94728173179688420961200561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63152115453125613974133707 94728173179688420961200561)
            ·
              refine ⟨71046129884766315720900421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94728173179688420961200561 71046129884766315720900421)
              ·
                refine ⟨13321149353393684197668829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71046129884766315720900421 13321149353393684197668829)
                ·
                  refine ⟨4995431007522631574125811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13321149353393684197668829 4995431007522631574125811)
                  ·
                    refine ⟨7493146511283947361188717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4995431007522631574125811 7493146511283947361188717)
                    ·
                      refine ⟨2809929941731480260445769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7493146511283947361188717 2809929941731480260445769)
                      ·
                        rfl

theorem cell23_5472319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 3, 1, 3].length) (baseStart_5472319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5472319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5472319 prefixEnd_5472319 := by exact prefixLift 5472319
  have htrace : WordTrace (prefixWord ++ tailWord_5472319) baseStart_5472319 baseEnd_5472319 := by
    simpa [prefixWord, tailWord_5472319, baseEnd_5472319] using wordTrace_append hprefix tailTrace_5472319
  have hstable : (prefixWord ++ tailWord_5472319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5472319).length < 2 ^ (prefixWord ++ tailWord_5472319).sum := by decide
  have hdescent : baseEnd_5472319 < baseStart_5472319 := by decide
  rcases family_descends (prefixWord ++ tailWord_5472319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5472369 : List Nat := [1, 2, 2, 2, 1, 1, 3, 5, 2, 4]
def baseStart_5472369 : Nat := 118140960795 + 5472369 * 2 ^ 59
def prefixEnd_5472369 : Nat := 4983230072969 + 3 ^ 40 * 5472369 * 2
def baseEnd_5472369 : Nat := 936651871921401688273513

theorem tailTrace_5472369 : CollatzResearch.WordTrace tailWord_5472369 prefixEnd_5472369 936651871921401688273513 := by
  unfold tailWord_5472369
  simp only [CollatzResearch.WordTrace]
  refine ⟨199593694711549194062508161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133062463141032796041672107 199593694711549194062508161)
  ·
    refine ⟨149695271033661895546881121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199593694711549194062508161 149695271033661895546881121)
    ·
      refine ⟨112271453275246421660160841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149695271033661895546881121 112271453275246421660160841)
      ·
        refine ⟨84203589956434816245120631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112271453275246421660160841 84203589956434816245120631)
        ·
          refine ⟨126305384934652224367680947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84203589956434816245120631 126305384934652224367680947)
          ·
            refine ⟨189458077401978336551521421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126305384934652224367680947 189458077401978336551521421)
            ·
              refine ⟨71046779025741876206820533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 189458077401978336551521421 71046779025741876206820533)
              ·
                refine ⟨6660635533663300894389425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71046779025741876206820533 6660635533663300894389425)
                ·
                  refine ⟨4995476650247475670792069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6660635533663300894389425 4995476650247475670792069)
                  ·
                    refine ⟨936651871921401688273513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4995476650247475670792069 936651871921401688273513)
                    ·
                      rfl

theorem cell23_5472369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 5, 2, 4].length) (baseStart_5472369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5472369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5472369 prefixEnd_5472369 := by exact prefixLift 5472369
  have htrace : WordTrace (prefixWord ++ tailWord_5472369) baseStart_5472369 baseEnd_5472369 := by
    simpa [prefixWord, tailWord_5472369, baseEnd_5472369] using wordTrace_append hprefix tailTrace_5472369
  have hstable : (prefixWord ++ tailWord_5472369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5472369).length < 2 ^ (prefixWord ++ tailWord_5472369).sum := by decide
  have hdescent : baseEnd_5472369 < baseStart_5472369 := by decide
  rcases family_descends (prefixWord ++ tailWord_5472369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5472389 : List Nat := [1, 3, 1, 1, 5, 1, 2, 2, 1, 2, 4]
def baseStart_5472389 : Nat := 118140960795 + 5472389 * 2 ^ 59
def prefixEnd_5472389 : Nat := 4983230072969 + 3 ^ 40 * 5472389 * 2
def baseEnd_5472389 : Nat := 2809965885377294986570447

theorem tailTrace_5472389 : CollatzResearch.WordTrace tailWord_5472389 prefixEnd_5472389 2809965885377294986570447 := by
  unfold tailWord_5472389
  simp only [CollatzResearch.WordTrace]
  refine ⟨199594424171476737478236221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133062949447651158318824147 199594424171476737478236221)
  ·
    refine ⟨74847909064303776554338583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199594424171476737478236221 74847909064303776554338583)
    ·
      refine ⟨112271863596455664831507875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74847909064303776554338583 112271863596455664831507875)
      ·
        refine ⟨168407795394683497247261813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112271863596455664831507875 168407795394683497247261813)
        ·
          refine ⟨15788230818251577866930795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 168407795394683497247261813 15788230818251577866930795)
          ·
            refine ⟨23682346227377366800396193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15788230818251577866930795 23682346227377366800396193)
            ·
              refine ⟨17761759670533025100297145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23682346227377366800396193 17761759670533025100297145)
              ·
                refine ⟨13321319752899768825222859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17761759670533025100297145 13321319752899768825222859)
                ·
                  refine ⟨19981979629349653237834289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13321319752899768825222859 19981979629349653237834289)
                  ·
                    refine ⟨14986484722012239928375717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19981979629349653237834289 14986484722012239928375717)
                    ·
                      refine ⟨2809965885377294986570447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14986484722012239928375717 2809965885377294986570447)
                      ·
                        rfl

theorem cell23_5472389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 2, 4].length) (baseStart_5472389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5472389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5472389 prefixEnd_5472389 := by exact prefixLift 5472389
  have htrace : WordTrace (prefixWord ++ tailWord_5472389) baseStart_5472389 baseEnd_5472389 := by
    simpa [prefixWord, tailWord_5472389, baseEnd_5472389] using wordTrace_append hprefix tailTrace_5472389
  have hstable : (prefixWord ++ tailWord_5472389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5472389).length < 2 ^ (prefixWord ++ tailWord_5472389).sum := by decide
  have hdescent : baseEnd_5472389 < baseStart_5472389 := by decide
  rcases family_descends (prefixWord ++ tailWord_5472389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5472410 : List Nat := [3, 1, 1, 5, 2, 1, 2, 1, 3, 2, 2]
def baseStart_5472410 : Nat := 118140960795 + 5472410 * 2 ^ 59
def prefixEnd_5472410 : Nat := 4983230072969 + 3 ^ 40 * 5472410 * 2
def baseEnd_5472410 : Nat := 2809976668471039404407851

theorem tailTrace_5472410 : CollatzResearch.WordTrace tailWord_5472410 prefixEnd_5472410 2809976668471039404407851 := by
  unfold tailWord_5472410
  simp only [CollatzResearch.WordTrace]
  refine ⟨49898797526100164516187671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133063460069600438709833789 49898797526100164516187671)
  ·
    refine ⟨74848196289150246774281507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49898797526100164516187671 74848196289150246774281507)
    ·
      refine ⟨112272294433725370161422261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74848196289150246774281507 112272294433725370161422261)
      ·
        refine ⟨10525527603161753452633337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 112272294433725370161422261 10525527603161753452633337)
        ·
          refine ⟨7894145702371315089475003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10525527603161753452633337 7894145702371315089475003)
          ·
            refine ⟨11841218553556972634212505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7894145702371315089475003 11841218553556972634212505)
            ·
              refine ⟨8880913915167729475659379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11841218553556972634212505 8880913915167729475659379)
              ·
                refine ⟨13321370872751594213489069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8880913915167729475659379 13321370872751594213489069)
                ·
                  refine ⟨4995514077281847830058401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13321370872751594213489069 4995514077281847830058401)
                  ·
                    refine ⟨3746635557961385872543801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4995514077281847830058401 3746635557961385872543801)
                    ·
                      refine ⟨2809976668471039404407851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3746635557961385872543801 2809976668471039404407851)
                      ·
                        rfl

theorem cell23_5472410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_5472410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5472410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5472410 prefixEnd_5472410 := by exact prefixLift 5472410
  have htrace : WordTrace (prefixWord ++ tailWord_5472410) baseStart_5472410 baseEnd_5472410 := by
    simpa [prefixWord, tailWord_5472410, baseEnd_5472410] using wordTrace_append hprefix tailTrace_5472410
  have hstable : (prefixWord ++ tailWord_5472410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5472410).length < 2 ^ (prefixWord ++ tailWord_5472410).sum := by decide
  have hdescent : baseEnd_5472410 < baseStart_5472410 := by decide
  rcases family_descends (prefixWord ++ tailWord_5472410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5472423 : List Nat := [1, 1, 6, 2, 2, 2, 1, 1, 1, 2, 4]
def baseStart_5472423 : Nat := 118140960795 + 5472423 * 2 ^ 59
def prefixEnd_5472423 : Nat := 4983230072969 + 3 ^ 40 * 5472423 * 2
def baseEnd_5472423 : Nat := 2809983343719547853545291

theorem tailTrace_5472423 : CollatzResearch.WordTrace tailWord_5472423 prefixEnd_5472423 2809983343719547853545291 := by
  unfold tailWord_5472423
  simp only [CollatzResearch.WordTrace]
  refine ⟨199595664253353561284973923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133063776168902374189982615 199595664253353561284973923)
  ·
    refine ⟨299393496380030341927460885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199595664253353561284973923 299393496380030341927460885)
    ·
      refine ⟨14034070142813922277849729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 299393496380030341927460885 14034070142813922277849729)
      ·
        refine ⟨10525552607110441708387297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14034070142813922277849729 10525552607110441708387297)
        ·
          refine ⟨7894164455332831281290473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10525552607110441708387297 7894164455332831281290473)
          ·
            refine ⟨5920623341499623460967855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7894164455332831281290473 5920623341499623460967855)
            ·
              refine ⟨8880935012249435191451783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5920623341499623460967855 8880935012249435191451783)
              ·
                refine ⟨13321402518374152787177675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8880935012249435191451783 13321402518374152787177675)
                ·
                  refine ⟨19982103777561229180766513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13321402518374152787177675 19982103777561229180766513)
                  ·
                    refine ⟨14986577833170921885574885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19982103777561229180766513 14986577833170921885574885)
                    ·
                      refine ⟨2809983343719547853545291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14986577833170921885574885 2809983343719547853545291)
                      ·
                        rfl

theorem cell23_5472423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_5472423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5472423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5472423 prefixEnd_5472423 := by exact prefixLift 5472423
  have htrace : WordTrace (prefixWord ++ tailWord_5472423) baseStart_5472423 baseEnd_5472423 := by
    simpa [prefixWord, tailWord_5472423, baseEnd_5472423] using wordTrace_append hprefix tailTrace_5472423
  have hstable : (prefixWord ++ tailWord_5472423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5472423).length < 2 ^ (prefixWord ++ tailWord_5472423).sum := by decide
  have hdescent : baseEnd_5472423 < baseStart_5472423 := by decide
  rcases family_descends (prefixWord ++ tailWord_5472423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5472433 : List Nat := [1, 2, 2, 5, 3, 1, 2, 7]
def baseStart_5472433 : Nat := 118140960795 + 5472433 * 2 ^ 59
def prefixEnd_5472433 : Nat := 4983230072969 + 3 ^ 40 * 5472433 * 2
def baseEnd_5472433 : Nat := 104073647352818252385935

theorem tailTrace_5472433 : CollatzResearch.WordTrace tailWord_5472433 prefixEnd_5472433 104073647352818252385935 := by
  unfold tailWord_5472433
  simp only [CollatzResearch.WordTrace]
  refine ⟨199596028983317332992837953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133064019322211555328558635 199596028983317332992837953)
  ·
    refine ⟨149697021737487999744628465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199596028983317332992837953 149697021737487999744628465)
    ·
      refine ⟨112272766303115999808471349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149697021737487999744628465 112272766303115999808471349)
      ·
        refine ⟨10525571840917124982044189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 112272766303115999808471349 10525571840917124982044189)
        ·
          refine ⟨3947089440343921868266571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10525571840917124982044189 3947089440343921868266571)
          ·
            refine ⟨5920634160515882802399857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3947089440343921868266571 5920634160515882802399857)
            ·
              refine ⟨4440475620386912101799893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5920634160515882802399857 4440475620386912101799893)
              ·
                refine ⟨104073647352818252385935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4440475620386912101799893 104073647352818252385935)
                ·
                  rfl

theorem cell23_5472433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 7].length) (baseStart_5472433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5472433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5472433 prefixEnd_5472433 := by exact prefixLift 5472433
  have htrace : WordTrace (prefixWord ++ tailWord_5472433) baseStart_5472433 baseEnd_5472433 := by
    simpa [prefixWord, tailWord_5472433, baseEnd_5472433] using wordTrace_append hprefix tailTrace_5472433
  have hstable : (prefixWord ++ tailWord_5472433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5472433).length < 2 ^ (prefixWord ++ tailWord_5472433).sum := by decide
  have hdescent : baseEnd_5472433 < baseStart_5472433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5472433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5472442 : List Nat := [3, 1, 1, 1, 2, 2, 2, 2, 1, 8]
def baseStart_5472442 : Nat := 118140960795 + 5472442 * 2 ^ 59
def prefixEnd_5472442 : Nat := 4983230072969 + 3 ^ 40 * 5472442 * 2
def baseEnd_5472442 : Nat := 936664366617327759735901

theorem tailTrace_5472442 : CollatzResearch.WordTrace tailWord_5472442 prefixEnd_5472442 936664366617327759735901 := by
  unfold tailWord_5472442
  simp only [CollatzResearch.WordTrace]
  refine ⟨49899089310071181882478895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133064238160189818353277053 49899089310071181882478895)
  ·
    refine ⟨74848633965106772823718343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49899089310071181882478895 74848633965106772823718343)
    ·
      refine ⟨112272950947660159235577515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74848633965106772823718343 112272950947660159235577515)
      ·
        refine ⟨168409426421490238853366273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112272950947660159235577515 168409426421490238853366273)
        ·
          refine ⟨126307069816117679140024705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168409426421490238853366273 126307069816117679140024705)
          ·
            refine ⟨94730302362088259355018529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126307069816117679140024705 94730302362088259355018529)
            ·
              refine ⟨71047726771566194516263897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94730302362088259355018529 71047726771566194516263897)
              ·
                refine ⟨53285795078674645887197923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71047726771566194516263897 53285795078674645887197923)
                ·
                  refine ⟨79928692618011968830796885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53285795078674645887197923 79928692618011968830796885)
                  ·
                    refine ⟨936664366617327759735901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 79928692618011968830796885 936664366617327759735901)
                    ·
                      rfl

theorem cell23_5472442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 1, 8].length) (baseStart_5472442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5472442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5472442 prefixEnd_5472442 := by exact prefixLift 5472442
  have htrace : WordTrace (prefixWord ++ tailWord_5472442) baseStart_5472442 baseEnd_5472442 := by
    simpa [prefixWord, tailWord_5472442, baseEnd_5472442] using wordTrace_append hprefix tailTrace_5472442
  have hstable : (prefixWord ++ tailWord_5472442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5472442).length < 2 ^ (prefixWord ++ tailWord_5472442).sum := by decide
  have hdescent : baseEnd_5472442 < baseStart_5472442 := by decide
  rcases family_descends (prefixWord ++ tailWord_5472442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5472444 : List Nat := [2, 2, 2, 3, 4, 1, 1, 3, 1, 2, 2]
def baseStart_5472444 : Nat := 118140960795 + 5472444 * 2 ^ 59
def prefixEnd_5472444 : Nat := 4983230072969 + 3 ^ 40 * 5472444 * 2
def baseEnd_5472444 : Nat := 2809994126813292271382695

theorem tailTrace_5472444 : CollatzResearch.WordTrace tailWord_5472444 prefixEnd_5472444 2809994126813292271382695 := by
  unfold tailWord_5472444
  simp only [CollatzResearch.WordTrace]
  refine ⟨99798215093138740935744193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133064286790851654580992257 99798215093138740935744193)
  ·
    refine ⟨74848661319854055701808145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99798215093138740935744193 74848661319854055701808145)
    ·
      refine ⟨56136495989890541776356109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74848661319854055701808145 56136495989890541776356109)
      ·
        refine ⟨21051185996208953166133541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56136495989890541776356109 21051185996208953166133541)
        ·
          refine ⟨3947097374289178718650039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21051185996208953166133541 3947097374289178718650039)
          ·
            refine ⟨5920646061433768077975059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3947097374289178718650039 5920646061433768077975059)
            ·
              refine ⟨8880969092150652116962589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5920646061433768077975059 8880969092150652116962589)
              ·
                refine ⟨3330363409556494543860971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8880969092150652116962589 3330363409556494543860971)
                ·
                  refine ⟨4995545114334741815791457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3330363409556494543860971 4995545114334741815791457)
                  ·
                    refine ⟨3746658835751056361843593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4995545114334741815791457 3746658835751056361843593)
                    ·
                      refine ⟨2809994126813292271382695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3746658835751056361843593 2809994126813292271382695)
                      ·
                        rfl

theorem cell23_5472444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_5472444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5472444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5472444 prefixEnd_5472444 := by exact prefixLift 5472444
  have htrace : WordTrace (prefixWord ++ tailWord_5472444) baseStart_5472444 baseEnd_5472444 := by
    simpa [prefixWord, tailWord_5472444, baseEnd_5472444] using wordTrace_append hprefix tailTrace_5472444
  have hstable : (prefixWord ++ tailWord_5472444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5472444).length < 2 ^ (prefixWord ++ tailWord_5472444).sum := by decide
  have hdescent : baseEnd_5472444 < baseStart_5472444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5472444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5472477 : List Nat := [1, 4, 3, 2, 1, 3, 2, 1, 2, 1, 3]
def baseStart_5472477 : Nat := 118140960795 + 5472477 * 2 ^ 59
def prefixEnd_5472477 : Nat := 4983230072969 + 3 ^ 40 * 5472477 * 2
def baseEnd_5472477 : Nat := 2810011071674890642270043

theorem tailTrace_5472477 : CollatzResearch.WordTrace tailWord_5472477 prefixEnd_5472477 2810011071674890642270043 := by
  unfold tailWord_5472477
  simp only [CollatzResearch.WordTrace]
  refine ⟨199597633795157928507439685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133065089196771952338293123 199597633795157928507439685)
  ·
    refine ⟨37424556336592111595144941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 199597633795157928507439685 37424556336592111595144941)
    ·
      refine ⟨14034208626222041848179353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37424556336592111595144941 14034208626222041848179353)
      ·
        refine ⟨10525656469666531386134515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14034208626222041848179353 10525656469666531386134515)
        ·
          refine ⟨15788484704499797079201773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10525656469666531386134515 15788484704499797079201773)
          ·
            refine ⟨5920681764187423904700665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15788484704499797079201773 5920681764187423904700665)
            ·
              refine ⟨4440511323140567928525499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5920681764187423904700665 4440511323140567928525499)
              ·
                refine ⟨6660766984710851892788249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4440511323140567928525499 6660766984710851892788249)
                ·
                  refine ⟨4995575238533138919591187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6660766984710851892788249 4995575238533138919591187)
                  ·
                    refine ⟨7493362857799708379386781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4995575238533138919591187 7493362857799708379386781)
                    ·
                      refine ⟨2810011071674890642270043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7493362857799708379386781 2810011071674890642270043)
                      ·
                        rfl

theorem cell23_5472477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_5472477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5472477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5472477 prefixEnd_5472477 := by exact prefixLift 5472477
  have htrace : WordTrace (prefixWord ++ tailWord_5472477) baseStart_5472477 baseEnd_5472477 := by
    simpa [prefixWord, tailWord_5472477, baseEnd_5472477] using wordTrace_append hprefix tailTrace_5472477
  have hstable : (prefixWord ++ tailWord_5472477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5472477).length < 2 ^ (prefixWord ++ tailWord_5472477).sum := by decide
  have hdescent : baseEnd_5472477 < baseStart_5472477 := by decide
  rcases family_descends (prefixWord ++ tailWord_5472477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5472526 : List Nat := [4, 1, 1, 2, 1, 2, 1, 1, 1, 7, 2]
def baseStart_5472526 : Nat := 118140960795 + 5472526 * 2 ^ 59
def prefixEnd_5472526 : Nat := 4983230072969 + 3 ^ 40 * 5472526 * 2
def baseEnd_5472526 : Nat := 2810036232226960950557317

theorem tailTrace_5472526 : CollatzResearch.WordTrace tailWord_5472526 prefixEnd_5472526 2810036232226960950557317 := by
  unfold tailWord_5472526
  simp only [CollatzResearch.WordTrace]
  refine ⟨24949927621497551234496679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133066280647986939917315621 24949927621497551234496679)
  ·
    refine ⟨37424891432246326851745019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24949927621497551234496679 37424891432246326851745019)
    ·
      refine ⟨56137337148369490277617529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37424891432246326851745019 56137337148369490277617529)
      ·
        refine ⟨42103002861277117708213147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56137337148369490277617529 42103002861277117708213147)
        ·
          refine ⟨63154504291915676562319721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42103002861277117708213147 63154504291915676562319721)
          ·
            refine ⟨47365878218936757421739791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63154504291915676562319721 47365878218936757421739791)
            ·
              refine ⟨71048817328405136132609687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47365878218936757421739791 71048817328405136132609687)
              ·
                refine ⟨106573225992607704198914531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71048817328405136132609687 106573225992607704198914531)
                ·
                  refine ⟨159859838988911556298371797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106573225992607704198914531 159859838988911556298371797)
                  ·
                    refine ⟨3746714976302614600743089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 159859838988911556298371797 3746714976302614600743089)
                    ·
                      refine ⟨2810036232226960950557317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3746714976302614600743089 2810036232226960950557317)
                      ·
                        rfl

theorem cell23_5472526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 1, 7, 2].length) (baseStart_5472526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5472526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5472526 prefixEnd_5472526 := by exact prefixLift 5472526
  have htrace : WordTrace (prefixWord ++ tailWord_5472526) baseStart_5472526 baseEnd_5472526 := by
    simpa [prefixWord, tailWord_5472526, baseEnd_5472526] using wordTrace_append hprefix tailTrace_5472526
  have hstable : (prefixWord ++ tailWord_5472526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5472526).length < 2 ^ (prefixWord ++ tailWord_5472526).sum := by decide
  have hdescent : baseEnd_5472526 < baseStart_5472526 := by decide
  rcases family_descends (prefixWord ++ tailWord_5472526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5472529 : List Nat := [1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 5]
def baseStart_5472529 : Nat := 118140960795 + 5472529 * 2 ^ 59
def prefixEnd_5472529 : Nat := 4983230072969 + 3 ^ 40 * 5472529 * 2
def baseEnd_5472529 : Nat := 2810037772668924438819803

theorem tailTrace_5472529 : CollatzResearch.WordTrace tailWord_5472529 prefixEnd_5472529 2810037772668924438819803 := by
  unfold tailWord_5472529
  simp only [CollatzResearch.WordTrace]
  refine ⟨199599530390969541388332641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133066353593979694258888427 199599530390969541388332641)
  ·
    refine ⟨149699647793227156041249481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199599530390969541388332641 149699647793227156041249481)
    ·
      refine ⟨112274735844920367030937111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149699647793227156041249481 112274735844920367030937111)
      ·
        refine ⟨168412103767380550546405667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112274735844920367030937111 168412103767380550546405667)
        ·
          refine ⟨252618155651070825819608501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168412103767380550546405667 252618155651070825819608501)
          ·
            refine ⟨23682952092287889920588297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 252618155651070825819608501 23682952092287889920588297)
            ·
              refine ⟨17762214069215917440441223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23682952092287889920588297 17762214069215917440441223)
              ·
                refine ⟨26643321103823876160661835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17762214069215917440441223 26643321103823876160661835)
                ·
                  refine ⟨39964981655735814240992753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26643321103823876160661835 39964981655735814240992753)
                  ·
                    refine ⟨29973736241801860680744565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39964981655735814240992753 29973736241801860680744565)
                    ·
                      refine ⟨2810037772668924438819803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29973736241801860680744565 2810037772668924438819803)
                      ·
                        rfl

theorem cell23_5472529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 5].length) (baseStart_5472529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5472529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5472529 prefixEnd_5472529 := by exact prefixLift 5472529
  have htrace : WordTrace (prefixWord ++ tailWord_5472529) baseStart_5472529 baseEnd_5472529 := by
    simpa [prefixWord, tailWord_5472529, baseEnd_5472529] using wordTrace_append hprefix tailTrace_5472529
  have hstable : (prefixWord ++ tailWord_5472529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5472529).length < 2 ^ (prefixWord ++ tailWord_5472529).sum := by decide
  have hdescent : baseEnd_5472529 < baseStart_5472529 := by decide
  rcases family_descends (prefixWord ++ tailWord_5472529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5472539 : List Nat := [1, 1, 1, 1, 1, 1, 6, 2, 4, 1, 4]
def baseStart_5472539 : Nat := 118140960795 + 5472539 * 2 ^ 59
def prefixEnd_5472539 : Nat := 4983230072969 + 3 ^ 40 * 5472539 * 2
def baseEnd_5472539 : Nat := 2810042907475469399694757

theorem tailTrace_5472539 : CollatzResearch.WordTrace tailWord_5472539 prefixEnd_5472539 2810042907475469399694757 := by
  unfold tailWord_5472539
  simp only [CollatzResearch.WordTrace]
  refine ⟨199599895120933313096196671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133066596747288875397464447 199599895120933313096196671)
  ·
    refine ⟨299399842681399969644295007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199599895120933313096196671 299399842681399969644295007)
    ·
      refine ⟨449099764022099954466442511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299399842681399969644295007 449099764022099954466442511)
      ·
        refine ⟨673649646033149931699663767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 449099764022099954466442511 673649646033149931699663767)
        ·
          refine ⟨1010474469049724897549495651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 673649646033149931699663767 1010474469049724897549495651)
          ·
            refine ⟨1515711703574587346324243477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1010474469049724897549495651 1515711703574587346324243477)
            ·
              refine ⟨71048986105058781858948913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1515711703574587346324243477 71048986105058781858948913)
              ·
                refine ⟨53286739578794086394211685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71048986105058781858948913 53286739578794086394211685)
                ·
                  refine ⟨9991263671023891198914691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53286739578794086394211685 9991263671023891198914691)
                  ·
                    refine ⟨14986895506535836798372037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9991263671023891198914691 14986895506535836798372037)
                    ·
                      refine ⟨2810042907475469399694757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14986895506535836798372037 2810042907475469399694757)
                      ·
                        rfl

theorem cell23_5472539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 4, 1, 4].length) (baseStart_5472539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5472539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5472539 prefixEnd_5472539 := by exact prefixLift 5472539
  have htrace : WordTrace (prefixWord ++ tailWord_5472539) baseStart_5472539 baseEnd_5472539 := by
    simpa [prefixWord, tailWord_5472539, baseEnd_5472539] using wordTrace_append hprefix tailTrace_5472539
  have hstable : (prefixWord ++ tailWord_5472539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5472539).length < 2 ^ (prefixWord ++ tailWord_5472539).sum := by decide
  have hdescent : baseEnd_5472539 < baseStart_5472539 := by decide
  rcases family_descends (prefixWord ++ tailWord_5472539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5472556 : List Nat := [2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 4]
def baseStart_5472556 : Nat := 118140960795 + 5472556 * 2 ^ 59
def prefixEnd_5472556 : Nat := 4983230072969 + 3 ^ 40 * 5472556 * 2
def baseEnd_5472556 : Nat := 2810051636646595833182179

theorem tailTrace_5472556 : CollatzResearch.WordTrace tailWord_5472556 prefixEnd_5472556 2810051636646595833182179 := by
  unfold tailWord_5472556
  simp only [CollatzResearch.WordTrace]
  refine ⟨99800257580935862499782761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133067010107914483333043681 99800257580935862499782761)
  ·
    refine ⟨74850193185701896874837071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99800257580935862499782761 74850193185701896874837071)
    ·
      refine ⟨112275289778552845312255607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74850193185701896874837071 112275289778552845312255607)
      ·
        refine ⟨168412934667829267968383411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112275289778552845312255607 168412934667829267968383411)
        ·
          refine ⟨252619402001743901952575117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168412934667829267968383411 252619402001743901952575117)
          ·
            refine ⟨94732275750653963232215669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 252619402001743901952575117 94732275750653963232215669)
            ·
              refine ⟨8881150851623809053020219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94732275750653963232215669 8881150851623809053020219)
              ·
                refine ⟨13321726277435713579530329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8881150851623809053020219 13321726277435713579530329)
                ·
                  refine ⟨9991294708076785184647747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13321726277435713579530329 9991294708076785184647747)
                  ·
                    refine ⟨14986942062115177776971621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9991294708076785184647747 14986942062115177776971621)
                    ·
                      refine ⟨2810051636646595833182179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14986942062115177776971621 2810051636646595833182179)
                      ·
                        rfl

theorem cell23_5472556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 4].length) (baseStart_5472556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5472556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5472556 prefixEnd_5472556 := by exact prefixLift 5472556
  have htrace : WordTrace (prefixWord ++ tailWord_5472556) baseStart_5472556 baseEnd_5472556 := by
    simpa [prefixWord, tailWord_5472556, baseEnd_5472556] using wordTrace_append hprefix tailTrace_5472556
  have hstable : (prefixWord ++ tailWord_5472556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5472556).length < 2 ^ (prefixWord ++ tailWord_5472556).sum := by decide
  have hdescent : baseEnd_5472556 < baseStart_5472556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5472556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5472583 : List Nat := [1, 1, 4, 1, 2, 2, 1, 6, 1, 4]
def baseStart_5472583 : Nat := 118140960795 + 5472583 * 2 ^ 59
def prefixEnd_5472583 : Nat := 4983230072969 + 3 ^ 40 * 5472583 * 2
def baseEnd_5472583 : Nat := 936688500208089075848185

theorem tailTrace_5472583 : CollatzResearch.WordTrace tailWord_5472583 prefixEnd_5472583 936688500208089075848185 := by
  unfold tailWord_5472583
  simp only [CollatzResearch.WordTrace]
  refine ⟨199601499932773908610798403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133067666621849272407198935 199601499932773908610798403)
  ·
    refine ⟨299402249899160862916197605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199601499932773908610798403 299402249899160862916197605)
    ·
      refine ⟨56137921856092661796787051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 299402249899160862916197605 56137921856092661796787051)
      ·
        refine ⟨84206882784138992695180577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56137921856092661796787051 84206882784138992695180577)
        ·
          refine ⟨63155162088104244521385433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84206882784138992695180577 63155162088104244521385433)
          ·
            refine ⟨47366371566078183391039075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63155162088104244521385433 47366371566078183391039075)
            ·
              refine ⟨71049557349117275086558613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47366371566078183391039075 71049557349117275086558613)
              ·
                refine ⟨3330448000739872269682435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 71049557349117275086558613 3330448000739872269682435)
                ·
                  refine ⟨4995672001109808404523653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3330448000739872269682435 4995672001109808404523653)
                  ·
                    refine ⟨936688500208089075848185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4995672001109808404523653 936688500208089075848185)
                    ·
                      rfl

theorem cell23_5472583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 6, 1, 4].length) (baseStart_5472583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5472583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5472583 prefixEnd_5472583 := by exact prefixLift 5472583
  have htrace : WordTrace (prefixWord ++ tailWord_5472583) baseStart_5472583 baseEnd_5472583 := by
    simpa [prefixWord, tailWord_5472583, baseEnd_5472583] using wordTrace_append hprefix tailTrace_5472583
  have hstable : (prefixWord ++ tailWord_5472583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5472583).length < 2 ^ (prefixWord ++ tailWord_5472583).sum := by decide
  have hdescent : baseEnd_5472583 < baseStart_5472583 := by decide
  rcases family_descends (prefixWord ++ tailWord_5472583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5472599 : List Nat := [1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 6]
def baseStart_5472599 : Nat := 118140960795 + 5472599 * 2 ^ 59
def prefixEnd_5472599 : Nat := 4983230072969 + 3 ^ 40 * 5472599 * 2
def baseEnd_5472599 : Nat := 2810073716314739164944481

theorem tailTrace_5472599 : CollatzResearch.WordTrace tailWord_5472599 prefixEnd_5472599 2810073716314739164944481 := by
  unfold tailWord_5472599
  simp only [CollatzResearch.WordTrace]
  refine ⟨199602083500715943343380851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133068055667143962228920567 199602083500715943343380851)
  ·
    refine ⟨299403125251073915015071277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199602083500715943343380851 299403125251073915015071277)
    ·
      refine ⟨112276171969152718130651729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 299403125251073915015071277 112276171969152718130651729)
      ·
        refine ⟨84207128976864538597988797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112276171969152718130651729 84207128976864538597988797)
        ·
          refine ⟨31577673366324201974245799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84207128976864538597988797 31577673366324201974245799)
          ·
            refine ⟨47366510049486302961368699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31577673366324201974245799 47366510049486302961368699)
            ·
              refine ⟨71049765074229454442053049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47366510049486302961368699 71049765074229454442053049)
              ·
                refine ⟨53287323805672090831539787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71049765074229454442053049 53287323805672090831539787)
                ·
                  refine ⟨79930985708508136247309681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53287323805672090831539787 79930985708508136247309681)
                  ·
                    refine ⟨59948239281381102185482261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 79930985708508136247309681 59948239281381102185482261)
                    ·
                      refine ⟨2810073716314739164944481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59948239281381102185482261 2810073716314739164944481)
                      ·
                        rfl

theorem cell23_5472599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_5472599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5472599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5472599 prefixEnd_5472599 := by exact prefixLift 5472599
  have htrace : WordTrace (prefixWord ++ tailWord_5472599) baseStart_5472599 baseEnd_5472599 := by
    simpa [prefixWord, tailWord_5472599, baseEnd_5472599] using wordTrace_append hprefix tailTrace_5472599
  have hstable : (prefixWord ++ tailWord_5472599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5472599).length < 2 ^ (prefixWord ++ tailWord_5472599).sum := by decide
  have hdescent : baseEnd_5472599 < baseStart_5472599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5472599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5472639 : List Nat := [1, 1, 2, 2, 1, 1, 2, 4, 3, 6]
def baseStart_5472639 : Nat := 118140960795 + 5472639 * 2 ^ 59
def prefixEnd_5472639 : Nat := 4983230072969 + 3 ^ 40 * 5472639 * 2
def baseEnd_5472639 : Nat := 936698085180306336148099

theorem tailTrace_5472639 : CollatzResearch.WordTrace tailWord_5472639 prefixEnd_5472639 936698085180306336148099 := by
  unfold tailWord_5472639
  simp only [CollatzResearch.WordTrace]
  refine ⟨199603542420571030174836971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133069028280380686783224647 199603542420571030174836971)
  ·
    refine ⟨299405313630856545262255457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199603542420571030174836971 299405313630856545262255457)
    ·
      refine ⟨224553985223142408946691593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299405313630856545262255457 224553985223142408946691593)
      ·
        refine ⟨168415488917356806710018695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224553985223142408946691593 168415488917356806710018695)
        ·
          refine ⟨252623233376035210065028043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168415488917356806710018695 252623233376035210065028043)
          ·
            refine ⟨378934850064052815097542065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252623233376035210065028043 378934850064052815097542065)
            ·
              refine ⟨284201137548039611323156549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 378934850064052815097542065 284201137548039611323156549)
              ·
                refine ⟨53287713290257427123091853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 284201137548039611323156549 53287713290257427123091853)
                ·
                  refine ⟨19982892483846535171159445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53287713290257427123091853 19982892483846535171159445)
                  ·
                    refine ⟨936698085180306336148099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19982892483846535171159445 936698085180306336148099)
                    ·
                      rfl

theorem cell23_5472639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 6].length) (baseStart_5472639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5472639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5472639 prefixEnd_5472639 := by exact prefixLift 5472639
  have htrace : WordTrace (prefixWord ++ tailWord_5472639) baseStart_5472639 baseEnd_5472639 := by
    simpa [prefixWord, tailWord_5472639, baseEnd_5472639] using wordTrace_append hprefix tailTrace_5472639
  have hstable : (prefixWord ++ tailWord_5472639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5472639).length < 2 ^ (prefixWord ++ tailWord_5472639).sum := by decide
  have hdescent : baseEnd_5472639 < baseStart_5472639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5472639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5472663 : List Nat := [1, 1, 3, 3, 1, 1, 5, 2, 1, 1, 4]
def baseStart_5472663 : Nat := 118140960795 + 5472663 * 2 ^ 59
def prefixEnd_5472663 : Nat := 4983230072969 + 3 ^ 40 * 5472663 * 2
def baseEnd_5472663 : Nat := 2810106579076626914544187

theorem tailTrace_5472663 : CollatzResearch.WordTrace tailWord_5472663 prefixEnd_5472663 2810106579076626914544187 := by
  unfold tailWord_5472663
  simp only [CollatzResearch.WordTrace]
  refine ⟨199604417772484082273710643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133069611848322721515807095 199604417772484082273710643)
  ·
    refine ⟨299406626658726123410565965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199604417772484082273710643 299406626658726123410565965)
    ·
      refine ⟨112277484997022296278962237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 299406626658726123410565965 112277484997022296278962237)
      ·
        refine ⟨42104056873883361104610839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112277484997022296278962237 42104056873883361104610839)
        ·
          refine ⟨63156085310825041656916259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42104056873883361104610839 63156085310825041656916259)
          ·
            refine ⟨94734127966237562485374389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63156085310825041656916259 94734127966237562485374389)
            ·
              refine ⟨8881324496834771483003849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94734127966237562485374389 8881324496834771483003849)
              ·
                refine ⟨6660993372626078612252887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8881324496834771483003849 6660993372626078612252887)
                ·
                  refine ⟨9991490058939117918379331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6660993372626078612252887 9991490058939117918379331)
                  ·
                    refine ⟨14987235088408676877568997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9991490058939117918379331 14987235088408676877568997)
                    ·
                      refine ⟨2810106579076626914544187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14987235088408676877568997 2810106579076626914544187)
                      ·
                        rfl

theorem cell23_5472663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_5472663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5472663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5472663 prefixEnd_5472663 := by exact prefixLift 5472663
  have htrace : WordTrace (prefixWord ++ tailWord_5472663) baseStart_5472663 baseEnd_5472663 := by
    simpa [prefixWord, tailWord_5472663, baseEnd_5472663] using wordTrace_append hprefix tailTrace_5472663
  have hstable : (prefixWord ++ tailWord_5472663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5472663).length < 2 ^ (prefixWord ++ tailWord_5472663).sum := by decide
  have hdescent : baseEnd_5472663 < baseStart_5472663 := by decide
  rcases family_descends (prefixWord ++ tailWord_5472663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5472676 : List Nat := [2, 3, 1, 2, 1, 1, 3, 1, 3, 2, 4]
def baseStart_5472676 : Nat := 118140960795 + 5472676 * 2 ^ 59
def prefixEnd_5472676 : Nat := 4983230072969 + 3 ^ 40 * 5472676 * 2
def baseEnd_5472676 : Nat := 2810113254325135363681627

theorem tailTrace_5472676 : CollatzResearch.WordTrace tailWord_5472676 prefixEnd_5472676 2810113254325135363681627 := by
  unfold tailWord_5472676
  simp only [CollatzResearch.WordTrace]
  refine ⟨99802445960718492746966941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133069927947624656995955921 99802445960718492746966941)
  ·
    refine ⟨37425917235269434780112603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99802445960718492746966941 37425917235269434780112603)
    ·
      refine ⟨56138875852904152170168905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37425917235269434780112603 56138875852904152170168905)
      ·
        refine ⟨42104156889678114127626679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56138875852904152170168905 42104156889678114127626679)
        ·
          refine ⟨63156235334517171191440019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42104156889678114127626679 63156235334517171191440019)
          ·
            refine ⟨94734353001775756787160029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63156235334517171191440019 94734353001775756787160029)
            ·
              refine ⟨35525382375665908795185011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94734353001775756787160029 35525382375665908795185011)
              ·
                refine ⟨53288073563498863192777517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35525382375665908795185011 53288073563498863192777517)
                ·
                  refine ⟨19983027586312073697291569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53288073563498863192777517 19983027586312073697291569)
                  ·
                    refine ⟨14987270689734055272968677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19983027586312073697291569 14987270689734055272968677)
                    ·
                      refine ⟨2810113254325135363681627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14987270689734055272968677 2810113254325135363681627)
                      ·
                        rfl

theorem cell23_5472676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_5472676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5472676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5472676 prefixEnd_5472676 := by exact prefixLift 5472676
  have htrace : WordTrace (prefixWord ++ tailWord_5472676) baseStart_5472676 baseEnd_5472676 := by
    simpa [prefixWord, tailWord_5472676, baseEnd_5472676] using wordTrace_append hprefix tailTrace_5472676
  have hstable : (prefixWord ++ tailWord_5472676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5472676).length < 2 ^ (prefixWord ++ tailWord_5472676).sum := by decide
  have hdescent : baseEnd_5472676 < baseStart_5472676 := by decide
  rcases family_descends (prefixWord ++ tailWord_5472676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5472696 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 5, 3, 3]
def baseStart_5472696 : Nat := 118140960795 + 5472696 * 2 ^ 59
def prefixEnd_5472696 : Nat := 4983230072969 + 3 ^ 40 * 5472696 * 2
def baseEnd_5472696 : Nat := 2810123523938225285431535

theorem tailTrace_5472696 : CollatzResearch.WordTrace tailWord_5472696 prefixEnd_5472696 2810123523938225285431535 := by
  unfold tailWord_5472696
  simp only [CollatzResearch.WordTrace]
  refine ⟨99802810690682264454830971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133070414254243019273107961 99802810690682264454830971)
  ·
    refine ⟨149704216036023396682246457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99802810690682264454830971 149704216036023396682246457)
    ·
      refine ⟨112278162027017547511684843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149704216036023396682246457 112278162027017547511684843)
      ·
        refine ⟨168417243040526321267527265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112278162027017547511684843 168417243040526321267527265)
        ·
          refine ⟨126312932280394740950645449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168417243040526321267527265 126312932280394740950645449)
          ·
            refine ⟨94734699210296055712984087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126312932280394740950645449 94734699210296055712984087)
            ·
              refine ⟨142102048815444083569476131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94734699210296055712984087 142102048815444083569476131)
              ·
                refine ⟨213153073223166125354214197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142102048815444083569476131 213153073223166125354214197)
                ·
                  refine ⟨19983100614671824251957581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 213153073223166125354214197 19983100614671824251957581)
                  ·
                    refine ⟨7493662730501934094484093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19983100614671824251957581 7493662730501934094484093)
                    ·
                      refine ⟨2810123523938225285431535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7493662730501934094484093 2810123523938225285431535)
                      ·
                        rfl

theorem cell23_5472696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 5, 3, 3].length) (baseStart_5472696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5472696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5472696 prefixEnd_5472696 := by exact prefixLift 5472696
  have htrace : WordTrace (prefixWord ++ tailWord_5472696) baseStart_5472696 baseEnd_5472696 := by
    simpa [prefixWord, tailWord_5472696, baseEnd_5472696] using wordTrace_append hprefix tailTrace_5472696
  have hstable : (prefixWord ++ tailWord_5472696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5472696).length < 2 ^ (prefixWord ++ tailWord_5472696).sum := by decide
  have hdescent : baseEnd_5472696 < baseStart_5472696 := by decide
  rcases family_descends (prefixWord ++ tailWord_5472696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5472810 : List Nat := [3, 1, 4, 1, 1, 4, 1, 1, 7]
def baseStart_5472810 : Nat := 118140960795 + 5472810 * 2 ^ 59
def prefixEnd_5472810 : Nat := 4983230072969 + 3 ^ 40 * 5472810 * 2
def baseEnd_5472810 : Nat := 312242451192537537711779

theorem tailTrace_5472810 : CollatzResearch.WordTrace tailWord_5472810 prefixEnd_5472810 312242451192537537711779 := by
  unfold tailWord_5472810
  simp only [CollatzResearch.WordTrace]
  refine ⟨49902444825737881594827971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133073186201967684252874589 49902444825737881594827971)
  ·
    refine ⟨74853667238606822392241957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49902444825737881594827971 74853667238606822392241957)
    ·
      refine ⟨14035062607238779198545367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74853667238606822392241957 14035062607238779198545367)
      ·
        refine ⟨21052593910858168797818051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14035062607238779198545367 21052593910858168797818051)
        ·
          refine ⟨31578890866287253196727077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21052593910858168797818051 31578890866287253196727077)
          ·
            refine ⟨5921042037428859974386327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31578890866287253196727077 5921042037428859974386327)
            ·
              refine ⟨8881563056143289961579491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5921042037428859974386327 8881563056143289961579491)
              ·
                refine ⟨13322344584214934942369237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8881563056143289961579491 13322344584214934942369237)
                ·
                  refine ⟨312242451192537537711779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13322344584214934942369237 312242451192537537711779)
                  ·
                    rfl

theorem cell23_5472810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 7].length) (baseStart_5472810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5472810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5472810 prefixEnd_5472810 := by exact prefixLift 5472810
  have htrace : WordTrace (prefixWord ++ tailWord_5472810) baseStart_5472810 baseEnd_5472810 := by
    simpa [prefixWord, tailWord_5472810, baseEnd_5472810] using wordTrace_append hprefix tailTrace_5472810
  have hstable : (prefixWord ++ tailWord_5472810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5472810).length < 2 ^ (prefixWord ++ tailWord_5472810).sum := by decide
  have hdescent : baseEnd_5472810 < baseStart_5472810 := by decide
  rcases family_descends (prefixWord ++ tailWord_5472810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5472816 : List Nat := [2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 7]
def baseStart_5472816 : Nat := 118140960795 + 5472816 * 2 ^ 59
def prefixEnd_5472816 : Nat := 4983230072969 + 3 ^ 40 * 5472816 * 2
def baseEnd_5472816 : Nat := 2810185141616764815930983

theorem tailTrace_5472816 : CollatzResearch.WordTrace tailWord_5472816 prefixEnd_5472816 2810185141616764815930983 := by
  unfold tailWord_5472816
  simp only [CollatzResearch.WordTrace]
  refine ⟨99804999070464894702015151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133073332093953192936020201 99804999070464894702015151)
  ·
    refine ⟨149707498605697342053022727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99804999070464894702015151 149707498605697342053022727)
    ·
      refine ⟨224561247908546013079534091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149707498605697342053022727 224561247908546013079534091)
      ·
        refine ⟨336841871862819019619301137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224561247908546013079534091 336841871862819019619301137)
        ·
          refine ⟨252631403897114264714475853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 336841871862819019619301137 252631403897114264714475853)
          ·
            refine ⟨94736776461417849267928445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 252631403897114264714475853 94736776461417849267928445)
            ·
              refine ⟨35526291173031693475473167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94736776461417849267928445 35526291173031693475473167)
              ·
                refine ⟨53289436759547540213209751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35526291173031693475473167 53289436759547540213209751)
                ·
                  refine ⟨79934155139321310319814627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53289436759547540213209751 79934155139321310319814627)
                  ·
                    refine ⟨119901232708981965479721941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 79934155139321310319814627 119901232708981965479721941)
                    ·
                      refine ⟨2810185141616764815930983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 119901232708981965479721941 2810185141616764815930983)
                      ·
                        rfl

theorem cell23_5472816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 7].length) (baseStart_5472816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5472816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5472816 prefixEnd_5472816 := by exact prefixLift 5472816
  have htrace : WordTrace (prefixWord ++ tailWord_5472816) baseStart_5472816 baseEnd_5472816 := by
    simpa [prefixWord, tailWord_5472816, baseEnd_5472816] using wordTrace_append hprefix tailTrace_5472816
  have hstable : (prefixWord ++ tailWord_5472816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5472816).length < 2 ^ (prefixWord ++ tailWord_5472816).sum := by decide
  have hdescent : baseEnd_5472816 < baseStart_5472816 := by decide
  rcases family_descends (prefixWord ++ tailWord_5472816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5472843 : List Nat := [1, 1, 1, 1, 3, 1, 5, 3, 2, 1, 4]
def baseStart_5472843 : Nat := 118140960795 + 5472843 * 2 ^ 59
def prefixEnd_5472843 : Nat := 4983230072969 + 3 ^ 40 * 5472843 * 2
def baseEnd_5472843 : Nat := 2810199005594436210293359

theorem tailTrace_5472843 : CollatzResearch.WordTrace tailWord_5472843 prefixEnd_5472843 2810199005594436210293359 := by
  unfold tailWord_5472843
  simp only [CollatzResearch.WordTrace]
  refine ⟨199610982911831973015263183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133073988607887982010175455 199610982911831973015263183)
  ·
    refine ⟨299416474367747959522894775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199610982911831973015263183 299416474367747959522894775)
    ·
      refine ⟨449124711551621939284342163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299416474367747959522894775 449124711551621939284342163)
      ·
        refine ⟨673687067327432908926513245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 449124711551621939284342163 673687067327432908926513245)
        ·
          refine ⟨252632650247787340847442467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 673687067327432908926513245 252632650247787340847442467)
          ·
            refine ⟨378948975371681011271163701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252632650247787340847442467 378948975371681011271163701)
            ·
              refine ⟨35526466441095094806671597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 378948975371681011271163701 35526466441095094806671597)
              ·
                refine ⟨13322424915410660552501849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35526466441095094806671597 13322424915410660552501849)
                ·
                  refine ⟨9991818686557995414376387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13322424915410660552501849 9991818686557995414376387)
                  ·
                    refine ⟨14987728029836993121564581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9991818686557995414376387 14987728029836993121564581)
                    ·
                      refine ⟨2810199005594436210293359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14987728029836993121564581 2810199005594436210293359)
                      ·
                        rfl

theorem cell23_5472843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 2, 1, 4].length) (baseStart_5472843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5472843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5472843 prefixEnd_5472843 := by exact prefixLift 5472843
  have htrace : WordTrace (prefixWord ++ tailWord_5472843) baseStart_5472843 baseEnd_5472843 := by
    simpa [prefixWord, tailWord_5472843, baseEnd_5472843] using wordTrace_append hprefix tailTrace_5472843
  have hstable : (prefixWord ++ tailWord_5472843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5472843).length < 2 ^ (prefixWord ++ tailWord_5472843).sum := by decide
  have hdescent : baseEnd_5472843 < baseStart_5472843 := by decide
  rcases family_descends (prefixWord ++ tailWord_5472843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5472877 : List Nat := [1, 5, 1, 1, 3, 2, 1, 1, 2, 4, 2]
def baseStart_5472877 : Nat := 118140960795 + 5472877 * 2 ^ 59
def prefixEnd_5472877 : Nat := 4983230072969 + 3 ^ 40 * 5472877 * 2
def baseEnd_5472877 : Nat := 2810216463936689077268203

theorem tailTrace_5472877 : CollatzResearch.WordTrace tailWord_5472877 prefixEnd_5472877 2810216463936689077268203 := by
  unfold tailWord_5472877
  simp only [CollatzResearch.WordTrace]
  refine ⟨199612222993708796822000885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133074815329139197881333923 199612222993708796822000885)
  ·
    refine ⟨18713645905660199702062583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 199612222993708796822000885 18713645905660199702062583)
    ·
      refine ⟨28070468858490299553093875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18713645905660199702062583 28070468858490299553093875)
      ·
        refine ⟨42105703287735449329640813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28070468858490299553093875 42105703287735449329640813)
        ·
          refine ⟨15789638732900793498615305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42105703287735449329640813 15789638732900793498615305)
          ·
            refine ⟨11842229049675595123961479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15789638732900793498615305 11842229049675595123961479)
            ·
              refine ⟨17763343574513392685942219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11842229049675595123961479 17763343574513392685942219)
              ·
                refine ⟨26645015361770089028913329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17763343574513392685942219 26645015361770089028913329)
                ·
                  refine ⟨19983761521327566771684997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26645015361770089028913329 19983761521327566771684997)
                  ·
                    refine ⟨3746955285248918769690937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19983761521327566771684997 3746955285248918769690937)
                    ·
                      refine ⟨2810216463936689077268203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3746955285248918769690937 2810216463936689077268203)
                      ·
                        rfl

theorem cell23_5472877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 4, 2].length) (baseStart_5472877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5472877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5472877 prefixEnd_5472877 := by exact prefixLift 5472877
  have htrace : WordTrace (prefixWord ++ tailWord_5472877) baseStart_5472877 baseEnd_5472877 := by
    simpa [prefixWord, tailWord_5472877, baseEnd_5472877] using wordTrace_append hprefix tailTrace_5472877
  have hstable : (prefixWord ++ tailWord_5472877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5472877).length < 2 ^ (prefixWord ++ tailWord_5472877).sum := by decide
  have hdescent : baseEnd_5472877 < baseStart_5472877 := by decide
  rcases family_descends (prefixWord ++ tailWord_5472877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5472953 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 5, 1, 5]
def baseStart_5472953 : Nat := 118140960795 + 5472953 * 2 ^ 59
def prefixEnd_5472953 : Nat := 4983230072969 + 3 ^ 40 * 5472953 * 2
def baseEnd_5472953 : Nat := 2810255488466430779917853

theorem tailTrace_5472953 : CollatzResearch.WordTrace tailWord_5472953 prefixEnd_5472953 2810255488466430779917853 := by
  unfold tailWord_5472953
  simp only [CollatzResearch.WordTrace]
  refine ⟨199614994941433461801767513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133076663294288974534511675 199614994941433461801767513)
  ·
    refine ⟨149711246206075096351325635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199614994941433461801767513 149711246206075096351325635)
    ·
      refine ⟨224566869309112644526988453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149711246206075096351325635 224566869309112644526988453)
      ·
        refine ⟨42106287995458620848810335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 224566869309112644526988453 42106287995458620848810335)
        ·
          refine ⟨63159431993187931273215503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42106287995458620848810335 63159431993187931273215503)
          ·
            refine ⟨94739147989781896909823255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63159431993187931273215503 94739147989781896909823255)
            ·
              refine ⟨142108721984672845364734883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94739147989781896909823255 142108721984672845364734883)
              ·
                refine ⟨213163082977009268047102325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142108721984672845364734883 213163082977009268047102325)
                ·
                  refine ⟨19984039029094618879415843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 213163082977009268047102325 19984039029094618879415843)
                  ·
                    refine ⟨29976058543641928319123765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19984039029094618879415843 29976058543641928319123765)
                    ·
                      refine ⟨2810255488466430779917853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29976058543641928319123765 2810255488466430779917853)
                      ·
                        rfl

theorem cell23_5472953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_5472953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5472953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5472953 prefixEnd_5472953 := by exact prefixLift 5472953
  have htrace : WordTrace (prefixWord ++ tailWord_5472953) baseStart_5472953 baseEnd_5472953 := by
    simpa [prefixWord, tailWord_5472953, baseEnd_5472953] using wordTrace_append hprefix tailTrace_5472953
  have hstable : (prefixWord ++ tailWord_5472953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5472953).length < 2 ^ (prefixWord ++ tailWord_5472953).sum := by decide
  have hdescent : baseEnd_5472953 < baseStart_5472953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5472953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5472960 : List Nat := [2, 1, 1, 2, 4, 2, 1, 2, 4, 4]
def baseStart_5472960 : Nat := 118140960795 + 5472960 * 2 ^ 59
def prefixEnd_5472960 : Nat := 4983230072969 + 3 ^ 40 * 5472960 * 2
def baseEnd_5472960 : Nat := 936753027610337417510107

theorem tailTrace_5472960 : CollatzResearch.WordTrace tailWord_5472960 prefixEnd_5472960 936753027610337417510107 := by
  unfold tailWord_5472960
  simp only [CollatzResearch.WordTrace]
  refine ⟨99807625126204050998636167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133076833501605401331514889 99807625126204050998636167)
  ·
    refine ⟨149711437689306076497954251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99807625126204050998636167 149711437689306076497954251)
    ·
      refine ⟨224567156533959114746931377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149711437689306076497954251 224567156533959114746931377)
      ·
        refine ⟨168425367400469336060198533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224567156533959114746931377 168425367400469336060198533)
        ·
          refine ⟨31579756387588000511287225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 168425367400469336060198533 31579756387588000511287225)
          ·
            refine ⟨23684817290691000383465419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31579756387588000511287225 23684817290691000383465419)
            ·
              refine ⟨35527225936036500575198129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23684817290691000383465419 35527225936036500575198129)
              ·
                refine ⟨26645419452027375431398597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35527225936036500575198129 26645419452027375431398597)
                ·
                  refine ⟨4996016147255132893387237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26645419452027375431398597 4996016147255132893387237)
                  ·
                    refine ⟨936753027610337417510107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4996016147255132893387237 936753027610337417510107)
                    ·
                      rfl

theorem cell23_5472960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 4, 4].length) (baseStart_5472960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5472960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5472960 prefixEnd_5472960 := by exact prefixLift 5472960
  have htrace : WordTrace (prefixWord ++ tailWord_5472960) baseStart_5472960 baseEnd_5472960 := by
    simpa [prefixWord, tailWord_5472960, baseEnd_5472960] using wordTrace_append hprefix tailTrace_5472960
  have hstable : (prefixWord ++ tailWord_5472960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5472960).length < 2 ^ (prefixWord ++ tailWord_5472960).sum := by decide
  have hdescent : baseEnd_5472960 < baseStart_5472960 := by decide
  rcases family_descends (prefixWord ++ tailWord_5472960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5472970 : List Nat := [3, 1, 2, 1, 4, 1, 1, 3, 1, 1, 5]
def baseStart_5472970 : Nat := 118140960795 + 5472970 * 2 ^ 59
def prefixEnd_5472970 : Nat := 4983230072969 + 3 ^ 40 * 5472970 * 2
def baseEnd_5472970 : Nat := 2810264217637557213405275

theorem tailTrace_5472970 : CollatzResearch.WordTrace tailWord_5472970 prefixEnd_5472970 2810264217637557213405275 := by
  unfold tailWord_5472970
  simp only [CollatzResearch.WordTrace]
  refine ⟨49903903745592968426284091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133077076654914582470090909 49903903745592968426284091)
  ·
    refine ⟨74855855618389452639426137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49903903745592968426284091 74855855618389452639426137)
    ·
      refine ⟨56141891713792089479569603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74855855618389452639426137 56141891713792089479569603)
      ·
        refine ⟨84212837570688134219354405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56141891713792089479569603 84212837570688134219354405)
        ·
          refine ⟨15789907044504025166128951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84212837570688134219354405 15789907044504025166128951)
          ·
            refine ⟨23684860566756037749193427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15789907044504025166128951 23684860566756037749193427)
            ·
              refine ⟨35527290850134056623790141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23684860566756037749193427 35527290850134056623790141)
              ·
                refine ⟨13322734068800271233921303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35527290850134056623790141 13322734068800271233921303)
                ·
                  refine ⟨19984101103200406850881955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13322734068800271233921303 19984101103200406850881955)
                  ·
                    refine ⟨29976151654800610276322933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19984101103200406850881955 29976151654800610276322933)
                    ·
                      refine ⟨2810264217637557213405275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29976151654800610276322933 2810264217637557213405275)
                      ·
                        rfl

theorem cell23_5472970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_5472970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5472970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5472970 prefixEnd_5472970 := by exact prefixLift 5472970
  have htrace : WordTrace (prefixWord ++ tailWord_5472970) baseStart_5472970 baseEnd_5472970 := by
    simpa [prefixWord, tailWord_5472970, baseEnd_5472970] using wordTrace_append hprefix tailTrace_5472970
  have hstable : (prefixWord ++ tailWord_5472970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5472970).length < 2 ^ (prefixWord ++ tailWord_5472970).sum := by decide
  have hdescent : baseEnd_5472970 < baseStart_5472970 := by decide
  rcases family_descends (prefixWord ++ tailWord_5472970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5472978 : List Nat := [3, 2, 2, 2, 3, 1, 3, 2, 1, 1, 3]
def baseStart_5472978 : Nat := 118140960795 + 5472978 * 2 ^ 59
def prefixEnd_5472978 : Nat := 4983230072969 + 3 ^ 40 * 5472978 * 2
def baseEnd_5472978 : Nat := 2810268325482793182105239

theorem tailTrace_5472978 : CollatzResearch.WordTrace tailWord_5472978 prefixEnd_5472978 2810268325482793182105239 := by
  unfold tailWord_5472978
  simp only [CollatzResearch.WordTrace]
  refine ⟨49903976691585722767856897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133077271177561927380951725 49903976691585722767856897)
  ·
    refine ⟨37427982518689292075892673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49903976691585722767856897 37427982518689292075892673)
    ·
      refine ⟨28070986889016969056919505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37427982518689292075892673 28070986889016969056919505)
      ·
        refine ⟨21053240166762726792689629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28070986889016969056919505 21053240166762726792689629)
        ·
          refine ⟨7894965062536022547258611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21053240166762726792689629 7894965062536022547258611)
          ·
            refine ⟨11842447593804033820887917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7894965062536022547258611 11842447593804033820887917)
            ·
              refine ⟨4440917847676512682832969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11842447593804033820887917 4440917847676512682832969)
              ·
                refine ⟨3330688385757384512124727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4440917847676512682832969 3330688385757384512124727)
                ·
                  refine ⟨4996032578636076768187091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3330688385757384512124727 4996032578636076768187091)
                  ·
                    refine ⟨7494048867954115152280637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4996032578636076768187091 7494048867954115152280637)
                    ·
                      refine ⟨2810268325482793182105239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7494048867954115152280637 2810268325482793182105239)
                      ·
                        rfl

theorem cell23_5472978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_5472978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5472978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5472978 prefixEnd_5472978 := by exact prefixLift 5472978
  have htrace : WordTrace (prefixWord ++ tailWord_5472978) baseStart_5472978 baseEnd_5472978 := by
    simpa [prefixWord, tailWord_5472978, baseEnd_5472978] using wordTrace_append hprefix tailTrace_5472978
  have hstable : (prefixWord ++ tailWord_5472978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5472978).length < 2 ^ (prefixWord ++ tailWord_5472978).sum := by decide
  have hdescent : baseEnd_5472978 < baseStart_5472978 := by decide
  rcases family_descends (prefixWord ++ tailWord_5472978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5472984 : List Nat := [2, 1, 2, 2, 3, 2, 3, 1, 3, 2, 2]
def baseStart_5472984 : Nat := 118140960795 + 5472984 * 2 ^ 59
def prefixEnd_5472984 : Nat := 4983230072969 + 3 ^ 40 * 5472984 * 2
def baseEnd_5472984 : Nat := 2810271406366720158630211

theorem tailTrace_5472984 : CollatzResearch.WordTrace tailWord_5472984 prefixEnd_5472984 2810271406366720158630211 := by
  unfold tailWord_5472984
  simp only [CollatzResearch.WordTrace]
  refine ⟨99808062802160577048073003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133077417069547436064097337 99808062802160577048073003)
  ·
    refine ⟨149712094203240865572109505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99808062802160577048073003 149712094203240865572109505)
    ·
      refine ⟨112284070652430649179082129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149712094203240865572109505 112284070652430649179082129)
      ·
        refine ⟨84213052989322986884311597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112284070652430649179082129 84213052989322986884311597)
        ·
          refine ⟨31579894870996120081616849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84213052989322986884311597 31579894870996120081616849)
          ·
            refine ⟨23684921153247090061212637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31579894870996120081616849 23684921153247090061212637)
            ·
              refine ⟨8881845432467658772954739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23684921153247090061212637 8881845432467658772954739)
              ·
                refine ⟨13322768148701488159432109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8881845432467658772954739 13322768148701488159432109)
                ·
                  refine ⟨4996038055763058059787041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13322768148701488159432109 4996038055763058059787041)
                  ·
                    refine ⟨3747028541822293544840281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4996038055763058059787041 3747028541822293544840281)
                    ·
                      refine ⟨2810271406366720158630211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3747028541822293544840281 2810271406366720158630211)
                      ·
                        rfl

theorem cell23_5472984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 3, 2, 2].length) (baseStart_5472984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5472984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5472984 prefixEnd_5472984 := by exact prefixLift 5472984
  have htrace : WordTrace (prefixWord ++ tailWord_5472984) baseStart_5472984 baseEnd_5472984 := by
    simpa [prefixWord, tailWord_5472984, baseEnd_5472984] using wordTrace_append hprefix tailTrace_5472984
  have hstable : (prefixWord ++ tailWord_5472984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5472984).length < 2 ^ (prefixWord ++ tailWord_5472984).sum := by decide
  have hdescent : baseEnd_5472984 < baseStart_5472984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5472984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5473034 : List Nat := [3, 1, 2, 2, 1, 2, 4, 2, 2, 1, 3]
def baseStart_5473034 : Nat := 118140960795 + 5473034 * 2 ^ 59
def prefixEnd_5473034 : Nat := 4983230072969 + 3 ^ 40 * 5473034 * 2
def baseEnd_5473034 : Nat := 2810297080399444963004981

theorem tailTrace_5473034 : CollatzResearch.WordTrace tailWord_5473034 prefixEnd_5473034 2810297080399444963004981 := by
  unfold tailWord_5473034
  simp only [CollatzResearch.WordTrace]
  refine ⟨49904487313535003158866539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133078632836093341756977437 49904487313535003158866539)
  ·
    refine ⟨74856730970302504738299809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49904487313535003158866539 74856730970302504738299809)
    ·
      refine ⟨56142548227726878553724857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74856730970302504738299809 56142548227726878553724857)
      ·
        refine ⟨42106911170795158915293643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56142548227726878553724857 42106911170795158915293643)
        ·
          refine ⟨63160366756192738372940465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42106911170795158915293643 63160366756192738372940465)
          ·
            refine ⟨47370275067144553779705349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63160366756192738372940465 47370275067144553779705349)
            ·
              refine ⟨8881926575089603833694753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47370275067144553779705349 8881926575089603833694753)
              ·
                refine ⟨6661444931317202875271065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8881926575089603833694753 6661444931317202875271065)
                ·
                  refine ⟨4996083698487902156453299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6661444931317202875271065 4996083698487902156453299)
                  ·
                    refine ⟨7494125547731853234679949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4996083698487902156453299 7494125547731853234679949)
                    ·
                      refine ⟨2810297080399444963004981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7494125547731853234679949 2810297080399444963004981)
                      ·
                        rfl

theorem cell23_5473034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_5473034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5473034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5473034 prefixEnd_5473034 := by exact prefixLift 5473034
  have htrace : WordTrace (prefixWord ++ tailWord_5473034) baseStart_5473034 baseEnd_5473034 := by
    simpa [prefixWord, tailWord_5473034, baseEnd_5473034] using wordTrace_append hprefix tailTrace_5473034
  have hstable : (prefixWord ++ tailWord_5473034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5473034).length < 2 ^ (prefixWord ++ tailWord_5473034).sum := by decide
  have hdescent : baseEnd_5473034 < baseStart_5473034 := by decide
  rcases family_descends (prefixWord ++ tailWord_5473034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5473050 : List Nat := [3, 1, 1, 3, 2, 1, 3, 1, 2, 6]
def baseStart_5473050 : Nat := 118140960795 + 5473050 * 2 ^ 59
def prefixEnd_5473050 : Nat := 4983230072969 + 3 ^ 40 * 5473050 * 2
def baseEnd_5473050 : Nat := 936768432029972300134969

theorem tailTrace_5473050 : CollatzResearch.WordTrace tailWord_5473050 prefixEnd_5473050 936768432029972300134969 := by
  unfold tailWord_5473050
  simp only [CollatzResearch.WordTrace]
  refine ⟨49904633205520511842012151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133079021881388031578699069 49904633205520511842012151)
  ·
    refine ⟨74856949808280767763018227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49904633205520511842012151 74856949808280767763018227)
    ·
      refine ⟨112285424712421151644527341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74856949808280767763018227 112285424712421151644527341)
      ·
        refine ⟨42107034267157931866697753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112285424712421151644527341 42107034267157931866697753)
        ·
          refine ⟨31580275700368448900023315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42107034267157931866697753 31580275700368448900023315)
          ·
            refine ⟨47370413550552673350034973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31580275700368448900023315 47370413550552673350034973)
            ·
              refine ⟨17763905081457252506263115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47370413550552673350034973 17763905081457252506263115)
              ·
                refine ⟨26645857622185878759394673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17763905081457252506263115 26645857622185878759394673)
                ·
                  refine ⟨19984393216639409069546005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26645857622185878759394673 19984393216639409069546005)
                  ·
                    refine ⟨936768432029972300134969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19984393216639409069546005 936768432029972300134969)
                    ·
                      rfl

theorem cell23_5473050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 2, 6].length) (baseStart_5473050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5473050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5473050 prefixEnd_5473050 := by exact prefixLift 5473050
  have htrace : WordTrace (prefixWord ++ tailWord_5473050) baseStart_5473050 baseEnd_5473050 := by
    simpa [prefixWord, tailWord_5473050, baseEnd_5473050] using wordTrace_append hprefix tailTrace_5473050
  have hstable : (prefixWord ++ tailWord_5473050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5473050).length < 2 ^ (prefixWord ++ tailWord_5473050).sum := by decide
  have hdescent : baseEnd_5473050 < baseStart_5473050 := by decide
  rcases family_descends (prefixWord ++ tailWord_5473050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5473074 : List Nat := [3, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2]
def baseStart_5473074 : Nat := 118140960795 + 5473074 * 2 ^ 59
def prefixEnd_5473074 : Nat := 4983230072969 + 3 ^ 40 * 5473074 * 2
def baseEnd_5473074 : Nat := 2810317619625624806504797

theorem tailTrace_5473074 : CollatzResearch.WordTrace tailWord_5473074 prefixEnd_5473074 2810317619625624806504797 := by
  unfold tailWord_5473074
  simp only [CollatzResearch.WordTrace]
  refine ⟨49904852043498774866730569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133079605449330066311281517 49904852043498774866730569)
  ·
    refine ⟨37428639032624081150047927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49904852043498774866730569 37428639032624081150047927)
    ·
      refine ⟨56142958548936121725071891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37428639032624081150047927 56142958548936121725071891)
      ·
        refine ⟨84214437823404182587607837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56142958548936121725071891 84214437823404182587607837)
        ·
          refine ⟨31580414183776568470352939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84214437823404182587607837 31580414183776568470352939)
          ·
            refine ⟨47370621275664852705529409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31580414183776568470352939 47370621275664852705529409)
            ·
              refine ⟨35527965956748639529147057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47370621275664852705529409 35527965956748639529147057)
              ·
                refine ⟨26645974467561479646860293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35527965956748639529147057 26645974467561479646860293)
                ·
                  refine ⟨4996120212667777433786305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26645974467561479646860293 4996120212667777433786305)
                  ·
                    refine ⟨3747090159500833075339729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4996120212667777433786305 3747090159500833075339729)
                    ·
                      refine ⟨2810317619625624806504797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3747090159500833075339729 2810317619625624806504797)
                      ·
                        rfl

theorem cell23_5473074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2].length) (baseStart_5473074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5473074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5473074 prefixEnd_5473074 := by exact prefixLift 5473074
  have htrace : WordTrace (prefixWord ++ tailWord_5473074) baseStart_5473074 baseEnd_5473074 := by
    simpa [prefixWord, tailWord_5473074, baseEnd_5473074] using wordTrace_append hprefix tailTrace_5473074
  have hstable : (prefixWord ++ tailWord_5473074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5473074).length < 2 ^ (prefixWord ++ tailWord_5473074).sum := by decide
  have hdescent : baseEnd_5473074 < baseStart_5473074 := by decide
  rcases family_descends (prefixWord ++ tailWord_5473074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5473078 : List Nat := [5, 1, 2, 2, 2, 1, 1, 3, 1, 3, 2]
def baseStart_5473078 : Nat := 118140960795 + 5473078 * 2 ^ 59
def prefixEnd_5473078 : Nat := 4983230072969 + 3 ^ 40 * 5473078 * 2
def baseEnd_5473078 : Nat := 2810319673548242790854779

theorem tailTrace_5473078 : CollatzResearch.WordTrace tailWord_5473078 prefixEnd_5473078 2810319673548242790854779 := by
  unfold tailWord_5473078
  simp only [CollatzResearch.WordTrace]
  refine ⟨12476222129123788009379243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 133079702710653738766711925 12476222129123788009379243)
  ·
    refine ⟨18714333193685682014068865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12476222129123788009379243 18714333193685682014068865)
    ·
      refine ⟨14035749895264261510551649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18714333193685682014068865 14035749895264261510551649)
      ·
        refine ⟨10526812421448196132913737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14035749895264261510551649 10526812421448196132913737)
        ·
          refine ⟨7895109316086147099685303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10526812421448196132913737 7895109316086147099685303)
          ·
            refine ⟨11842663974129220649527955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7895109316086147099685303 11842663974129220649527955)
            ·
              refine ⟨17763995961193830974291933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11842663974129220649527955 17763995961193830974291933)
              ·
                refine ⟨6661498485447686615359475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17763995961193830974291933 6661498485447686615359475)
                ·
                  refine ⟨9992247728171529923039213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6661498485447686615359475 9992247728171529923039213)
                  ·
                    refine ⟨3747092898064323721139705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9992247728171529923039213 3747092898064323721139705)
                    ·
                      refine ⟨2810319673548242790854779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3747092898064323721139705 2810319673548242790854779)
                      ·
                        rfl

theorem cell23_5473078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_5473078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5473078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5473078 prefixEnd_5473078 := by exact prefixLift 5473078
  have htrace : WordTrace (prefixWord ++ tailWord_5473078) baseStart_5473078 baseEnd_5473078 := by
    simpa [prefixWord, tailWord_5473078, baseEnd_5473078] using wordTrace_append hprefix tailTrace_5473078
  have hstable : (prefixWord ++ tailWord_5473078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5473078).length < 2 ^ (prefixWord ++ tailWord_5473078).sum := by decide
  have hdescent : baseEnd_5473078 < baseStart_5473078 := by decide
  rcases family_descends (prefixWord ++ tailWord_5473078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5473097 : List Nat := [1, 2, 1, 1, 2, 5, 2, 4, 5]
def baseStart_5473097 : Nat := 118140960795 + 5473097 * 2 ^ 59
def prefixEnd_5473097 : Nat := 4983230072969 + 3 ^ 40 * 5473097 * 2
def baseEnd_5473097 : Nat := 312258825520075357390799

theorem tailTrace_5473097 : CollatzResearch.WordTrace tailWord_5473097 prefixEnd_5473097 312258825520075357390799 := by
  unfold tailWord_5473097
  simp only [CollatzResearch.WordTrace]
  refine ⟨199620247052911774395009545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133080164701941182930006363 199620247052911774395009545)
  ·
    refine ⟨149715185289683830796257159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199620247052911774395009545 149715185289683830796257159)
    ·
      refine ⟨224572777934525746194385739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149715185289683830796257159 224572777934525746194385739)
      ·
        refine ⟨336859166901788619291578609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224572777934525746194385739 336859166901788619291578609)
        ·
          refine ⟨252644375176341464468683957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 336859166901788619291578609 252644375176341464468683957)
          ·
            refine ⟨23685410172782012293939121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 252644375176341464468683957 23685410172782012293939121)
            ·
              refine ⟨17764057629586509220454341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23685410172782012293939121 17764057629586509220454341)
              ·
                refine ⟨3330760805547470478835189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17764057629586509220454341 3330760805547470478835189)
                ·
                  refine ⟨312258825520075357390799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3330760805547470478835189 312258825520075357390799)
                  ·
                    rfl

theorem cell23_5473097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 4, 5].length) (baseStart_5473097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5473097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5473097 prefixEnd_5473097 := by exact prefixLift 5473097
  have htrace : WordTrace (prefixWord ++ tailWord_5473097) baseStart_5473097 baseEnd_5473097 := by
    simpa [prefixWord, tailWord_5473097, baseEnd_5473097] using wordTrace_append hprefix tailTrace_5473097
  have hstable : (prefixWord ++ tailWord_5473097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5473097).length < 2 ^ (prefixWord ++ tailWord_5473097).sum := by decide
  have hdescent : baseEnd_5473097 < baseStart_5473097 := by decide
  rcases family_descends (prefixWord ++ tailWord_5473097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5473108 : List Nat := [2, 4, 1, 1, 5, 1, 1, 1, 1, 4, 2]
def baseStart_5473108 : Nat := 118140960795 + 5473108 * 2 ^ 59
def prefixEnd_5473108 : Nat := 4983230072969 + 3 ^ 40 * 5473108 * 2
def baseEnd_5473108 : Nat := 2810335077967877673479641

theorem tailTrace_5473108 : CollatzResearch.WordTrace tailWord_5473108 prefixEnd_5473108 2810335077967877673479641 := by
  unfold tailWord_5473108
  simp only [CollatzResearch.WordTrace]
  refine ⟨99810324127935961636829989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133080432170581282182439985 99810324127935961636829989)
  ·
    refine ⟨18714435773987992806905623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99810324127935961636829989 18714435773987992806905623)
    ·
      refine ⟨28071653660981989210358435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18714435773987992806905623 28071653660981989210358435)
      ·
        refine ⟨42107480491472983815537653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28071653660981989210358435 42107480491472983815537653)
        ·
          refine ⟨3947576296075592232706655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42107480491472983815537653 3947576296075592232706655)
          ·
            refine ⟨5921364444113388349059983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3947576296075592232706655 5921364444113388349059983)
            ·
              refine ⟨8882046666170082523589975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5921364444113388349059983 8882046666170082523589975)
              ·
                refine ⟨13323069999255123785384963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8882046666170082523589975 13323069999255123785384963)
                ·
                  refine ⟨19984604998882685678077445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13323069999255123785384963 19984604998882685678077445)
                  ·
                    refine ⟨3747113437290503564639521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19984604998882685678077445 3747113437290503564639521)
                    ·
                      refine ⟨2810335077967877673479641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3747113437290503564639521 2810335077967877673479641)
                      ·
                        rfl

theorem cell23_5473108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 1, 4, 2].length) (baseStart_5473108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5473108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5473108 prefixEnd_5473108 := by exact prefixLift 5473108
  have htrace : WordTrace (prefixWord ++ tailWord_5473108) baseStart_5473108 baseEnd_5473108 := by
    simpa [prefixWord, tailWord_5473108, baseEnd_5473108] using wordTrace_append hprefix tailTrace_5473108
  have hstable : (prefixWord ++ tailWord_5473108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5473108).length < 2 ^ (prefixWord ++ tailWord_5473108).sum := by decide
  have hdescent : baseEnd_5473108 < baseStart_5473108 := by decide
  rcases family_descends (prefixWord ++ tailWord_5473108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5473147 : List Nat := [1, 1, 1, 1, 1, 5, 2, 1, 4, 4, 2]
def baseStart_5473147 : Nat := 118140960795 + 5473147 * 2 ^ 59
def prefixEnd_5473147 : Nat := 4983230072969 + 3 ^ 40 * 5473147 * 2
def baseEnd_5473147 : Nat := 2810355103713403020891961

theorem tailTrace_5473147 : CollatzResearch.WordTrace tailWord_5473147 prefixEnd_5473147 2810355103713403020891961 := by
  unfold tailWord_5473147
  simp only [CollatzResearch.WordTrace]
  refine ⟨199622070702730632934329695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133081380468487088622886463 199622070702730632934329695)
  ·
    refine ⟨299433106054095949401494543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199622070702730632934329695 299433106054095949401494543)
    ·
      refine ⟨449149659081143924102241815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299433106054095949401494543 449149659081143924102241815)
      ·
        refine ⟨673724488621715886153362723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 449149659081143924102241815 673724488621715886153362723)
        ·
          refine ⟨1010586732932573829230044085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 673724488621715886153362723 1010586732932573829230044085)
          ·
            refine ⟨94742506212428796490316633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1010586732932573829230044085 94742506212428796490316633)
            ·
              refine ⟨71056879659321597367737475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94742506212428796490316633 71056879659321597367737475)
              ·
                refine ⟨106585319488982396051606213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71056879659321597367737475 106585319488982396051606213)
                ·
                  refine ⟨19984747404184199259676165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 106585319488982396051606213 19984747404184199259676165)
                  ·
                    refine ⟨3747140138284537361189281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19984747404184199259676165 3747140138284537361189281)
                    ·
                      refine ⟨2810355103713403020891961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3747140138284537361189281 2810355103713403020891961)
                      ·
                        rfl

theorem cell23_5473147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 4, 2].length) (baseStart_5473147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5473147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5473147 prefixEnd_5473147 := by exact prefixLift 5473147
  have htrace : WordTrace (prefixWord ++ tailWord_5473147) baseStart_5473147 baseEnd_5473147 := by
    simpa [prefixWord, tailWord_5473147, baseEnd_5473147] using wordTrace_append hprefix tailTrace_5473147
  have hstable : (prefixWord ++ tailWord_5473147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5473147).length < 2 ^ (prefixWord ++ tailWord_5473147).sum := by decide
  have hdescent : baseEnd_5473147 < baseStart_5473147 := by decide
  rcases family_descends (prefixWord ++ tailWord_5473147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5473208 : List Nat := [2, 1, 2, 1, 2, 6, 2, 2, 1, 4]
def baseStart_5473208 : Nat := 118140960795 + 5473208 * 2 ^ 59
def prefixEnd_5473208 : Nat := 4983230072969 + 3 ^ 40 * 5473208 * 2
def baseEnd_5473208 : Nat := 936795475344442427409727

theorem tailTrace_5473208 : CollatzResearch.WordTrace tailWord_5473208 prefixEnd_5473208 936795475344442427409727 := by
  unfold tailWord_5473208
  simp only [CollatzResearch.WordTrace]
  refine ⟨99812147777754820176150139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133082863703673093568200185 99812147777754820176150139)
  ·
    refine ⟨149718221666632230264225209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99812147777754820176150139 149718221666632230264225209)
    ·
      refine ⟨112288666249974172698168907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149718221666632230264225209 112288666249974172698168907)
      ·
        refine ⟨168432999374961259047253361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112288666249974172698168907 168432999374961259047253361)
        ·
          refine ⟨126324749531220944285440021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168432999374961259047253361 126324749531220944285440021)
          ·
            refine ⟨5921472634275981763380001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 126324749531220944285440021 5921472634275981763380001)
            ·
              refine ⟨4441104475706986322535001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5921472634275981763380001 4441104475706986322535001)
              ·
                refine ⟨3330828356780239741901251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4441104475706986322535001 3330828356780239741901251)
                ·
                  refine ⟨4996242535170359612851877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3330828356780239741901251 4996242535170359612851877)
                  ·
                    refine ⟨936795475344442427409727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4996242535170359612851877 936795475344442427409727)
                    ·
                      rfl

theorem cell23_5473208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 2, 1, 4].length) (baseStart_5473208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5473208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5473208 prefixEnd_5473208 := by exact prefixLift 5473208
  have htrace : WordTrace (prefixWord ++ tailWord_5473208) baseStart_5473208 baseEnd_5473208 := by
    simpa [prefixWord, tailWord_5473208, baseEnd_5473208] using wordTrace_append hprefix tailTrace_5473208
  have hstable : (prefixWord ++ tailWord_5473208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5473208).length < 2 ^ (prefixWord ++ tailWord_5473208).sum := by decide
  have hdescent : baseEnd_5473208 < baseStart_5473208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5473208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5473234 : List Nat := [3, 2, 2, 3, 1, 1, 2, 1, 3, 5]
def baseStart_5473234 : Nat := 118140960795 + 5473234 * 2 ^ 59
def prefixEnd_5473234 : Nat := 4983230072969 + 3 ^ 40 * 5473234 * 2
def baseEnd_5473234 : Nat := 936799925510114726834687

theorem tailTrace_5473234 : CollatzResearch.WordTrace tailWord_5473234 prefixEnd_5473234 936799925510114726834687 := by
  unfold tailWord_5473234
  simp only [CollatzResearch.WordTrace]
  refine ⟨49906310963353861698186689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133083495902276964528497837 49906310963353861698186689)
  ·
    refine ⟨37429733222515396273640017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49906310963353861698186689 37429733222515396273640017)
    ·
      refine ⟨28072299916886547205230013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37429733222515396273640017 28072299916886547205230013)
      ·
        refine ⟨10527112468832455201961255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28072299916886547205230013 10527112468832455201961255)
        ·
          refine ⟨15790668703248682802941883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10527112468832455201961255 15790668703248682802941883)
          ·
            refine ⟨23686003054873024204412825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15790668703248682802941883 23686003054873024204412825)
            ·
              refine ⟨17764502291154768153309619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23686003054873024204412825 17764502291154768153309619)
              ·
                refine ⟨26646753436732152229964429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17764502291154768153309619 26646753436732152229964429)
                ·
                  refine ⟨9992532538774557086236661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26646753436732152229964429 9992532538774557086236661)
                  ·
                    refine ⟨936799925510114726834687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9992532538774557086236661 936799925510114726834687)
                    ·
                      rfl

theorem cell23_5473234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_5473234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5473234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5473234 prefixEnd_5473234 := by exact prefixLift 5473234
  have htrace : WordTrace (prefixWord ++ tailWord_5473234) baseStart_5473234 baseEnd_5473234 := by
    simpa [prefixWord, tailWord_5473234, baseEnd_5473234] using wordTrace_append hprefix tailTrace_5473234
  have hstable : (prefixWord ++ tailWord_5473234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5473234).length < 2 ^ (prefixWord ++ tailWord_5473234).sum := by decide
  have hdescent : baseEnd_5473234 < baseStart_5473234 := by decide
  rcases family_descends (prefixWord ++ tailWord_5473234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5473241 : List Nat := [1, 2, 1, 2, 5, 1, 3, 1, 2, 3, 2]
def baseStart_5473241 : Nat := 118140960795 + 5473241 * 2 ^ 59
def prefixEnd_5473241 : Nat := 4983230072969 + 3 ^ 40 * 5473241 * 2
def baseEnd_5473241 : Nat := 2810403370894925653116529

theorem tailTrace_5473241 : CollatzResearch.WordTrace tailWord_5473241 prefixEnd_5473241 2810403370894925653116529 := by
  unfold tailWord_5473241
  simp only [CollatzResearch.WordTrace]
  refine ⟨199625499164390086988251577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133083666109593391325501051 199625499164390086988251577)
  ·
    refine ⟨149719124373292565241188683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199625499164390086988251577 149719124373292565241188683)
    ·
      refine ⟨224578686559938847861783025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149719124373292565241188683 224578686559938847861783025)
      ·
        refine ⟨168434014919954135896337269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224578686559938847861783025 168434014919954135896337269)
        ·
          refine ⟨15790688898745700240281619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 168434014919954135896337269 15790688898745700240281619)
          ·
            refine ⟨23686033348118550360422429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15790688898745700240281619 23686033348118550360422429)
            ·
              refine ⟨8882262505544456385158411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23686033348118550360422429 8882262505544456385158411)
              ·
                refine ⟨13323393758316684577737617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8882262505544456385158411 13323393758316684577737617)
                ·
                  refine ⟨9992545318737513433303213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13323393758316684577737617 9992545318737513433303213)
                  ·
                    refine ⟨3747204494526567537488705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9992545318737513433303213 3747204494526567537488705)
                    ·
                      refine ⟨2810403370894925653116529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3747204494526567537488705 2810403370894925653116529)
                      ·
                        rfl

theorem cell23_5473241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 2, 3, 2].length) (baseStart_5473241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5473241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5473241 prefixEnd_5473241 := by exact prefixLift 5473241
  have htrace : WordTrace (prefixWord ++ tailWord_5473241) baseStart_5473241 baseEnd_5473241 := by
    simpa [prefixWord, tailWord_5473241, baseEnd_5473241] using wordTrace_append hprefix tailTrace_5473241
  have hstable : (prefixWord ++ tailWord_5473241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5473241).length < 2 ^ (prefixWord ++ tailWord_5473241).sum := by decide
  have hdescent : baseEnd_5473241 < baseStart_5473241 := by decide
  rcases family_descends (prefixWord ++ tailWord_5473241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5473291 : List Nat := [1, 1, 1, 1, 6, 3, 2, 2, 1, 2, 3]
def baseStart_5473291 : Nat := 118140960795 + 5473291 * 2 ^ 59
def prefixEnd_5473291 : Nat := 4983230072969 + 3 ^ 40 * 5473291 * 2
def baseEnd_5473291 : Nat := 2810429044927650457491299

theorem tailTrace_5473291 : CollatzResearch.WordTrace tailWord_5473291 prefixEnd_5473291 2810429044927650457491299 := by
  unfold tailWord_5473291
  simp only [CollatzResearch.WordTrace]
  refine ⟨199627322814208945527571727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133084881876139297018381151 199627322814208945527571727)
  ·
    refine ⟨299440984221313418291357591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199627322814208945527571727 299440984221313418291357591)
    ·
      refine ⟨449161476331970127437036387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299440984221313418291357591 449161476331970127437036387)
      ·
        refine ⟨673742214497955191155554581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 449161476331970127437036387 673742214497955191155554581)
        ·
          refine ⟨31581666304591649585416621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 673742214497955191155554581 31581666304591649585416621)
          ·
            refine ⟨11843124864221868594531233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31581666304591649585416621 11843124864221868594531233)
            ·
              refine ⟨8882343648166401445898425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11843124864221868594531233 8882343648166401445898425)
              ·
                refine ⟨6661757736124801084423819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8882343648166401445898425 6661757736124801084423819)
                ·
                  refine ⟨9992636604187201626635729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6661757736124801084423819 9992636604187201626635729)
                  ·
                    refine ⟨7494477453140401219976797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9992636604187201626635729 7494477453140401219976797)
                    ·
                      refine ⟨2810429044927650457491299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7494477453140401219976797 2810429044927650457491299)
                      ·
                        rfl

theorem cell23_5473291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 2, 1, 2, 3].length) (baseStart_5473291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5473291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5473291 prefixEnd_5473291 := by exact prefixLift 5473291
  have htrace : WordTrace (prefixWord ++ tailWord_5473291) baseStart_5473291 baseEnd_5473291 := by
    simpa [prefixWord, tailWord_5473291, baseEnd_5473291] using wordTrace_append hprefix tailTrace_5473291
  have hstable : (prefixWord ++ tailWord_5473291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5473291).length < 2 ^ (prefixWord ++ tailWord_5473291).sum := by decide
  have hdescent : baseEnd_5473291 < baseStart_5473291 := by decide
  rcases family_descends (prefixWord ++ tailWord_5473291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5473294 : List Nat := [4, 1, 1, 2, 2, 2, 4, 7]
def baseStart_5473294 : Nat := 118140960795 + 5473294 * 2 ^ 59
def prefixEnd_5473294 : Nat := 4983230072969 + 3 ^ 40 * 5473294 * 2
def baseEnd_5473294 : Nat := 104090021680356072064955

theorem tailTrace_5473294 : CollatzResearch.WordTrace tailWord_5473294 prefixEnd_5473294 104090021680356072064955 := by
  unfold tailWord_5473294
  simp only [CollatzResearch.WordTrace]
  refine ⟨24953429029149759629991367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133084954822132051359953957 24953429029149759629991367)
  ·
    refine ⟨37430143543724639444987051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24953429029149759629991367 37430143543724639444987051)
    ·
      refine ⟨56145215315586959167480577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37430143543724639444987051 56145215315586959167480577)
      ·
        refine ⟨42108911486690219375610433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56145215315586959167480577 42108911486690219375610433)
        ·
          refine ⟨31581683615017664531707825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42108911486690219375610433 31581683615017664531707825)
          ·
            refine ⟨23686262711263248398780869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31581683615017664531707825 23686262711263248398780869)
            ·
              refine ⟨4441174258361859074771413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23686262711263248398780869 4441174258361859074771413)
              ·
                refine ⟨104090021680356072064955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4441174258361859074771413 104090021680356072064955)
                ·
                  rfl

theorem cell23_5473294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 7].length) (baseStart_5473294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5473294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5473294 prefixEnd_5473294 := by exact prefixLift 5473294
  have htrace : WordTrace (prefixWord ++ tailWord_5473294) baseStart_5473294 baseEnd_5473294 := by
    simpa [prefixWord, tailWord_5473294, baseEnd_5473294] using wordTrace_append hprefix tailTrace_5473294
  have hstable : (prefixWord ++ tailWord_5473294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5473294).length < 2 ^ (prefixWord ++ tailWord_5473294).sum := by decide
  have hdescent : baseEnd_5473294 < baseStart_5473294 := by decide
  rcases family_descends (prefixWord ++ tailWord_5473294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5473317 : List Nat := [1, 3, 1, 2, 2, 2, 1, 2, 2, 2, 5]
def baseStart_5473317 : Nat := 118140960795 + 5473317 * 2 ^ 59
def prefixEnd_5473317 : Nat := 4983230072969 + 3 ^ 40 * 5473317 * 2
def baseEnd_5473317 : Nat := 2810442395424667355766179

theorem tailTrace_5473317 : CollatzResearch.WordTrace tailWord_5473317 prefixEnd_5473317 2810442395424667355766179 := by
  unfold tailWord_5473317
  simp only [CollatzResearch.WordTrace]
  refine ⟨199628271112114751968018205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133085514074743167978678803 199628271112114751968018205)
  ·
    refine ⟨74860601667043031988006827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199628271112114751968018205 74860601667043031988006827)
    ·
      refine ⟨112290902500564547982010241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74860601667043031988006827 112290902500564547982010241)
      ·
        refine ⟨84218176875423410986507681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112290902500564547982010241 84218176875423410986507681)
        ·
          refine ⟨63163632656567558239880761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84218176875423410986507681 63163632656567558239880761)
          ·
            refine ⟨47372724492425668679910571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63163632656567558239880761 47372724492425668679910571)
            ·
              refine ⟨71059086738638503019865857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47372724492425668679910571 71059086738638503019865857)
              ·
                refine ⟨53294315053978877264899393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71059086738638503019865857 53294315053978877264899393)
                ·
                  refine ⟨39970736290484157948674545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53294315053978877264899393 39970736290484157948674545)
                  ·
                    refine ⟨29978052217863118461505909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39970736290484157948674545 29978052217863118461505909)
                    ·
                      refine ⟨2810442395424667355766179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29978052217863118461505909 2810442395424667355766179)
                      ·
                        rfl

theorem cell23_5473317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_5473317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5473317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5473317 prefixEnd_5473317 := by exact prefixLift 5473317
  have htrace : WordTrace (prefixWord ++ tailWord_5473317) baseStart_5473317 baseEnd_5473317 := by
    simpa [prefixWord, tailWord_5473317, baseEnd_5473317] using wordTrace_append hprefix tailTrace_5473317
  have hstable : (prefixWord ++ tailWord_5473317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5473317).length < 2 ^ (prefixWord ++ tailWord_5473317).sum := by decide
  have hdescent : baseEnd_5473317 < baseStart_5473317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5473317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5473322 : List Nat := [3, 1, 4, 1, 4, 1, 1, 1, 3, 2, 2]
def baseStart_5473322 : Nat := 118140960795 + 5473322 * 2 ^ 59
def prefixEnd_5473322 : Nat := 4983230072969 + 3 ^ 40 * 5473322 * 2
def baseEnd_5473322 : Nat := 2810444962827939836203657

theorem tailTrace_5473322 : CollatzResearch.WordTrace tailWord_5473322 prefixEnd_5473322 2810444962827939836203657 := by
  unfold tailWord_5473322
  simp only [CollatzResearch.WordTrace]
  refine ⟨49907113369274159455487555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133085635651397758547966813 49907113369274159455487555)
  ·
    refine ⟨74860670053911239183231333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49907113369274159455487555 74860670053911239183231333)
    ·
      refine ⟨14036375635108357346855875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74860670053911239183231333 14036375635108357346855875)
      ·
        refine ⟨21054563452662536020283813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14036375635108357346855875 21054563452662536020283813)
        ·
          refine ⟨3947730647374225503803215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21054563452662536020283813 3947730647374225503803215)
          ·
            refine ⟨5921595971061338255704823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3947730647374225503803215 5921595971061338255704823)
            ·
              refine ⟨8882393956592007383557235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5921595971061338255704823 8882393956592007383557235)
              ·
                refine ⟨13323590934888011075335853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8882393956592007383557235 13323590934888011075335853)
                ·
                  refine ⟨4996346600583004153250945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13323590934888011075335853 4996346600583004153250945)
                  ·
                    refine ⟨3747259950437253114938209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4996346600583004153250945 3747259950437253114938209)
                    ·
                      refine ⟨2810444962827939836203657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3747259950437253114938209 2810444962827939836203657)
                      ·
                        rfl

theorem cell23_5473322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_5473322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5473322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5473322 prefixEnd_5473322 := by exact prefixLift 5473322
  have htrace : WordTrace (prefixWord ++ tailWord_5473322) baseStart_5473322 baseEnd_5473322 := by
    simpa [prefixWord, tailWord_5473322, baseEnd_5473322] using wordTrace_append hprefix tailTrace_5473322
  have hstable : (prefixWord ++ tailWord_5473322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5473322).length < 2 ^ (prefixWord ++ tailWord_5473322).sum := by decide
  have hdescent : baseEnd_5473322 < baseStart_5473322 := by decide
  rcases family_descends (prefixWord ++ tailWord_5473322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5473338 : List Nat := [3, 1, 1, 1, 3, 1, 6, 1, 2, 1, 3]
def baseStart_5473338 : Nat := 118140960795 + 5473338 * 2 ^ 59
def prefixEnd_5473338 : Nat := 4983230072969 + 3 ^ 40 * 5473338 * 2
def baseEnd_5473338 : Nat := 2810453178518411773603583

theorem tailTrace_5473338 : CollatzResearch.WordTrace tailWord_5473338 prefixEnd_5473338 2810453178518411773603583 := by
  unfold tailWord_5473338
  simp only [CollatzResearch.WordTrace]
  refine ⟨49907259261259668138633167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133086024696692448369688445 49907259261259668138633167)
  ·
    refine ⟨74860888891889502207949751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49907259261259668138633167 74860888891889502207949751)
    ·
      refine ⟨112291333337834253311924627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74860888891889502207949751 112291333337834253311924627)
      ·
        refine ⟨168437000006751379967886941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112291333337834253311924627 168437000006751379967886941)
        ·
          refine ⟨63163875002531767487957603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168437000006751379967886941 63163875002531767487957603)
          ·
            refine ⟨94745812503797651231936405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63163875002531767487957603 94745812503797651231936405)
            ·
              refine ⟨4441209961115514901497019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 94745812503797651231936405 4441209961115514901497019)
              ·
                refine ⟨6661814941673272352245529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4441209961115514901497019 6661814941673272352245529)
                ·
                  refine ⟨4996361206254954264184147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6661814941673272352245529 4996361206254954264184147)
                  ·
                    refine ⟨7494541809382431396276221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4996361206254954264184147 7494541809382431396276221)
                    ·
                      refine ⟨2810453178518411773603583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7494541809382431396276221 2810453178518411773603583)
                      ·
                        rfl

theorem cell23_5473338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 1, 2, 1, 3].length) (baseStart_5473338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5473338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5473338 prefixEnd_5473338 := by exact prefixLift 5473338
  have htrace : WordTrace (prefixWord ++ tailWord_5473338) baseStart_5473338 baseEnd_5473338 := by
    simpa [prefixWord, tailWord_5473338, baseEnd_5473338] using wordTrace_append hprefix tailTrace_5473338
  have hstable : (prefixWord ++ tailWord_5473338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5473338).length < 2 ^ (prefixWord ++ tailWord_5473338).sum := by decide
  have hdescent : baseEnd_5473338 < baseStart_5473338 := by decide
  rcases family_descends (prefixWord ++ tailWord_5473338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5473347 : List Nat := [1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 5]
def baseStart_5473347 : Nat := 118140960795 + 5473347 * 2 ^ 59
def prefixEnd_5473347 : Nat := 4983230072969 + 3 ^ 40 * 5473347 * 2
def baseEnd_5473347 : Nat := 2810457799844302238391041

theorem tailTrace_5473347 : CollatzResearch.WordTrace tailWord_5473347 prefixEnd_5473347 2810457799844302238391041 := by
  unfold tailWord_5473347
  simp only [CollatzResearch.WordTrace]
  refine ⟨199629365302006067091610295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133086243534670711394406863 199629365302006067091610295)
  ·
    refine ⟨299444047953009100637415443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199629365302006067091610295 299444047953009100637415443)
    ·
      refine ⟨449166071929513650956123165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299444047953009100637415443 449166071929513650956123165)
      ·
        refine ⟨168437276973567619108546187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 449166071929513650956123165 168437276973567619108546187)
        ·
          refine ⟨252655915460351428662819281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168437276973567619108546187 252655915460351428662819281)
          ·
            refine ⟨189491936595263571497114461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 252655915460351428662819281 189491936595263571497114461)
            ·
              refine ⟨71059476223223839311417923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 189491936595263571497114461 71059476223223839311417923)
              ·
                refine ⟨106589214334835758967126885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71059476223223839311417923 106589214334835758967126885)
                ·
                  refine ⟨19985477687781704806336291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 106589214334835758967126885 19985477687781704806336291)
                  ·
                    refine ⟨29978216531672557209504437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19985477687781704806336291 29978216531672557209504437)
                    ·
                      refine ⟨2810457799844302238391041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29978216531672557209504437 2810457799844302238391041)
                      ·
                        rfl

theorem cell23_5473347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 5].length) (baseStart_5473347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5473347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5473347 prefixEnd_5473347 := by exact prefixLift 5473347
  have htrace : WordTrace (prefixWord ++ tailWord_5473347) baseStart_5473347 baseEnd_5473347 := by
    simpa [prefixWord, tailWord_5473347, baseEnd_5473347] using wordTrace_append hprefix tailTrace_5473347
  have hstable : (prefixWord ++ tailWord_5473347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5473347).length < 2 ^ (prefixWord ++ tailWord_5473347).sum := by decide
  have hdescent : baseEnd_5473347 < baseStart_5473347 := by decide
  rcases family_descends (prefixWord ++ tailWord_5473347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5473361 : List Nat := [1, 2, 2, 1, 3, 1, 2, 1, 6, 2, 2]
def baseStart_5473361 : Nat := 118140960795 + 5473361 * 2 ^ 59
def prefixEnd_5473361 : Nat := 4983230072969 + 3 ^ 40 * 5473361 * 2
def baseEnd_5473361 : Nat := 2810464988573465183615977

theorem tailTrace_5473361 : CollatzResearch.WordTrace tailWord_5473361 prefixEnd_5473361 2810464988573465183615977 := by
  unfold tailWord_5473361
  simp only [CollatzResearch.WordTrace]
  refine ⟨199629875923955347482619937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133086583949303564988413291 199629875923955347482619937)
  ·
    refine ⟨149722406942966510611964953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199629875923955347482619937 149722406942966510611964953)
    ·
      refine ⟨112291805207224882958973715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149722406942966510611964953 112291805207224882958973715)
      ·
        refine ⟨168437707810837324438460573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112291805207224882958973715 168437707810837324438460573)
        ·
          refine ⟨63164140429063996664422715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168437707810837324438460573 63164140429063996664422715)
          ·
            refine ⟨94746210643595994996634073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63164140429063996664422715 94746210643595994996634073)
            ·
              refine ⟨71059657982696996247475555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94746210643595994996634073 71059657982696996247475555)
              ·
                refine ⟨106589486974045494371213333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71059657982696996247475555 106589486974045494371213333)
                ·
                  refine ⟨4996382201908382548650625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 106589486974045494371213333 4996382201908382548650625)
                  ·
                    refine ⟨3747286651431286911487969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4996382201908382548650625 3747286651431286911487969)
                    ·
                      refine ⟨2810464988573465183615977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3747286651431286911487969 2810464988573465183615977)
                      ·
                        rfl

theorem cell23_5473361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 6, 2, 2].length) (baseStart_5473361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5473361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5473361 prefixEnd_5473361 := by exact prefixLift 5473361
  have htrace : WordTrace (prefixWord ++ tailWord_5473361) baseStart_5473361 baseEnd_5473361 := by
    simpa [prefixWord, tailWord_5473361, baseEnd_5473361] using wordTrace_append hprefix tailTrace_5473361
  have hstable : (prefixWord ++ tailWord_5473361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5473361).length < 2 ^ (prefixWord ++ tailWord_5473361).sum := by decide
  have hdescent : baseEnd_5473361 < baseStart_5473361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5473361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5473364 : List Nat := [2, 4, 1, 1, 1, 1, 4, 1, 2, 1, 5]
def baseStart_5473364 : Nat := 118140960795 + 5473364 * 2 ^ 59
def prefixEnd_5473364 : Nat := 4983230072969 + 3 ^ 40 * 5473364 * 2
def baseEnd_5473364 : Nat := 2810466529015428671878463

theorem tailTrace_5473364 : CollatzResearch.WordTrace tailWord_5473364 prefixEnd_5473364 2810466529015428671878463 := by
  unfold tailWord_5473364
  simp only [CollatzResearch.WordTrace]
  refine ⟨99814992671472239497489573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133086656895296319329986097 99814992671472239497489573)
  ·
    refine ⟨18715311125901044905779295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99814992671472239497489573 18715311125901044905779295)
    ·
      refine ⟨28072966688851567358668943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18715311125901044905779295 28072966688851567358668943)
      ·
        refine ⟨42109450033277351038003415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28072966688851567358668943 42109450033277351038003415)
        ·
          refine ⟨63164175049916026557005123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42109450033277351038003415 63164175049916026557005123)
          ·
            refine ⟨94746262574874039835507685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63164175049916026557005123 94746262574874039835507685)
            ·
              refine ⟨17764924232788882469157691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94746262574874039835507685 17764924232788882469157691)
              ·
                refine ⟨26647386349183323703736537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17764924232788882469157691 26647386349183323703736537)
                ·
                  refine ⟨19985539761887492777802403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26647386349183323703736537 19985539761887492777802403)
                  ·
                    refine ⟨29978309642831239166703605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19985539761887492777802403 29978309642831239166703605)
                    ·
                      refine ⟨2810466529015428671878463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29978309642831239166703605 2810466529015428671878463)
                      ·
                        rfl

theorem cell23_5473364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_5473364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5473364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5473364 prefixEnd_5473364 := by exact prefixLift 5473364
  have htrace : WordTrace (prefixWord ++ tailWord_5473364) baseStart_5473364 baseEnd_5473364 := by
    simpa [prefixWord, tailWord_5473364, baseEnd_5473364] using wordTrace_append hprefix tailTrace_5473364
  have hstable : (prefixWord ++ tailWord_5473364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5473364).length < 2 ^ (prefixWord ++ tailWord_5473364).sum := by decide
  have hdescent : baseEnd_5473364 < baseStart_5473364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5473364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5473377 : List Nat := [1, 2, 3, 1, 1, 2, 2, 1, 1, 2, 7]
def baseStart_5473377 : Nat := 118140960795 + 5473377 * 2 ^ 59
def prefixEnd_5473377 : Nat := 4983230072969 + 3 ^ 40 * 5473377 * 2
def baseEnd_5473377 : Nat := 2810473204263937121015903

theorem tailTrace_5473377 : CollatzResearch.WordTrace tailWord_5473377 prefixEnd_5473377 2810473204263937121015903 := by
  unfold tailWord_5473377
  simp only [CollatzResearch.WordTrace]
  refine ⟨199630459491897382215202385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133086972994598254810134923 199630459491897382215202385)
  ·
    refine ⟨149722844618923036661401789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199630459491897382215202385 149722844618923036661401789)
    ·
      refine ⟨56146066732096138748025671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149722844618923036661401789 56146066732096138748025671)
      ·
        refine ⟨84219100098144208122038507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56146066732096138748025671 84219100098144208122038507)
        ·
          refine ⟨126328650147216312183057761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84219100098144208122038507 126328650147216312183057761)
          ·
            refine ⟨94746487610412234137293321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126328650147216312183057761 94746487610412234137293321)
            ·
              refine ⟨71059865707809175602969991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94746487610412234137293321 71059865707809175602969991)
              ·
                refine ⟨106589798561713763404454987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71059865707809175602969991 106589798561713763404454987)
                ·
                  refine ⟨159884697842570645106682481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106589798561713763404454987 159884697842570645106682481)
                  ·
                    refine ⟨119913523381927983830011861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 159884697842570645106682481 119913523381927983830011861)
                    ·
                      refine ⟨2810473204263937121015903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 119913523381927983830011861 2810473204263937121015903)
                      ·
                        rfl

theorem cell23_5473377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_5473377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5473377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5473377 prefixEnd_5473377 := by exact prefixLift 5473377
  have htrace : WordTrace (prefixWord ++ tailWord_5473377) baseStart_5473377 baseEnd_5473377 := by
    simpa [prefixWord, tailWord_5473377, baseEnd_5473377] using wordTrace_append hprefix tailTrace_5473377
  have hstable : (prefixWord ++ tailWord_5473377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5473377).length < 2 ^ (prefixWord ++ tailWord_5473377).sum := by decide
  have hdescent : baseEnd_5473377 < baseStart_5473377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5473377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5473407 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 5]
def baseStart_5473407 : Nat := 118140960795 + 5473407 * 2 ^ 59
def prefixEnd_5473407 : Nat := 4983230072969 + 3 ^ 40 * 5473407 * 2
def baseEnd_5473407 : Nat := 2810488608683572003640765

theorem tailTrace_5473407 : CollatzResearch.WordTrace tailWord_5473407 prefixEnd_5473407 2810488608683572003640765 := by
  unfold tailWord_5473407
  simp only [CollatzResearch.WordTrace]
  refine ⟨199631553681788697338794475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133087702454525798225862983 199631553681788697338794475)
  ·
    refine ⟨299447330522683046008191713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199631553681788697338794475 299447330522683046008191713)
    ·
      refine ⟨224585497892012284506143785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299447330522683046008191713 224585497892012284506143785)
      ·
        refine ⟨168439123419009213379607839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224585497892012284506143785 168439123419009213379607839)
        ·
          refine ⟨252658685128513820069411759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168439123419009213379607839 252658685128513820069411759)
          ·
            refine ⟨378988027692770730104117639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252658685128513820069411759 378988027692770730104117639)
            ·
              refine ⟨568482041539156095156176459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 378988027692770730104117639 568482041539156095156176459)
              ·
                refine ⟨852723062308734142734264689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 568482041539156095156176459 852723062308734142734264689)
                ·
                  refine ⟨639542296731550607050698517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 852723062308734142734264689 639542296731550607050698517)
                  ·
                    refine ⟨29978545159291434705501493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 639542296731550607050698517 29978545159291434705501493)
                    ·
                      refine ⟨2810488608683572003640765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29978545159291434705501493 2810488608683572003640765)
                      ·
                        rfl

theorem cell23_5473407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 5].length) (baseStart_5473407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5473407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5473407 prefixEnd_5473407 := by exact prefixLift 5473407
  have htrace : WordTrace (prefixWord ++ tailWord_5473407) baseStart_5473407 baseEnd_5473407 := by
    simpa [prefixWord, tailWord_5473407, baseEnd_5473407] using wordTrace_append hprefix tailTrace_5473407
  have hstable : (prefixWord ++ tailWord_5473407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5473407).length < 2 ^ (prefixWord ++ tailWord_5473407).sum := by decide
  have hdescent : baseEnd_5473407 < baseStart_5473407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5473407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5473518 : List Nat := [4, 1, 2, 1, 1, 1, 2, 4, 3, 1, 3]
def baseStart_5473518 : Nat := 118140960795 + 5473518 * 2 ^ 59
def prefixEnd_5473518 : Nat := 4983230072969 + 3 ^ 40 * 5473518 * 2
def baseEnd_5473518 : Nat := 2810545605036221069352755

theorem tailTrace_5473518 : CollatzResearch.WordTrace tailWord_5473518 prefixEnd_5473518 2810545605036221069352755 := by
  unfold tailWord_5473518
  simp only [CollatzResearch.WordTrace]
  refine ⟨24954450273048320412010651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133090401456257708864056805 24954450273048320412010651)
  ·
    refine ⟨37431675409572480618015977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24954450273048320412010651 37431675409572480618015977)
    ·
      refine ⟨28073756557179360463511983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37431675409572480618015977 28073756557179360463511983)
      ·
        refine ⟨42110634835769040695267975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28073756557179360463511983 42110634835769040695267975)
        ·
          refine ⟨63165952253653561042901963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42110634835769040695267975 63165952253653561042901963)
          ·
            refine ⟨94748928380480341564352945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63165952253653561042901963 94748928380480341564352945)
            ·
              refine ⟨71061696285360256173264709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94748928380480341564352945 71061696285360256173264709)
              ·
                refine ⟨13324068053505048032487133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71061696285360256173264709 13324068053505048032487133)
                ·
                  refine ⟨4996525520064393012182675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13324068053505048032487133 4996525520064393012182675)
                  ·
                    refine ⟨7494788280096589518274013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4996525520064393012182675 7494788280096589518274013)
                    ·
                      refine ⟨2810545605036221069352755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7494788280096589518274013 2810545605036221069352755)
                      ·
                        rfl

theorem cell23_5473518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_5473518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5473518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5473518 prefixEnd_5473518 := by exact prefixLift 5473518
  have htrace : WordTrace (prefixWord ++ tailWord_5473518) baseStart_5473518 baseEnd_5473518 := by
    simpa [prefixWord, tailWord_5473518, baseEnd_5473518] using wordTrace_append hprefix tailTrace_5473518
  have hstable : (prefixWord ++ tailWord_5473518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5473518).length < 2 ^ (prefixWord ++ tailWord_5473518).sum := by decide
  have hdescent : baseEnd_5473518 < baseStart_5473518 := by decide
  rcases family_descends (prefixWord ++ tailWord_5473518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5473568 : List Nat := [2, 1, 1, 5, 3, 1, 2, 1, 1, 6]
def baseStart_5473568 : Nat := 118140960795 + 5473568 * 2 ^ 59
def prefixEnd_5473568 : Nat := 4983230072969 + 3 ^ 40 * 5473568 * 2
def baseEnd_5473568 : Nat := 936857093022981957909175

theorem tailTrace_5473568 : CollatzResearch.WordTrace tailWord_5473568 prefixEnd_5473568 936857093022981957909175 := by
  unfold tailWord_5473568
  simp only [CollatzResearch.WordTrace]
  refine ⟨99818712917102710917702679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133091617222803614556936905 99818712917102710917702679)
  ·
    refine ⟨149728069375654066376554019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99818712917102710917702679 149728069375654066376554019)
    ·
      refine ⟨224592104063481099564831029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149728069375654066376554019 224592104063481099564831029)
      ·
        refine ⟨21055509755951353084202909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 224592104063481099564831029 21055509755951353084202909)
        ·
          refine ⟨7895816158481757406576091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21055509755951353084202909 7895816158481757406576091)
          ·
            refine ⟨11843724237722636109864137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7895816158481757406576091 11843724237722636109864137)
            ·
              refine ⟨8882793178291977082398103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11843724237722636109864137 8882793178291977082398103)
              ·
                refine ⟨13324189767437965623597155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8882793178291977082398103 13324189767437965623597155)
                ·
                  refine ⟨19986284651156948435395733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13324189767437965623597155 19986284651156948435395733)
                  ·
                    refine ⟨936857093022981957909175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19986284651156948435395733 936857093022981957909175)
                    ·
                      rfl

theorem cell23_5473568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 1, 6].length) (baseStart_5473568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5473568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5473568 prefixEnd_5473568 := by exact prefixLift 5473568
  have htrace : WordTrace (prefixWord ++ tailWord_5473568) baseStart_5473568 baseEnd_5473568 := by
    simpa [prefixWord, tailWord_5473568, baseEnd_5473568] using wordTrace_append hprefix tailTrace_5473568
  have hstable : (prefixWord ++ tailWord_5473568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5473568).length < 2 ^ (prefixWord ++ tailWord_5473568).sum := by decide
  have hdescent : baseEnd_5473568 < baseStart_5473568 := by decide
  rcases family_descends (prefixWord ++ tailWord_5473568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5473571 : List Nat := [1, 1, 1, 4, 2, 3, 1, 3, 1, 2, 4]
def baseStart_5473571 : Nat := 118140960795 + 5473571 * 2 ^ 59
def prefixEnd_5473571 : Nat := 4983230072969 + 3 ^ 40 * 5473571 * 2
def baseEnd_5473571 : Nat := 2810572819510909361990011

theorem tailTrace_5473571 : CollatzResearch.WordTrace tailWord_5473571 prefixEnd_5473571 2810572819510909361990011 := by
  unfold tailWord_5473571
  simp only [CollatzResearch.WordTrace]
  refine ⟨199637535253194553347764567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133091690168796368898509711 199637535253194553347764567)
  ·
    refine ⟨299456302879791830021646851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199637535253194553347764567 299456302879791830021646851)
    ·
      refine ⟨449184454319687745032470277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299456302879791830021646851 449184454319687745032470277)
      ·
        refine ⟨84222085184941452193588177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 449184454319687745032470277 84222085184941452193588177)
        ·
          refine ⟨63166563888706089145191133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84222085184941452193588177 63166563888706089145191133)
          ·
            refine ⟨23687461458264783429446675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63166563888706089145191133 23687461458264783429446675)
            ·
              refine ⟨35531192187397175144170013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23687461458264783429446675 35531192187397175144170013)
              ·
                refine ⟨13324197070273940679063755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35531192187397175144170013 13324197070273940679063755)
                ·
                  refine ⟨19986295605410911018595633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13324197070273940679063755 19986295605410911018595633)
                  ·
                    refine ⟨14989721704058183263946725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19986295605410911018595633 14989721704058183263946725)
                    ·
                      refine ⟨2810572819510909361990011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14989721704058183263946725 2810572819510909361990011)
                      ·
                        rfl

theorem cell23_5473571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_5473571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5473571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5473571 prefixEnd_5473571 := by exact prefixLift 5473571
  have htrace : WordTrace (prefixWord ++ tailWord_5473571) baseStart_5473571 baseEnd_5473571 := by
    simpa [prefixWord, tailWord_5473571, baseEnd_5473571] using wordTrace_append hprefix tailTrace_5473571
  have hstable : (prefixWord ++ tailWord_5473571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5473571).length < 2 ^ (prefixWord ++ tailWord_5473571).sum := by decide
  have hdescent : baseEnd_5473571 < baseStart_5473571 := by decide
  rcases family_descends (prefixWord ++ tailWord_5473571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5473588 : List Nat := [2, 5, 1, 1, 1, 1, 1, 4, 1, 2, 4]
def baseStart_5473588 : Nat := 118140960795 + 5473588 * 2 ^ 59
def prefixEnd_5473588 : Nat := 4983230072969 + 3 ^ 40 * 5473588 * 2
def baseEnd_5473588 : Nat := 2810581548682035795477433

theorem tailTrace_5473588 : CollatzResearch.WordTrace tailWord_5473588 prefixEnd_5473588 2810581548682035795477433 := by
  unfold tailWord_5473588
  simp only [CollatzResearch.WordTrace]
  refine ⟨99819077647066482625566709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133092103529421976834088945 99819077647066482625566709)
  ·
    refine ⟨9358038529412482746146879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 99819077647066482625566709 9358038529412482746146879)
    ·
      refine ⟨14037057794118724119220319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9358038529412482746146879 14037057794118724119220319)
      ·
        refine ⟨21055586691178086178830479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14037057794118724119220319 21055586691178086178830479)
        ·
          refine ⟨31583380036767129268245719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21055586691178086178830479 31583380036767129268245719)
          ·
            refine ⟨47375070055150693902368579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31583380036767129268245719 47375070055150693902368579)
            ·
              refine ⟨71062605082726040853552869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47375070055150693902368579 71062605082726040853552869)
              ·
                refine ⟨13324238453011132660041163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71062605082726040853552869 13324238453011132660041163)
                ·
                  refine ⟨19986357679516698990061745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13324238453011132660041163 19986357679516698990061745)
                  ·
                    refine ⟨14989768259637524242546309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19986357679516698990061745 14989768259637524242546309)
                    ·
                      refine ⟨2810581548682035795477433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14989768259637524242546309 2810581548682035795477433)
                      ·
                        rfl

theorem cell23_5473588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_5473588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5473588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5473588 prefixEnd_5473588 := by exact prefixLift 5473588
  have htrace : WordTrace (prefixWord ++ tailWord_5473588) baseStart_5473588 baseEnd_5473588 := by
    simpa [prefixWord, tailWord_5473588, baseEnd_5473588] using wordTrace_append hprefix tailTrace_5473588
  have hstable : (prefixWord ++ tailWord_5473588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5473588).length < 2 ^ (prefixWord ++ tailWord_5473588).sum := by decide
  have hdescent : baseEnd_5473588 < baseStart_5473588 := by decide
  rcases family_descends (prefixWord ++ tailWord_5473588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5473635 : List Nat := [1, 1, 1, 5, 2, 2, 1, 4, 1, 3, 2]
def baseStart_5473635 : Nat := 118140960795 + 5473635 * 2 ^ 59
def prefixEnd_5473635 : Nat := 4983230072969 + 3 ^ 40 * 5473635 * 2
def baseEnd_5473635 : Nat := 2810605682272797111589717

theorem tailTrace_5473635 : CollatzResearch.WordTrace tailWord_5473635 prefixEnd_5473635 2810605682272797111589717 := by
  unfold tailWord_5473635
  simp only [CollatzResearch.WordTrace]
  refine ⟨199639869524962692278094359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133093246349975128185396239 199639869524962692278094359)
  ·
    refine ⟨299459804287444038417141539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199639869524962692278094359 299459804287444038417141539)
    ·
      refine ⟨449189706431166057625712309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299459804287444038417141539 449189706431166057625712309)
      ·
        refine ⟨42111534977921817902410529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 449189706431166057625712309 42111534977921817902410529)
        ·
          refine ⟨31583651233441363426807897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42111534977921817902410529 31583651233441363426807897)
          ·
            refine ⟨23687738425081022570105923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31583651233441363426807897 23687738425081022570105923)
            ·
              refine ⟨35531607637621533855158885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23687738425081022570105923 35531607637621533855158885)
              ·
                refine ⟨6662176432054037597842291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35531607637621533855158885 6662176432054037597842291)
                ·
                  refine ⟨9993264648081056396763437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6662176432054037597842291 9993264648081056396763437)
                  ·
                    refine ⟨3747474243030396148786289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9993264648081056396763437 3747474243030396148786289)
                    ·
                      refine ⟨2810605682272797111589717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3747474243030396148786289 2810605682272797111589717)
                      ·
                        rfl

theorem cell23_5473635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 4, 1, 3, 2].length) (baseStart_5473635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5473635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5473635 prefixEnd_5473635 := by exact prefixLift 5473635
  have htrace : WordTrace (prefixWord ++ tailWord_5473635) baseStart_5473635 baseEnd_5473635 := by
    simpa [prefixWord, tailWord_5473635, baseEnd_5473635] using wordTrace_append hprefix tailTrace_5473635
  have hstable : (prefixWord ++ tailWord_5473635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5473635).length < 2 ^ (prefixWord ++ tailWord_5473635).sum := by decide
  have hdescent : baseEnd_5473635 < baseStart_5473635 := by decide
  rcases family_descends (prefixWord ++ tailWord_5473635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5473648 : List Nat := [2, 1, 1, 1, 4, 2, 2, 1, 3, 4, 2]
def baseStart_5473648 : Nat := 118140960795 + 5473648 * 2 ^ 59
def prefixEnd_5473648 : Nat := 4983230072969 + 3 ^ 40 * 5473648 * 2
def baseEnd_5473648 : Nat := 2810612357521305560727157

theorem tailTrace_5473648 : CollatzResearch.WordTrace tailWord_5473648 prefixEnd_5473648 2810612357521305560727157 := by
  unfold tailWord_5473648
  simp only [CollatzResearch.WordTrace]
  refine ⟨99820171836957797749158799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133093562449277063665545065 99820171836957797749158799)
  ·
    refine ⟨149730257755436696623738199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99820171836957797749158799 149730257755436696623738199)
    ·
      refine ⟨224595386633155044935607299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149730257755436696623738199 224595386633155044935607299)
      ·
        refine ⟨336893079949732567403410949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224595386633155044935607299 336893079949732567403410949)
        ·
          refine ⟨63167452490574856388139553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 336893079949732567403410949 63167452490574856388139553)
          ·
            refine ⟨47375589367931142291104665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63167452490574856388139553 47375589367931142291104665)
            ·
              refine ⟨35531692025948356718328499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47375589367931142291104665 35531692025948356718328499)
              ·
                refine ⟨53297538038922535077492749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35531692025948356718328499 53297538038922535077492749)
                ·
                  refine ⟨19986576764595950654059781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53297538038922535077492749 19986576764595950654059781)
                  ·
                    refine ⟨3747483143361740747636209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19986576764595950654059781 3747483143361740747636209)
                    ·
                      refine ⟨2810612357521305560727157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3747483143361740747636209 2810612357521305560727157)
                      ·
                        rfl

theorem cell23_5473648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 3, 4, 2].length) (baseStart_5473648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5473648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5473648 prefixEnd_5473648 := by exact prefixLift 5473648
  have htrace : WordTrace (prefixWord ++ tailWord_5473648) baseStart_5473648 baseEnd_5473648 := by
    simpa [prefixWord, tailWord_5473648, baseEnd_5473648] using wordTrace_append hprefix tailTrace_5473648
  have hstable : (prefixWord ++ tailWord_5473648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5473648).length < 2 ^ (prefixWord ++ tailWord_5473648).sum := by decide
  have hdescent : baseEnd_5473648 < baseStart_5473648 := by decide
  rcases family_descends (prefixWord ++ tailWord_5473648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5473751 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 6]
def baseStart_5473751 : Nat := 118140960795 + 5473751 * 2 ^ 59
def prefixEnd_5473751 : Nat := 4983230072969 + 3 ^ 40 * 5473751 * 2
def baseEnd_5473751 : Nat := 2810665246028718657739183

theorem tailTrace_5473751 : CollatzResearch.WordTrace tailWord_5473751 prefixEnd_5473751 2810665246028718657739183 := by
  unfold tailWord_5473751
  simp only [CollatzResearch.WordTrace]
  refine ⟨199644100392542444089317107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133096066928361629392878071 199644100392542444089317107)
  ·
    refine ⟨299466150588813666133975661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199644100392542444089317107 299466150588813666133975661)
    ·
      refine ⟨112299806470805124800240873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 299466150588813666133975661 112299806470805124800240873)
      ·
        refine ⟨84224854853103843600180655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112299806470805124800240873 84224854853103843600180655)
        ·
          refine ⟨126337282279655765400270983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84224854853103843600180655 126337282279655765400270983)
          ·
            refine ⟨189505923419483648100406475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126337282279655765400270983 189505923419483648100406475)
            ·
              refine ⟨284258885129225472150609713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189505923419483648100406475 284258885129225472150609713)
              ·
                refine ⟨213194163846919104112957285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 284258885129225472150609713 213194163846919104112957285)
                ·
                  refine ⟨39973905721297332021179491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 213194163846919104112957285 39973905721297332021179491)
                  ·
                    refine ⟨59960858581945998031769237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39973905721297332021179491 59960858581945998031769237)
                    ·
                      refine ⟨2810665246028718657739183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59960858581945998031769237 2810665246028718657739183)
                      ·
                        rfl

theorem cell23_5473751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_5473751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5473751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5473751 prefixEnd_5473751 := by exact prefixLift 5473751
  have htrace : WordTrace (prefixWord ++ tailWord_5473751) baseStart_5473751 baseEnd_5473751 := by
    simpa [prefixWord, tailWord_5473751, baseEnd_5473751] using wordTrace_append hprefix tailTrace_5473751
  have hstable : (prefixWord ++ tailWord_5473751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5473751).length < 2 ^ (prefixWord ++ tailWord_5473751).sum := by decide
  have hdescent : baseEnd_5473751 < baseStart_5473751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5473751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5473782 : List Nat := [5, 1, 1, 1, 2, 3, 2, 1, 3, 4]
def baseStart_5473782 : Nat := 118140960795 + 5473782 * 2 ^ 59
def prefixEnd_5473782 : Nat := 4983230072969 + 3 ^ 40 * 5473782 * 2
def baseEnd_5473782 : Nat := 936893721309669345483847

theorem tailTrace_5473782 : CollatzResearch.WordTrace tailWord_5473782 prefixEnd_5473782 936893721309669345483847 := by
  unfold tailWord_5473782
  simp only [CollatzResearch.WordTrace]
  refine ⟨12477826940964383523980975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 133096820703620090922463733 12477826940964383523980975)
  ·
    refine ⟨18716740411446575285971463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12477826940964383523980975 18716740411446575285971463)
    ·
      refine ⟨28075110617169862928957195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18716740411446575285971463 28075110617169862928957195)
      ·
        refine ⟨42112665925754794393435793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28075110617169862928957195 42112665925754794393435793)
        ·
          refine ⟨31584499444316095795076845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42112665925754794393435793 31584499444316095795076845)
          ·
            refine ⟨11844187291618535923153817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31584499444316095795076845 11844187291618535923153817)
            ·
              refine ⟨8883140468713901942365363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11844187291618535923153817 8883140468713901942365363)
              ·
                refine ⟨13324710703070852913548045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8883140468713901942365363 13324710703070852913548045)
                ·
                  refine ⟨4996766513651569842580517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13324710703070852913548045 4996766513651569842580517)
                  ·
                    refine ⟨936893721309669345483847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4996766513651569842580517 936893721309669345483847)
                    ·
                      rfl

theorem cell23_5473782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_5473782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5473782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5473782 prefixEnd_5473782 := by exact prefixLift 5473782
  have htrace : WordTrace (prefixWord ++ tailWord_5473782) baseStart_5473782 baseEnd_5473782 := by
    simpa [prefixWord, tailWord_5473782, baseEnd_5473782] using wordTrace_append hprefix tailTrace_5473782
  have hstable : (prefixWord ++ tailWord_5473782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5473782).length < 2 ^ (prefixWord ++ tailWord_5473782).sum := by decide
  have hdescent : baseEnd_5473782 < baseStart_5473782 := by decide
  rcases family_descends (prefixWord ++ tailWord_5473782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5473791 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 2, 9]
def baseStart_5473791 : Nat := 118140960795 + 5473791 * 2 ^ 59
def prefixEnd_5473791 : Nat := 4983230072969 + 3 ^ 40 * 5473791 * 2
def baseEnd_5473791 : Nat := 936895261751632833746333

theorem tailTrace_5473791 : CollatzResearch.WordTrace tailWord_5473791 prefixEnd_5473791 936895261751632833746333 := by
  unfold tailWord_5473791
  simp only [CollatzResearch.WordTrace]
  refine ⟨199645559312397530920773227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133097039541598353947182151 199645559312397530920773227)
  ·
    refine ⟨299468338968596296381159841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199645559312397530920773227 299468338968596296381159841)
    ·
      refine ⟨224601254226447222285869881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299468338968596296381159841 224601254226447222285869881)
      ·
        refine ⟨168450940669835416714402411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224601254226447222285869881 168450940669835416714402411)
        ·
          refine ⟨252676411004753125071603617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168450940669835416714402411 252676411004753125071603617)
          ·
            refine ⟨189507308253564843803702713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 252676411004753125071603617 189507308253564843803702713)
            ·
              refine ⟨142130481190173632852777035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189507308253564843803702713 142130481190173632852777035)
              ·
                refine ⟨213195721785260449279165553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142130481190173632852777035 213195721785260449279165553)
                ·
                  refine ⟨159896791338945336959374165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 213195721785260449279165553 159896791338945336959374165)
                  ·
                    refine ⟨936895261751632833746333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 159896791338945336959374165 936895261751632833746333)
                    ·
                      rfl

theorem cell23_5473791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 9].length) (baseStart_5473791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5473791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5473791 prefixEnd_5473791 := by exact prefixLift 5473791
  have htrace : WordTrace (prefixWord ++ tailWord_5473791) baseStart_5473791 baseEnd_5473791 := by
    simpa [prefixWord, tailWord_5473791, baseEnd_5473791] using wordTrace_append hprefix tailTrace_5473791
  have hstable : (prefixWord ++ tailWord_5473791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5473791).length < 2 ^ (prefixWord ++ tailWord_5473791).sum := by decide
  have hdescent : baseEnd_5473791 < baseStart_5473791 := by decide
  rcases family_descends (prefixWord ++ tailWord_5473791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5473816 : List Nat := [2, 1, 2, 3, 5, 1, 1, 3, 1, 4]
def baseStart_5473816 : Nat := 118140960795 + 5473816 * 2 ^ 59
def prefixEnd_5473816 : Nat := 4983230072969 + 3 ^ 40 * 5473816 * 2
def baseEnd_5473816 : Nat := 936899540757086967808795

theorem tailTrace_5473816 : CollatzResearch.WordTrace tailWord_5473816 prefixEnd_5473816 936899540757086967808795 := by
  unfold tailWord_5473816
  simp only [CollatzResearch.WordTrace]
  refine ⟨99823235568653480095216651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133097647424871306793622201 99823235568653480095216651)
  ·
    refine ⟨149734853352980220142824977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99823235568653480095216651 149734853352980220142824977)
    ·
      refine ⟨112301140014735165107118733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149734853352980220142824977 112301140014735165107118733)
      ·
        refine ⟨42112927505525686915169525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112301140014735165107118733 42112927505525686915169525)
        ·
          refine ⟨3948086953643033148297143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42112927505525686915169525 3948086953643033148297143)
          ·
            refine ⟨5922130430464549722445715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3948086953643033148297143 5922130430464549722445715)
            ·
              refine ⟨8883195645696824583668573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5922130430464549722445715 8883195645696824583668573)
              ·
                refine ⟨3331198367136309218875715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8883195645696824583668573 3331198367136309218875715)
                ·
                  refine ⟨4996797550704463828313573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3331198367136309218875715 4996797550704463828313573)
                  ·
                    refine ⟨936899540757086967808795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4996797550704463828313573 936899540757086967808795)
                    ·
                      rfl

theorem cell23_5473816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 3, 1, 4].length) (baseStart_5473816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5473816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5473816 prefixEnd_5473816 := by exact prefixLift 5473816
  have htrace : WordTrace (prefixWord ++ tailWord_5473816) baseStart_5473816 baseEnd_5473816 := by
    simpa [prefixWord, tailWord_5473816, baseEnd_5473816] using wordTrace_append hprefix tailTrace_5473816
  have hstable : (prefixWord ++ tailWord_5473816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5473816).length < 2 ^ (prefixWord ++ tailWord_5473816).sum := by decide
  have hdescent : baseEnd_5473816 < baseStart_5473816 := by decide
  rcases family_descends (prefixWord ++ tailWord_5473816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5473825 : List Nat := [1, 2, 3, 2, 2, 2, 2, 3, 1, 5]
def baseStart_5473825 : Nat := 118140960795 + 5473825 * 2 ^ 59
def prefixEnd_5473825 : Nat := 4983230072969 + 3 ^ 40 * 5473825 * 2
def baseEnd_5473825 : Nat := 936901081199050456071281

theorem tailTrace_5473825 : CollatzResearch.WordTrace tailWord_5473825 prefixEnd_5473825 936901081199050456071281 := by
  unfold tailWord_5473825
  simp only [CollatzResearch.WordTrace]
  refine ⟨199646799394274354727510929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133097866262849569818340619 199646799394274354727510929)
  ·
    refine ⟨149735099545705766045633197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199646799394274354727510929 149735099545705766045633197)
    ·
      refine ⟨56150662329639662267112449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149735099545705766045633197 56150662329639662267112449)
      ·
        refine ⟨42112996747229746700334337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56150662329639662267112449 42112996747229746700334337)
        ·
          refine ⟨31584747560422310025250753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42112996747229746700334337 31584747560422310025250753)
          ·
            refine ⟨23688560670316732518938065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31584747560422310025250753 23688560670316732518938065)
            ·
              refine ⟨17766420502737549389203549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23688560670316732518938065 17766420502737549389203549)
              ·
                refine ⟨6662407688526581020951331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17766420502737549389203549 6662407688526581020951331)
                ·
                  refine ⟨9993611532789871531426997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6662407688526581020951331 9993611532789871531426997)
                  ·
                    refine ⟨936901081199050456071281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9993611532789871531426997 936901081199050456071281)
                    ·
                      rfl

theorem cell23_5473825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 3, 1, 5].length) (baseStart_5473825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5473825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5473825 prefixEnd_5473825 := by exact prefixLift 5473825
  have htrace : WordTrace (prefixWord ++ tailWord_5473825) baseStart_5473825 baseEnd_5473825 := by
    simpa [prefixWord, tailWord_5473825, baseEnd_5473825] using wordTrace_append hprefix tailTrace_5473825
  have hstable : (prefixWord ++ tailWord_5473825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5473825).length < 2 ^ (prefixWord ++ tailWord_5473825).sum := by decide
  have hdescent : baseEnd_5473825 < baseStart_5473825 := by decide
  rcases family_descends (prefixWord ++ tailWord_5473825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5473846 : List Nat := [5, 1, 2, 1, 4, 1, 2, 1, 6]
def baseStart_5473846 : Nat := 118140960795 + 5473846 * 2 ^ 59
def prefixEnd_5473846 : Nat := 4983230072969 + 3 ^ 40 * 5473846 * 2
def baseEnd_5473846 : Nat := 312301558521210642894583

theorem tailTrace_5473846 : CollatzResearch.WordTrace tailWord_5473846 prefixEnd_5473846 312301558521210642894583 := by
  unfold tailWord_5473846
  simp only [CollatzResearch.WordTrace]
  refine ⟨12477972832949892207126587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 133098376884798850209350261 12477972832949892207126587)
  ·
    refine ⟨18716959249424838310689881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12477972832949892207126587 18716959249424838310689881)
    ·
      refine ⟨14037719437068628733017411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18716959249424838310689881 14037719437068628733017411)
      ·
        refine ⟨21056579155602943099526117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14037719437068628733017411 21056579155602943099526117)
        ·
          refine ⟨3948108591675551831161147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21056579155602943099526117 3948108591675551831161147)
          ·
            refine ⟨5922162887513327746741721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3948108591675551831161147 5922162887513327746741721)
            ·
              refine ⟨4441622165634995810056291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5922162887513327746741721 4441622165634995810056291)
              ·
                refine ⟨6662433248452493715084437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4441622165634995810056291 6662433248452493715084437)
                ·
                  refine ⟨312301558521210642894583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6662433248452493715084437 312301558521210642894583)
                  ·
                    rfl

theorem cell23_5473846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 1, 6].length) (baseStart_5473846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5473846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5473846 prefixEnd_5473846 := by exact prefixLift 5473846
  have htrace : WordTrace (prefixWord ++ tailWord_5473846) baseStart_5473846 baseEnd_5473846 := by
    simpa [prefixWord, tailWord_5473846, baseEnd_5473846] using wordTrace_append hprefix tailTrace_5473846
  have hstable : (prefixWord ++ tailWord_5473846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5473846).length < 2 ^ (prefixWord ++ tailWord_5473846).sum := by decide
  have hdescent : baseEnd_5473846 < baseStart_5473846 := by decide
  rcases family_descends (prefixWord ++ tailWord_5473846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5473868 : List Nat := [2, 2, 1, 3, 1, 3, 2, 9]
def baseStart_5473868 : Nat := 118140960795 + 5473868 * 2 ^ 59
def prefixEnd_5473868 : Nat := 4983230072969 + 3 ^ 40 * 5473868 * 2
def baseEnd_5473868 : Nat := 104100937898714618517635

theorem tailTrace_5473868 : CollatzResearch.WordTrace tailWord_5473868 prefixEnd_5473868 104100937898714618517635 := by
  unfold tailWord_5473868
  simp only [CollatzResearch.WordTrace]
  refine ⟨99824183866559286535663129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133098911822079048714217505 99824183866559286535663129)
  ·
    refine ⟨74868137899919464901747347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99824183866559286535663129 74868137899919464901747347)
    ·
      refine ⟨112302206849879197352621021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74868137899919464901747347 112302206849879197352621021)
      ·
        refine ⟨42113327568704699007232883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112302206849879197352621021 42113327568704699007232883)
        ·
          refine ⟨63169991353057048510849325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42113327568704699007232883 63169991353057048510849325)
          ·
            refine ⟨23688746757396393191568497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63169991353057048510849325 23688746757396393191568497)
            ·
              refine ⟨17766560068047294893676373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23688746757396393191568497 17766560068047294893676373)
              ·
                refine ⟨104100937898714618517635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17766560068047294893676373 104100937898714618517635)
                ·
                  rfl

theorem cell23_5473868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 9].length) (baseStart_5473868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5473868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5473868 prefixEnd_5473868 := by exact prefixLift 5473868
  have htrace : WordTrace (prefixWord ++ tailWord_5473868) baseStart_5473868 baseEnd_5473868 := by
    simpa [prefixWord, tailWord_5473868, baseEnd_5473868] using wordTrace_append hprefix tailTrace_5473868
  have hstable : (prefixWord ++ tailWord_5473868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5473868).length < 2 ^ (prefixWord ++ tailWord_5473868).sum := by decide
  have hdescent : baseEnd_5473868 < baseStart_5473868 := by decide
  rcases family_descends (prefixWord ++ tailWord_5473868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5473885 : List Nat := [1, 4, 4, 2, 12]
def baseStart_5473885 : Nat := 118140960795 + 5473885 * 2 ^ 59
def prefixEnd_5473885 : Nat := 4983230072969 + 3 ^ 40 * 5473885 * 2
def baseEnd_5473885 : Nat := 3855602266716627069223

theorem tailTrace_5473885 : CollatzResearch.WordTrace tailWord_5473885 prefixEnd_5473885 3855602266716627069223 := by
  unfold tailWord_5473885
  simp only [CollatzResearch.WordTrace]
  refine ⟨199648987774056984974695109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133099325182704656649796739 199648987774056984974695109)
  ·
    refine ⟨37434185207635684682755333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 199648987774056984974695109 37434185207635684682755333)
    ·
      refine ⟨7018909726431690878016625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37434185207635684682755333 7018909726431690878016625)
      ·
        refine ⟨5264182294823768158512469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7018909726431690878016625 5264182294823768158512469)
        ·
          refine ⟨3855602266716627069223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 5264182294823768158512469 3855602266716627069223)
          ·
            rfl

theorem cell23_5473885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 12].length) (baseStart_5473885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5473885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5473885 prefixEnd_5473885 := by exact prefixLift 5473885
  have htrace : WordTrace (prefixWord ++ tailWord_5473885) baseStart_5473885 baseEnd_5473885 := by
    simpa [prefixWord, tailWord_5473885, baseEnd_5473885] using wordTrace_append hprefix tailTrace_5473885
  have hstable : (prefixWord ++ tailWord_5473885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5473885).length < 2 ^ (prefixWord ++ tailWord_5473885).sum := by decide
  have hdescent : baseEnd_5473885 < baseStart_5473885 := by decide
  rcases family_descends (prefixWord ++ tailWord_5473885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5473902 : List Nat := [4, 1, 2, 2, 3, 2, 1, 8]
def baseStart_5473902 : Nat := 118140960795 + 5473902 * 2 ^ 59
def prefixEnd_5473902 : Nat := 4983230072969 + 3 ^ 40 * 5473902 * 2
def baseEnd_5473902 : Nat := 104101584503983243220407

theorem tailTrace_5473902 : CollatzResearch.WordTrace tailWord_5473902 prefixEnd_5473902 104101584503983243220407 := by
  unfold tailWord_5473902
  simp only [CollatzResearch.WordTrace]
  refine ⟨24956200976874424609757995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133099738543330264585375973 24956200976874424609757995)
  ·
    refine ⟨37434301465311636914636993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24956200976874424609757995 37434301465311636914636993)
    ·
      refine ⟨28075726098983727685977745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37434301465311636914636993 28075726098983727685977745)
      ·
        refine ⟨21056794574237795764483309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28075726098983727685977745 21056794574237795764483309)
        ·
          refine ⟨7896297965339173411681241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21056794574237795764483309 7896297965339173411681241)
          ·
            refine ⟨5922223474004380058760931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7896297965339173411681241 5922223474004380058760931)
            ·
              refine ⟨8883335211006570088141397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5922223474004380058760931 8883335211006570088141397)
              ·
                refine ⟨104101584503983243220407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8883335211006570088141397 104101584503983243220407)
                ·
                  rfl

theorem cell23_5473902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 8].length) (baseStart_5473902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5473902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5473902 prefixEnd_5473902 := by exact prefixLift 5473902
  have htrace : WordTrace (prefixWord ++ tailWord_5473902) baseStart_5473902 baseEnd_5473902 := by
    simpa [prefixWord, tailWord_5473902, baseEnd_5473902] using wordTrace_append hprefix tailTrace_5473902
  have hstable : (prefixWord ++ tailWord_5473902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5473902).length < 2 ^ (prefixWord ++ tailWord_5473902).sum := by decide
  have hdescent : baseEnd_5473902 < baseStart_5473902 := by decide
  rcases family_descends (prefixWord ++ tailWord_5473902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5473975 : List Nat := [1, 1, 3, 1, 5, 1, 2, 2, 7]
def baseStart_5473975 : Nat := 118140960795 + 5473975 * 2 ^ 59
def prefixEnd_5473975 : Nat := 4983230072969 + 3 ^ 40 * 5473975 * 2
def baseEnd_5473975 : Nat := 312308918410591753482017

theorem tailTrace_5473975 : CollatzResearch.WordTrace tailWord_5473975 prefixEnd_5473975 312308918410591753482017 := by
  unfold tailWord_5473975
  simp only [CollatzResearch.WordTrace]
  refine ⟨199652270343730930345471379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133101513562487286896980919 199652270343730930345471379)
  ·
    refine ⟨299478405515596395518207069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199652270343730930345471379 299478405515596395518207069)
    ·
      refine ⟨112304402068348648319327651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 299478405515596395518207069 112304402068348648319327651)
      ·
        refine ⟨168456603102522972478991477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112304402068348648319327651 168456603102522972478991477)
        ·
          refine ⟨15792806540861528669905451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 168456603102522972478991477 15792806540861528669905451)
          ·
            refine ⟨23689209811292293004858177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15792806540861528669905451 23689209811292293004858177)
            ·
              refine ⟨17766907358469219753643633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23689209811292293004858177 17766907358469219753643633)
              ·
                refine ⟨13325180518851914815232725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17766907358469219753643633 13325180518851914815232725)
                ·
                  refine ⟨312308918410591753482017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13325180518851914815232725 312308918410591753482017)
                  ·
                    rfl

theorem cell23_5473975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 7].length) (baseStart_5473975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5473975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5473975 prefixEnd_5473975 := by exact prefixLift 5473975
  have htrace : WordTrace (prefixWord ++ tailWord_5473975) baseStart_5473975 baseEnd_5473975 := by
    simpa [prefixWord, tailWord_5473975, baseEnd_5473975] using wordTrace_append hprefix tailTrace_5473975
  have hstable : (prefixWord ++ tailWord_5473975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5473975).length < 2 ^ (prefixWord ++ tailWord_5473975).sum := by decide
  have hdescent : baseEnd_5473975 < baseStart_5473975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5473975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5474009 : List Nat := [1, 2, 1, 2, 3, 4, 3, 2, 5]
def baseStart_5474009 : Nat := 118140960795 + 5474009 * 2 ^ 59
def prefixEnd_5474009 : Nat := 4983230072969 + 3 ^ 40 * 5474009 * 2
def baseEnd_5474009 : Nat := 312310858226397627590333

theorem tailTrace_5474009 : CollatzResearch.WordTrace tailWord_5474009 prefixEnd_5474009 312310858226397627590333 := by
  unfold tailWord_5474009
  simp only [CollatzResearch.WordTrace]
  refine ⟨199653510425607754152209081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133102340283738502768139387 199653510425607754152209081)
  ·
    refine ⟨149740132819205815614156811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199653510425607754152209081 149740132819205815614156811)
    ·
      refine ⟨224610199228808723421235217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149740132819205815614156811 224610199228808723421235217)
      ·
        refine ⟨168457649421606542565926413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224610199228808723421235217 168457649421606542565926413)
        ·
          refine ⟨63171618533102453462222405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168457649421606542565926413 63171618533102453462222405)
          ·
            refine ⟨11844678474956710024166701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63171618533102453462222405 11844678474956710024166701)
            ·
              refine ⟨4441754428108766259062513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11844678474956710024166701 4441754428108766259062513)
              ·
                refine ⟨3331315821081574694296885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4441754428108766259062513 3331315821081574694296885)
                ·
                  refine ⟨312310858226397627590333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3331315821081574694296885 312310858226397627590333)
                  ·
                    rfl

theorem cell23_5474009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 2, 5].length) (baseStart_5474009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5474009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5474009 prefixEnd_5474009 := by exact prefixLift 5474009
  have htrace : WordTrace (prefixWord ++ tailWord_5474009) baseStart_5474009 baseEnd_5474009 := by
    simpa [prefixWord, tailWord_5474009, baseEnd_5474009] using wordTrace_append hprefix tailTrace_5474009
  have hstable : (prefixWord ++ tailWord_5474009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5474009).length < 2 ^ (prefixWord ++ tailWord_5474009).sum := by decide
  have hdescent : baseEnd_5474009 < baseStart_5474009 := by decide
  rcases family_descends (prefixWord ++ tailWord_5474009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5474015 : List Nat := [1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 5]
def baseStart_5474015 : Nat := 118140960795 + 5474015 * 2 ^ 59
def prefixEnd_5474015 : Nat := 4983230072969 + 3 ^ 40 * 5474015 * 2
def baseEnd_5474015 : Nat := 2810800804921505624837969

theorem tailTrace_5474015 : CollatzResearch.WordTrace tailWord_5474015 prefixEnd_5474015 2810800804921505624837969 := by
  unfold tailWord_5474015
  simp only [CollatzResearch.WordTrace]
  refine ⟨199653729263586017176927499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133102486175724011451284999 199653729263586017176927499)
  ·
    refine ⟨299480593895379025765391249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199653729263586017176927499 299480593895379025765391249)
    ·
      refine ⟨224610445421534269324043437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299480593895379025765391249 224610445421534269324043437)
      ·
        refine ⟨84228917033075350996516289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 224610445421534269324043437 84228917033075350996516289)
        ·
          refine ⟨63171687774806513247387217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84228917033075350996516289 63171687774806513247387217)
          ·
            refine ⟨47378765831104884935540413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63171687774806513247387217 47378765831104884935540413)
            ·
              refine ⟨17767037186664331850827655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47378765831104884935540413 17767037186664331850827655)
              ·
                refine ⟨26650555779996497776241483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17767037186664331850827655 26650555779996497776241483)
                ·
                  refine ⟨39975833669994746664362225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26650555779996497776241483 39975833669994746664362225)
                  ·
                    refine ⟨29981875252496059998271669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39975833669994746664362225 29981875252496059998271669)
                    ·
                      refine ⟨2810800804921505624837969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29981875252496059998271669 2810800804921505624837969)
                      ·
                        rfl

theorem cell23_5474015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_5474015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5474015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5474015 prefixEnd_5474015 := by exact prefixLift 5474015
  have htrace : WordTrace (prefixWord ++ tailWord_5474015) baseStart_5474015 baseEnd_5474015 := by
    simpa [prefixWord, tailWord_5474015, baseEnd_5474015] using wordTrace_append hprefix tailTrace_5474015
  have hstable : (prefixWord ++ tailWord_5474015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5474015).length < 2 ^ (prefixWord ++ tailWord_5474015).sum := by decide
  have hdescent : baseEnd_5474015 < baseStart_5474015 := by decide
  rcases family_descends (prefixWord ++ tailWord_5474015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5474025 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 6, 1, 4]
def baseStart_5474025 : Nat := 118140960795 + 5474025 * 2 ^ 59
def prefixEnd_5474025 : Nat := 4983230072969 + 3 ^ 40 * 5474025 * 2
def baseEnd_5474025 : Nat := 2810805939728050585712923

theorem tailTrace_5474025 : CollatzResearch.WordTrace tailWord_5474025 prefixEnd_5474025 2810805939728050585712923 := by
  unfold tailWord_5474025
  simp only [CollatzResearch.WordTrace]
  refine ⟨199654093993549788884791529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133102729329033192589861019 199654093993549788884791529)
  ·
    refine ⟨149740570495162341663593647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199654093993549788884791529 149740570495162341663593647)
    ·
      refine ⟨224610855742743512495390471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149740570495162341663593647 224610855742743512495390471)
      ·
        refine ⟨336916283614115268743085707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224610855742743512495390471 336916283614115268743085707)
        ·
          refine ⟨505374425421172903114628561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 336916283614115268743085707 505374425421172903114628561)
          ·
            refine ⟨379030819065879677335971421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 505374425421172903114628561 379030819065879677335971421)
            ·
              refine ⟨142136557149704879000989283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 379030819065879677335971421 142136557149704879000989283)
              ·
                refine ⟨213204835724557318501483925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142136557149704879000989283 213204835724557318501483925)
                ·
                  refine ⟨9993976674588624304757059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 213204835724557318501483925 9993976674588624304757059)
                  ·
                    refine ⟨14990965011882936457135589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9993976674588624304757059 14990965011882936457135589)
                    ·
                      refine ⟨2810805939728050585712923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14990965011882936457135589 2810805939728050585712923)
                      ·
                        rfl

theorem cell23_5474025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 6, 1, 4].length) (baseStart_5474025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5474025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5474025 prefixEnd_5474025 := by exact prefixLift 5474025
  have htrace : WordTrace (prefixWord ++ tailWord_5474025) baseStart_5474025 baseEnd_5474025 := by
    simpa [prefixWord, tailWord_5474025, baseEnd_5474025] using wordTrace_append hprefix tailTrace_5474025
  have hstable : (prefixWord ++ tailWord_5474025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5474025).length < 2 ^ (prefixWord ++ tailWord_5474025).sum := by decide
  have hdescent : baseEnd_5474025 < baseStart_5474025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5474025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5474042 : List Nat := [3, 1, 1, 1, 1, 3, 1, 2, 4, 4, 2]
def baseStart_5474042 : Nat := 118140960795 + 5474042 * 2 ^ 59
def prefixEnd_5474042 : Nat := 4983230072969 + 3 ^ 40 * 5474042 * 2
def baseEnd_5474042 : Nat := 2810814668899177019200345

theorem tailTrace_5474042 : CollatzResearch.WordTrace tailWord_5474042 prefixEnd_5474042 2810814668899177019200345 := by
  unfold tailWord_5474042
  simp only [CollatzResearch.WordTrace]
  refine ⟨49913678508622050197040095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133103142689658800525440253 49913678508622050197040095)
  ·
    refine ⟨74870517762933075295560143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49913678508622050197040095 74870517762933075295560143)
    ·
      refine ⟨112305776644399612943340215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74870517762933075295560143 112305776644399612943340215)
      ·
        refine ⟨168458664966599419415010323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112305776644399612943340215 168458664966599419415010323)
        ·
          refine ⟨252687997449899129122515485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168458664966599419415010323 252687997449899129122515485)
          ·
            refine ⟨94757999043712173420943307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 252687997449899129122515485 94757999043712173420943307)
            ·
              refine ⟨142136998565568260131414961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94757999043712173420943307 142136998565568260131414961)
              ·
                refine ⟨106602748924176195098561221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142136998565568260131414961 106602748924176195098561221)
                ·
                  refine ⟨19988015423283036580980229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 106602748924176195098561221 19988015423283036580980229)
                  ·
                    refine ⟨3747752891865569358933793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19988015423283036580980229 3747752891865569358933793)
                    ·
                      refine ⟨2810814668899177019200345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3747752891865569358933793 2810814668899177019200345)
                      ·
                        rfl

theorem cell23_5474042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 4, 4, 2].length) (baseStart_5474042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5474042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5474042 prefixEnd_5474042 := by exact prefixLift 5474042
  have htrace : WordTrace (prefixWord ++ tailWord_5474042) baseStart_5474042 baseEnd_5474042 := by
    simpa [prefixWord, tailWord_5474042, baseEnd_5474042] using wordTrace_append hprefix tailTrace_5474042
  have hstable : (prefixWord ++ tailWord_5474042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5474042).length < 2 ^ (prefixWord ++ tailWord_5474042).sum := by decide
  have hdescent : baseEnd_5474042 < baseStart_5474042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5474042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5474082 : List Nat := [3, 3, 1, 1, 2, 1, 1, 5, 6]
def baseStart_5474082 : Nat := 118140960795 + 5474082 * 2 ^ 59
def prefixEnd_5474082 : Nat := 4983230072969 + 3 ^ 40 * 5474082 * 2
def baseEnd_5474082 : Nat := 312315023125039651411129

theorem tailTrace_5474082 : CollatzResearch.WordTrace tailWord_5474082 prefixEnd_5474082 312315023125039651411129 := by
  unfold tailWord_5474082
  simp only [CollatzResearch.WordTrace]
  refine ⟨49914043238585821904904125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133104115302895525079744333 49914043238585821904904125)
  ·
    refine ⟨18717766214469683214339047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49914043238585821904904125 18717766214469683214339047)
    ·
      refine ⟨28076649321704524821508571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18717766214469683214339047 28076649321704524821508571)
      ·
        refine ⟨42114973982556787232262857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28076649321704524821508571 42114973982556787232262857)
        ·
          refine ⟨31586230486917590424197143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42114973982556787232262857 31586230486917590424197143)
          ·
            refine ⟨47379345730376385636295715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31586230486917590424197143 47379345730376385636295715)
            ·
              refine ⟨71069018595564578454443573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47379345730376385636295715 71069018595564578454443573)
              ·
                refine ⟨6662720493334179230104085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71069018595564578454443573 6662720493334179230104085)
                ·
                  refine ⟨312315023125039651411129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6662720493334179230104085 312315023125039651411129)
                  ·
                    rfl

theorem cell23_5474082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 5, 6].length) (baseStart_5474082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5474082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5474082 prefixEnd_5474082 := by exact prefixLift 5474082
  have htrace : WordTrace (prefixWord ++ tailWord_5474082) baseStart_5474082 baseEnd_5474082 := by
    simpa [prefixWord, tailWord_5474082, baseEnd_5474082] using wordTrace_append hprefix tailTrace_5474082
  have hstable : (prefixWord ++ tailWord_5474082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5474082).length < 2 ^ (prefixWord ++ tailWord_5474082).sum := by decide
  have hdescent : baseEnd_5474082 < baseStart_5474082 := by decide
  rcases family_descends (prefixWord ++ tailWord_5474082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5474119 : List Nat := [1, 1, 4, 1, 2, 1, 2, 4, 2, 3, 2]
def baseStart_5474119 : Nat := 118140960795 + 5474119 * 2 ^ 59
def prefixEnd_5474119 : Nat := 4983230072969 + 3 ^ 40 * 5474119 * 2
def baseEnd_5474119 : Nat := 2810854206909573217937491

theorem tailTrace_5474119 : CollatzResearch.WordTrace tailWord_5474119 prefixEnd_5474119 2810854206909573217937491 := by
  unfold tailWord_5474119
  simp only [CollatzResearch.WordTrace]
  refine ⟨199657522455209242938713411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133105014970139495292475607 199657522455209242938713411)
  ·
    refine ⟨299486283682813864408070117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199657522455209242938713411 299486283682813864408070117)
    ·
      refine ⟨56153678190527599576513147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 299486283682813864408070117 56153678190527599576513147)
      ·
        refine ⟨84230517285791399364769721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56153678190527599576513147 84230517285791399364769721)
        ·
          refine ⟨63172887964343549523577291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84230517285791399364769721 63172887964343549523577291)
          ·
            refine ⟨94759331946515324285365937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63172887964343549523577291 94759331946515324285365937)
            ·
              refine ⟨71069498959886493214024453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94759331946515324285365937 71069498959886493214024453)
              ·
                refine ⟨13325531054978717477629585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71069498959886493214024453 13325531054978717477629585)
                ·
                  refine ⟨9994148291234038108222189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13325531054978717477629585 9994148291234038108222189)
                  ·
                    refine ⟨3747805609212764290583321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9994148291234038108222189 3747805609212764290583321)
                    ·
                      refine ⟨2810854206909573217937491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3747805609212764290583321 2810854206909573217937491)
                      ·
                        rfl

theorem cell23_5474119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 2, 3, 2].length) (baseStart_5474119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5474119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5474119 prefixEnd_5474119 := by exact prefixLift 5474119
  have htrace : WordTrace (prefixWord ++ tailWord_5474119) baseStart_5474119 baseEnd_5474119 := by
    simpa [prefixWord, tailWord_5474119, baseEnd_5474119] using wordTrace_append hprefix tailTrace_5474119
  have hstable : (prefixWord ++ tailWord_5474119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5474119).length < 2 ^ (prefixWord ++ tailWord_5474119).sum := by decide
  have hdescent : baseEnd_5474119 < baseStart_5474119 := by decide
  rcases family_descends (prefixWord ++ tailWord_5474119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5474146 : List Nat := [3, 3, 2, 1, 2, 2, 2, 2, 1, 5]
def baseStart_5474146 : Nat := 118140960795 + 5474146 * 2 ^ 59
def prefixEnd_5474146 : Nat := 4983230072969 + 3 ^ 40 * 5474146 * 2
def baseEnd_5474146 : Nat := 936956023629081537433289

theorem tailTrace_5474146 : CollatzResearch.WordTrace tailWord_5474146 prefixEnd_5474146 936956023629081537433289 := by
  unfold tailWord_5474146
  simp only [CollatzResearch.WordTrace]
  refine ⟨49914626806527856637486573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133105671484074284366630861 49914626806527856637486573)
  ·
    refine ⟨18717985052447946239057465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49914626806527856637486573 18717985052447946239057465)
    ·
      refine ⟨14038488789335959679293099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18717985052447946239057465 14038488789335959679293099)
      ·
        refine ⟨21057733184003939518939649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14038488789335959679293099 21057733184003939518939649)
        ·
          refine ⟨15793299888002954639204737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21057733184003939518939649 15793299888002954639204737)
          ·
            refine ⟨11844974916002215979403553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15793299888002954639204737 11844974916002215979403553)
            ·
              refine ⟨8883731187001661984552665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11844974916002215979403553 8883731187001661984552665)
              ·
                refine ⟨6662798390251246488414499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8883731187001661984552665 6662798390251246488414499)
                ·
                  refine ⟨9994197585376869732621749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6662798390251246488414499 9994197585376869732621749)
                  ·
                    refine ⟨936956023629081537433289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9994197585376869732621749 936956023629081537433289)
                    ·
                      rfl

theorem cell23_5474146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_5474146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5474146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5474146 prefixEnd_5474146 := by exact prefixLift 5474146
  have htrace : WordTrace (prefixWord ++ tailWord_5474146) baseStart_5474146 baseEnd_5474146 := by
    simpa [prefixWord, tailWord_5474146, baseEnd_5474146] using wordTrace_append hprefix tailTrace_5474146
  have hstable : (prefixWord ++ tailWord_5474146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5474146).length < 2 ^ (prefixWord ++ tailWord_5474146).sum := by decide
  have hdescent : baseEnd_5474146 < baseStart_5474146 := by decide
  rcases family_descends (prefixWord ++ tailWord_5474146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5474152 : List Nat := [2, 1, 4, 2, 1, 1, 1, 2, 3, 1, 5]
def baseStart_5474152 : Nat := 118140960795 + 5474152 * 2 ^ 59
def prefixEnd_5474152 : Nat := 4983230072969 + 3 ^ 40 * 5474152 * 2
def baseEnd_5474152 : Nat := 2810871151771171588824839

theorem tailTrace_5474152 : CollatzResearch.WordTrace tailWord_5474152 prefixEnd_5474152 2810871151771171588824839 := by
  unfold tailWord_5474152
  simp only [CollatzResearch.WordTrace]
  refine ⟨99829363032044844787332355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133105817376059793049776473 99829363032044844787332355)
  ·
    refine ⟨149744044548067267180998533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99829363032044844787332355 149744044548067267180998533)
    ·
      refine ⟨28077008352762612596437225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149744044548067267180998533 28077008352762612596437225)
      ·
        refine ⟨21057756264571959447327919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28077008352762612596437225 21057756264571959447327919)
        ·
          refine ⟨31586634396857939170991879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21057756264571959447327919 31586634396857939170991879)
          ·
            refine ⟨47379951595286908756487819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31586634396857939170991879 47379951595286908756487819)
            ·
              refine ⟨71069927392930363134731729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47379951595286908756487819 71069927392930363134731729)
              ·
                refine ⟨53302445544697772351048797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71069927392930363134731729 53302445544697772351048797)
                ·
                  refine ⟨19988417079261664631643299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53302445544697772351048797 19988417079261664631643299)
                  ·
                    refine ⟨29982625618892496947464949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19988417079261664631643299 29982625618892496947464949)
                    ·
                      refine ⟨2810871151771171588824839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29982625618892496947464949 2810871151771171588824839)
                      ·
                        rfl

theorem cell23_5474152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_5474152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5474152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5474152 prefixEnd_5474152 := by exact prefixLift 5474152
  have htrace : WordTrace (prefixWord ++ tailWord_5474152) baseStart_5474152 baseEnd_5474152 := by
    simpa [prefixWord, tailWord_5474152, baseEnd_5474152] using wordTrace_append hprefix tailTrace_5474152
  have hstable : (prefixWord ++ tailWord_5474152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5474152).length < 2 ^ (prefixWord ++ tailWord_5474152).sum := by decide
  have hdescent : baseEnd_5474152 < baseStart_5474152 := by decide
  rcases family_descends (prefixWord ++ tailWord_5474152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5474162 : List Nat := [3, 2, 1, 2, 1, 1, 1, 3, 3, 2, 4]
def baseStart_5474162 : Nat := 118140960795 + 5474162 * 2 ^ 59
def prefixEnd_5474162 : Nat := 4983230072969 + 3 ^ 40 * 5474162 * 2
def baseEnd_5474162 : Nat := 2810876286577716549699793

theorem tailTrace_5474162 : CollatzResearch.WordTrace tailWord_5474162 prefixEnd_5474162 2810876286577716549699793 := by
  unfold tailWord_5474162
  simp only [CollatzResearch.WordTrace]
  refine ⟨49914772698513365320632185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133106060529368974188352493 49914772698513365320632185)
  ·
    refine ⟨37436079523885023990474139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49914772698513365320632185 37436079523885023990474139)
    ·
      refine ⟨56154119285827535985711209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37436079523885023990474139 56154119285827535985711209)
      ·
        refine ⟨42115589464370651989283407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56154119285827535985711209 42115589464370651989283407)
        ·
          refine ⟨63173384196555977983925111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42115589464370651989283407 63173384196555977983925111)
          ·
            refine ⟨94760076294833966975887667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63173384196555977983925111 94760076294833966975887667)
            ·
              refine ⟨142140114442250950463831501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94760076294833966975887667 142140114442250950463831501)
              ·
                refine ⟨53302542915844106423936813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 142140114442250950463831501 53302542915844106423936813)
                ·
                  refine ⟨19988453593441539908976305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53302542915844106423936813 19988453593441539908976305)
                  ·
                    refine ⟨14991340195081154931732229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19988453593441539908976305 14991340195081154931732229)
                    ·
                      refine ⟨2810876286577716549699793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14991340195081154931732229 2810876286577716549699793)
                      ·
                        rfl

theorem cell23_5474162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_5474162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5474162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5474162 prefixEnd_5474162 := by exact prefixLift 5474162
  have htrace : WordTrace (prefixWord ++ tailWord_5474162) baseStart_5474162 baseEnd_5474162 := by
    simpa [prefixWord, tailWord_5474162, baseEnd_5474162] using wordTrace_append hprefix tailTrace_5474162
  have hstable : (prefixWord ++ tailWord_5474162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5474162).length < 2 ^ (prefixWord ++ tailWord_5474162).sum := by decide
  have hdescent : baseEnd_5474162 < baseStart_5474162 := by decide
  rcases family_descends (prefixWord ++ tailWord_5474162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5474169 : List Nat := [1, 2, 1, 3, 2, 2, 1, 5, 1, 2, 3]
def baseStart_5474169 : Nat := 118140960795 + 5474169 * 2 ^ 59
def prefixEnd_5474169 : Nat := 4983230072969 + 3 ^ 40 * 5474169 * 2
def baseEnd_5474169 : Nat := 2810879880942298022312261

theorem tailTrace_5474169 : CollatzResearch.WordTrace tailWord_5474169 prefixEnd_5474169 2810879880942298022312261 := by
  unfold tailWord_5474169
  simp only [CollatzResearch.WordTrace]
  refine ⟨199659346105028101478033561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133106230736685400985355707 199659346105028101478033561)
  ·
    refine ⟨149744509578771076108525171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199659346105028101478033561 149744509578771076108525171)
    ·
      refine ⟨224616764368156614162787757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149744509578771076108525171 224616764368156614162787757)
      ·
        refine ⟨84231286638058730311045409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 224616764368156614162787757 84231286638058730311045409)
        ·
          refine ⟨63173464978544047733284057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84231286638058730311045409 63173464978544047733284057)
          ·
            refine ⟨47380098733908035799963043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63173464978544047733284057 47380098733908035799963043)
            ·
              refine ⟨71070148100862053699944565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47380098733908035799963043 71070148100862053699944565)
              ·
                refine ⟨6662826384455817534369803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71070148100862053699944565 6662826384455817534369803)
                ·
                  refine ⟨9994239576683726301554705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6662826384455817534369803 9994239576683726301554705)
                  ·
                    refine ⟨7495679682512794726166029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9994239576683726301554705 7495679682512794726166029)
                    ·
                      refine ⟨2810879880942298022312261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7495679682512794726166029 2810879880942298022312261)
                      ·
                        rfl

theorem cell23_5474169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 5, 1, 2, 3].length) (baseStart_5474169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5474169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5474169 prefixEnd_5474169 := by exact prefixLift 5474169
  have htrace : WordTrace (prefixWord ++ tailWord_5474169) baseStart_5474169 baseEnd_5474169 := by
    simpa [prefixWord, tailWord_5474169, baseEnd_5474169] using wordTrace_append hprefix tailTrace_5474169
  have hstable : (prefixWord ++ tailWord_5474169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5474169).length < 2 ^ (prefixWord ++ tailWord_5474169).sum := by decide
  have hdescent : baseEnd_5474169 < baseStart_5474169 := by decide
  rcases family_descends (prefixWord ++ tailWord_5474169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5474177 : List Nat := [1, 2, 4, 4, 1, 1, 3, 2, 1, 1, 3]
def baseStart_5474177 : Nat := 118140960795 + 5474177 * 2 ^ 59
def prefixEnd_5474177 : Nat := 4983230072969 + 3 ^ 40 * 5474177 * 2
def baseEnd_5474177 : Nat := 2810883988787533991012225

theorem tailTrace_5474177 : CollatzResearch.WordTrace tailWord_5474177 prefixEnd_5474177 2810883988787533991012225 := by
  unfold tailWord_5474177
  simp only [CollatzResearch.WordTrace]
  refine ⟨199659637888999118844324785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133106425259332745896216523 199659637888999118844324785)
  ·
    refine ⟨149744728416749339133243589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199659637888999118844324785 149744728416749339133243589)
    ·
      refine ⟨28077136578140501087483173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149744728416749339133243589 28077136578140501087483173)
      ·
        refine ⟨5264463108401343953903095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28077136578140501087483173 5264463108401343953903095)
        ·
          refine ⟨7896694662602015930854643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5264463108401343953903095 7896694662602015930854643)
          ·
            refine ⟨11845041993903023896281965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7896694662602015930854643 11845041993903023896281965)
            ·
              refine ⟨4441890747713633961105737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11845041993903023896281965 4441890747713633961105737)
              ·
                refine ⟨3331418060785225470829303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4441890747713633961105737 3331418060785225470829303)
                ·
                  refine ⟨4997127091177838206243955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3331418060785225470829303 4997127091177838206243955)
                  ·
                    refine ⟨7495690636766757309365933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4997127091177838206243955 7495690636766757309365933)
                    ·
                      refine ⟨2810883988787533991012225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7495690636766757309365933 2810883988787533991012225)
                      ·
                        rfl

theorem cell23_5474177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_5474177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5474177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5474177 prefixEnd_5474177 := by exact prefixLift 5474177
  have htrace : WordTrace (prefixWord ++ tailWord_5474177) baseStart_5474177 baseEnd_5474177 := by
    simpa [prefixWord, tailWord_5474177, baseEnd_5474177] using wordTrace_append hprefix tailTrace_5474177
  have hstable : (prefixWord ++ tailWord_5474177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5474177).length < 2 ^ (prefixWord ++ tailWord_5474177).sum := by decide
  have hdescent : baseEnd_5474177 < baseStart_5474177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5474177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5474200 : List Nat := [2, 1, 2, 6, 2, 1, 1, 2, 1, 1, 4]
def baseStart_5474200 : Nat := 118140960795 + 5474200 * 2 ^ 59
def prefixEnd_5474200 : Nat := 4983230072969 + 3 ^ 40 * 5474200 * 2
def baseEnd_5474200 : Nat := 2810895798842587401024619

theorem tailTrace_5474200 : CollatzResearch.WordTrace tailWord_5474200 prefixEnd_5474200 2810895798842587401024619 := by
  unfold tailWord_5474200
  simp only [CollatzResearch.WordTrace]
  refine ⟨99830238383957896886206027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133106984511943862514941369 99830238383957896886206027)
  ·
    refine ⟨149745357575936845329309041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99830238383957896886206027 149745357575936845329309041)
    ·
      refine ⟨112309018181952633996981781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149745357575936845329309041 112309018181952633996981781)
      ·
        refine ⟨5264485227279029718608521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 112309018181952633996981781 5264485227279029718608521)
        ·
          refine ⟨3948363920459272288956391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5264485227279029718608521 3948363920459272288956391)
          ·
            refine ⟨5922545880688908433434587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3948363920459272288956391 5922545880688908433434587)
            ·
              refine ⟨8883818821033362650151881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5922545880688908433434587 8883818821033362650151881)
              ·
                refine ⟨6662864115775021987613911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8883818821033362650151881 6662864115775021987613911)
                ·
                  refine ⟨9994296173662532981420867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6662864115775021987613911 9994296173662532981420867)
                  ·
                    refine ⟨14991444260493799472131301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9994296173662532981420867 14991444260493799472131301)
                    ·
                      refine ⟨2810895798842587401024619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14991444260493799472131301 2810895798842587401024619)
                      ·
                        rfl

theorem cell23_5474200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_5474200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5474200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5474200 prefixEnd_5474200 := by exact prefixLift 5474200
  have htrace : WordTrace (prefixWord ++ tailWord_5474200) baseStart_5474200 baseEnd_5474200 := by
    simpa [prefixWord, tailWord_5474200, baseEnd_5474200] using wordTrace_append hprefix tailTrace_5474200
  have hstable : (prefixWord ++ tailWord_5474200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5474200).length < 2 ^ (prefixWord ++ tailWord_5474200).sum := by decide
  have hdescent : baseEnd_5474200 < baseStart_5474200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5474200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5474226 : List Nat := [3, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2]
def baseStart_5474226 : Nat := 118140960795 + 5474226 * 2 ^ 59
def prefixEnd_5474226 : Nat := 4983230072969 + 3 ^ 40 * 5474226 * 2
def baseEnd_5474226 : Nat := 2810909149339604299299499

theorem tailTrace_5474226 : CollatzResearch.WordTrace tailWord_5474226 prefixEnd_5474226 2810909149339604299299499 := by
  unfold tailWord_5474226
  simp only [CollatzResearch.WordTrace]
  refine ⟨49915356266455400053214633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133107616710547733475239021 49915356266455400053214633)
  ·
    refine ⟨37436517199841550039910975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49915356266455400053214633 37436517199841550039910975)
    ·
      refine ⟨56154775799762325059866463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37436517199841550039910975 56154775799762325059866463)
      ·
        refine ⟨84232163699643487589799695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56154775799762325059866463 84232163699643487589799695)
        ·
          refine ⟨126348245549465231384699543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84232163699643487589799695 126348245549465231384699543)
          ·
            refine ⟨189522368324197847077049315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126348245549465231384699543 189522368324197847077049315)
            ·
              refine ⟨284283552486296770615573973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189522368324197847077049315 284283552486296770615573973)
              ·
                refine ⟨6662895761397580561302515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 284283552486296770615573973 6662895761397580561302515)
                ·
                  refine ⟨9994343642096370841953773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6662895761397580561302515 9994343642096370841953773)
                  ·
                    refine ⟨3747878865786139065732665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9994343642096370841953773 3747878865786139065732665)
                    ·
                      refine ⟨2810909149339604299299499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3747878865786139065732665 2810909149339604299299499)
                      ·
                        rfl

theorem cell23_5474226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2].length) (baseStart_5474226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5474226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5474226 prefixEnd_5474226 := by exact prefixLift 5474226
  have htrace : WordTrace (prefixWord ++ tailWord_5474226) baseStart_5474226 baseEnd_5474226 := by
    simpa [prefixWord, tailWord_5474226, baseEnd_5474226] using wordTrace_append hprefix tailTrace_5474226
  have hstable : (prefixWord ++ tailWord_5474226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5474226).length < 2 ^ (prefixWord ++ tailWord_5474226).sum := by decide
  have hdescent : baseEnd_5474226 < baseStart_5474226 := by decide
  rcases family_descends (prefixWord ++ tailWord_5474226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5474232 : List Nat := [2, 1, 2, 1, 2, 3, 2, 2, 2, 6]
def baseStart_5474232 : Nat := 118140960795 + 5474232 * 2 ^ 59
def prefixEnd_5474232 : Nat := 4983230072969 + 3 ^ 40 * 5474232 * 2
def baseEnd_5474232 : Nat := 936970743407843758608157

theorem tailTrace_5474232 : CollatzResearch.WordTrace tailWord_5474232 prefixEnd_5474232 936970743407843758608157 := by
  unfold tailWord_5474232
  simp only [CollatzResearch.WordTrace]
  refine ⟨99830821951899931618788475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133107762602533242158384633 99830821951899931618788475)
  ·
    refine ⟨149746232927849897428182713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99830821951899931618788475 149746232927849897428182713)
    ·
      refine ⟨112309674695887423071137035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149746232927849897428182713 112309674695887423071137035)
      ·
        refine ⟨168464512043831134606705553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112309674695887423071137035 168464512043831134606705553)
        ·
          refine ⟨126348384032873350955029165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168464512043831134606705553 126348384032873350955029165)
          ·
            refine ⟨47380644012327506608135937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126348384032873350955029165 47380644012327506608135937)
            ·
              refine ⟨35535483009245629956101953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47380644012327506608135937 35535483009245629956101953)
              ·
                refine ⟨26651612256934222467076465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35535483009245629956101953 26651612256934222467076465)
                ·
                  refine ⟨19988709192700666850307349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26651612256934222467076465 19988709192700666850307349)
                  ·
                    refine ⟨936970743407843758608157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19988709192700666850307349 936970743407843758608157)
                    ·
                      rfl

theorem cell23_5474232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 2, 6].length) (baseStart_5474232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5474232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5474232 prefixEnd_5474232 := by exact prefixLift 5474232
  have htrace : WordTrace (prefixWord ++ tailWord_5474232) baseStart_5474232 baseEnd_5474232 := by
    simpa [prefixWord, tailWord_5474232, baseEnd_5474232] using wordTrace_append hprefix tailTrace_5474232
  have hstable : (prefixWord ++ tailWord_5474232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5474232).length < 2 ^ (prefixWord ++ tailWord_5474232).sum := by decide
  have hdescent : baseEnd_5474232 < baseStart_5474232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5474232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5474239 : List Nat := [1, 1, 2, 2, 2, 1, 3, 2, 3, 4, 2]
def baseStart_5474239 : Nat := 118140960795 + 5474239 * 2 ^ 59
def prefixEnd_5474239 : Nat := 4983230072969 + 3 ^ 40 * 5474239 * 2
def baseEnd_5474239 : Nat := 2810915824588112748436939

theorem tailTrace_5474239 : CollatzResearch.WordTrace tailWord_5474239 prefixEnd_5474239 2810915824588112748436939 := by
  unfold tailWord_5474239
  simp only [CollatzResearch.WordTrace]
  refine ⟨199661899214774503433081771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133107932809849668955387847 199661899214774503433081771)
  ·
    refine ⟨299492848822161755149622657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199661899214774503433081771 299492848822161755149622657)
    ·
      refine ⟨224619636616621316362216993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299492848822161755149622657 224619636616621316362216993)
      ·
        refine ⟨168464727462465987271662745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224619636616621316362216993 168464727462465987271662745)
        ·
          refine ⟨126348545596849490453747059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168464727462465987271662745 126348545596849490453747059)
          ·
            refine ⟨189522818395274235680620589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126348545596849490453747059 189522818395274235680620589)
            ·
              refine ⟨71071056898227838380232721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 189522818395274235680620589 71071056898227838380232721)
              ·
                refine ⟨53303292673670878785174541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71071056898227838380232721 53303292673670878785174541)
                ·
                  refine ⟨19988734752626579544440453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53303292673670878785174541 19988734752626579544440453)
                  ·
                    refine ⟨3747887766117483664582585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19988734752626579544440453 3747887766117483664582585)
                    ·
                      refine ⟨2810915824588112748436939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3747887766117483664582585 2810915824588112748436939)
                      ·
                        rfl

theorem cell23_5474239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 4, 2].length) (baseStart_5474239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5474239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5474239 prefixEnd_5474239 := by exact prefixLift 5474239
  have htrace : WordTrace (prefixWord ++ tailWord_5474239) baseStart_5474239 baseEnd_5474239 := by
    simpa [prefixWord, tailWord_5474239, baseEnd_5474239] using wordTrace_append hprefix tailTrace_5474239
  have hstable : (prefixWord ++ tailWord_5474239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5474239).length < 2 ^ (prefixWord ++ tailWord_5474239).sum := by decide
  have hdescent : baseEnd_5474239 < baseStart_5474239 := by decide
  rcases family_descends (prefixWord ++ tailWord_5474239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5474299 : List Nat := [1, 1, 1, 1, 1, 3, 4, 1, 1, 7, 2]
def baseStart_5474299 : Nat := 118140960795 + 5474299 * 2 ^ 59
def prefixEnd_5474299 : Nat := 4983230072969 + 3 ^ 40 * 5474299 * 2
def baseEnd_5474299 : Nat := 2810946633427382513686663

theorem tailTrace_5474299 : CollatzResearch.WordTrace tailWord_5474299 prefixEnd_5474299 2810946633427382513686663 := by
  unfold tailWord_5474299
  simp only [CollatzResearch.WordTrace]
  refine ⟨199664087594557133680265951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133109391729704755786843967 199664087594557133680265951)
  ·
    refine ⟨299496131391835700520398927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199664087594557133680265951 299496131391835700520398927)
    ·
      refine ⟨449244197087753550780598391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299496131391835700520398927 449244197087753550780598391)
      ·
        refine ⟨673866295631630326170897587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 449244197087753550780598391 673866295631630326170897587)
        ·
          refine ⟨1010799443447445489256346381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 673866295631630326170897587 1010799443447445489256346381)
          ·
            refine ⟨379049791292792058471129893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1010799443447445489256346381 379049791292792058471129893)
            ·
              refine ⟨71071835867398510963336855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 379049791292792058471129893 71071835867398510963336855)
              ·
                refine ⟨106607753801097766445005283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71071835867398510963336855 106607753801097766445005283)
                ·
                  refine ⟨159911630701646649667507925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106607753801097766445005283 159911630701646649667507925)
                  ·
                    refine ⟨3747928844569843351582217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 159911630701646649667507925 3747928844569843351582217)
                    ·
                      refine ⟨2810946633427382513686663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3747928844569843351582217 2810946633427382513686663)
                      ·
                        rfl

theorem cell23_5474299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 7, 2].length) (baseStart_5474299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5474299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5474299 prefixEnd_5474299 := by exact prefixLift 5474299
  have htrace : WordTrace (prefixWord ++ tailWord_5474299) baseStart_5474299 baseEnd_5474299 := by
    simpa [prefixWord, tailWord_5474299, baseEnd_5474299] using wordTrace_append hprefix tailTrace_5474299
  have hstable : (prefixWord ++ tailWord_5474299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5474299).length < 2 ^ (prefixWord ++ tailWord_5474299).sum := by decide
  have hdescent : baseEnd_5474299 < baseStart_5474299 := by decide
  rcases family_descends (prefixWord ++ tailWord_5474299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5474329 : List Nat := [1, 2, 1, 2, 1, 1, 3, 5, 2, 1, 4]
def baseStart_5474329 : Nat := 118140960795 + 5474329 * 2 ^ 59
def prefixEnd_5474329 : Nat := 4983230072969 + 3 ^ 40 * 5474329 * 2
def baseEnd_5474329 : Nat := 2810962037847017396311525

theorem tailTrace_5474329 : CollatzResearch.WordTrace tailWord_5474329 prefixEnd_5474329 2810962037847017396311525 := by
  unfold tailWord_5474329
  simp only [CollatzResearch.WordTrace]
  refine ⟨199665181784448448803858041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133110121189632299202572027 199665181784448448803858041)
  ·
    refine ⟨149748886338336336602893531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199665181784448448803858041 149748886338336336602893531)
    ·
      refine ⟨224623329507504504904340297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149748886338336336602893531 224623329507504504904340297)
      ·
        refine ⟨168467497130628378678255223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224623329507504504904340297 168467497130628378678255223)
        ·
          refine ⟨252701245695942568017382835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168467497130628378678255223 252701245695942568017382835)
          ·
            refine ⟨379051868543913852026074253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252701245695942568017382835 379051868543913852026074253)
            ·
              refine ⟨142144450703967694509777845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 379051868543913852026074253 142144450703967694509777845)
              ·
                refine ⟨13326042253496971360291673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 142144450703967694509777845 13326042253496971360291673)
                ·
                  refine ⟨9994531690122728520218755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13326042253496971360291673 9994531690122728520218755)
                  ·
                    refine ⟨14991797535184092780328133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9994531690122728520218755 14991797535184092780328133)
                    ·
                      refine ⟨2810962037847017396311525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14991797535184092780328133 2810962037847017396311525)
                      ·
                        rfl

theorem cell23_5474329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 2, 1, 4].length) (baseStart_5474329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5474329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5474329 prefixEnd_5474329 := by exact prefixLift 5474329
  have htrace : WordTrace (prefixWord ++ tailWord_5474329) baseStart_5474329 baseEnd_5474329 := by
    simpa [prefixWord, tailWord_5474329, baseEnd_5474329] using wordTrace_append hprefix tailTrace_5474329
  have hstable : (prefixWord ++ tailWord_5474329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5474329).length < 2 ^ (prefixWord ++ tailWord_5474329).sum := by decide
  have hdescent : baseEnd_5474329 < baseStart_5474329 := by decide
  rcases family_descends (prefixWord ++ tailWord_5474329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5474343 : List Nat := [1, 1, 7, 1, 2, 1, 1, 2, 2, 5]
def baseStart_5474343 : Nat := 118140960795 + 5474343 * 2 ^ 59
def prefixEnd_5474343 : Nat := 4983230072969 + 3 ^ 40 * 5474343 * 2
def baseEnd_5474343 : Nat := 936989742192060113845487

theorem tailTrace_5474343 : CollatzResearch.WordTrace tailWord_5474343 prefixEnd_5474343 936989742192060113845487 := by
  unfold tailWord_5474343
  simp only [CollatzResearch.WordTrace]
  refine ⟨199665692406397729194867683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133110461604265152796578455 199665692406397729194867683)
  ·
    refine ⟨299498538609596593792301525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199665692406397729194867683 299498538609596593792301525)
    ·
      refine ⟨7019496998662420167007067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 299498538609596593792301525 7019496998662420167007067)
      ·
        refine ⟨10529245497993630250510601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7019496998662420167007067 10529245497993630250510601)
        ·
          refine ⟨7896934123495222687882951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10529245497993630250510601 7896934123495222687882951)
          ·
            refine ⟨11845401185242834031824427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7896934123495222687882951 11845401185242834031824427)
            ·
              refine ⟨17768101777864251047736641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11845401185242834031824427 17768101777864251047736641)
              ·
                refine ⟨13326076333398188285802481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17768101777864251047736641 13326076333398188285802481)
                ·
                  refine ⟨9994557250048641214351861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13326076333398188285802481 9994557250048641214351861)
                  ·
                    refine ⟨936989742192060113845487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9994557250048641214351861 936989742192060113845487)
                    ·
                      rfl

theorem cell23_5474343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_5474343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5474343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5474343 prefixEnd_5474343 := by exact prefixLift 5474343
  have htrace : WordTrace (prefixWord ++ tailWord_5474343) baseStart_5474343 baseEnd_5474343 := by
    simpa [prefixWord, tailWord_5474343, baseEnd_5474343] using wordTrace_append hprefix tailTrace_5474343
  have hstable : (prefixWord ++ tailWord_5474343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5474343).length < 2 ^ (prefixWord ++ tailWord_5474343).sum := by decide
  have hdescent : baseEnd_5474343 < baseStart_5474343 := by decide
  rcases family_descends (prefixWord ++ tailWord_5474343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5474346 : List Nat := [3, 1, 4, 1, 2, 1, 1, 1, 4, 1, 4]
def baseStart_5474346 : Nat := 118140960795 + 5474346 * 2 ^ 59
def prefixEnd_5474346 : Nat := 4983230072969 + 3 ^ 40 * 5474346 * 2
def baseEnd_5474346 : Nat := 2810970767018143829798947

theorem tailTrace_5474346 : CollatzResearch.WordTrace tailWord_5474346 prefixEnd_5474346 2810970767018143829798947 := by
  unfold tailWord_5474346
  simp only [CollatzResearch.WordTrace]
  refine ⟨49916450456346715176806723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133110534550257907138151261 49916450456346715176806723)
  ·
    refine ⟨74874675684520072765210085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49916450456346715176806723 74874675684520072765210085)
    ·
      refine ⟨14039001690847513643476891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74874675684520072765210085 14039001690847513643476891)
      ·
        refine ⟨21058502536271270465215337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14039001690847513643476891 21058502536271270465215337)
        ·
          refine ⟨15793876902203452848911503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21058502536271270465215337 15793876902203452848911503)
          ·
            refine ⟨23690815353305179273367255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15793876902203452848911503 23690815353305179273367255)
            ·
              refine ⟨35536223029957768910050883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23690815353305179273367255 35536223029957768910050883)
              ·
                refine ⟨53304334544936653365076325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35536223029957768910050883 53304334544936653365076325)
                ·
                  refine ⟨9994562727175622505951811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53304334544936653365076325 9994562727175622505951811)
                  ·
                    refine ⟨14991844090763433758927717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9994562727175622505951811 14991844090763433758927717)
                    ·
                      refine ⟨2810970767018143829798947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14991844090763433758927717 2810970767018143829798947)
                      ·
                        rfl

theorem cell23_5474346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_5474346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5474346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5474346 prefixEnd_5474346 := by exact prefixLift 5474346
  have htrace : WordTrace (prefixWord ++ tailWord_5474346) baseStart_5474346 baseEnd_5474346 := by
    simpa [prefixWord, tailWord_5474346, baseEnd_5474346] using wordTrace_append hprefix tailTrace_5474346
  have hstable : (prefixWord ++ tailWord_5474346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5474346).length < 2 ^ (prefixWord ++ tailWord_5474346).sum := by decide
  have hdescent : baseEnd_5474346 < baseStart_5474346 := by decide
  rcases family_descends (prefixWord ++ tailWord_5474346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5474413 : List Nat := [1, 5, 1, 1, 2, 1, 2, 3, 3, 1, 3]
def baseStart_5474413 : Nat := 118140960795 + 5474413 * 2 ^ 59
def prefixEnd_5474413 : Nat := 4983230072969 + 3 ^ 40 * 5474413 * 2
def baseEnd_5474413 : Nat := 2811005170221995067661139

theorem tailTrace_5474413 : CollatzResearch.WordTrace tailWord_5474413 prefixEnd_5474413 2811005170221995067661139 := by
  unfold tailWord_5474413
  simp only [CollatzResearch.WordTrace]
  refine ⟨199668245516144131149915893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133112163677429420766610595 199668245516144131149915893)
  ·
    refine ⟨18718898017138512295304615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 199668245516144131149915893 18718898017138512295304615)
    ·
      refine ⟨28078347025707768442956923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18718898017138512295304615 28078347025707768442956923)
      ·
        refine ⟨42117520538561652664435385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28078347025707768442956923 42117520538561652664435385)
        ·
          refine ⟨31588140403921239498326539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42117520538561652664435385 31588140403921239498326539)
          ·
            refine ⟨47382210605881859247489809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31588140403921239498326539 47382210605881859247489809)
            ·
              refine ⟨35536657954411394435617357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47382210605881859247489809 35536657954411394435617357)
              ·
                refine ⟨13326246732904272913356509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35536657954411394435617357 13326246732904272913356509)
                ·
                  refine ⟨4997342524839102342508691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13326246732904272913356509 4997342524839102342508691)
                  ·
                    refine ⟨7496013787258653513763037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4997342524839102342508691 7496013787258653513763037)
                    ·
                      refine ⟨2811005170221995067661139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7496013787258653513763037 2811005170221995067661139)
                      ·
                        rfl

theorem cell23_5474413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_5474413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5474413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5474413 prefixEnd_5474413 := by exact prefixLift 5474413
  have htrace : WordTrace (prefixWord ++ tailWord_5474413) baseStart_5474413 baseEnd_5474413 := by
    simpa [prefixWord, tailWord_5474413, baseEnd_5474413] using wordTrace_append hprefix tailTrace_5474413
  have hstable : (prefixWord ++ tailWord_5474413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5474413).length < 2 ^ (prefixWord ++ tailWord_5474413).sum := by decide
  have hdescent : baseEnd_5474413 < baseStart_5474413 := by decide
  rcases family_descends (prefixWord ++ tailWord_5474413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5474436 : List Nat := [2, 3, 2, 1, 2, 1, 1, 3, 3, 1, 4]
def baseStart_5474436 : Nat := 118140960795 + 5474436 * 2 ^ 59
def prefixEnd_5474436 : Nat := 4983230072969 + 3 ^ 40 * 5474436 * 2
def baseEnd_5474436 : Nat := 2811016980277048477673533

theorem tailTrace_5474436 : CollatzResearch.WordTrace tailWord_5474436 prefixEnd_5474436 2811016980277048477673533 := by
  unfold tailWord_5474436
  simp only [CollatzResearch.WordTrace]
  refine ⟨99834542197530403039001581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133112722930040537385335441 99834542197530403039001581)
  ·
    refine ⟨37437953324073901139625593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99834542197530403039001581 37437953324073901139625593)
    ·
      refine ⟨28078464993055425854719195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37437953324073901139625593 28078464993055425854719195)
      ·
        refine ⟨42117697489583138782078793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28078464993055425854719195 42117697489583138782078793)
        ·
          refine ⟨31588273117187354086559095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42117697489583138782078793 31588273117187354086559095)
          ·
            refine ⟨47382409675781031129838643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31588273117187354086559095 47382409675781031129838643)
            ·
              refine ⟨71073614513671546694757965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47382409675781031129838643 71073614513671546694757965)
              ·
                refine ⟨26652605442626830010534237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71073614513671546694757965 26652605442626830010534237)
                ·
                  refine ⟨9994727040985061253950339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26652605442626830010534237 9994727040985061253950339)
                  ·
                    refine ⟨14992090561477591880925509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9994727040985061253950339 14992090561477591880925509)
                    ·
                      refine ⟨2811016980277048477673533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14992090561477591880925509 2811016980277048477673533)
                      ·
                        rfl

theorem cell23_5474436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_5474436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5474436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5474436 prefixEnd_5474436 := by exact prefixLift 5474436
  have htrace : WordTrace (prefixWord ++ tailWord_5474436) baseStart_5474436 baseEnd_5474436 := by
    simpa [prefixWord, tailWord_5474436, baseEnd_5474436] using wordTrace_append hprefix tailTrace_5474436
  have hstable : (prefixWord ++ tailWord_5474436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5474436).length < 2 ^ (prefixWord ++ tailWord_5474436).sum := by decide
  have hdescent : baseEnd_5474436 < baseStart_5474436 := by decide
  rcases family_descends (prefixWord ++ tailWord_5474436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
