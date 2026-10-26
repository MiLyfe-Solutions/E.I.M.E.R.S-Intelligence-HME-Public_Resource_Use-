import V185TrunkScan23Chunk0464

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2750583 : List Nat := [1, 1, 3, 1, 1, 5, 3, 2, 1, 5]
def baseStart_2750583 : Nat := 118140960795 + 2750583 * 2 ^ 59
def prefixEnd_2750583 : Nat := 4983230072969 + 3 ^ 40 * 2750583 * 2
def baseEnd_2750583 : Nat := 470790386361972355020935

theorem tailTrace_2750583 : CollatzResearch.WordTrace tailWord_2750583 prefixEnd_2750583 470790386361972355020935 := by
  unfold tailWord_2750583
  simp only [CollatzResearch.WordTrace]
  refine ⟨100322003794115028021832403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66881335862743352014554935 100322003794115028021832403)
  ·
    refine ⟨150483005691172542032748605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100322003794115028021832403 150483005691172542032748605)
    ·
      refine ⟨56431127134189703262280727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150483005691172542032748605 56431127134189703262280727)
      ·
        refine ⟨84646690701284554893421091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56431127134189703262280727 84646690701284554893421091)
        ·
          refine ⟨126970036051926832340131637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84646690701284554893421091 126970036051926832340131637)
          ·
            refine ⟨11903440879868140531887341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 126970036051926832340131637 11903440879868140531887341)
            ·
              refine ⟨4463790329950552699457753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11903440879868140531887341 4463790329950552699457753)
              ·
                refine ⟨3347842747462914524593315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4463790329950552699457753 3347842747462914524593315)
                ·
                  refine ⟨5021764121194371786889973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3347842747462914524593315 5021764121194371786889973)
                  ·
                    refine ⟨470790386361972355020935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5021764121194371786889973 470790386361972355020935)
                    ·
                      rfl

theorem cell23_2750583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 2, 1, 5].length) (baseStart_2750583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2750583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2750583 prefixEnd_2750583 := by exact prefixLift 2750583
  have htrace : WordTrace (prefixWord ++ tailWord_2750583) baseStart_2750583 baseEnd_2750583 := by
    simpa [prefixWord, tailWord_2750583, baseEnd_2750583] using wordTrace_append hprefix tailTrace_2750583
  have hstable : (prefixWord ++ tailWord_2750583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750583).length < 2 ^ (prefixWord ++ tailWord_2750583).sum := by decide
  have hdescent : baseEnd_2750583 < baseStart_2750583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750637 : List Nat := [1, 5, 2, 1, 2, 1, 1, 1, 5, 2, 2]
def baseStart_2750637 : Nat := 118140960795 + 2750637 * 2 ^ 59
def prefixEnd_2750637 : Nat := 4983230072969 + 3 ^ 40 * 2750637 * 2
def baseEnd_2750637 : Nat := 1412398887041259853787557

theorem tailTrace_2750637 : CollatzResearch.WordTrace tailWord_2750637 prefixEnd_2750637 1412398887041259853787557 := by
  unfold tailWord_2750637
  simp only [CollatzResearch.WordTrace]
  refine ⟨100323973335919395244298165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66882648890612930162865443 100323973335919395244298165)
  ·
    refine ⟨9405372500242443304152953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 100323973335919395244298165 9405372500242443304152953)
    ·
      refine ⟨7054029375181832478114715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9405372500242443304152953 7054029375181832478114715)
      ·
        refine ⟨10581044062772748717172073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7054029375181832478114715 10581044062772748717172073)
        ·
          refine ⟨7935783047079561537879055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10581044062772748717172073 7935783047079561537879055)
          ·
            refine ⟨11903674570619342306818583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7935783047079561537879055 11903674570619342306818583)
            ·
              refine ⟨17855511855929013460227875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11903674570619342306818583 17855511855929013460227875)
              ·
                refine ⟨26783267783893520190341813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17855511855929013460227875 26783267783893520190341813)
                ·
                  refine ⟨2510931354740017517844545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26783267783893520190341813 2510931354740017517844545)
                  ·
                    refine ⟨1883198516055013138383409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2510931354740017517844545 1883198516055013138383409)
                    ·
                      refine ⟨1412398887041259853787557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1883198516055013138383409 1412398887041259853787557)
                      ·
                        rfl

theorem cell23_2750637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_2750637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2750637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2750637 prefixEnd_2750637 := by exact prefixLift 2750637
  have htrace : WordTrace (prefixWord ++ tailWord_2750637) baseStart_2750637 baseEnd_2750637 := by
    simpa [prefixWord, tailWord_2750637, baseEnd_2750637] using wordTrace_append hprefix tailTrace_2750637
  have hstable : (prefixWord ++ tailWord_2750637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750637).length < 2 ^ (prefixWord ++ tailWord_2750637).sum := by decide
  have hdescent : baseEnd_2750637 < baseStart_2750637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750654 : List Nat := [4, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4]
def baseStart_2750654 : Nat := 118140960795 + 2750654 * 2 ^ 59
def prefixEnd_2750654 : Nat := 4983230072969 + 3 ^ 40 * 2750654 * 2
def baseEnd_2750654 : Nat := 1412407616212386287274979

theorem tailTrace_2750654 : CollatzResearch.WordTrace tailWord_2750654 prefixEnd_2750654 1412407616212386287274979 := by
  unfold tailWord_2750654
  simp only [CollatzResearch.WordTrace]
  refine ⟨12540574172107225893458377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66883062251238538098444677 12540574172107225893458377)
  ·
    refine ⟨9405430629080419420093783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12540574172107225893458377 9405430629080419420093783)
    ·
      refine ⟨14108145943620629130140675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9405430629080419420093783 14108145943620629130140675)
      ·
        refine ⟨21162218915430943695211013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14108145943620629130140675 21162218915430943695211013)
        ·
          refine ⟨3967916046643301942852065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21162218915430943695211013 3967916046643301942852065)
          ·
            refine ⟨2975937034982476457139049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3967916046643301942852065 2975937034982476457139049)
            ·
              refine ⟨2231952776236857342854287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2975937034982476457139049 2231952776236857342854287)
              ·
                refine ⟨3347929164355286014281431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2231952776236857342854287 3347929164355286014281431)
                ·
                  refine ⟨5021893746532929021422147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3347929164355286014281431 5021893746532929021422147)
                  ·
                    refine ⟨7532840619799393532133221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5021893746532929021422147 7532840619799393532133221)
                    ·
                      refine ⟨1412407616212386287274979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7532840619799393532133221 1412407616212386287274979)
                      ·
                        rfl

theorem cell23_2750654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4].length) (baseStart_2750654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2750654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2750654 prefixEnd_2750654 := by exact prefixLift 2750654
  have htrace : WordTrace (prefixWord ++ tailWord_2750654) baseStart_2750654 baseEnd_2750654 := by
    simpa [prefixWord, tailWord_2750654, baseEnd_2750654] using wordTrace_append hprefix tailTrace_2750654
  have hstable : (prefixWord ++ tailWord_2750654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750654).length < 2 ^ (prefixWord ++ tailWord_2750654).sum := by decide
  have hdescent : baseEnd_2750654 < baseStart_2750654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750684 : List Nat := [2, 2, 5, 2, 1, 2, 1, 1, 1, 2, 4]
def baseStart_2750684 : Nat := 118140960795 + 2750684 * 2 ^ 59
def prefixEnd_2750684 : Nat := 4983230072969 + 3 ^ 40 * 2750684 * 2
def baseEnd_2750684 : Nat := 1412423020632021169899841

theorem tailTrace_2750684 : CollatzResearch.WordTrace tailWord_2750684 prefixEnd_2750684 1412423020632021169899841 := by
  unfold tailWord_2750684
  simp only [CollatzResearch.WordTrace]
  refine ⟨50162843783374561135629553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66883791711166081514172737 50162843783374561135629553)
  ·
    refine ⟨37622132837530920851722165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50162843783374561135629553 37622132837530920851722165)
    ·
      refine ⟨3527074953518523829848953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37622132837530920851722165 3527074953518523829848953)
      ·
        refine ⟨2645306215138892872386715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3527074953518523829848953 2645306215138892872386715)
        ·
          refine ⟨3967959322708339308580073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2645306215138892872386715 3967959322708339308580073)
          ·
            refine ⟨2975969492031254481435055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3967959322708339308580073 2975969492031254481435055)
            ·
              refine ⟨4463954238046881722152583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2975969492031254481435055 4463954238046881722152583)
              ·
                refine ⟨6695931357070322583228875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4463954238046881722152583 6695931357070322583228875)
                ·
                  refine ⟨10043897035605483874843313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6695931357070322583228875 10043897035605483874843313)
                  ·
                    refine ⟨7532922776704112906132485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10043897035605483874843313 7532922776704112906132485)
                    ·
                      refine ⟨1412423020632021169899841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7532922776704112906132485 1412423020632021169899841)
                      ·
                        rfl

theorem cell23_2750684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_2750684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2750684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2750684 prefixEnd_2750684 := by exact prefixLift 2750684
  have htrace : WordTrace (prefixWord ++ tailWord_2750684) baseStart_2750684 baseEnd_2750684 := by
    simpa [prefixWord, tailWord_2750684, baseEnd_2750684] using wordTrace_append hprefix tailTrace_2750684
  have hstable : (prefixWord ++ tailWord_2750684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750684).length < 2 ^ (prefixWord ++ tailWord_2750684).sum := by decide
  have hdescent : baseEnd_2750684 < baseStart_2750684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750773 : List Nat := [1, 3, 3, 1, 2, 1, 1, 1, 3, 2, 5]
def baseStart_2750773 : Nat := 118140960795 + 2750773 * 2 ^ 59
def prefixEnd_2750773 : Nat := 4983230072969 + 3 ^ 40 * 2750773 * 2
def baseEnd_2750773 : Nat := 1412468720410271321686931

theorem tailTrace_2750773 : CollatzResearch.WordTrace tailWord_2750773 prefixEnd_2750773 1412468720410271321686931 := by
  unfold tailWord_2750773
  simp only [CollatzResearch.WordTrace]
  refine ⟨100328933663426690471248973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66885955775617793647499315 100328933663426690471248973)
  ·
    refine ⟨37623350123785008926718365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100328933663426690471248973 37623350123785008926718365)
    ·
      refine ⟨14108756296419378347519387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37623350123785008926718365 14108756296419378347519387)
      ·
        refine ⟨21163134444629067521279081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14108756296419378347519387 21163134444629067521279081)
        ·
          refine ⟨15872350833471800640959311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21163134444629067521279081 15872350833471800640959311)
          ·
            refine ⟨23808526250207700961438967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15872350833471800640959311 23808526250207700961438967)
            ·
              refine ⟨35712789375311551442158451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23808526250207700961438967 35712789375311551442158451)
              ·
                refine ⟨53569184062967327163237677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35712789375311551442158451 53569184062967327163237677)
                ·
                  refine ⟨20088444023612747686214129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53569184062967327163237677 20088444023612747686214129)
                  ·
                    refine ⟨15066333017709560764660597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20088444023612747686214129 15066333017709560764660597)
                    ·
                      refine ⟨1412468720410271321686931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15066333017709560764660597 1412468720410271321686931)
                      ·
                        rfl

theorem cell23_2750773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_2750773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2750773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2750773 prefixEnd_2750773 := by exact prefixLift 2750773
  have htrace : WordTrace (prefixWord ++ tailWord_2750773) baseStart_2750773 baseEnd_2750773 := by
    simpa [prefixWord, tailWord_2750773, baseEnd_2750773] using wordTrace_append hprefix tailTrace_2750773
  have hstable : (prefixWord ++ tailWord_2750773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750773).length < 2 ^ (prefixWord ++ tailWord_2750773).sum := by decide
  have hdescent : baseEnd_2750773 < baseStart_2750773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750800 : List Nat := [2, 1, 1, 1, 1, 6, 1, 1, 1, 6, 2]
def baseStart_2750800 : Nat := 118140960795 + 2750800 * 2 ^ 59
def prefixEnd_2750800 : Nat := 4983230072969 + 3 ^ 40 * 2750800 * 2
def baseEnd_2750800 : Nat := 1412482584387942716049307

theorem tailTrace_2750800 : CollatzResearch.WordTrace tailWord_2750800 prefixEnd_2750800 1412482584387942716049307 := by
  unfold tailWord_2750800
  simp only [CollatzResearch.WordTrace]
  refine ⟨50164959217164437041240927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66886612289552582721654569 50164959217164437041240927)
  ·
    refine ⟨75247438825746655561861391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50164959217164437041240927 75247438825746655561861391)
    ·
      refine ⟨112871158238619983342792087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75247438825746655561861391 112871158238619983342792087)
      ·
        refine ⟨169306737357929975014188131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112871158238619983342792087 169306737357929975014188131)
        ·
          refine ⟨253960106036894962521282197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169306737357929975014188131 253960106036894962521282197)
          ·
            refine ⟨11904379970479451368185103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 253960106036894962521282197 11904379970479451368185103)
            ·
              refine ⟨17856569955719177052277655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11904379970479451368185103 17856569955719177052277655)
              ·
                refine ⟨26784854933578765578416483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17856569955719177052277655 26784854933578765578416483)
                ·
                  refine ⟨40177282400368148367624725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26784854933578765578416483 40177282400368148367624725)
                  ·
                    refine ⟨1883310112517256954732409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 40177282400368148367624725 1883310112517256954732409)
                    ·
                      refine ⟨1412482584387942716049307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1883310112517256954732409 1412482584387942716049307)
                      ·
                        rfl

theorem cell23_2750800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 1, 6, 2].length) (baseStart_2750800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2750800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2750800 prefixEnd_2750800 := by exact prefixLift 2750800
  have htrace : WordTrace (prefixWord ++ tailWord_2750800) baseStart_2750800 baseEnd_2750800 := by
    simpa [prefixWord, tailWord_2750800, baseEnd_2750800] using wordTrace_append hprefix tailTrace_2750800
  have hstable : (prefixWord ++ tailWord_2750800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750800).length < 2 ^ (prefixWord ++ tailWord_2750800).sum := by decide
  have hdescent : baseEnd_2750800 < baseStart_2750800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750820 : List Nat := [2, 3, 1, 1, 3, 1, 3, 1, 1, 4, 3]
def baseStart_2750820 : Nat := 118140960795 + 2750820 * 2 ^ 59
def prefixEnd_2750820 : Nat := 4983230072969 + 3 ^ 40 * 2750820 * 2
def baseEnd_2750820 : Nat := 1412492854001032637799215

theorem tailTrace_2750820 : CollatzResearch.WordTrace tailWord_2750820 prefixEnd_2750820 1412492854001032637799215 := by
  unfold tailWord_2750820
  simp only [CollatzResearch.WordTrace]
  refine ⟨50165323947128208749104957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66887098596170944998806609 50165323947128208749104957)
  ·
    refine ⟨18811996480173078280914359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50165323947128208749104957 18811996480173078280914359)
    ·
      refine ⟨28217994720259617421371539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18811996480173078280914359 28217994720259617421371539)
      ·
        refine ⟨42326992080389426132057309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28217994720259617421371539 42326992080389426132057309)
        ·
          refine ⟨15872622030146034799521491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42326992080389426132057309 15872622030146034799521491)
          ·
            refine ⟨23808933045219052199282237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15872622030146034799521491 23808933045219052199282237)
            ·
              refine ⟨8928349891957144574730839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23808933045219052199282237 8928349891957144574730839)
              ·
                refine ⟨13392524837935716862096259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8928349891957144574730839 13392524837935716862096259)
                ·
                  refine ⟨20088787256903575293144389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13392524837935716862096259 20088787256903575293144389)
                  ·
                    refine ⟨3766647610669420367464573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20088787256903575293144389 3766647610669420367464573)
                    ·
                      refine ⟨1412492854001032637799215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3766647610669420367464573 1412492854001032637799215)
                      ·
                        rfl

theorem cell23_2750820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 1, 4, 3].length) (baseStart_2750820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2750820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2750820 prefixEnd_2750820 := by exact prefixLift 2750820
  have htrace : WordTrace (prefixWord ++ tailWord_2750820) baseStart_2750820 baseEnd_2750820 := by
    simpa [prefixWord, tailWord_2750820, baseEnd_2750820] using wordTrace_append hprefix tailTrace_2750820
  have hstable : (prefixWord ++ tailWord_2750820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750820).length < 2 ^ (prefixWord ++ tailWord_2750820).sum := by decide
  have hdescent : baseEnd_2750820 < baseStart_2750820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750843 : List Nat := [1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 6]
def baseStart_2750843 : Nat := 118140960795 + 2750843 * 2 ^ 59
def prefixEnd_2750843 : Nat := 4983230072969 + 3 ^ 40 * 2750843 * 2
def baseEnd_2750843 : Nat := 1412504664056086047811609

theorem tailTrace_2750843 : CollatzResearch.WordTrace tailWord_2750843 prefixEnd_2750843 1412504664056086047811609 := by
  unfold tailWord_2750843
  simp only [CollatzResearch.WordTrace]
  refine ⟨100331486773173092426297183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66887657848782061617531455 100331486773173092426297183)
  ·
    refine ⟨150497230159759638639445775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100331486773173092426297183 150497230159759638639445775)
    ·
      refine ⟨225745845239639457959168663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150497230159759638639445775 225745845239639457959168663)
      ·
        refine ⟨338618767859459186938752995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225745845239639457959168663 338618767859459186938752995)
        ·
          refine ⟨507928151789188780408129493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338618767859459186938752995 507928151789188780408129493)
          ·
            refine ⟨11904566057559112040815535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 507928151789188780408129493 11904566057559112040815535)
            ·
              refine ⟨17856849086338668061223303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11904566057559112040815535 17856849086338668061223303)
              ·
                refine ⟨26785273629508002091834955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17856849086338668061223303 26785273629508002091834955)
                ·
                  refine ⟨40177910444262003137752433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26785273629508002091834955 40177910444262003137752433)
                  ·
                    refine ⟨30133432833196502353314325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40177910444262003137752433 30133432833196502353314325)
                    ·
                      refine ⟨1412504664056086047811609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30133432833196502353314325 1412504664056086047811609)
                      ·
                        rfl

theorem cell23_2750843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 6].length) (baseStart_2750843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2750843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2750843 prefixEnd_2750843 := by exact prefixLift 2750843
  have htrace : WordTrace (prefixWord ++ tailWord_2750843) baseStart_2750843 baseEnd_2750843 := by
    simpa [prefixWord, tailWord_2750843, baseEnd_2750843] using wordTrace_append hprefix tailTrace_2750843
  have hstable : (prefixWord ++ tailWord_2750843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750843).length < 2 ^ (prefixWord ++ tailWord_2750843).sum := by decide
  have hdescent : baseEnd_2750843 < baseStart_2750843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750857 : List Nat := [1, 2, 1, 1, 6, 2, 3, 1, 6]
def baseStart_2750857 : Nat := 118140960795 + 2750857 * 2 ^ 59
def prefixEnd_2750857 : Nat := 4983230072969 + 3 ^ 40 * 2750857 * 2
def baseEnd_2750857 : Nat := 156945761420583221448505

theorem tailTrace_2750857 : CollatzResearch.WordTrace tailWord_2750857 prefixEnd_2750857 156945761420583221448505 := by
  unfold tailWord_2750857
  simp only [CollatzResearch.WordTrace]
  refine ⟨100331997395122372817306825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66887998263414915211537883 100331997395122372817306825)
  ·
    refine ⟨75248998046341779612980119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100331997395122372817306825 75248998046341779612980119)
    ·
      refine ⟨112873497069512669419470179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75248998046341779612980119 112873497069512669419470179)
      ·
        refine ⟨169310245604269004129205269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112873497069512669419470179 169310245604269004129205269)
        ·
          refine ⟨7936417762700109568556497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 169310245604269004129205269 7936417762700109568556497)
          ·
            refine ⟨5952313322025082176417373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7936417762700109568556497 5952313322025082176417373)
            ·
              refine ⟨2232117495759405816156515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5952313322025082176417373 2232117495759405816156515)
              ·
                refine ⟨3348176243639108724234773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2232117495759405816156515 3348176243639108724234773)
                ·
                  refine ⟨156945761420583221448505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3348176243639108724234773 156945761420583221448505)
                  ·
                    rfl

theorem cell23_2750857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 1, 6].length) (baseStart_2750857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2750857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2750857 prefixEnd_2750857 := by exact prefixLift 2750857
  have htrace : WordTrace (prefixWord ++ tailWord_2750857) baseStart_2750857 baseEnd_2750857 := by
    simpa [prefixWord, tailWord_2750857, baseEnd_2750857] using wordTrace_append hprefix tailTrace_2750857
  have hstable : (prefixWord ++ tailWord_2750857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750857).length < 2 ^ (prefixWord ++ tailWord_2750857).sum := by decide
  have hdescent : baseEnd_2750857 < baseStart_2750857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750878 : List Nat := [4, 3, 1, 2, 1, 3, 1, 3, 1, 4]
def baseStart_2750878 : Nat := 118140960795 + 2750878 * 2 ^ 59
def prefixEnd_2750878 : Nat := 4983230072969 + 3 ^ 40 * 2750878 * 2
def baseEnd_2750878 : Nat := 470840878626331136957983

theorem tailTrace_2750878 : CollatzResearch.WordTrace tailWord_2750878 prefixEnd_2750878 470840878626331136957983 := by
  unfold tailWord_2750878
  simp only [CollatzResearch.WordTrace]
  refine ⟨12541595416005786675477661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66888508885364195602547525 12541595416005786675477661)
  ·
    refine ⟨4703098281002170003304123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12541595416005786675477661 4703098281002170003304123)
    ·
      refine ⟨7054647421503255004956185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4703098281002170003304123 7054647421503255004956185)
      ·
        refine ⟨5290985566127441253717139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7054647421503255004956185 5290985566127441253717139)
        ·
          refine ⟨7936478349191161880575709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5290985566127441253717139 7936478349191161880575709)
          ·
            refine ⟨2976179380946685705215891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7936478349191161880575709 2976179380946685705215891)
            ·
              refine ⟨4464269071420028557823837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2976179380946685705215891 4464269071420028557823837)
              ·
                refine ⟨1674100901782510709183939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4464269071420028557823837 1674100901782510709183939)
                ·
                  refine ⟨2511151352673766063775909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1674100901782510709183939 2511151352673766063775909)
                  ·
                    refine ⟨470840878626331136957983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2511151352673766063775909 470840878626331136957983)
                    ·
                      rfl

theorem cell23_2750878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_2750878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2750878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2750878 prefixEnd_2750878 := by exact prefixLift 2750878
  have htrace : WordTrace (prefixWord ++ tailWord_2750878) baseStart_2750878 baseEnd_2750878 := by
    simpa [prefixWord, tailWord_2750878, baseEnd_2750878] using wordTrace_append hprefix tailTrace_2750878
  have hstable : (prefixWord ++ tailWord_2750878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750878).length < 2 ^ (prefixWord ++ tailWord_2750878).sum := by decide
  have hdescent : baseEnd_2750878 < baseStart_2750878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750887 : List Nat := [1, 1, 6, 1, 1, 2, 2, 3, 1, 5]
def baseStart_2750887 : Nat := 118140960795 + 2750887 * 2 ^ 59
def prefixEnd_2750887 : Nat := 4983230072969 + 3 ^ 40 * 2750887 * 2
def baseEnd_2750887 : Nat := 470842419068294625220469

theorem tailTrace_2750887 : CollatzResearch.WordTrace tailWord_2750887 prefixEnd_2750887 470842419068294625220469 := by
  unfold tailWord_2750887
  simp only [CollatzResearch.WordTrace]
  refine ⟨100333091585013687940898915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66888727723342458627265943 100333091585013687940898915)
  ·
    refine ⟨150499637377520531911348373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100333091585013687940898915 150499637377520531911348373)
    ·
      refine ⟨7054670502071274933344455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 150499637377520531911348373 7054670502071274933344455)
      ·
        refine ⟨10582005753106912400016683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7054670502071274933344455 10582005753106912400016683)
        ·
          refine ⟨15873008629660368600025025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10582005753106912400016683 15873008629660368600025025)
          ·
            refine ⟨11904756472245276450018769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15873008629660368600025025 11904756472245276450018769)
            ·
              refine ⟨8928567354183957337514077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11904756472245276450018769 8928567354183957337514077)
              ·
                refine ⟨3348212757818984001567779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8928567354183957337514077 3348212757818984001567779)
                ·
                  refine ⟨5022319136728476002351669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3348212757818984001567779 5022319136728476002351669)
                  ·
                    refine ⟨470842419068294625220469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5022319136728476002351669 470842419068294625220469)
                    ·
                      rfl

theorem cell23_2750887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_2750887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2750887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2750887 prefixEnd_2750887 := by exact prefixLift 2750887
  have htrace : WordTrace (prefixWord ++ tailWord_2750887) baseStart_2750887 baseEnd_2750887 := by
    simpa [prefixWord, tailWord_2750887, baseEnd_2750887] using wordTrace_append hprefix tailTrace_2750887
  have hstable : (prefixWord ++ tailWord_2750887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750887).length < 2 ^ (prefixWord ++ tailWord_2750887).sum := by decide
  have hdescent : baseEnd_2750887 < baseStart_2750887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750901 : List Nat := [1, 3, 3, 2, 3, 2, 1, 1, 3, 1, 3]
def baseStart_2750901 : Nat := 118140960795 + 2750901 * 2 ^ 59
def prefixEnd_2750901 : Nat := 4983230072969 + 3 ^ 40 * 2750901 * 2
def baseEnd_2750901 : Nat := 1412534445934046820886343

theorem tailTrace_2750901 : CollatzResearch.WordTrace tailWord_2750901 prefixEnd_2750901 1412534445934046820886343 := by
  unfold tailWord_2750901
  simp only [CollatzResearch.WordTrace]
  refine ⟨100333602206962968331908557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66889068137975312221272371 100333602206962968331908557)
  ·
    refine ⟨37625100827611113124465709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100333602206962968331908557 37625100827611113124465709)
    ·
      refine ⟨14109412810354167421674641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37625100827611113124465709 14109412810354167421674641)
      ·
        refine ⟨10582059607765625566255981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14109412810354167421674641 10582059607765625566255981)
        ·
          refine ⟨3968272352912109587345993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10582059607765625566255981 3968272352912109587345993)
          ·
            refine ⟨2976204264684082190509495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3968272352912109587345993 2976204264684082190509495)
            ·
              refine ⟨4464306397026123285764243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2976204264684082190509495 4464306397026123285764243)
              ·
                refine ⟨6696459595539184928646365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4464306397026123285764243 6696459595539184928646365)
                ·
                  refine ⟨2511172348327194348242387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6696459595539184928646365 2511172348327194348242387)
                  ·
                    refine ⟨3766758522490791522363581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2511172348327194348242387 3766758522490791522363581)
                    ·
                      refine ⟨1412534445934046820886343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3766758522490791522363581 1412534445934046820886343)
                      ·
                        rfl

theorem cell23_2750901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_2750901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2750901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2750901 prefixEnd_2750901 := by exact prefixLift 2750901
  have htrace : WordTrace (prefixWord ++ tailWord_2750901) baseStart_2750901 baseEnd_2750901 := by
    simpa [prefixWord, tailWord_2750901, baseEnd_2750901] using wordTrace_append hprefix tailTrace_2750901
  have hstable : (prefixWord ++ tailWord_2750901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750901).length < 2 ^ (prefixWord ++ tailWord_2750901).sum := by decide
  have hdescent : baseEnd_2750901 < baseStart_2750901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750907 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 9, 2, 2]
def baseStart_2750907 : Nat := 118140960795 + 2750907 * 2 ^ 59
def prefixEnd_2750907 : Nat := 4983230072969 + 3 ^ 40 * 2750907 * 2
def baseEnd_2750907 : Nat := 1412537526817973797411315

theorem tailTrace_2750907 : CollatzResearch.WordTrace tailWord_2750907 prefixEnd_2750907 1412537526817973797411315 := by
  unfold tailWord_2750907
  simp only [CollatzResearch.WordTrace]
  refine ⟨100333821044941231356626975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66889214029960820904417983 100333821044941231356626975)
  ·
    refine ⟨150500731567411847034940463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100333821044941231356626975 150500731567411847034940463)
    ·
      refine ⟨225751097351117770552410695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150500731567411847034940463 225751097351117770552410695)
      ·
        refine ⟨338626646026676655828616043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225751097351117770552410695 338626646026676655828616043)
        ·
          refine ⟨507939969040014983742924065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338626646026676655828616043 507939969040014983742924065)
          ·
            refine ⟨380954976780011237807193049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 507939969040014983742924065 380954976780011237807193049)
            ·
              refine ⟨285716232585008428355394787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 380954976780011237807193049 285716232585008428355394787)
              ·
                refine ⟨428574348877512642533092181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 285716232585008428355394787 428574348877512642533092181)
                ·
                  refine ⟨2511177825454175639842337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 428574348877512642533092181 2511177825454175639842337)
                  ·
                    refine ⟨1883383369090631729881753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2511177825454175639842337 1883383369090631729881753)
                    ·
                      refine ⟨1412537526817973797411315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1883383369090631729881753 1412537526817973797411315)
                      ·
                        rfl

theorem cell23_2750907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 9, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 9, 2, 2].length) (baseStart_2750907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2750907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2750907 prefixEnd_2750907 := by exact prefixLift 2750907
  have htrace : WordTrace (prefixWord ++ tailWord_2750907) baseStart_2750907 baseEnd_2750907 := by
    simpa [prefixWord, tailWord_2750907, baseEnd_2750907] using wordTrace_append hprefix tailTrace_2750907
  have hstable : (prefixWord ++ tailWord_2750907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750907).length < 2 ^ (prefixWord ++ tailWord_2750907).sum := by decide
  have hdescent : baseEnd_2750907 < baseStart_2750907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750920 : List Nat := [2, 1, 3, 1, 3, 2, 2, 1, 1, 1, 6]
def baseStart_2750920 : Nat := 118140960795 + 2750920 * 2 ^ 59
def prefixEnd_2750920 : Nat := 4983230072969 + 3 ^ 40 * 2750920 * 2
def baseEnd_2750920 : Nat := 1412544202066482246548755

theorem tailTrace_2750920 : CollatzResearch.WordTrace tailWord_2750920 prefixEnd_2750920 1412544202066482246548755 := by
  unfold tailWord_2750920
  simp only [CollatzResearch.WordTrace]
  refine ⟨50167147596947067288425107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66889530129262756384566809 50167147596947067288425107)
  ·
    refine ⟨75250721395420600932637661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50167147596947067288425107 75250721395420600932637661)
    ·
      refine ⟨28219020523282725349739123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75250721395420600932637661 28219020523282725349739123)
      ·
        refine ⟨42328530784924088024608685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28219020523282725349739123 42328530784924088024608685)
        ·
          refine ⟨15873199044346533009228257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42328530784924088024608685 15873199044346533009228257)
          ·
            refine ⟨11904899283259899756921193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15873199044346533009228257 11904899283259899756921193)
            ·
              refine ⟨8928674462444924817690895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11904899283259899756921193 8928674462444924817690895)
              ·
                refine ⟨13393011693667387226536343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8928674462444924817690895 13393011693667387226536343)
                ·
                  refine ⟨20089517540501080839804515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13393011693667387226536343 20089517540501080839804515)
                  ·
                    refine ⟨30134276310751621259706773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20089517540501080839804515 30134276310751621259706773)
                    ·
                      refine ⟨1412544202066482246548755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30134276310751621259706773 1412544202066482246548755)
                      ·
                        rfl

theorem cell23_2750920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_2750920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2750920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2750920 prefixEnd_2750920 := by exact prefixLift 2750920
  have htrace : WordTrace (prefixWord ++ tailWord_2750920) baseStart_2750920 baseEnd_2750920 := by
    simpa [prefixWord, tailWord_2750920, baseEnd_2750920] using wordTrace_append hprefix tailTrace_2750920
  have hstable : (prefixWord ++ tailWord_2750920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750920).length < 2 ^ (prefixWord ++ tailWord_2750920).sum := by decide
  have hdescent : baseEnd_2750920 < baseStart_2750920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750944 : List Nat := [2, 1, 1, 3, 1, 1, 7, 1, 1, 2, 3]
def baseStart_2750944 : Nat := 118140960795 + 2750944 * 2 ^ 59
def prefixEnd_2750944 : Nat := 4983230072969 + 3 ^ 40 * 2750944 * 2
def baseEnd_2750944 : Nat := 1412556525602190152648645

theorem tailTrace_2750944 : CollatzResearch.WordTrace tailWord_2750944 prefixEnd_2750944 1412556525602190152648645 := by
  unfold tailWord_2750944
  simp only [CollatzResearch.WordTrace]
  refine ⟨50167585272903593337861943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66890113697204791117149257 50167585272903593337861943)
  ·
    refine ⟨75251377909355390006792915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50167585272903593337861943 75251377909355390006792915)
    ·
      refine ⟨112877066864033085010189373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75251377909355390006792915 112877066864033085010189373)
      ·
        refine ⟨42328900074012406878821015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112877066864033085010189373 42328900074012406878821015)
        ·
          refine ⟨63493350111018610318231523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42328900074012406878821015 63493350111018610318231523)
          ·
            refine ⟨95240025166527915477347285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63493350111018610318231523 95240025166527915477347285)
            ·
              refine ⟨2232188089840498019000327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 95240025166527915477347285 2232188089840498019000327)
              ·
                refine ⟨3348282134760747028500491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2232188089840498019000327 3348282134760747028500491)
                ·
                  refine ⟨5022423202141120542750737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3348282134760747028500491 5022423202141120542750737)
                  ·
                    refine ⟨3766817401605840407063053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5022423202141120542750737 3766817401605840407063053)
                    ·
                      refine ⟨1412556525602190152648645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3766817401605840407063053 1412556525602190152648645)
                      ·
                        rfl

theorem cell23_2750944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 1, 1, 2, 3].length) (baseStart_2750944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2750944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2750944 prefixEnd_2750944 := by exact prefixLift 2750944
  have htrace : WordTrace (prefixWord ++ tailWord_2750944) baseStart_2750944 baseEnd_2750944 := by
    simpa [prefixWord, tailWord_2750944, baseEnd_2750944] using wordTrace_append hprefix tailTrace_2750944
  have hstable : (prefixWord ++ tailWord_2750944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750944).length < 2 ^ (prefixWord ++ tailWord_2750944).sum := by decide
  have hdescent : baseEnd_2750944 < baseStart_2750944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750958 : List Nat := [4, 1, 2, 1, 2, 3, 1, 4, 1, 2, 2]
def baseStart_2750958 : Nat := 118140960795 + 2750958 * 2 ^ 59
def prefixEnd_2750958 : Nat := 4983230072969 + 3 ^ 40 * 2750958 * 2
def baseEnd_2750958 : Nat := 1412563714331353097873581

theorem tailTrace_2750958 : CollatzResearch.WordTrace tailWord_2750958 prefixEnd_2750958 1412563714331353097873581 := by
  unfold tailWord_2750958
  simp only [CollatzResearch.WordTrace]
  refine ⟨12541960145969558383341691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66890454111837644711155685 12541960145969558383341691)
  ·
    refine ⟨18812940218954337575012537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12541960145969558383341691 18812940218954337575012537)
    ·
      refine ⟨14109705164215753181259403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18812940218954337575012537 14109705164215753181259403)
      ·
        refine ⟨21164557746323629771889105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14109705164215753181259403 21164557746323629771889105)
        ·
          refine ⟨15873418309742722328916829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21164557746323629771889105 15873418309742722328916829)
          ·
            refine ⟨5952531866153520873343811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15873418309742722328916829 5952531866153520873343811)
            ·
              refine ⟨8928797799230281310015717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5952531866153520873343811 8928797799230281310015717)
              ·
                refine ⟨1674149587355677745627947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8928797799230281310015717 1674149587355677745627947)
                ·
                  refine ⟨2511224381033516618441921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1674149587355677745627947 2511224381033516618441921)
                  ·
                    refine ⟨1883418285775137463831441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2511224381033516618441921 1883418285775137463831441)
                    ·
                      refine ⟨1412563714331353097873581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1883418285775137463831441 1412563714331353097873581)
                      ·
                        rfl

theorem cell23_2750958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 4, 1, 2, 2].length) (baseStart_2750958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2750958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2750958 prefixEnd_2750958 := by exact prefixLift 2750958
  have htrace : WordTrace (prefixWord ++ tailWord_2750958) baseStart_2750958 baseEnd_2750958 := by
    simpa [prefixWord, tailWord_2750958, baseEnd_2750958] using wordTrace_append hprefix tailTrace_2750958
  have hstable : (prefixWord ++ tailWord_2750958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750958).length < 2 ^ (prefixWord ++ tailWord_2750958).sum := by decide
  have hdescent : baseEnd_2750958 < baseStart_2750958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750984 : List Nat := [2, 1, 3, 2, 1, 1, 1, 6, 1, 3, 2]
def baseStart_2750984 : Nat := 118140960795 + 2750984 * 2 ^ 59
def prefixEnd_2750984 : Nat := 4983230072969 + 3 ^ 40 * 2750984 * 2
def baseEnd_2750984 : Nat := 1412577064828369996148461

theorem tailTrace_2750984 : CollatzResearch.WordTrace tailWord_2750984 prefixEnd_2750984 1412577064828369996148461 := by
  unfold tailWord_2750984
  simp only [CollatzResearch.WordTrace]
  refine ⟨50168314732831136753590003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66891086310441515671453337 50168314732831136753590003)
  ·
    refine ⟨75252472099246705130385005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50168314732831136753590003 75252472099246705130385005)
    ·
      refine ⟨28219677037217514423894377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75252472099246705130385005 28219677037217514423894377)
      ·
        refine ⟨21164757777913135817920783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28219677037217514423894377 21164757777913135817920783)
        ·
          refine ⟨31747136666869703726881175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21164757777913135817920783 31747136666869703726881175)
          ·
            refine ⟨47620705000304555590321763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31747136666869703726881175 47620705000304555590321763)
            ·
              refine ⟨71431057500456833385482645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47620705000304555590321763 71431057500456833385482645)
              ·
                refine ⟨3348330820333914064944499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 71431057500456833385482645 3348330820333914064944499)
                ·
                  refine ⟨5022496230500871097416749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3348330820333914064944499 5022496230500871097416749)
                  ·
                    refine ⟨1883436086437826661531281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5022496230500871097416749 1883436086437826661531281)
                    ·
                      refine ⟨1412577064828369996148461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1883436086437826661531281 1412577064828369996148461)
                      ·
                        rfl

theorem cell23_2750984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 6, 1, 3, 2].length) (baseStart_2750984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2750984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2750984 prefixEnd_2750984 := by exact prefixLift 2750984
  have htrace : WordTrace (prefixWord ++ tailWord_2750984) baseStart_2750984 baseEnd_2750984 := by
    simpa [prefixWord, tailWord_2750984, baseEnd_2750984] using wordTrace_append hprefix tailTrace_2750984
  have hstable : (prefixWord ++ tailWord_2750984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750984).length < 2 ^ (prefixWord ++ tailWord_2750984).sum := by decide
  have hdescent : baseEnd_2750984 < baseStart_2750984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751008 : List Nat := [2, 1, 1, 6, 2, 2, 1, 2, 2, 1, 3]
def baseStart_2751008 : Nat := 118140960795 + 2751008 * 2 ^ 59
def prefixEnd_2751008 : Nat := 4983230072969 + 3 ^ 40 * 2751008 * 2
def baseEnd_2751008 : Nat := 1412589388364077902248351

theorem tailTrace_2751008 : CollatzResearch.WordTrace tailWord_2751008 prefixEnd_2751008 1412589388364077902248351 := by
  unfold tailWord_2751008
  simp only [CollatzResearch.WordTrace]
  refine ⟨50168752408787662803026839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66891669878383550404035785 50168752408787662803026839)
  ·
    refine ⟨75253128613181494204540259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50168752408787662803026839 75253128613181494204540259)
    ·
      refine ⟨112879692919772241306810389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75253128613181494204540259 112879692919772241306810389)
      ·
        refine ⟨5291235605614323811256737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 112879692919772241306810389 5291235605614323811256737)
        ·
          refine ⟨3968426704210742858442553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5291235605614323811256737 3968426704210742858442553)
          ·
            refine ⟨2976320028158057143831915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3968426704210742858442553 2976320028158057143831915)
            ·
              refine ⟨4464480042237085715747873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2976320028158057143831915 4464480042237085715747873)
              ·
                refine ⟨3348360031677814286810905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4464480042237085715747873 3348360031677814286810905)
                ·
                  refine ⟨2511270023758360715108179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3348360031677814286810905 2511270023758360715108179)
                  ·
                    refine ⟨3766905035637541072662269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2511270023758360715108179 3766905035637541072662269)
                    ·
                      refine ⟨1412589388364077902248351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3766905035637541072662269 1412589388364077902248351)
                      ·
                        rfl

theorem cell23_2751008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_2751008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751008 prefixEnd_2751008 := by exact prefixLift 2751008
  have htrace : WordTrace (prefixWord ++ tailWord_2751008) baseStart_2751008 baseEnd_2751008 := by
    simpa [prefixWord, tailWord_2751008, baseEnd_2751008] using wordTrace_append hprefix tailTrace_2751008
  have hstable : (prefixWord ++ tailWord_2751008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751008).length < 2 ^ (prefixWord ++ tailWord_2751008).sum := by decide
  have hdescent : baseEnd_2751008 < baseStart_2751008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751037 : List Nat := [1, 4, 1, 3, 2, 1, 2, 2, 7]
def baseStart_2751037 : Nat := 118140960795 + 2751037 * 2 ^ 59
def prefixEnd_2751037 : Nat := 4983230072969 + 3 ^ 40 * 2751037 * 2
def baseEnd_2751037 : Nat := 156956031033673143198413

theorem tailTrace_2751037 : CollatzResearch.WordTrace tailWord_2751037 prefixEnd_2751037 156956031033673143198413 := by
  unfold tailWord_2751037
  simp only [CollatzResearch.WordTrace]
  refine ⟨100338562534470263558859365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66892375022980175705906243 100338562534470263558859365)
  ·
    refine ⟨18813480475213174417286131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100338562534470263558859365 18813480475213174417286131)
    ·
      refine ⟨28220220712819761625929197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18813480475213174417286131 28220220712819761625929197)
      ·
        refine ⟨10582582767307410609723449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28220220712819761625929197 10582582767307410609723449)
        ·
          refine ⟨7936937075480557957292587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10582582767307410609723449 7936937075480557957292587)
          ·
            refine ⟨11905405613220836935938881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7936937075480557957292587 11905405613220836935938881)
            ·
              refine ⟨8929054209915627701954161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11905405613220836935938881 8929054209915627701954161)
              ·
                refine ⟨6696790657436720776465621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8929054209915627701954161 6696790657436720776465621)
                ·
                  refine ⟨156956031033673143198413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6696790657436720776465621 156956031033673143198413)
                  ·
                    rfl

theorem cell23_2751037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 7].length) (baseStart_2751037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751037 prefixEnd_2751037 := by exact prefixLift 2751037
  have htrace : WordTrace (prefixWord ++ tailWord_2751037) baseStart_2751037 baseEnd_2751037 := by
    simpa [prefixWord, tailWord_2751037, baseEnd_2751037] using wordTrace_append hprefix tailTrace_2751037
  have hstable : (prefixWord ++ tailWord_2751037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751037).length < 2 ^ (prefixWord ++ tailWord_2751037).sum := by decide
  have hdescent : baseEnd_2751037 < baseStart_2751037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751054 : List Nat := [4, 1, 1, 1, 1, 2, 5, 3, 5]
def baseStart_2751054 : Nat := 118140960795 + 2751054 * 2 ^ 59
def prefixEnd_2751054 : Nat := 4983230072969 + 3 ^ 40 * 2751054 * 2
def baseEnd_2751054 : Nat := 156957000941576080252571

theorem tailTrace_2751054 : CollatzResearch.WordTrace tailWord_2751054 prefixEnd_2751054 156957000941576080252571 := by
  unfold tailWord_2751054
  simp only [CollatzResearch.WordTrace]
  refine ⟨12542397821926084432778527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66892788383605783641485477 12542397821926084432778527)
  ·
    refine ⟨18813596732889126649167791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12542397821926084432778527 18813596732889126649167791)
    ·
      refine ⟨28220395099333689973751687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18813596732889126649167791 28220395099333689973751687)
      ·
        refine ⟨42330592649000534960627531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28220395099333689973751687 42330592649000534960627531)
        ·
          refine ⟨63495888973500802440941297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42330592649000534960627531 63495888973500802440941297)
          ·
            refine ⟨47621916730125601830705973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63495888973500802440941297 47621916730125601830705973)
            ·
              refine ⟨4464554693449275171628685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47621916730125601830705973 4464554693449275171628685)
              ·
                refine ⟨1674208010043478189360757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4464554693449275171628685 1674208010043478189360757)
                ·
                  refine ⟨156957000941576080252571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1674208010043478189360757 156957000941576080252571)
                  ·
                    rfl

theorem cell23_2751054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 3, 5].length) (baseStart_2751054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751054 prefixEnd_2751054 := by exact prefixLift 2751054
  have htrace : WordTrace (prefixWord ++ tailWord_2751054) baseStart_2751054 baseEnd_2751054 := by
    simpa [prefixWord, tailWord_2751054, baseEnd_2751054] using wordTrace_append hprefix tailTrace_2751054
  have hstable : (prefixWord ++ tailWord_2751054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751054).length < 2 ^ (prefixWord ++ tailWord_2751054).sum := by decide
  have hdescent : baseEnd_2751054 < baseStart_2751054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751104 : List Nat := [2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 4]
def baseStart_2751104 : Nat := 118140960795 + 2751104 * 2 ^ 59
def prefixEnd_2751104 : Nat := 4983230072969 + 3 ^ 40 * 2751104 * 2
def baseEnd_2751104 : Nat := 1412638682506909526647909

theorem tailTrace_2751104 : CollatzResearch.WordTrace tailWord_2751104 prefixEnd_2751104 1412638682506909526647909 := by
  unfold tailWord_2751104
  simp only [CollatzResearch.WordTrace]
  refine ⟨50170503112613767000774183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66894004150151689334365577 50170503112613767000774183)
  ·
    refine ⟨75255754668920650501161275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50170503112613767000774183 75255754668920650501161275)
    ·
      refine ⟨112883632003380975751741913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75255754668920650501161275 112883632003380975751741913)
      ·
        refine ⟨84662724002535731813806435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112883632003380975751741913 84662724002535731813806435)
        ·
          refine ⟨126994086003803597720709653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84662724002535731813806435 126994086003803597720709653)
          ·
            refine ⟨5952847781428293643158265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 126994086003803597720709653 5952847781428293643158265)
            ·
              refine ⟨4464635836071220232368699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5952847781428293643158265 4464635836071220232368699)
              ·
                refine ⟨6696953754106830348553049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4464635836071220232368699 6696953754106830348553049)
                ·
                  refine ⟨5022715315580122761414787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6696953754106830348553049 5022715315580122761414787)
                  ·
                    refine ⟨7534072973370184142122181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5022715315580122761414787 7534072973370184142122181)
                    ·
                      refine ⟨1412638682506909526647909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7534072973370184142122181 1412638682506909526647909)
                      ·
                        rfl

theorem cell23_2751104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 4].length) (baseStart_2751104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751104 prefixEnd_2751104 := by exact prefixLift 2751104
  have htrace : WordTrace (prefixWord ++ tailWord_2751104) baseStart_2751104 baseEnd_2751104 := by
    simpa [prefixWord, tailWord_2751104, baseEnd_2751104] using wordTrace_append hprefix tailTrace_2751104
  have hstable : (prefixWord ++ tailWord_2751104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751104).length < 2 ^ (prefixWord ++ tailWord_2751104).sum := by decide
  have hdescent : baseEnd_2751104 < baseStart_2751104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751107 : List Nat := [1, 1, 1, 3, 3, 1, 2, 3, 1, 4, 3]
def baseStart_2751107 : Nat := 118140960795 + 2751107 * 2 ^ 59
def prefixEnd_2751107 : Nat := 4983230072969 + 3 ^ 40 * 2751107 * 2
def baseEnd_2751107 : Nat := 1412640222948873014910395

theorem tailTrace_2751107 : CollatzResearch.WordTrace tailWord_2751107 prefixEnd_2751107 1412640222948873014910395 := by
  unfold tailWord_2751107
  simp only [CollatzResearch.WordTrace]
  refine ⟨100341115644216665513907575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66894077096144443675938383 100341115644216665513907575)
  ·
    refine ⟨150511673466324998270861363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100341115644216665513907575 150511673466324998270861363)
    ·
      refine ⟨225767510199487497406292045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150511673466324998270861363 225767510199487497406292045)
      ·
        refine ⟨84662816324807811527359517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 225767510199487497406292045 84662816324807811527359517)
        ·
          refine ⟨31748556121802929322759819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84662816324807811527359517 31748556121802929322759819)
          ·
            refine ⟨47622834182704393984139729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31748556121802929322759819 47622834182704393984139729)
            ·
              refine ⟨35717125637028295488104797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47622834182704393984139729 35717125637028295488104797)
              ·
                refine ⟨13393922113885610808039299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35717125637028295488104797 13393922113885610808039299)
                ·
                  refine ⟨20090883170828416212058949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13393922113885610808039299 20090883170828416212058949)
                  ·
                    refine ⟨3767040594530328039761053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20090883170828416212058949 3767040594530328039761053)
                    ·
                      refine ⟨1412640222948873014910395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3767040594530328039761053 1412640222948873014910395)
                      ·
                        rfl

theorem cell23_2751107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 4, 3].length) (baseStart_2751107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751107 prefixEnd_2751107 := by exact prefixLift 2751107
  have htrace : WordTrace (prefixWord ++ tailWord_2751107) baseStart_2751107 baseEnd_2751107 := by
    simpa [prefixWord, tailWord_2751107, baseEnd_2751107] using wordTrace_append hprefix tailTrace_2751107
  have hstable : (prefixWord ++ tailWord_2751107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751107).length < 2 ^ (prefixWord ++ tailWord_2751107).sum := by decide
  have hdescent : baseEnd_2751107 < baseStart_2751107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751158 : List Nat := [5, 1, 3, 1, 2, 1, 1, 1, 1, 4, 3]
def baseStart_2751158 : Nat := 118140960795 + 2751158 * 2 ^ 59
def prefixEnd_2751158 : Nat := 4983230072969 + 3 ^ 40 * 2751158 * 2
def baseEnd_2751158 : Nat := 1412666410462252315372661

theorem tailTrace_2751158 : CollatzResearch.WordTrace tailWord_2751158 prefixEnd_2751158 1412666410462252315372661 := by
  unfold tailWord_2751158
  simp only [CollatzResearch.WordTrace]
  refine ⟨6271435985439493826500883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66895317178021267482676085 6271435985439493826500883)
  ·
    refine ⟨9407153978159240739751325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6271435985439493826500883 9407153978159240739751325)
    ·
      refine ⟨3527682741809715277406747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9407153978159240739751325 3527682741809715277406747)
      ·
        refine ⟨5291524112714572916110121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3527682741809715277406747 5291524112714572916110121)
        ·
          refine ⟨3968643084535929687082591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5291524112714572916110121 3968643084535929687082591)
          ·
            refine ⟨5952964626803894530623887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3968643084535929687082591 5952964626803894530623887)
            ·
              refine ⟨8929446940205841795935831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5952964626803894530623887 8929446940205841795935831)
              ·
                refine ⟨13394170410308762693903747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8929446940205841795935831 13394170410308762693903747)
                ·
                  refine ⟨20091255615463144040855621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13394170410308762693903747 20091255615463144040855621)
                  ·
                    refine ⟨3767110427899339507660429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20091255615463144040855621 3767110427899339507660429)
                    ·
                      refine ⟨1412666410462252315372661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3767110427899339507660429 1412666410462252315372661)
                      ·
                        rfl

theorem cell23_2751158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_2751158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751158 prefixEnd_2751158 := by exact prefixLift 2751158
  have htrace : WordTrace (prefixWord ++ tailWord_2751158) baseStart_2751158 baseEnd_2751158 := by
    simpa [prefixWord, tailWord_2751158, baseEnd_2751158] using wordTrace_append hprefix tailTrace_2751158
  have hstable : (prefixWord ++ tailWord_2751158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751158).length < 2 ^ (prefixWord ++ tailWord_2751158).sum := by decide
  have hdescent : baseEnd_2751158 < baseStart_2751158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751204 : List Nat := [2, 3, 1, 1, 1, 4, 3, 1, 1, 6]
def baseStart_2751204 : Nat := 118140960795 + 2751204 * 2 ^ 59
def prefixEnd_2751204 : Nat := 4983230072969 + 3 ^ 40 * 2751204 * 2
def baseEnd_2751204 : Nat := 470896676857453045132483

theorem tailTrace_2751204 : CollatzResearch.WordTrace tailWord_2751204 prefixEnd_2751204 470896676857453045132483 := by
  unfold tailWord_2751204
  simp only [CollatzResearch.WordTrace]
  refine ⟨50172326762432625540094333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66896435683243500720125777 50172326762432625540094333)
  ·
    refine ⟨18814622535912234577535375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50172326762432625540094333 18814622535912234577535375)
    ·
      refine ⟨28221933803868351866303063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18814622535912234577535375 28221933803868351866303063)
      ·
        refine ⟨42332900705802527799454595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28221933803868351866303063 42332900705802527799454595)
        ·
          refine ⟨63499351058703791699181893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42332900705802527799454595 63499351058703791699181893)
          ·
            refine ⟨11906128323506960943596605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63499351058703791699181893 11906128323506960943596605)
            ·
              refine ⟨4464798121315110353848727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11906128323506960943596605 4464798121315110353848727)
              ·
                refine ⟨6697197181972665530773091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4464798121315110353848727 6697197181972665530773091)
                ·
                  refine ⟨10045795772958998296159637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6697197181972665530773091 10045795772958998296159637)
                  ·
                    refine ⟨470896676857453045132483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10045795772958998296159637 470896676857453045132483)
                    ·
                      rfl

theorem cell23_2751204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 1, 6].length) (baseStart_2751204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751204 prefixEnd_2751204 := by exact prefixLift 2751204
  have htrace : WordTrace (prefixWord ++ tailWord_2751204) baseStart_2751204 baseEnd_2751204 := by
    simpa [prefixWord, tailWord_2751204, baseEnd_2751204] using wordTrace_append hprefix tailTrace_2751204
  have hstable : (prefixWord ++ tailWord_2751204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751204).length < 2 ^ (prefixWord ++ tailWord_2751204).sum := by decide
  have hdescent : baseEnd_2751204 < baseStart_2751204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751217 : List Nat := [1, 2, 2, 2, 2, 2, 3, 9]
def baseStart_2751217 : Nat := 118140960795 + 2751217 * 2 ^ 59
def prefixEnd_2751217 : Nat := 4983230072969 + 3 ^ 40 * 2751217 * 2
def baseEnd_2751217 : Nat := 52322100215587688316107

theorem tailTrace_2751217 : CollatzResearch.WordTrace tailWord_2751217 prefixEnd_2751217 52322100215587688316107 := by
  unfold tailWord_2751217
  simp only [CollatzResearch.WordTrace]
  refine ⟨100345127673818154300411905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66896751782545436200274603 100345127673818154300411905)
  ·
    refine ⟨75258845755363615725308929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100345127673818154300411905 75258845755363615725308929)
    ·
      refine ⟨56444134316522711793981697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75258845755363615725308929 56444134316522711793981697)
      ·
        refine ⟨42333100737392033845486273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56444134316522711793981697 42333100737392033845486273)
        ·
          refine ⟨31749825553044025384114705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42333100737392033845486273 31749825553044025384114705)
          ·
            refine ⟨23812369164783019038086029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31749825553044025384114705 23812369164783019038086029)
            ·
              refine ⟨8929638436793632139282261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23812369164783019038086029 8929638436793632139282261)
              ·
                refine ⟨52322100215587688316107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8929638436793632139282261 52322100215587688316107)
                ·
                  rfl

theorem cell23_2751217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 9].length) (baseStart_2751217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751217 prefixEnd_2751217 := by exact prefixLift 2751217
  have htrace : WordTrace (prefixWord ++ tailWord_2751217) baseStart_2751217 baseEnd_2751217 := by
    simpa [prefixWord, tailWord_2751217, baseEnd_2751217] using wordTrace_append hprefix tailTrace_2751217
  have hstable : (prefixWord ++ tailWord_2751217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751217).length < 2 ^ (prefixWord ++ tailWord_2751217).sum := by decide
  have hdescent : baseEnd_2751217 < baseStart_2751217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751234 : List Nat := [3, 4, 1, 1, 1, 2, 11]
def baseStart_2751234 : Nat := 118140960795 + 2751234 * 2 ^ 59
def prefixEnd_2751234 : Nat := 4983230072969 + 3 ^ 40 * 2751234 * 2
def baseEnd_2751234 : Nat := 17440807839407333555831

theorem tailTrace_2751234 : CollatzResearch.WordTrace tailWord_2751234 prefixEnd_2751234 17440807839407333555831 := by
  unfold tailWord_2751234
  simp only [CollatzResearch.WordTrace]
  refine ⟨25086436928689141550945189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66897165143171044135853837 25086436928689141550945189)
  ·
    refine ⟨4703706924129214040802223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25086436928689141550945189 4703706924129214040802223)
    ·
      refine ⟨7055560386193821061203335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4703706924129214040802223 7055560386193821061203335)
      ·
        refine ⟨10583340579290731591805003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7055560386193821061203335 10583340579290731591805003)
        ·
          refine ⟨15875010868936097387707505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10583340579290731591805003 15875010868936097387707505)
          ·
            refine ⟨11906258151702073040780629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15875010868936097387707505 11906258151702073040780629)
            ·
              refine ⟨17440807839407333555831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 11906258151702073040780629 17440807839407333555831)
              ·
                rfl

theorem cell23_2751234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 11].length) (baseStart_2751234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751234 prefixEnd_2751234 := by exact prefixLift 2751234
  have htrace : WordTrace (prefixWord ++ tailWord_2751234) baseStart_2751234 baseEnd_2751234 := by
    simpa [prefixWord, tailWord_2751234, baseEnd_2751234] using wordTrace_append hprefix tailTrace_2751234
  have hstable : (prefixWord ++ tailWord_2751234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751234).length < 2 ^ (prefixWord ++ tailWord_2751234).sum := by decide
  have hdescent : baseEnd_2751234 < baseStart_2751234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751247 : List Nat := [1, 1, 2, 1, 1, 1, 6, 1, 2, 7]
def baseStart_2751247 : Nat := 118140960795 + 2751247 * 2 ^ 59
def prefixEnd_2751247 : Nat := 4983230072969 + 3 ^ 40 * 2751247 * 2
def baseEnd_2751247 : Nat := 470904036746834155719917

theorem tailTrace_2751247 : CollatzResearch.WordTrace tailWord_2751247 prefixEnd_2751247 470904036746834155719917 := by
  unfold tailWord_2751247
  simp only [CollatzResearch.WordTrace]
  refine ⟨100346221863709469424003995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66897481242472979616002663 100346221863709469424003995)
  ·
    refine ⟨150519332795564204136005993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100346221863709469424003995 150519332795564204136005993)
    ·
      refine ⟨112889499596673153102004495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150519332795564204136005993 112889499596673153102004495)
      ·
        refine ⟨169334249395009729653006743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112889499596673153102004495 169334249395009729653006743)
        ·
          refine ⟨254001374092514594479510115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169334249395009729653006743 254001374092514594479510115)
          ·
            refine ⟨381002061138771891719265173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254001374092514594479510115 381002061138771891719265173)
            ·
              refine ⟨17859471615879932424340555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 381002061138771891719265173 17859471615879932424340555)
              ·
                refine ⟨26789207423819898636510833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17859471615879932424340555 26789207423819898636510833)
                ·
                  refine ⟨20091905567864923977383125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26789207423819898636510833 20091905567864923977383125)
                  ·
                    refine ⟨470904036746834155719917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20091905567864923977383125 470904036746834155719917)
                    ·
                      rfl

theorem cell23_2751247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 7].length) (baseStart_2751247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751247 prefixEnd_2751247 := by exact prefixLift 2751247
  have htrace : WordTrace (prefixWord ++ tailWord_2751247) baseStart_2751247 baseEnd_2751247 := by
    simpa [prefixWord, tailWord_2751247, baseEnd_2751247] using wordTrace_append hprefix tailTrace_2751247
  have hstable : (prefixWord ++ tailWord_2751247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751247).length < 2 ^ (prefixWord ++ tailWord_2751247).sum := by decide
  have hdescent : baseEnd_2751247 < baseStart_2751247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751255 : List Nat := [1, 1, 3, 4, 3, 2, 2, 1, 2, 4]
def baseStart_2751255 : Nat := 118140960795 + 2751255 * 2 ^ 59
def prefixEnd_2751255 : Nat := 4983230072969 + 3 ^ 40 * 2751255 * 2
def baseEnd_2751255 : Nat := 470905406028579478619905

theorem tailTrace_2751255 : CollatzResearch.WordTrace tailWord_2751255 prefixEnd_2751255 470905406028579478619905 := by
  unfold tailWord_2751255
  simp only [CollatzResearch.WordTrace]
  refine ⟨100346513647680486790295219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66897675765120324526863479 100346513647680486790295219)
  ·
    refine ⟨150519770471520730185442829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100346513647680486790295219 150519770471520730185442829)
    ·
      refine ⟨56444913926820273819541061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150519770471520730185442829 56444913926820273819541061)
      ·
        refine ⟨10583421361278801341163949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56444913926820273819541061 10583421361278801341163949)
        ·
          refine ⟨3968783010479550502936481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10583421361278801341163949 3968783010479550502936481)
          ·
            refine ⟨2976587257859662877202361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3968783010479550502936481 2976587257859662877202361)
            ·
              refine ⟨2232440443394747157901771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2976587257859662877202361 2232440443394747157901771)
              ·
                refine ⟨3348660665092120736852657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2232440443394747157901771 3348660665092120736852657)
                ·
                  refine ⟨2511495498819090552639493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3348660665092120736852657 2511495498819090552639493)
                  ·
                    refine ⟨470905406028579478619905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2511495498819090552639493 470905406028579478619905)
                    ·
                      rfl

theorem cell23_2751255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 1, 2, 4].length) (baseStart_2751255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751255 prefixEnd_2751255 := by exact prefixLift 2751255
  have htrace : WordTrace (prefixWord ++ tailWord_2751255) baseStart_2751255 baseEnd_2751255 := by
    simpa [prefixWord, tailWord_2751255, baseEnd_2751255] using wordTrace_append hprefix tailTrace_2751255
  have hstable : (prefixWord ++ tailWord_2751255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751255).length < 2 ^ (prefixWord ++ tailWord_2751255).sum := by decide
  have hdescent : baseEnd_2751255 < baseStart_2751255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751257 : List Nat := [1, 2, 1, 2, 1, 1, 1, 4, 1, 4, 5]
def baseStart_2751257 : Nat := 118140960795 + 2751257 * 2 ^ 59
def prefixEnd_2751257 : Nat := 4983230072969 + 3 ^ 40 * 2751257 * 2
def baseEnd_2751257 : Nat := 1412717245047047428034705

theorem tailTrace_2751257 : CollatzResearch.WordTrace tailWord_2751257 prefixEnd_2751257 1412717245047047428034705 := by
  unfold tailWord_2751257
  simp only [CollatzResearch.WordTrace]
  refine ⟨100346586593673241131868025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66897724395782160754578683 100346586593673241131868025)
  ·
    refine ⟨75259939945254930848901019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100346586593673241131868025 75259939945254930848901019)
    ·
      refine ⟨112889909917882396273351529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75259939945254930848901019 112889909917882396273351529)
      ·
        refine ⟨84667432438411797205013647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112889909917882396273351529 84667432438411797205013647)
        ·
          refine ⟨127001148657617695807520471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84667432438411797205013647 127001148657617695807520471)
          ·
            refine ⟨190501722986426543711280707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127001148657617695807520471 190501722986426543711280707)
            ·
              refine ⟨285752584479639815566921061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190501722986426543711280707 285752584479639815566921061)
              ·
                refine ⟨53578609589932465418797699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 285752584479639815566921061 53578609589932465418797699)
                ·
                  refine ⟨80367914384898698128196549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53578609589932465418797699 80367914384898698128196549)
                  ·
                    refine ⟨15068983947168505899036853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 80367914384898698128196549 15068983947168505899036853)
                    ·
                      refine ⟨1412717245047047428034705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15068983947168505899036853 1412717245047047428034705)
                      ·
                        rfl

theorem cell23_2751257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 4, 5].length) (baseStart_2751257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751257 prefixEnd_2751257 := by exact prefixLift 2751257
  have htrace : WordTrace (prefixWord ++ tailWord_2751257) baseStart_2751257 baseEnd_2751257 := by
    simpa [prefixWord, tailWord_2751257, baseEnd_2751257] using wordTrace_append hprefix tailTrace_2751257
  have hstable : (prefixWord ++ tailWord_2751257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751257).length < 2 ^ (prefixWord ++ tailWord_2751257).sum := by decide
  have hdescent : baseEnd_2751257 < baseStart_2751257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751267 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 8]
def baseStart_2751267 : Nat := 118140960795 + 2751267 * 2 ^ 59
def prefixEnd_2751267 : Nat := 4983230072969 + 3 ^ 40 * 2751267 * 2
def baseEnd_2751267 : Nat := 1412722379853592388909659

theorem tailTrace_2751267 : CollatzResearch.WordTrace tailWord_2751267 prefixEnd_2751267 1412722379853592388909659 := by
  unfold tailWord_2751267
  simp only [CollatzResearch.WordTrace]
  refine ⟨100346951323637012839732055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66897967549091341893154703 100346951323637012839732055)
  ·
    refine ⟨150520426985455519259598083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100346951323637012839732055 150520426985455519259598083)
    ·
      refine ⟨225780640478183278889397125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150520426985455519259598083 225780640478183278889397125)
      ·
        refine ⟨42333870089659364791761961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 225780640478183278889397125 42333870089659364791761961)
        ·
          refine ⟨31750402567244523593821471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42333870089659364791761961 31750402567244523593821471)
          ·
            refine ⟨47625603850866785390732207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31750402567244523593821471 47625603850866785390732207)
            ·
              refine ⟨71438405776300178086098311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47625603850866785390732207 71438405776300178086098311)
              ·
                refine ⟨107157608664450267129147467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71438405776300178086098311 107157608664450267129147467)
                ·
                  refine ⟨160736412996675400693721201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107157608664450267129147467 160736412996675400693721201)
                  ·
                    refine ⟨120552309747506550520290901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 160736412996675400693721201 120552309747506550520290901)
                    ·
                      refine ⟨1412722379853592388909659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 120552309747506550520290901 1412722379853592388909659)
                      ·
                        rfl

theorem cell23_2751267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_2751267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751267 prefixEnd_2751267 := by exact prefixLift 2751267
  have htrace : WordTrace (prefixWord ++ tailWord_2751267) baseStart_2751267 baseEnd_2751267 := by
    simpa [prefixWord, tailWord_2751267, baseEnd_2751267] using wordTrace_append hprefix tailTrace_2751267
  have hstable : (prefixWord ++ tailWord_2751267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751267).length < 2 ^ (prefixWord ++ tailWord_2751267).sum := by decide
  have hdescent : baseEnd_2751267 < baseStart_2751267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751278 : List Nat := [4, 1, 3, 2, 1, 2, 1, 2, 1, 3, 3]
def baseStart_2751278 : Nat := 118140960795 + 2751278 * 2 ^ 59
def prefixEnd_2751278 : Nat := 4983230072969 + 3 ^ 40 * 2751278 * 2
def baseEnd_2751278 : Nat := 1412728028140791845872109

theorem tailTrace_2751278 : CollatzResearch.WordTrace tailWord_2751278 prefixEnd_2751278 1412728028140791845872109 := by
  unfold tailWord_2751278
  simp only [CollatzResearch.WordTrace]
  refine ⟨12543419065824645214797811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66898235017731441145588325 12543419065824645214797811)
  ·
    refine ⟨18815128598736967822196717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12543419065824645214797811 18815128598736967822196717)
    ·
      refine ⟨7055673224526362933323769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18815128598736967822196717 7055673224526362933323769)
      ·
        refine ⟨5291754918394772199992827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7055673224526362933323769 5291754918394772199992827)
        ·
          refine ⟨7937632377592158299989241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5291754918394772199992827 7937632377592158299989241)
          ·
            refine ⟨5953224283194118724991931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7937632377592158299989241 5953224283194118724991931)
            ·
              refine ⟨8929836424791178087487897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5953224283194118724991931 8929836424791178087487897)
              ·
                refine ⟨6697377318593383565615923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8929836424791178087487897 6697377318593383565615923)
                ·
                  refine ⟨10046065977890075348423885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6697377318593383565615923 10046065977890075348423885)
                  ·
                    refine ⟨3767274741708778255658957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10046065977890075348423885 3767274741708778255658957)
                    ·
                      refine ⟨1412728028140791845872109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3767274741708778255658957 1412728028140791845872109)
                      ·
                        rfl

theorem cell23_2751278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_2751278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751278 prefixEnd_2751278 := by exact prefixLift 2751278
  have htrace : WordTrace (prefixWord ++ tailWord_2751278) baseStart_2751278 baseEnd_2751278 := by
    simpa [prefixWord, tailWord_2751278, baseEnd_2751278] using wordTrace_append hprefix tailTrace_2751278
  have hstable : (prefixWord ++ tailWord_2751278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751278).length < 2 ^ (prefixWord ++ tailWord_2751278).sum := by decide
  have hdescent : baseEnd_2751278 < baseStart_2751278 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751304 : List Nat := [2, 1, 3, 1, 1, 3, 1, 1, 1, 6, 3]
def baseStart_2751304 : Nat := 118140960795 + 2751304 * 2 ^ 59
def prefixEnd_2751304 : Nat := 4983230072969 + 3 ^ 40 * 2751304 * 2
def baseEnd_2751304 : Nat := 1412741378637808744146989

theorem tailTrace_2751304 : CollatzResearch.WordTrace tailWord_2751304 prefixEnd_2751304 1412741378637808744146989 := by
  unfold tailWord_2751304
  simp only [CollatzResearch.WordTrace]
  refine ⟨50174150412251484079414483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66898867216335312105885977 50174150412251484079414483)
  ·
    refine ⟨75261225618377226119121725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50174150412251484079414483 75261225618377226119121725)
    ·
      refine ⟨28222959606891459794670647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75261225618377226119121725 28222959606891459794670647)
      ·
        refine ⟨42334439410337189692005971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28222959606891459794670647 42334439410337189692005971)
        ·
          refine ⟨63501659115505784538008957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42334439410337189692005971 63501659115505784538008957)
          ·
            refine ⟨23813122168314669201753359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63501659115505784538008957 23813122168314669201753359)
            ·
              refine ⟨35719683252472003802630039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23813122168314669201753359 35719683252472003802630039)
              ·
                refine ⟨53579524878708005703945059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35719683252472003802630039 53579524878708005703945059)
                ·
                  refine ⟨80369287318062008555917589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53579524878708005703945059 80369287318062008555917589)
                  ·
                    refine ⟨3767310343034156651058637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 80369287318062008555917589 3767310343034156651058637)
                    ·
                      refine ⟨1412741378637808744146989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3767310343034156651058637 1412741378637808744146989)
                      ·
                        rfl

theorem cell23_2751304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 1, 6, 3].length) (baseStart_2751304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751304 prefixEnd_2751304 := by exact prefixLift 2751304
  have htrace : WordTrace (prefixWord ++ tailWord_2751304) baseStart_2751304 baseEnd_2751304 := by
    simpa [prefixWord, tailWord_2751304, baseEnd_2751304] using wordTrace_append hprefix tailTrace_2751304
  have hstable : (prefixWord ++ tailWord_2751304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751304).length < 2 ^ (prefixWord ++ tailWord_2751304).sum := by decide
  have hdescent : baseEnd_2751304 < baseStart_2751304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751307 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 13]
def baseStart_2751307 : Nat := 118140960795 + 2751307 * 2 ^ 59
def prefixEnd_2751307 : Nat := 4983230072969 + 3 ^ 40 * 2751307 * 2
def baseEnd_2751307 : Nat := 156971435453308025823275

theorem tailTrace_2751307 : CollatzResearch.WordTrace tailWord_2751307 prefixEnd_2751307 156971435453308025823275 := by
  unfold tailWord_2751307
  simp only [CollatzResearch.WordTrace]
  refine ⟨100348410243492099671188175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66898940162328066447458783 100348410243492099671188175)
  ·
    refine ⟨150522615365238149506782263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100348410243492099671188175 150522615365238149506782263)
    ·
      refine ⟨225783923047857224260173395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150522615365238149506782263 225783923047857224260173395)
      ·
        refine ⟨338675884571785836390260093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225783923047857224260173395 338675884571785836390260093)
        ·
          refine ⟨127003456714419688646347535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 338675884571785836390260093 127003456714419688646347535)
          ·
            refine ⟨190505185071629532969521303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127003456714419688646347535 190505185071629532969521303)
            ·
              refine ⟨285757777607444299454281955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190505185071629532969521303 285757777607444299454281955)
              ·
                refine ⟨428636666411166449181422933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 285757777607444299454281955 428636666411166449181422933)
                ·
                  refine ⟨156971435453308025823275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 13 428636666411166449181422933 156971435453308025823275)
                  ·
                    rfl

theorem cell23_2751307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 13].length) (baseStart_2751307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751307 prefixEnd_2751307 := by exact prefixLift 2751307
  have htrace : WordTrace (prefixWord ++ tailWord_2751307) baseStart_2751307 baseEnd_2751307 := by
    simpa [prefixWord, tailWord_2751307, baseEnd_2751307] using wordTrace_append hprefix tailTrace_2751307
  have hstable : (prefixWord ++ tailWord_2751307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751307).length < 2 ^ (prefixWord ++ tailWord_2751307).sum := by decide
  have hdescent : baseEnd_2751307 < baseStart_2751307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751354 : List Nat := [3, 1, 1, 1, 1, 1, 3, 3, 4, 5]
def baseStart_2751354 : Nat := 118140960795 + 2751354 * 2 ^ 59
def prefixEnd_2751354 : Nat := 4983230072969 + 3 ^ 40 * 2751354 * 2
def baseEnd_2751354 : Nat := 470922350890177849507253

theorem tailTrace_2751354 : CollatzResearch.WordTrace tailWord_2751354 prefixEnd_2751354 470922350890177849507253 := by
  unfold tailWord_2751354
  simp only [CollatzResearch.WordTrace]
  refine ⟨25087531118580456674537279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66900082982881217798766077 25087531118580456674537279)
  ·
    refine ⟨37631296677870685011805919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25087531118580456674537279 37631296677870685011805919)
    ·
      refine ⟨56446945016806027517708879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37631296677870685011805919 56446945016806027517708879)
      ·
        refine ⟨84670417525209041276563319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56446945016806027517708879 84670417525209041276563319)
        ·
          refine ⟨127005626287813561914844979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84670417525209041276563319 127005626287813561914844979)
          ·
            refine ⟨190508439431720342872267469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127005626287813561914844979 190508439431720342872267469)
            ·
              refine ⟨71440664786895128577100301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 190508439431720342872267469 71440664786895128577100301)
              ·
                refine ⟨26790249295085673216412613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71440664786895128577100301 26790249295085673216412613)
                ·
                  refine ⟨5023171742828563728077365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26790249295085673216412613 5023171742828563728077365)
                  ·
                    refine ⟨470922350890177849507253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5023171742828563728077365 470922350890177849507253)
                    ·
                      rfl

theorem cell23_2751354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 4, 5].length) (baseStart_2751354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751354 prefixEnd_2751354 := by exact prefixLift 2751354
  have htrace : WordTrace (prefixWord ++ tailWord_2751354) baseStart_2751354 baseEnd_2751354 := by
    simpa [prefixWord, tailWord_2751354, baseEnd_2751354] using wordTrace_append hprefix tailTrace_2751354
  have hstable : (prefixWord ++ tailWord_2751354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751354).length < 2 ^ (prefixWord ++ tailWord_2751354).sum := by decide
  have hdescent : baseEnd_2751354 < baseStart_2751354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751364 : List Nat := [2, 3, 2, 1, 1, 1, 1, 3, 1, 1, 7]
def baseStart_2751364 : Nat := 118140960795 + 2751364 * 2 ^ 59
def prefixEnd_2751364 : Nat := 4983230072969 + 3 ^ 40 * 2751364 * 2
def baseEnd_2751364 : Nat := 1412772187477078509396713

theorem tailTrace_2751364 : CollatzResearch.WordTrace tailWord_2751364 prefixEnd_2751364 1412772187477078509396713 := by
  unfold tailWord_2751364
  simp only [CollatzResearch.WordTrace]
  refine ⟨50175244602142799203006573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66900326136190398937342097 50175244602142799203006573)
  ·
    refine ⟨18815716725803549701127465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50175244602142799203006573 18815716725803549701127465)
    ·
      refine ⟨14111787544352662275845599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18815716725803549701127465 14111787544352662275845599)
      ·
        refine ⟨21167681316528993413768399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14111787544352662275845599 21167681316528993413768399)
        ·
          refine ⟨31751521974793490120652599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21167681316528993413768399 31751521974793490120652599)
          ·
            refine ⟨47627282962190235180978899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31751521974793490120652599 47627282962190235180978899)
            ·
              refine ⟨71440924443285352771468349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47627282962190235180978899 71440924443285352771468349)
              ·
                refine ⟨26790346666232007289300631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71440924443285352771468349 26790346666232007289300631)
                ·
                  refine ⟨40185519999348010933950947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26790346666232007289300631 40185519999348010933950947)
                  ·
                    refine ⟨60278279999022016400926421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40185519999348010933950947 60278279999022016400926421)
                    ·
                      refine ⟨1412772187477078509396713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 60278279999022016400926421 1412772187477078509396713)
                      ·
                        rfl

theorem cell23_2751364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_2751364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751364 prefixEnd_2751364 := by exact prefixLift 2751364
  have htrace : WordTrace (prefixWord ++ tailWord_2751364) baseStart_2751364 baseEnd_2751364 := by
    simpa [prefixWord, tailWord_2751364, baseEnd_2751364] using wordTrace_append hprefix tailTrace_2751364
  have hstable : (prefixWord ++ tailWord_2751364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751364).length < 2 ^ (prefixWord ++ tailWord_2751364).sum := by decide
  have hdescent : baseEnd_2751364 < baseStart_2751364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751391 : List Nat := [1, 1, 2, 5, 2, 1, 2, 1, 1, 3, 4]
def baseStart_2751391 : Nat := 118140960795 + 2751391 * 2 ^ 59
def prefixEnd_2751391 : Nat := 4983230072969 + 3 ^ 40 * 2751391 * 2
def baseEnd_2751391 : Nat := 1412786051454749903759089

theorem tailTrace_2751391 : CollatzResearch.WordTrace tailWord_2751391 prefixEnd_2751391 1412786051454749903759089 := by
  unfold tailWord_2751391
  simp only [CollatzResearch.WordTrace]
  refine ⟨100351473975187782017246027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66900982650125188011497351 100351473975187782017246027)
  ·
    refine ⟨150527210962781673025869041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100351473975187782017246027 150527210962781673025869041)
    ·
      refine ⟨112895408222086254769401781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150527210962781673025869041 112895408222086254769401781)
      ·
        refine ⟨10583944520820586384631417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 112895408222086254769401781 10583944520820586384631417)
        ·
          refine ⟨7937958390615439788473563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10583944520820586384631417 7937958390615439788473563)
          ·
            refine ⟨11906937585923159682710345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7937958390615439788473563 11906937585923159682710345)
            ·
              refine ⟨8930203189442369762032759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11906937585923159682710345 8930203189442369762032759)
              ·
                refine ⟨13395304784163554643049139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8930203189442369762032759 13395304784163554643049139)
                ·
                  refine ⟨20092957176245331964573709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13395304784163554643049139 20092957176245331964573709)
                  ·
                    refine ⟨7534858941091999486715141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20092957176245331964573709 7534858941091999486715141)
                    ·
                      refine ⟨1412786051454749903759089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7534858941091999486715141 1412786051454749903759089)
                      ·
                        rfl

theorem cell23_2751391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_2751391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751391 prefixEnd_2751391 := by exact prefixLift 2751391
  have htrace : WordTrace (prefixWord ++ tailWord_2751391) baseStart_2751391 baseEnd_2751391 := by
    simpa [prefixWord, tailWord_2751391, baseEnd_2751391] using wordTrace_append hprefix tailTrace_2751391
  have hstable : (prefixWord ++ tailWord_2751391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751391).length < 2 ^ (prefixWord ++ tailWord_2751391).sum := by decide
  have hdescent : baseEnd_2751391 < baseStart_2751391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751404 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 4]
def baseStart_2751404 : Nat := 118140960795 + 2751404 * 2 ^ 59
def prefixEnd_2751404 : Nat := 4983230072969 + 3 ^ 40 * 2751404 * 2
def baseEnd_2751404 : Nat := 1412792726703258352896529

theorem tailTrace_2751404 : CollatzResearch.WordTrace tailWord_2751404 prefixEnd_2751404 1412792726703258352896529 := by
  unfold tailWord_2751404
  simp only [CollatzResearch.WordTrace]
  refine ⟨50175974062070342618734633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66901298749427123491646177 50175974062070342618734633)
  ·
    refine ⟨37631980546552756964050975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50175974062070342618734633 37631980546552756964050975)
    ·
      refine ⟨56447970819829135446076463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37631980546552756964050975 56447970819829135446076463)
      ·
        refine ⟨84671956229743703169114695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56447970819829135446076463 84671956229743703169114695)
        ·
          refine ⟨127007934344615554753672043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84671956229743703169114695 127007934344615554753672043)
          ·
            refine ⟨190511901516923332130508065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127007934344615554753672043 190511901516923332130508065)
            ·
              refine ⟨142883926137692499097881049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190511901516923332130508065 142883926137692499097881049)
              ·
                refine ⟨107162944603269374323410787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142883926137692499097881049 107162944603269374323410787)
                ·
                  refine ⟨160744416904904061485116181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107162944603269374323410787 160744416904904061485116181)
                  ·
                    refine ⟨7534894542417377882114821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 160744416904904061485116181 7534894542417377882114821)
                    ·
                      refine ⟨1412792726703258352896529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7534894542417377882114821 1412792726703258352896529)
                      ·
                        rfl

theorem cell23_2751404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 4].length) (baseStart_2751404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751404 prefixEnd_2751404 := by exact prefixLift 2751404
  have htrace : WordTrace (prefixWord ++ tailWord_2751404) baseStart_2751404 baseEnd_2751404 := by
    simpa [prefixWord, tailWord_2751404, baseEnd_2751404] using wordTrace_append hprefix tailTrace_2751404
  have hstable : (prefixWord ++ tailWord_2751404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751404).length < 2 ^ (prefixWord ++ tailWord_2751404).sum := by decide
  have hdescent : baseEnd_2751404 < baseStart_2751404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751405 : List Nat := [1, 5, 2, 3, 1, 1, 1, 2, 2, 5]
def baseStart_2751405 : Nat := 118140960795 + 2751405 * 2 ^ 59
def prefixEnd_2751405 : Nat := 4983230072969 + 3 ^ 40 * 2751405 * 2
def baseEnd_2751405 : Nat := 470931080061304282994675

theorem tailTrace_2751405 : CollatzResearch.WordTrace tailWord_2751405 prefixEnd_2751405 470931080061304282994675 := by
  unfold tailWord_2751405
  simp only [CollatzResearch.WordTrace]
  refine ⟨100351984597137062408255669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66901323064758041605503779 100351984597137062408255669)
  ·
    refine ⟨9407998555981599600773969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 100351984597137062408255669 9407998555981599600773969)
    ·
      refine ⟨7055998916986199700580477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9407998555981599600773969 7055998916986199700580477)
      ·
        refine ⟨2645999593869824887717679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7055998916986199700580477 2645999593869824887717679)
        ·
          refine ⟨3968999390804737331576519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2645999593869824887717679 3968999390804737331576519)
          ·
            refine ⟨5953499086207105997364779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3968999390804737331576519 5953499086207105997364779)
            ·
              refine ⟨8930248629310658996047169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5953499086207105997364779 8930248629310658996047169)
              ·
                refine ⟨6697686471982994247035377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8930248629310658996047169 6697686471982994247035377)
                ·
                  refine ⟨5023264853987245685276533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6697686471982994247035377 5023264853987245685276533)
                  ·
                    refine ⟨470931080061304282994675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5023264853987245685276533 470931080061304282994675)
                    ·
                      rfl

theorem cell23_2751405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_2751405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751405 prefixEnd_2751405 := by exact prefixLift 2751405
  have htrace : WordTrace (prefixWord ++ tailWord_2751405) baseStart_2751405 baseEnd_2751405 := by
    simpa [prefixWord, tailWord_2751405, baseEnd_2751405] using wordTrace_append hprefix tailTrace_2751405
  have hstable : (prefixWord ++ tailWord_2751405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751405).length < 2 ^ (prefixWord ++ tailWord_2751405).sum := by decide
  have hdescent : baseEnd_2751405 < baseStart_2751405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751445 : List Nat := [1, 3, 2, 3, 3, 1, 2, 1, 2, 2, 3]
def baseStart_2751445 : Nat := 118140960795 + 2751445 * 2 ^ 59
def prefixEnd_2751445 : Nat := 4983230072969 + 3 ^ 40 * 2751445 * 2
def baseEnd_2751445 : Nat := 1412813779410092692483841

theorem tailTrace_2751445 : CollatzResearch.WordTrace tailWord_2751445 prefixEnd_2751445 1412813779410092692483841 := by
  unfold tailWord_2751445
  simp only [CollatzResearch.WordTrace]
  refine ⟨100353443516992149239711789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66902295677994766159807859 100353443516992149239711789)
  ·
    refine ⟨37632541318872055964891921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100353443516992149239711789 37632541318872055964891921)
    ·
      refine ⟨28224405989154041973668941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37632541318872055964891921 28224405989154041973668941)
      ·
        refine ⟨10584152245932765740125853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28224405989154041973668941 10584152245932765740125853)
        ·
          refine ⟨3969057092224787152547195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10584152245932765740125853 3969057092224787152547195)
          ·
            refine ⟨5953585638337180728820793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3969057092224787152547195 5953585638337180728820793)
            ·
              refine ⟨4465189228752885546615595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5953585638337180728820793 4465189228752885546615595)
              ·
                refine ⟨6697783843129328319923393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4465189228752885546615595 6697783843129328319923393)
                ·
                  refine ⟨5023337882346996239942545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6697783843129328319923393 5023337882346996239942545)
                  ·
                    refine ⟨3767503411760247179956909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5023337882346996239942545 3767503411760247179956909)
                    ·
                      refine ⟨1412813779410092692483841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3767503411760247179956909 1412813779410092692483841)
                      ·
                        rfl

theorem cell23_2751445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_2751445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751445 prefixEnd_2751445 := by exact prefixLift 2751445
  have htrace : WordTrace (prefixWord ++ tailWord_2751445) baseStart_2751445 baseEnd_2751445 := by
    simpa [prefixWord, tailWord_2751445, baseEnd_2751445] using wordTrace_append hprefix tailTrace_2751445
  have hstable : (prefixWord ++ tailWord_2751445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751445).length < 2 ^ (prefixWord ++ tailWord_2751445).sum := by decide
  have hdescent : baseEnd_2751445 < baseStart_2751445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751451 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 1, 11, 2]
def baseStart_2751451 : Nat := 118140960795 + 2751451 * 2 ^ 59
def prefixEnd_2751451 : Nat := 4983230072969 + 3 ^ 40 * 2751451 * 2
def baseEnd_2751451 : Nat := 1412816860294019669008813

theorem tailTrace_2751451 : CollatzResearch.WordTrace tailWord_2751451 prefixEnd_2751451 1412816860294019669008813 := by
  unfold tailWord_2751451
  simp only [CollatzResearch.WordTrace]
  refine ⟨100353662354970412264430207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66902441569980274842953471 100353662354970412264430207)
  ·
    refine ⟨150530493532455618396645311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100353662354970412264430207 150530493532455618396645311)
    ·
      refine ⟨225795740298683427594967967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150530493532455618396645311 225795740298683427594967967)
      ·
        refine ⟨338693610448025141392451951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225795740298683427594967967 338693610448025141392451951)
        ·
          refine ⟨508040415672037712088677927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338693610448025141392451951 508040415672037712088677927)
          ·
            refine ⟨762060623508056568133016891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 508040415672037712088677927 762060623508056568133016891)
            ·
              refine ⟨1143090935262084852199525337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 762060623508056568133016891 1143090935262084852199525337)
              ·
                refine ⟨857318201446563639149644003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1143090935262084852199525337 857318201446563639149644003)
                ·
                  refine ⟨1285977302169845458724466005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 857318201446563639149644003 1285977302169845458724466005)
                  ·
                    refine ⟨1883755813725359558678417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 1285977302169845458724466005 1883755813725359558678417)
                    ·
                      refine ⟨1412816860294019669008813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1883755813725359558678417 1412816860294019669008813)
                      ·
                        rfl

theorem cell23_2751451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 11, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 11, 2].length) (baseStart_2751451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751451 prefixEnd_2751451 := by exact prefixLift 2751451
  have htrace : WordTrace (prefixWord ++ tailWord_2751451) baseStart_2751451 baseEnd_2751451 := by
    simpa [prefixWord, tailWord_2751451, baseEnd_2751451] using wordTrace_append hprefix tailTrace_2751451
  have hstable : (prefixWord ++ tailWord_2751451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751451).length < 2 ^ (prefixWord ++ tailWord_2751451).sum := by decide
  have hdescent : baseEnd_2751451 < baseStart_2751451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751476 : List Nat := [2, 6, 2, 1, 1, 1, 1, 1, 2, 4, 2]
def baseStart_2751476 : Nat := 118140960795 + 2751476 * 2 ^ 59
def prefixEnd_2751476 : Nat := 4983230072969 + 3 ^ 40 * 2751476 * 2
def baseEnd_2751476 : Nat := 1412829697310382071196199

theorem tailTrace_2751476 : CollatzResearch.WordTrace tailWord_2751476 prefixEnd_2751476 1412829697310382071196199 := by
  unfold tailWord_2751476
  simp only [CollatzResearch.WordTrace]
  refine ⟨50177287089939920767045141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66903049453253227689393521 50177287089939920767045141)
  ·
    refine ⟨2352060332340933785955241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 50177287089939920767045141 2352060332340933785955241)
    ·
      refine ⟨1764045249255700339466431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2352060332340933785955241 1764045249255700339466431)
      ·
        refine ⟨2646067873883550509199647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1764045249255700339466431 2646067873883550509199647)
        ·
          refine ⟨3969101810825325763799471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2646067873883550509199647 3969101810825325763799471)
          ·
            refine ⟨5953652716237988645699207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3969101810825325763799471 5953652716237988645699207)
            ·
              refine ⟨8930479074356982968548811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5953652716237988645699207 8930479074356982968548811)
              ·
                refine ⟨13395718611535474452823217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8930479074356982968548811 13395718611535474452823217)
                ·
                  refine ⟨10046788958651605839617413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13395718611535474452823217 10046788958651605839617413)
                  ·
                    refine ⟨1883772929747176094928265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10046788958651605839617413 1883772929747176094928265)
                    ·
                      refine ⟨1412829697310382071196199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1883772929747176094928265 1412829697310382071196199)
                      ·
                        rfl

theorem cell23_2751476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_2751476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751476 prefixEnd_2751476 := by exact prefixLift 2751476
  have htrace : WordTrace (prefixWord ++ tailWord_2751476) baseStart_2751476 baseEnd_2751476 := by
    simpa [prefixWord, tailWord_2751476, baseEnd_2751476] using wordTrace_append hprefix tailTrace_2751476
  have hstable : (prefixWord ++ tailWord_2751476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751476).length < 2 ^ (prefixWord ++ tailWord_2751476).sum := by decide
  have hdescent : baseEnd_2751476 < baseStart_2751476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751478 : List Nat := [5, 1, 1, 1, 3, 1, 1, 2, 3, 5]
def baseStart_2751478 : Nat := 118140960795 + 2751478 * 2 ^ 59
def prefixEnd_2751478 : Nat := 4983230072969 + 3 ^ 40 * 2751478 * 2
def baseEnd_2751478 : Nat := 470943574757230354457063

theorem tailTrace_2751478 : CollatzResearch.WordTrace tailWord_2751478 prefixEnd_2751478 470943574757230354457063 := by
  unfold tailWord_2751478
  simp only [CollatzResearch.WordTrace]
  refine ⟨6272165445367037242228943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66903098083915063917108725 6272165445367037242228943)
  ·
    refine ⟨9408248168050555863343415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6272165445367037242228943 9408248168050555863343415)
    ·
      refine ⟨14112372252075833795015123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9408248168050555863343415 14112372252075833795015123)
      ·
        refine ⟨21168558378113750692522685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14112372252075833795015123 21168558378113750692522685)
        ·
          refine ⟨7938209391792656509696007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21168558378113750692522685 7938209391792656509696007)
          ·
            refine ⟨11907314087688984764544011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7938209391792656509696007 11907314087688984764544011)
            ·
              refine ⟨17860971131533477146816017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11907314087688984764544011 17860971131533477146816017)
              ·
                refine ⟨13395728348650107860112013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17860971131533477146816017 13395728348650107860112013)
                ·
                  refine ⟨5023398130743790447542005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13395728348650107860112013 5023398130743790447542005)
                  ·
                    refine ⟨470943574757230354457063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5023398130743790447542005 470943574757230354457063)
                    ·
                      rfl

theorem cell23_2751478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_2751478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751478 prefixEnd_2751478 := by exact prefixLift 2751478
  have htrace : WordTrace (prefixWord ++ tailWord_2751478) baseStart_2751478 baseEnd_2751478 := by
    simpa [prefixWord, tailWord_2751478, baseEnd_2751478] using wordTrace_append hprefix tailTrace_2751478
  have hstable : (prefixWord ++ tailWord_2751478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751478).length < 2 ^ (prefixWord ++ tailWord_2751478).sum := by decide
  have hdescent : baseEnd_2751478 < baseStart_2751478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751481 : List Nat := [1, 2, 1, 3, 1, 3, 1, 1, 5, 1, 4]
def baseStart_2751481 : Nat := 118140960795 + 2751481 * 2 ^ 59
def prefixEnd_2751481 : Nat := 4983230072969 + 3 ^ 40 * 2751481 * 2
def baseEnd_2751481 : Nat := 1412832264713654551633675

theorem tailTrace_2751481 : CollatzResearch.WordTrace tailWord_2751481 prefixEnd_2751481 1412832264713654551633675 := by
  unfold tailWord_2751481
  simp only [CollatzResearch.WordTrace]
  refine ⟨100354756544861727388022297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66903171029907818258681531 100354756544861727388022297)
  ·
    refine ⟨75266067408646295541016723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100354756544861727388022297 75266067408646295541016723)
    ·
      refine ⟨112899101112969443311525085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75266067408646295541016723 112899101112969443311525085)
      ·
        refine ⟨42337162917363541241821907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112899101112969443311525085 42337162917363541241821907)
        ·
          refine ⟨63505744376045311862732861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42337162917363541241821907 63505744376045311862732861)
          ·
            refine ⟨23814654141016991948524823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63505744376045311862732861 23814654141016991948524823)
            ·
              refine ⟨35721981211525487922787235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23814654141016991948524823 35721981211525487922787235)
              ·
                refine ⟨53582971817288231884180853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35721981211525487922787235 53582971817288231884180853)
                ·
                  refine ⟨5023403607870771739141955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53582971817288231884180853 5023403607870771739141955)
                  ·
                    refine ⟨7535105411806157608712933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5023403607870771739141955 7535105411806157608712933)
                    ·
                      refine ⟨1412832264713654551633675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7535105411806157608712933 1412832264713654551633675)
                      ·
                        rfl

theorem cell23_2751481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_2751481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751481 prefixEnd_2751481 := by exact prefixLift 2751481
  have htrace : WordTrace (prefixWord ++ tailWord_2751481) baseStart_2751481 baseEnd_2751481 := by
    simpa [prefixWord, tailWord_2751481, baseEnd_2751481] using wordTrace_append hprefix tailTrace_2751481
  have hstable : (prefixWord ++ tailWord_2751481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751481).length < 2 ^ (prefixWord ++ tailWord_2751481).sum := by decide
  have hdescent : baseEnd_2751481 < baseStart_2751481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751491 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 8, 4]
def baseStart_2751491 : Nat := 118140960795 + 2751491 * 2 ^ 59
def prefixEnd_2751491 : Nat := 4983230072969 + 3 ^ 40 * 2751491 * 2
def baseEnd_2751491 : Nat := 470945799840066504169543

theorem tailTrace_2751491 : CollatzResearch.WordTrace tailWord_2751491 prefixEnd_2751491 470945799840066504169543 := by
  unfold tailWord_2751491
  simp only [CollatzResearch.WordTrace]
  refine ⟨100355121274825499095886327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66903414183216999397257551 100355121274825499095886327)
  ·
    refine ⟨150532681912238248643829491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100355121274825499095886327 150532681912238248643829491)
    ·
      refine ⟨225799022868357372965744237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150532681912238248643829491 225799022868357372965744237)
      ·
        refine ⟨84674633575634014862154089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 225799022868357372965744237 84674633575634014862154089)
        ·
          refine ⟨63505975181725511146615567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84674633575634014862154089 63505975181725511146615567)
          ·
            refine ⟨95258962772588266719923351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63505975181725511146615567 95258962772588266719923351)
            ·
              refine ⟨142888444158882400079885027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95258962772588266719923351 142888444158882400079885027)
              ·
                refine ⟨214332666238323600119827541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142888444158882400079885027 214332666238323600119827541)
                ·
                  refine ⟨2511710932480354688904229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 214332666238323600119827541 2511710932480354688904229)
                  ·
                    refine ⟨470945799840066504169543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2511710932480354688904229 470945799840066504169543)
                    ·
                      rfl

theorem cell23_2751491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 8, 4].length) (baseStart_2751491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751491 prefixEnd_2751491 := by exact prefixLift 2751491
  have htrace : WordTrace (prefixWord ++ tailWord_2751491) baseStart_2751491 baseEnd_2751491 := by
    simpa [prefixWord, tailWord_2751491, baseEnd_2751491] using wordTrace_append hprefix tailTrace_2751491
  have hstable : (prefixWord ++ tailWord_2751491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751491).length < 2 ^ (prefixWord ++ tailWord_2751491).sum := by decide
  have hdescent : baseEnd_2751491 < baseStart_2751491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751498 : List Nat := [3, 1, 2, 2, 3, 1, 2, 1, 3, 1, 4]
def baseStart_2751498 : Nat := 118140960795 + 2751498 * 2 ^ 59
def prefixEnd_2751498 : Nat := 4983230072969 + 3 ^ 40 * 2751498 * 2
def baseEnd_2751498 : Nat := 1412840993884780985121097

theorem tailTrace_2751498 : CollatzResearch.WordTrace tailWord_2751498 prefixEnd_2751498 1412840993884780985121097 := by
  unfold tailWord_2751498
  simp only [CollatzResearch.WordTrace]
  refine ⟨25088844146450034822847787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66903584390533426194260765 25088844146450034822847787)
  ·
    refine ⟨37633266219675052234271681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25088844146450034822847787 37633266219675052234271681)
    ·
      refine ⟨28224949664756289175703761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37633266219675052234271681 28224949664756289175703761)
      ·
        refine ⟨21168712248567216881777821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28224949664756289175703761 21168712248567216881777821)
        ·
          refine ⟨7938267093212706330666683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21168712248567216881777821 7938267093212706330666683)
          ·
            refine ⟨11907400639819059496000025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7938267093212706330666683 11907400639819059496000025)
            ·
              refine ⟨8930550479864294622000019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11907400639819059496000025 8930550479864294622000019)
              ·
                refine ⟨13395825719796441933000029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8930550479864294622000019 13395825719796441933000029)
                ·
                  refine ⟨5023434644923665724875011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13395825719796441933000029 5023434644923665724875011)
                  ·
                    refine ⟨7535151967385498587312517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5023434644923665724875011 7535151967385498587312517)
                    ·
                      refine ⟨1412840993884780985121097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7535151967385498587312517 1412840993884780985121097)
                      ·
                        rfl

theorem cell23_2751498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_2751498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751498 prefixEnd_2751498 := by exact prefixLift 2751498
  have htrace : WordTrace (prefixWord ++ tailWord_2751498) baseStart_2751498 baseEnd_2751498 := by
    simpa [prefixWord, tailWord_2751498, baseEnd_2751498] using wordTrace_append hprefix tailTrace_2751498
  have hstable : (prefixWord ++ tailWord_2751498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751498).length < 2 ^ (prefixWord ++ tailWord_2751498).sum := by decide
  have hdescent : baseEnd_2751498 < baseStart_2751498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751502 : List Nat := [4, 1, 1, 2, 2, 4, 1, 1, 2, 3, 2]
def baseStart_2751502 : Nat := 118140960795 + 2751502 * 2 ^ 59
def prefixEnd_2751502 : Nat := 4983230072969 + 3 ^ 40 * 2751502 * 2
def baseEnd_2751502 : Nat := 1412843047807398969471079

theorem tailTrace_2751502 : CollatzResearch.WordTrace tailWord_2751502 prefixEnd_2751502 1412843047807398969471079 := by
  unfold tailWord_2751502
  simp only [CollatzResearch.WordTrace]
  refine ⟨12544440309723205996817095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66903681651857098649691173 12544440309723205996817095)
  ·
    refine ⟨18816660464584808995225643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12544440309723205996817095 18816660464584808995225643)
    ·
      refine ⟨28224990696877213492838465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18816660464584808995225643 28224990696877213492838465)
      ·
        refine ⟨21168743022657910119628849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28224990696877213492838465 21168743022657910119628849)
        ·
          refine ⟨15876557266993432589721637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21168743022657910119628849 15876557266993432589721637)
          ·
            refine ⟨2976854487561268610572807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15876557266993432589721637 2976854487561268610572807)
            ·
              refine ⟨4465281731341902915859211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2976854487561268610572807 4465281731341902915859211)
              ·
                refine ⟨6697922597012854373788817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4465281731341902915859211 6697922597012854373788817)
                ·
                  refine ⟨5023441947759640780341613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6697922597012854373788817 5023441947759640780341613)
                  ·
                    refine ⟨1883790730409865292628105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5023441947759640780341613 1883790730409865292628105)
                    ·
                      refine ⟨1412843047807398969471079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1883790730409865292628105 1412843047807398969471079)
                      ·
                        rfl

theorem cell23_2751502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 2, 3, 2].length) (baseStart_2751502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751502 prefixEnd_2751502 := by exact prefixLift 2751502
  have htrace : WordTrace (prefixWord ++ tailWord_2751502) baseStart_2751502 baseEnd_2751502 := by
    simpa [prefixWord, tailWord_2751502, baseEnd_2751502] using wordTrace_append hprefix tailTrace_2751502
  have hstable : (prefixWord ++ tailWord_2751502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751502).length < 2 ^ (prefixWord ++ tailWord_2751502).sum := by decide
  have hdescent : baseEnd_2751502 < baseStart_2751502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751521 : List Nat := [1, 2, 3, 2, 3, 2, 10]
def baseStart_2751521 : Nat := 118140960795 + 2751521 * 2 ^ 59
def prefixEnd_2751521 : Nat := 4983230072969 + 3 ^ 40 * 2751521 * 2
def baseEnd_2751521 : Nat := 17442627209133757964611

theorem tailTrace_2751521 : CollatzResearch.WordTrace tailWord_2751521 prefixEnd_2751521 17442627209133757964611 := by
  unfold tailWord_2751521
  simp only [CollatzResearch.WordTrace]
  refine ⟨100356215464716814219478417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66904143643144542812985611 100356215464716814219478417)
  ·
    refine ⟨75267161598537610664608813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100356215464716814219478417 75267161598537610664608813)
    ·
      refine ⟨28225185599451603999228305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75267161598537610664608813 28225185599451603999228305)
      ·
        refine ⟨21168889199588702999421229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28225185599451603999228305 21168889199588702999421229)
        ·
          refine ⟨7938333449845763624782961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21168889199588702999421229 7938333449845763624782961)
          ·
            refine ⟨5953750087384322718587221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7938333449845763624782961 5953750087384322718587221)
            ·
              refine ⟨17442627209133757964611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5953750087384322718587221 17442627209133757964611)
              ·
                rfl

theorem cell23_2751521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 10].length) (baseStart_2751521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751521 prefixEnd_2751521 := by exact prefixLift 2751521
  have htrace : WordTrace (prefixWord ++ tailWord_2751521) baseStart_2751521 baseEnd_2751521 := by
    simpa [prefixWord, tailWord_2751521, baseEnd_2751521] using wordTrace_append hprefix tailTrace_2751521
  have hstable : (prefixWord ++ tailWord_2751521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751521).length < 2 ^ (prefixWord ++ tailWord_2751521).sum := by decide
  have hdescent : baseEnd_2751521 < baseStart_2751521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751532 : List Nat := [2, 2, 1, 1, 1, 2, 3, 6, 1, 2, 2]
def baseStart_2751532 : Nat := 118140960795 + 2751532 * 2 ^ 59
def prefixEnd_2751532 : Nat := 4983230072969 + 3 ^ 40 * 2751532 * 2
def baseEnd_2751532 : Nat := 1412858452227033852095941

theorem tailTrace_2751532 : CollatzResearch.WordTrace tailWord_2751532 prefixEnd_2751532 1412858452227033852095941 := by
  unfold tailWord_2751532
  simp only [CollatzResearch.WordTrace]
  refine ⟨50178308333838481549064425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66904411111784642065419233 50178308333838481549064425)
  ·
    refine ⟨37633731250378861161798319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50178308333838481549064425 37633731250378861161798319)
    ·
      refine ⟨56450596875568291742697479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37633731250378861161798319 56450596875568291742697479)
      ·
        refine ⟨84675895313352437614046219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56450596875568291742697479 84675895313352437614046219)
        ·
          refine ⟨127013842970028656421069329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84675895313352437614046219 127013842970028656421069329)
          ·
            refine ⟨95260382227521492315801997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127013842970028656421069329 95260382227521492315801997)
            ·
              refine ⟨35722643335320559618425749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95260382227521492315801997 35722643335320559618425749)
              ·
                refine ⟨1674498906343151232113707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35722643335320559618425749 1674498906343151232113707)
                ·
                  refine ⟨2511748359514726848170561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1674498906343151232113707 2511748359514726848170561)
                  ·
                    refine ⟨1883811269636045136127921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2511748359514726848170561 1883811269636045136127921)
                    ·
                      refine ⟨1412858452227033852095941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1883811269636045136127921 1412858452227033852095941)
                      ·
                        rfl

theorem cell23_2751532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 6, 1, 2, 2].length) (baseStart_2751532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751532 prefixEnd_2751532 := by exact prefixLift 2751532
  have htrace : WordTrace (prefixWord ++ tailWord_2751532) baseStart_2751532 baseEnd_2751532 := by
    simpa [prefixWord, tailWord_2751532, baseEnd_2751532] using wordTrace_append hprefix tailTrace_2751532
  have hstable : (prefixWord ++ tailWord_2751532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751532).length < 2 ^ (prefixWord ++ tailWord_2751532).sum := by decide
  have hdescent : baseEnd_2751532 < baseStart_2751532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751545 : List Nat := [1, 2, 1, 5, 2, 3, 1, 1, 1, 2, 4]
def baseStart_2751545 : Nat := 118140960795 + 2751545 * 2 ^ 59
def prefixEnd_2751545 : Nat := 4983230072969 + 3 ^ 40 * 2751545 * 2
def baseEnd_2751545 : Nat := 1412865127475542301233381

theorem tailTrace_2751545 : CollatzResearch.WordTrace tailWord_2751545 prefixEnd_2751545 1412865127475542301233381 := by
  unfold tailWord_2751545
  simp only [CollatzResearch.WordTrace]
  refine ⟨100357090816629866318352089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66904727211086577545568059 100357090816629866318352089)
  ·
    refine ⟨75267818112472399738764067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100357090816629866318352089 75267818112472399738764067)
    ·
      refine ⟨112901727168708599608146101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75267818112472399738764067 112901727168708599608146101)
      ·
        refine ⟨10584536922066431213263697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 112901727168708599608146101 10584536922066431213263697)
        ·
          refine ⟨7938402691549823409947773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10584536922066431213263697 7938402691549823409947773)
          ·
            refine ⟨2976901009331183778730415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7938402691549823409947773 2976901009331183778730415)
            ·
              refine ⟨4465351513996775668095623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2976901009331183778730415 4465351513996775668095623)
              ·
                refine ⟨6698027270995163502143435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4465351513996775668095623 6698027270995163502143435)
                ·
                  refine ⟨10047040906492745253215153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6698027270995163502143435 10047040906492745253215153)
                  ·
                    refine ⟨7535280679869558939911365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10047040906492745253215153 7535280679869558939911365)
                    ·
                      refine ⟨1412865127475542301233381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7535280679869558939911365 1412865127475542301233381)
                      ·
                        rfl

theorem cell23_2751545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_2751545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751545 prefixEnd_2751545 := by exact prefixLift 2751545
  have htrace : WordTrace (prefixWord ++ tailWord_2751545) baseStart_2751545 baseEnd_2751545 := by
    simpa [prefixWord, tailWord_2751545, baseEnd_2751545] using wordTrace_append hprefix tailTrace_2751545
  have hstable : (prefixWord ++ tailWord_2751545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751545).length < 2 ^ (prefixWord ++ tailWord_2751545).sum := by decide
  have hdescent : baseEnd_2751545 < baseStart_2751545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751609 : List Nat := [1, 2, 1, 3, 5, 2, 1, 2, 1, 3, 2]
def baseStart_2751609 : Nat := 118140960795 + 2751609 * 2 ^ 59
def prefixEnd_2751609 : Nat := 4983230072969 + 3 ^ 40 * 2751609 * 2
def baseEnd_2751609 : Nat := 1412897990237430050833087

theorem tailTrace_2751609 : CollatzResearch.WordTrace tailWord_2751609 prefixEnd_2751609 1412897990237430050833087 := by
  unfold tailWord_2751609
  simp only [CollatzResearch.WordTrace]
  refine ⟨100359425088398005248681881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66906283392265336832454587 100359425088398005248681881)
  ·
    refine ⟨75269568816298503936511411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100359425088398005248681881 75269568816298503936511411)
    ·
      refine ⟨112904353224447755904767117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75269568816298503936511411 112904353224447755904767117)
      ·
        refine ⟨42339132459167908464287669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112904353224447755904767117 42339132459167908464287669)
        ·
          refine ⟨3969293668046991418526969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42339132459167908464287669 3969293668046991418526969)
          ·
            refine ⟨2976970251035243563895227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3969293668046991418526969 2976970251035243563895227)
            ·
              refine ⟨4465455376552865345842841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2976970251035243563895227 4465455376552865345842841)
              ·
                refine ⟨3349091532414649009382131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4465455376552865345842841 3349091532414649009382131)
                ·
                  refine ⟨5023637298621973514073197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3349091532414649009382131 5023637298621973514073197)
                  ·
                    refine ⟨1883863986983240067777449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5023637298621973514073197 1883863986983240067777449)
                    ·
                      refine ⟨1412897990237430050833087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1883863986983240067777449 1412897990237430050833087)
                      ·
                        rfl

theorem cell23_2751609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 2, 1, 3, 2].length) (baseStart_2751609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751609 prefixEnd_2751609 := by exact prefixLift 2751609
  have htrace : WordTrace (prefixWord ++ tailWord_2751609) baseStart_2751609 baseEnd_2751609 := by
    simpa [prefixWord, tailWord_2751609, baseEnd_2751609] using wordTrace_append hprefix tailTrace_2751609
  have hstable : (prefixWord ++ tailWord_2751609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751609).length < 2 ^ (prefixWord ++ tailWord_2751609).sum := by decide
  have hdescent : baseEnd_2751609 < baseStart_2751609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751611 : List Nat := [1, 1, 1, 1, 1, 4, 1, 6, 7]
def baseStart_2751611 : Nat := 118140960795 + 2751611 * 2 ^ 59
def prefixEnd_2751611 : Nat := 4983230072969 + 3 ^ 40 * 2751611 * 2
def baseEnd_2751611 : Nat := 156988779688748782556453

theorem tailTrace_2751611 : CollatzResearch.WordTrace tailWord_2751611 prefixEnd_2751611 156988779688748782556453 := by
  unfold tailWord_2751611
  simp only [CollatzResearch.WordTrace]
  refine ⟨100359498034390759590254687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66906332022927173060169791 100359498034390759590254687)
  ·
    refine ⟨150539247051586139385382031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100359498034390759590254687 150539247051586139385382031)
    ·
      refine ⟨225808870577379209078073047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150539247051586139385382031 225808870577379209078073047)
      ·
        refine ⟨338713305866068813617109571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225808870577379209078073047 338713305866068813617109571)
        ·
          refine ⟨508069958799103220425664357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338713305866068813617109571 508069958799103220425664357)
          ·
            refine ⟨95263117274831853829812067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 508069958799103220425664357 95263117274831853829812067)
            ·
              refine ⟨142894675912247780744718101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95263117274831853829812067 142894675912247780744718101)
              ·
                refine ⟨6698187933386614722408661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 142894675912247780744718101 6698187933386614722408661)
                ·
                  refine ⟨156988779688748782556453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6698187933386614722408661 156988779688748782556453)
                  ·
                    rfl

theorem cell23_2751611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 7].length) (baseStart_2751611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751611 prefixEnd_2751611 := by exact prefixLift 2751611
  have htrace : WordTrace (prefixWord ++ tailWord_2751611) baseStart_2751611 baseEnd_2751611 := by
    simpa [prefixWord, tailWord_2751611, baseEnd_2751611] using wordTrace_append hprefix tailTrace_2751611
  have hstable : (prefixWord ++ tailWord_2751611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751611).length < 2 ^ (prefixWord ++ tailWord_2751611).sum := by decide
  have hdescent : baseEnd_2751611 < baseStart_2751611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751639 : List Nat := [1, 1, 3, 3, 3, 2, 2, 2, 2, 2, 2]
def baseStart_2751639 : Nat := 118140960795 + 2751639 * 2 ^ 59
def prefixEnd_2751639 : Nat := 4983230072969 + 3 ^ 40 * 2751639 * 2
def baseEnd_2751639 : Nat := 1412913394657064933457949

theorem tailTrace_2751639 : CollatzResearch.WordTrace tailWord_2751639 prefixEnd_2751639 1412913394657064933457949 := by
  unfold tailWord_2751639
  simp only [CollatzResearch.WordTrace]
  refine ⟨100360519278289320372273971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66907012852192880248182647 100360519278289320372273971)
  ·
    refine ⟨150540778917433980558410957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100360519278289320372273971 150540778917433980558410957)
    ·
      refine ⟨56452792094037742709404109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150540778917433980558410957 56452792094037742709404109)
      ·
        refine ⟨21169797035264153516026541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56452792094037742709404109 21169797035264153516026541)
        ·
          refine ⟨7938673888224057568509953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21169797035264153516026541 7938673888224057568509953)
          ·
            refine ⟨5954005416168043176382465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7938673888224057568509953 5954005416168043176382465)
            ·
              refine ⟨4465504062126032382286849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5954005416168043176382465 4465504062126032382286849)
              ·
                refine ⟨3349128046594524286715137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4465504062126032382286849 3349128046594524286715137)
                ·
                  refine ⟨2511846034945893215036353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3349128046594524286715137 2511846034945893215036353)
                  ·
                    refine ⟨1883884526209419911277265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2511846034945893215036353 1883884526209419911277265)
                    ·
                      refine ⟨1412913394657064933457949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1883884526209419911277265 1412913394657064933457949)
                      ·
                        rfl

theorem cell23_2751639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 2, 2, 2, 2].length) (baseStart_2751639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751639 prefixEnd_2751639 := by exact prefixLift 2751639
  have htrace : WordTrace (prefixWord ++ tailWord_2751639) baseStart_2751639 baseEnd_2751639 := by
    simpa [prefixWord, tailWord_2751639, baseEnd_2751639] using wordTrace_append hprefix tailTrace_2751639
  have hstable : (prefixWord ++ tailWord_2751639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751639).length < 2 ^ (prefixWord ++ tailWord_2751639).sum := by decide
  have hdescent : baseEnd_2751639 < baseStart_2751639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751641 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 5, 7]
def baseStart_2751641 : Nat := 118140960795 + 2751641 * 2 ^ 59
def prefixEnd_2751641 : Nat := 4983230072969 + 3 ^ 40 * 2751641 * 2
def baseEnd_2751641 : Nat := 470971473872791308544313

theorem tailTrace_2751641 : CollatzResearch.WordTrace tailWord_2751641 prefixEnd_2751641 470971473872791308544313 := by
  unfold tailWord_2751641
  simp only [CollatzResearch.WordTrace]
  refine ⟨100360592224282074713846777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66907061482854716475897851 100360592224282074713846777)
  ·
    refine ⟨75270444168211556035385083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100360592224282074713846777 75270444168211556035385083)
    ·
      refine ⟨112905666252317334053077625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75270444168211556035385083 112905666252317334053077625)
      ·
        refine ⟨84679249689238000539808219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112905666252317334053077625 84679249689238000539808219)
        ·
          refine ⟨127018874533857000809712329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84679249689238000539808219 127018874533857000809712329)
          ·
            refine ⟨95264155900392750607284247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127018874533857000809712329 95264155900392750607284247)
            ·
              refine ⟨142896233850589125910926371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95264155900392750607284247 142896233850589125910926371)
              ·
                refine ⟨214344350775883688866389557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142896233850589125910926371 214344350775883688866389557)
                ·
                  refine ⟨20094782885239095831224021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 214344350775883688866389557 20094782885239095831224021)
                  ·
                    refine ⟨470971473872791308544313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20094782885239095831224021 470971473872791308544313)
                    ·
                      rfl

theorem cell23_2751641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 7].length) (baseStart_2751641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751641 prefixEnd_2751641 := by exact prefixLift 2751641
  have htrace : WordTrace (prefixWord ++ tailWord_2751641) baseStart_2751641 baseEnd_2751641 := by
    simpa [prefixWord, tailWord_2751641, baseEnd_2751641] using wordTrace_append hprefix tailTrace_2751641
  have hstable : (prefixWord ++ tailWord_2751641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751641).length < 2 ^ (prefixWord ++ tailWord_2751641).sum := by decide
  have hdescent : baseEnd_2751641 < baseStart_2751641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751645 : List Nat := [1, 4, 2, 1, 1, 2, 3, 4, 5]
def baseStart_2751645 : Nat := 118140960795 + 2751645 * 2 ^ 59
def prefixEnd_2751645 : Nat := 4983230072969 + 3 ^ 40 * 2751645 * 2
def baseEnd_2751645 : Nat := 156990719504554656664769

theorem tailTrace_2751645 : CollatzResearch.WordTrace tailWord_2751645 prefixEnd_2751645 156990719504554656664769 := by
  unfold tailWord_2751645
  simp only [CollatzResearch.WordTrace]
  refine ⟨100360738116267583396992389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66907158744178388931328259 100360738116267583396992389)
  ·
    refine ⟨18817638396800171886936073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100360738116267583396992389 18817638396800171886936073)
    ·
      refine ⟨14113228797600128915202055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18817638396800171886936073 14113228797600128915202055)
      ·
        refine ⟨21169843196400193372803083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14113228797600128915202055 21169843196400193372803083)
        ·
          refine ⟨31754764794600290059204625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21169843196400193372803083 31754764794600290059204625)
          ·
            refine ⟨23816073595950217544403469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31754764794600290059204625 23816073595950217544403469)
            ·
              refine ⟨8931027598481331579151301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23816073595950217544403469 8931027598481331579151301)
              ·
                refine ⟨1674567674715249671090869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8931027598481331579151301 1674567674715249671090869)
                ·
                  refine ⟨156990719504554656664769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1674567674715249671090869 156990719504554656664769)
                  ·
                    rfl

theorem cell23_2751645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 4, 5].length) (baseStart_2751645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751645 prefixEnd_2751645 := by exact prefixLift 2751645
  have htrace : WordTrace (prefixWord ++ tailWord_2751645) baseStart_2751645 baseEnd_2751645 := by
    simpa [prefixWord, tailWord_2751645, baseEnd_2751645] using wordTrace_append hprefix tailTrace_2751645
  have hstable : (prefixWord ++ tailWord_2751645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751645).length < 2 ^ (prefixWord ++ tailWord_2751645).sum := by decide
  have hdescent : baseEnd_2751645 < baseStart_2751645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751655 : List Nat := [1, 1, 6, 2, 1, 1, 1, 1, 1, 5, 3]
def baseStart_2751655 : Nat := 118140960795 + 2751655 * 2 ^ 59
def prefixEnd_2751655 : Nat := 4983230072969 + 3 ^ 40 * 2751655 * 2
def baseEnd_2751655 : Nat := 1412921610347536870857875

theorem tailTrace_2751655 : CollatzResearch.WordTrace tailWord_2751655 prefixEnd_2751655 1412921610347536870857875 := by
  unfold tailWord_2751655
  simp only [CollatzResearch.WordTrace]
  refine ⟨100361102846231355104856419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66907401897487570069904279 100361102846231355104856419)
  ·
    refine ⟨150541654269347032657284629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100361102846231355104856419 150541654269347032657284629)
    ·
      refine ⟨7056640043875642155810217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 150541654269347032657284629 7056640043875642155810217)
      ·
        refine ⟨5292480032906731616857663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7056640043875642155810217 5292480032906731616857663)
        ·
          refine ⟨7938720049360097425286495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5292480032906731616857663 7938720049360097425286495)
          ·
            refine ⟨11908080074040146137929743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7938720049360097425286495 11908080074040146137929743)
            ·
              refine ⟨17862120111060219206894615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11908080074040146137929743 17862120111060219206894615)
              ·
                refine ⟨26793180166590328810341923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17862120111060219206894615 26793180166590328810341923)
                ·
                  refine ⟨40189770249885493215512885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26793180166590328810341923 40189770249885493215512885)
                  ·
                    refine ⟨3767790960926764988954333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40189770249885493215512885 3767790960926764988954333)
                    ·
                      refine ⟨1412921610347536870857875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3767790960926764988954333 1412921610347536870857875)
                      ·
                        rfl

theorem cell23_2751655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_2751655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751655 prefixEnd_2751655 := by exact prefixLift 2751655
  have htrace : WordTrace (prefixWord ++ tailWord_2751655) baseStart_2751655 baseEnd_2751655 := by
    simpa [prefixWord, tailWord_2751655, baseEnd_2751655] using wordTrace_append hprefix tailTrace_2751655
  have hstable : (prefixWord ++ tailWord_2751655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751655).length < 2 ^ (prefixWord ++ tailWord_2751655).sum := by decide
  have hdescent : baseEnd_2751655 < baseStart_2751655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751795 : List Nat := [1, 1, 1, 2, 5, 3, 1, 2, 1, 6]
def baseStart_2751795 : Nat := 118140960795 + 2751795 * 2 ^ 59
def prefixEnd_2751795 : Nat := 4983230072969 + 3 ^ 40 * 2751795 * 2
def baseEnd_2751795 : Nat := 470997832546388774369077

theorem tailTrace_2751795 : CollatzResearch.WordTrace tailWord_2751795 prefixEnd_2751795 470997832546388774369077 := by
  unfold tailWord_2751795
  simp only [CollatzResearch.WordTrace]
  refine ⟨100366209065724159014952839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66910806043816106009968559 100366209065724159014952839)
  ·
    refine ⟨150549313598586238522429259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100366209065724159014952839 150549313598586238522429259)
    ·
      refine ⟨225823970397879357783643889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150549313598586238522429259 225823970397879357783643889)
      ·
        refine ⟨169367977798409518337732917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225823970397879357783643889 169367977798409518337732917)
        ·
          refine ⟨15878247918600892344162461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 169367977798409518337732917 15878247918600892344162461)
          ·
            refine ⟨5954342969475334629060923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15878247918600892344162461 5954342969475334629060923)
            ·
              refine ⟨8931514454213001943591385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5954342969475334629060923 8931514454213001943591385)
              ·
                refine ⟨6698635840659751457693539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8931514454213001943591385 6698635840659751457693539)
                ·
                  refine ⟨10047953760989627186540309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6698635840659751457693539 10047953760989627186540309)
                  ·
                    refine ⟨470997832546388774369077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10047953760989627186540309 470997832546388774369077)
                    ·
                      rfl

theorem cell23_2751795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 6].length) (baseStart_2751795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751795 prefixEnd_2751795 := by exact prefixLift 2751795
  have htrace : WordTrace (prefixWord ++ tailWord_2751795) baseStart_2751795 baseEnd_2751795 := by
    simpa [prefixWord, tailWord_2751795, baseEnd_2751795] using wordTrace_append hprefix tailTrace_2751795
  have hstable : (prefixWord ++ tailWord_2751795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751795).length < 2 ^ (prefixWord ++ tailWord_2751795).sum := by decide
  have hdescent : baseEnd_2751795 < baseStart_2751795 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751796 : List Nat := [2, 5, 1, 1, 1, 1, 2, 5, 1, 1, 3]
def baseStart_2751796 : Nat := 118140960795 + 2751796 * 2 ^ 59
def prefixEnd_2751796 : Nat := 4983230072969 + 3 ^ 40 * 2751796 * 2
def baseEnd_2751796 : Nat := 1412994011119820819194727

theorem tailTrace_2751796 : CollatzResearch.WordTrace tailWord_2751796 prefixEnd_2751796 1412994011119820819194727 := by
  unfold tailWord_2751796
  simp only [CollatzResearch.WordTrace]
  refine ⟨50183122769360268092869621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66910830359147024123826161 50183122769360268092869621)
  ·
    refine ⟨4704667759627525133706527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50183122769360268092869621 4704667759627525133706527)
    ·
      refine ⟨7057001639441287700559791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4704667759627525133706527 7057001639441287700559791)
      ·
        refine ⟨10585502459161931550839687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7057001639441287700559791 10585502459161931550839687)
        ·
          refine ⟨15878253688742897326259531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10585502459161931550839687 15878253688742897326259531)
          ·
            refine ⟨23817380533114345989389297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15878253688742897326259531 23817380533114345989389297)
            ·
              refine ⟨17863035399835759492041973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23817380533114345989389297 17863035399835759492041973)
              ·
                refine ⟨1674659568734602452378935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17863035399835759492041973 1674659568734602452378935)
                ·
                  refine ⟨2511989353101903678568403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1674659568734602452378935 2511989353101903678568403)
                  ·
                    refine ⟨3767984029652855517852605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2511989353101903678568403 3767984029652855517852605)
                    ·
                      refine ⟨1412994011119820819194727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3767984029652855517852605 1412994011119820819194727)
                      ·
                        rfl

theorem cell23_2751796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_2751796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751796 prefixEnd_2751796 := by exact prefixLift 2751796
  have htrace : WordTrace (prefixWord ++ tailWord_2751796) baseStart_2751796 baseEnd_2751796 := by
    simpa [prefixWord, tailWord_2751796, baseEnd_2751796] using wordTrace_append hprefix tailTrace_2751796
  have hstable : (prefixWord ++ tailWord_2751796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751796).length < 2 ^ (prefixWord ++ tailWord_2751796).sum := by decide
  have hdescent : baseEnd_2751796 < baseStart_2751796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751830 : List Nat := [5, 2, 3, 1, 1, 1, 1, 2, 3, 1, 3]
def baseStart_2751830 : Nat := 118140960795 + 2751830 * 2 ^ 59
def prefixEnd_2751830 : Nat := 4983230072969 + 3 ^ 40 * 2751830 * 2
def baseEnd_2751830 : Nat := 1413011469462073686169571

theorem tailTrace_2751830 : CollatzResearch.WordTrace tailWord_2751830 prefixEnd_2751830 1413011469462073686169571 := by
  unfold tailWord_2751830
  simp only [CollatzResearch.WordTrace]
  refine ⟨6272967851287334999529809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66911657080398239994984629 6272967851287334999529809)
  ·
    refine ⟨4704725888465501249647357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6272967851287334999529809 4704725888465501249647357)
    ·
      refine ⟨1764272208174562968617759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4704725888465501249647357 1764272208174562968617759)
      ·
        refine ⟨2646408312261844452926639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1764272208174562968617759 2646408312261844452926639)
        ·
          refine ⟨3969612468392766679389959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2646408312261844452926639 3969612468392766679389959)
          ·
            refine ⟨5954418702589150019084939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3969612468392766679389959 5954418702589150019084939)
            ·
              refine ⟨8931628053883725028627409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5954418702589150019084939 8931628053883725028627409)
              ·
                refine ⟨6698721040412793771470557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8931628053883725028627409 6698721040412793771470557)
                ·
                  refine ⟨2512020390154797664301459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6698721040412793771470557 2512020390154797664301459)
                  ·
                    refine ⟨3768030585232196496452189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2512020390154797664301459 3768030585232196496452189)
                    ·
                      refine ⟨1413011469462073686169571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3768030585232196496452189 1413011469462073686169571)
                      ·
                        rfl

theorem cell23_2751830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_2751830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751830 prefixEnd_2751830 := by exact prefixLift 2751830
  have htrace : WordTrace (prefixWord ++ tailWord_2751830) baseStart_2751830 baseEnd_2751830 := by
    simpa [prefixWord, tailWord_2751830, baseEnd_2751830] using wordTrace_append hprefix tailTrace_2751830
  have hstable : (prefixWord ++ tailWord_2751830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751830).length < 2 ^ (prefixWord ++ tailWord_2751830).sum := by decide
  have hdescent : baseEnd_2751830 < baseStart_2751830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751842 : List Nat := [3, 3, 2, 1, 1, 1, 5, 7]
def baseStart_2751842 : Nat := 118140960795 + 2751842 * 2 ^ 59
def prefixEnd_2751842 : Nat := 4983230072969 + 3 ^ 40 * 2751842 * 2
def baseEnd_2751842 : Nat := 52333986341849171822945

theorem tailTrace_2751842 : CollatzResearch.WordTrace tailWord_2751842 prefixEnd_2751842 52333986341849171822945 := by
  unfold tailWord_2751842
  simp only [CollatzResearch.WordTrace]
  refine ⟨25091980824138471510478445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66911948864369257361275853 25091980824138471510478445)
  ·
    refine ⟨9409492809051926816429417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25091980824138471510478445 9409492809051926816429417)
    ·
      refine ⟨7057119606788945112322063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9409492809051926816429417 7057119606788945112322063)
      ·
        refine ⟨10585679410183417668483095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7057119606788945112322063 10585679410183417668483095)
        ·
          refine ⟨15878519115275126502724643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10585679410183417668483095 15878519115275126502724643)
          ·
            refine ⟨23817778672912689754086965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15878519115275126502724643 23817778672912689754086965)
            ·
              refine ⟨2232916750585564664445653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23817778672912689754086965 2232916750585564664445653)
              ·
                refine ⟨52333986341849171822945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2232916750585564664445653 52333986341849171822945)
                ·
                  rfl

theorem cell23_2751842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 7].length) (baseStart_2751842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751842 prefixEnd_2751842 := by exact prefixLift 2751842
  have htrace : WordTrace (prefixWord ++ tailWord_2751842) baseStart_2751842 baseEnd_2751842 := by
    simpa [prefixWord, tailWord_2751842, baseEnd_2751842] using wordTrace_append hprefix tailTrace_2751842
  have hstable : (prefixWord ++ tailWord_2751842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751842).length < 2 ^ (prefixWord ++ tailWord_2751842).sum := by decide
  have hdescent : baseEnd_2751842 < baseStart_2751842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751852 : List Nat := [2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 3]
def baseStart_2751852 : Nat := 118140960795 + 2751852 * 2 ^ 59
def prefixEnd_2751852 : Nat := 4983230072969 + 3 ^ 40 * 2751852 * 2
def baseEnd_2751852 : Nat := 1413022766036472600094469

theorem tailTrace_2751852 : CollatzResearch.WordTrace tailWord_2751852 prefixEnd_2751852 1413022766036472600094469 := by
  unfold tailWord_2751852
  simp only [CollatzResearch.WordTrace]
  refine ⟨50184144013258828874888905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66912192017678438499851873 50184144013258828874888905)
  ·
    refine ⟨37638108009944121656166679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50184144013258828874888905 37638108009944121656166679)
    ·
      refine ⟨56457162014916182484250019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37638108009944121656166679 56457162014916182484250019)
      ·
        refine ⟨84685743022374273726375029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56457162014916182484250019 84685743022374273726375029)
        ·
          refine ⟨7939288408347588161847659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 84685743022374273726375029 7939288408347588161847659)
          ·
            refine ⟨11908932612521382242771489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7939288408347588161847659 11908932612521382242771489)
            ·
              refine ⟨8931699459391036682078617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11908932612521382242771489 8931699459391036682078617)
              ·
                refine ⟨6698774594543277511558963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8931699459391036682078617 6698774594543277511558963)
                ·
                  refine ⟨10048161891814916267338445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6698774594543277511558963 10048161891814916267338445)
                  ·
                    refine ⟨3768060709430593600251917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10048161891814916267338445 3768060709430593600251917)
                    ·
                      refine ⟨1413022766036472600094469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3768060709430593600251917 1413022766036472600094469)
                      ·
                        rfl

theorem cell23_2751852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 3].length) (baseStart_2751852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751852 prefixEnd_2751852 := by exact prefixLift 2751852
  have htrace : WordTrace (prefixWord ++ tailWord_2751852) baseStart_2751852 baseEnd_2751852 := by
    simpa [prefixWord, tailWord_2751852, baseEnd_2751852] using wordTrace_append hprefix tailTrace_2751852
  have hstable : (prefixWord ++ tailWord_2751852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751852).length < 2 ^ (prefixWord ++ tailWord_2751852).sum := by decide
  have hdescent : baseEnd_2751852 < baseStart_2751852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751853 : List Nat := [1, 5, 1, 1, 1, 4, 2, 3, 1, 2, 2]
def baseStart_2751853 : Nat := 118140960795 + 2751853 * 2 ^ 59
def prefixEnd_2751853 : Nat := 4983230072969 + 3 ^ 40 * 2751853 * 2
def baseEnd_2751853 : Nat := 1413023279517127096181965

theorem tailTrace_2751853 : CollatzResearch.WordTrace tailWord_2751853 prefixEnd_2751853 1413023279517127096181965 := by
  unfold tailWord_2751853
  simp only [CollatzResearch.WordTrace]
  refine ⟨100368324499514034920564213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66912216333009356613709475 100368324499514034920564213)
  ·
    refine ⟨9409530421829440773802895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 100368324499514034920564213 9409530421829440773802895)
    ·
      refine ⟨14114295632744161160704343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9409530421829440773802895 14114295632744161160704343)
      ·
        refine ⟨21171443449116241741056515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14114295632744161160704343 21171443449116241741056515)
        ·
          refine ⟨31757165173674362611584773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21171443449116241741056515 31757165173674362611584773)
          ·
            refine ⟨5954468470063942989672145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31757165173674362611584773 5954468470063942989672145)
            ·
              refine ⟨4465851352547957242254109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5954468470063942989672145 4465851352547957242254109)
              ·
                refine ⟨1674694257205483965845291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4465851352547957242254109 1674694257205483965845291)
                ·
                  refine ⟨2512041385808225948767937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1674694257205483965845291 2512041385808225948767937)
                  ·
                    refine ⟨1884031039356169461575953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2512041385808225948767937 1884031039356169461575953)
                    ·
                      refine ⟨1413023279517127096181965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1884031039356169461575953 1413023279517127096181965)
                      ·
                        rfl

theorem cell23_2751853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 3, 1, 2, 2].length) (baseStart_2751853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751853 prefixEnd_2751853 := by exact prefixLift 2751853
  have htrace : WordTrace (prefixWord ++ tailWord_2751853) baseStart_2751853 baseEnd_2751853 := by
    simpa [prefixWord, tailWord_2751853, baseEnd_2751853] using wordTrace_append hprefix tailTrace_2751853
  have hstable : (prefixWord ++ tailWord_2751853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751853).length < 2 ^ (prefixWord ++ tailWord_2751853).sum := by decide
  have hdescent : baseEnd_2751853 < baseStart_2751853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751870 : List Nat := [4, 2, 3, 2, 1, 1, 2, 1, 3, 2, 2]
def baseStart_2751870 : Nat := 118140960795 + 2751870 * 2 ^ 59
def prefixEnd_2751870 : Nat := 4983230072969 + 3 ^ 40 * 2751870 * 2
def baseEnd_2751870 : Nat := 1413032008688253529669387

theorem tailTrace_2751870 : CollatzResearch.WordTrace tailWord_2751870 prefixEnd_2751870 1413032008688253529669387 := by
  unfold tailWord_2751870
  simp only [CollatzResearch.WordTrace]
  refine ⟨12546118067556555852991633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66912629693634964549288709 12546118067556555852991633)
  ·
    refine ⟨9409588550667416889743725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12546118067556555852991633 9409588550667416889743725)
    ·
      refine ⟨3528595706500281333653897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9409588550667416889743725 3528595706500281333653897)
      ·
        refine ⟨2646446779875211000240423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3528595706500281333653897 2646446779875211000240423)
        ·
          refine ⟨3969670169812816500360635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2646446779875211000240423 3969670169812816500360635)
          ·
            refine ⟨5954505254719224750540953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3969670169812816500360635 5954505254719224750540953)
            ·
              refine ⟨4465878941039418562905715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5954505254719224750540953 4465878941039418562905715)
              ·
                refine ⟨6698818411559127844358573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4465878941039418562905715 6698818411559127844358573)
                ·
                  refine ⟨2512056904334672941634465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6698818411559127844358573 2512056904334672941634465)
                  ·
                    refine ⟨1884042678251004706225849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2512056904334672941634465 1884042678251004706225849)
                    ·
                      refine ⟨1413032008688253529669387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1884042678251004706225849 1413032008688253529669387)
                      ·
                        rfl

theorem cell23_2751870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_2751870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751870 prefixEnd_2751870 := by exact prefixLift 2751870
  have htrace : WordTrace (prefixWord ++ tailWord_2751870) baseStart_2751870 baseEnd_2751870 := by
    simpa [prefixWord, tailWord_2751870, baseEnd_2751870] using wordTrace_append hprefix tailTrace_2751870
  have hstable : (prefixWord ++ tailWord_2751870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751870).length < 2 ^ (prefixWord ++ tailWord_2751870).sum := by decide
  have hdescent : baseEnd_2751870 < baseStart_2751870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751886 : List Nat := [4, 1, 1, 4, 2, 2, 1, 1, 1, 3, 3]
def baseStart_2751886 : Nat := 118140960795 + 2751886 * 2 ^ 59
def prefixEnd_2751886 : Nat := 4983230072969 + 3 ^ 40 * 2751886 * 2
def baseEnd_2751886 : Nat := 1413040224378725467069313

theorem tailTrace_2751886 : CollatzResearch.WordTrace tailWord_2751886 prefixEnd_2751886 1413040224378725467069313 := by
  unfold tailWord_2751886
  simp only [CollatzResearch.WordTrace]
  refine ⟨12546191013549310194564439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66913018738929654371010341 12546191013549310194564439)
  ·
    refine ⟨18819286520323965291846659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12546191013549310194564439 18819286520323965291846659)
    ·
      refine ⟨28228929780485947937769989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18819286520323965291846659 28228929780485947937769989)
      ·
        refine ⟨5292924333841115238331873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28228929780485947937769989 5292924333841115238331873)
        ·
          refine ⟨3969693250380836428748905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5292924333841115238331873 3969693250380836428748905)
          ·
            refine ⟨2977269937785627321561679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3969693250380836428748905 2977269937785627321561679)
            ·
              refine ⟨4465904906678440982342519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2977269937785627321561679 4465904906678440982342519)
              ·
                refine ⟨6698857360017661473513779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4465904906678440982342519 6698857360017661473513779)
                ·
                  refine ⟨10048286040026492210270669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6698857360017661473513779 10048286040026492210270669)
                  ·
                    refine ⟨3768107265009934578851501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10048286040026492210270669 3768107265009934578851501)
                    ·
                      refine ⟨1413040224378725467069313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3768107265009934578851501 1413040224378725467069313)
                      ·
                        rfl

theorem cell23_2751886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_2751886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751886 prefixEnd_2751886 := by exact prefixLift 2751886
  have htrace : WordTrace (prefixWord ++ tailWord_2751886) baseStart_2751886 baseEnd_2751886 := by
    simpa [prefixWord, tailWord_2751886, baseEnd_2751886] using wordTrace_append hprefix tailTrace_2751886
  have hstable : (prefixWord ++ tailWord_2751886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751886).length < 2 ^ (prefixWord ++ tailWord_2751886).sum := by decide
  have hdescent : baseEnd_2751886 < baseStart_2751886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751895 : List Nat := [1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 5]
def baseStart_2751895 : Nat := 118140960795 + 2751895 * 2 ^ 59
def prefixEnd_2751895 : Nat := 4983230072969 + 3 ^ 40 * 2751895 * 2
def baseEnd_2751895 : Nat := 1413044845704615931856771

theorem tailTrace_2751895 : CollatzResearch.WordTrace tailWord_2751895 prefixEnd_2751895 1413044845704615931856771 := by
  unfold tailWord_2751895
  simp only [CollatzResearch.WordTrace]
  refine ⟨100369856365361876093593139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66913237576907917395728759 100369856365361876093593139)
  ·
    refine ⟨150554784548042814140389709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100369856365361876093593139 150554784548042814140389709)
    ·
      refine ⟨56458044205516055302646141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150554784548042814140389709 56458044205516055302646141)
      ·
        refine ⟨21171766577068520738492303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56458044205516055302646141 21171766577068520738492303)
        ·
          refine ⟨31757649865602781107738455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21171766577068520738492303 31757649865602781107738455)
          ·
            refine ⟨47636474798404171661607683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31757649865602781107738455 47636474798404171661607683)
            ·
              refine ⟨71454712197606257492411525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47636474798404171661607683 71454712197606257492411525)
              ·
                refine ⟨13397758537051173279827161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71454712197606257492411525 13397758537051173279827161)
                ·
                  refine ⟨10048318902788379959870371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13397758537051173279827161 10048318902788379959870371)
                  ·
                    refine ⟨15072478354182569939805557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10048318902788379959870371 15072478354182569939805557)
                    ·
                      refine ⟨1413044845704615931856771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15072478354182569939805557 1413044845704615931856771)
                      ·
                        rfl

theorem cell23_2751895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_2751895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751895 prefixEnd_2751895 := by exact prefixLift 2751895
  have htrace : WordTrace (prefixWord ++ tailWord_2751895) baseStart_2751895 baseEnd_2751895 := by
    simpa [prefixWord, tailWord_2751895, baseEnd_2751895] using wordTrace_append hprefix tailTrace_2751895
  have hstable : (prefixWord ++ tailWord_2751895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751895).length < 2 ^ (prefixWord ++ tailWord_2751895).sum := by decide
  have hdescent : baseEnd_2751895 < baseStart_2751895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751945 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 6, 5]
def baseStart_2751945 : Nat := 118140960795 + 2751945 * 2 ^ 59
def prefixEnd_2751945 : Nat := 4983230072969 + 3 ^ 40 * 2751945 * 2
def baseEnd_2751945 : Nat := 471023506579113578743847

theorem tailTrace_2751945 : CollatzResearch.WordTrace tailWord_2751945 prefixEnd_2751945 471023506579113578743847 := by
  unfold tailWord_2751945
  simp only [CollatzResearch.WordTrace]
  refine ⟨100371680015180734632913289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66914453343453823088608859 100371680015180734632913289)
  ·
    refine ⟨75278760011385550974684967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100371680015180734632913289 75278760011385550974684967)
    ·
      refine ⟨112918140017078326462027451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75278760011385550974684967 112918140017078326462027451)
      ·
        refine ⟨169377210025617489693041177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112918140017078326462027451 169377210025617489693041177)
        ·
          refine ⟨127032907519213117269780883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169377210025617489693041177 127032907519213117269780883)
          ·
            refine ⟨190549361278819675904671325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127032907519213117269780883 190549361278819675904671325)
            ·
              refine ⟨71456010479557378464251747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 190549361278819675904671325 71456010479557378464251747)
              ·
                refine ⟨107184015719336067696377621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71456010479557378464251747 107184015719336067696377621)
                ·
                  refine ⟨5024250736843878173267701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 107184015719336067696377621 5024250736843878173267701)
                  ·
                    refine ⟨471023506579113578743847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5024250736843878173267701 471023506579113578743847)
                    ·
                      rfl

theorem cell23_2751945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 6, 5].length) (baseStart_2751945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751945 prefixEnd_2751945 := by exact prefixLift 2751945
  have htrace : WordTrace (prefixWord ++ tailWord_2751945) baseStart_2751945 baseEnd_2751945 := by
    simpa [prefixWord, tailWord_2751945, baseEnd_2751945] using wordTrace_append hprefix tailTrace_2751945
  have hstable : (prefixWord ++ tailWord_2751945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751945).length < 2 ^ (prefixWord ++ tailWord_2751945).sum := by decide
  have hdescent : baseEnd_2751945 < baseStart_2751945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751952 : List Nat := [2, 1, 1, 1, 1, 2, 2, 4, 2, 5, 2]
def baseStart_2751952 : Nat := 118140960795 + 2751952 * 2 ^ 59
def prefixEnd_2751952 : Nat := 4983230072969 + 3 ^ 40 * 2751952 * 2
def baseEnd_2751952 : Nat := 1413074114101922208844009

theorem tailTrace_2751952 : CollatzResearch.WordTrace tailWord_2751952 prefixEnd_2751952 1413074114101922208844009 := by
  unfold tailWord_2751952
  simp only [CollatzResearch.WordTrace]
  refine ⟨50185967663077687414209055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66914623550770249885612073 50185967663077687414209055)
  ·
    refine ⟨75278951494616531121313583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50185967663077687414209055 75278951494616531121313583)
    ·
      refine ⟨112918427241924796681970375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75278951494616531121313583 112918427241924796681970375)
      ·
        refine ⟨169377640862887195022955563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112918427241924796681970375 169377640862887195022955563)
        ·
          refine ⟨254066461294330792534433345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169377640862887195022955563 254066461294330792534433345)
          ·
            refine ⟨190549845970748094400825009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 254066461294330792534433345 190549845970748094400825009)
            ·
              refine ⟨142912384478061070800618757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190549845970748094400825009 142912384478061070800618757)
              ·
                refine ⟨26796072089636450775116017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 142912384478061070800618757 26796072089636450775116017)
                ·
                  refine ⟨20097054067227338081337013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26796072089636450775116017 20097054067227338081337013)
                  ·
                    refine ⟨1884098818802562945125345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20097054067227338081337013 1884098818802562945125345)
                    ·
                      refine ⟨1413074114101922208844009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1884098818802562945125345 1413074114101922208844009)
                      ·
                        rfl

theorem cell23_2751952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 2, 5, 2].length) (baseStart_2751952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751952 prefixEnd_2751952 := by exact prefixLift 2751952
  have htrace : WordTrace (prefixWord ++ tailWord_2751952) baseStart_2751952 baseEnd_2751952 := by
    simpa [prefixWord, tailWord_2751952, baseEnd_2751952] using wordTrace_append hprefix tailTrace_2751952
  have hstable : (prefixWord ++ tailWord_2751952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751952).length < 2 ^ (prefixWord ++ tailWord_2751952).sum := by decide
  have hdescent : baseEnd_2751952 < baseStart_2751952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751962 : List Nat := [3, 1, 1, 2, 3, 2, 1, 3, 2, 5]
def baseStart_2751962 : Nat := 118140960795 + 2751962 * 2 ^ 59
def prefixEnd_2751962 : Nat := 4983230072969 + 3 ^ 40 * 2751962 * 2
def baseEnd_2751962 : Nat := 471026416302822389906321

theorem tailTrace_2751962 : CollatzResearch.WordTrace tailWord_2751962 prefixEnd_2751962 471026416302822389906321 := by
  unfold tailWord_2751962
  simp only [CollatzResearch.WordTrace]
  refine ⟨25093075014029786634070535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66914866704079431024188093 25093075014029786634070535)
  ·
    refine ⟨37639612521044679951105803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25093075014029786634070535 37639612521044679951105803)
    ·
      refine ⟨56459418781567019926658705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37639612521044679951105803 56459418781567019926658705)
      ·
        refine ⟨42344564086175264944994029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56459418781567019926658705 42344564086175264944994029)
        ·
          refine ⟨15879211532315724354372761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42344564086175264944994029 15879211532315724354372761)
          ·
            refine ⟨11909408649236793265779571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15879211532315724354372761 11909408649236793265779571)
            ·
              refine ⟨17864112973855189898669357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11909408649236793265779571 17864112973855189898669357)
              ·
                refine ⟨6699042365195696212001009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17864112973855189898669357 6699042365195696212001009)
                ·
                  refine ⟨5024281773896772159000757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6699042365195696212001009 5024281773896772159000757)
                  ·
                    refine ⟨471026416302822389906321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5024281773896772159000757 471026416302822389906321)
                    ·
                      rfl

theorem cell23_2751962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 2, 5].length) (baseStart_2751962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751962 prefixEnd_2751962 := by exact prefixLift 2751962
  have htrace : WordTrace (prefixWord ++ tailWord_2751962) baseStart_2751962 baseEnd_2751962 := by
    simpa [prefixWord, tailWord_2751962, baseEnd_2751962] using wordTrace_append hprefix tailTrace_2751962
  have hstable : (prefixWord ++ tailWord_2751962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751962).length < 2 ^ (prefixWord ++ tailWord_2751962).sum := by decide
  have hdescent : baseEnd_2751962 < baseStart_2751962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751989 : List Nat := [1, 3, 5, 1, 1, 1, 2, 1, 1, 2, 5]
def baseStart_2751989 : Nat := 118140960795 + 2751989 * 2 ^ 59
def prefixEnd_2751989 : Nat := 4983230072969 + 3 ^ 40 * 2751989 * 2
def baseEnd_2751989 : Nat := 1413093112886138564081339

theorem tailTrace_2751989 : CollatzResearch.WordTrace tailWord_2751989 prefixEnd_2751989 1413093112886138564081339 := by
  unfold tailWord_2751989
  simp only [CollatzResearch.WordTrace]
  refine ⟨100373284827021330147515021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66915523218014220098343347 100373284827021330147515021)
  ·
    refine ⟨37639981810132998805318133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100373284827021330147515021 37639981810132998805318133)
    ·
      refine ⟨3528748294699968637998575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37639981810132998805318133 3528748294699968637998575)
      ·
        refine ⟨5293122442049952956997863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3528748294699968637998575 5293122442049952956997863)
        ·
          refine ⟨7939683663074929435496795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5293122442049952956997863 7939683663074929435496795)
          ·
            refine ⟨11909525494612394153245193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7939683663074929435496795 11909525494612394153245193)
            ·
              refine ⟨8932144120959295614933895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11909525494612394153245193 8932144120959295614933895)
              ·
                refine ⟨13398216181438943422400843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8932144120959295614933895 13398216181438943422400843)
                ·
                  refine ⟨20097324272158415133601265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13398216181438943422400843 20097324272158415133601265)
                  ·
                    refine ⟨15072993204118811350200949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20097324272158415133601265 15072993204118811350200949)
                    ·
                      refine ⟨1413093112886138564081339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15072993204118811350200949 1413093112886138564081339)
                      ·
                        rfl

theorem cell23_2751989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_2751989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751989 prefixEnd_2751989 := by exact prefixLift 2751989
  have htrace : WordTrace (prefixWord ++ tailWord_2751989) baseStart_2751989 baseEnd_2751989 := by
    simpa [prefixWord, tailWord_2751989, baseEnd_2751989] using wordTrace_append hprefix tailTrace_2751989
  have hstable : (prefixWord ++ tailWord_2751989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751989).length < 2 ^ (prefixWord ++ tailWord_2751989).sum := by decide
  have hdescent : baseEnd_2751989 < baseStart_2751989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751995 : List Nat := [1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 6]
def baseStart_2751995 : Nat := 118140960795 + 2751995 * 2 ^ 59
def prefixEnd_2751995 : Nat := 4983230072969 + 3 ^ 40 * 2751995 * 2
def baseEnd_2751995 : Nat := 1413096193770065540606311

theorem tailTrace_2751995 : CollatzResearch.WordTrace tailWord_2751995 prefixEnd_2751995 1413096193770065540606311 := by
  unfold tailWord_2751995
  simp only [CollatzResearch.WordTrace]
  refine ⟨100373503664999593172233439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66915669109999728781488959 100373503664999593172233439)
  ·
    refine ⟨150560255497499389758350159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100373503664999593172233439 150560255497499389758350159)
    ·
      refine ⟨225840383246249084637525239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150560255497499389758350159 225840383246249084637525239)
      ·
        refine ⟨338760574869373626956287859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225840383246249084637525239 338760574869373626956287859)
        ·
          refine ⟨508140862304060440434431789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338760574869373626956287859 508140862304060440434431789)
          ·
            refine ⟨190552823364022665162911921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 508140862304060440434431789 190552823364022665162911921)
            ·
              refine ⟨142914617523016998872183941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190552823364022665162911921 142914617523016998872183941)
              ·
                refine ⟨26796490785565687288534489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 142914617523016998872183941 26796490785565687288534489)
                ·
                  refine ⟨20097368089174265466400867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26796490785565687288534489 20097368089174265466400867)
                  ·
                    refine ⟨30146052133761398199601301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20097368089174265466400867 30146052133761398199601301)
                    ·
                      refine ⟨1413096193770065540606311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30146052133761398199601301 1413096193770065540606311)
                      ·
                        rfl

theorem cell23_2751995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 6].length) (baseStart_2751995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2751995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2751995 prefixEnd_2751995 := by exact prefixLift 2751995
  have htrace : WordTrace (prefixWord ++ tailWord_2751995) baseStart_2751995 baseEnd_2751995 := by
    simpa [prefixWord, tailWord_2751995, baseEnd_2751995] using wordTrace_append hprefix tailTrace_2751995
  have hstable : (prefixWord ++ tailWord_2751995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751995).length < 2 ^ (prefixWord ++ tailWord_2751995).sum := by decide
  have hdescent : baseEnd_2751995 < baseStart_2751995 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752005 : List Nat := [1, 3, 1, 1, 2, 2, 1, 2, 10]
def baseStart_2752005 : Nat := 118140960795 + 2752005 * 2 ^ 59
def prefixEnd_2752005 : Nat := 4983230072969 + 3 ^ 40 * 2752005 * 2
def baseEnd_2752005 : Nat := 157011258730734500164585

theorem tailTrace_2752005 : CollatzResearch.WordTrace tailWord_2752005 prefixEnd_2752005 157011258730734500164585 := by
  unfold tailWord_2752005
  simp only [CollatzResearch.WordTrace]
  refine ⟨100373868394963364880097469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66915912263308909920064979 100373868394963364880097469)
  ·
    refine ⟨37640200648111261830036551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100373868394963364880097469 37640200648111261830036551)
    ·
      refine ⟨56460300972166892745054827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37640200648111261830036551 56460300972166892745054827)
      ·
        refine ⟨84690451458250339117582241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56460300972166892745054827 84690451458250339117582241)
        ·
          refine ⟨63517838593687754338186681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84690451458250339117582241 63517838593687754338186681)
          ·
            refine ⟨47638378945265815753640011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63517838593687754338186681 47638378945265815753640011)
            ·
              refine ⟨71457568417898723630460017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47638378945265815753640011 71457568417898723630460017)
              ·
                refine ⟨53593176313424042722845013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71457568417898723630460017 53593176313424042722845013)
                ·
                  refine ⟨157011258730734500164585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 53593176313424042722845013 157011258730734500164585)
                  ·
                    rfl

theorem cell23_2752005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 10].length) (baseStart_2752005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2752005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2752005 prefixEnd_2752005 := by exact prefixLift 2752005
  have htrace : WordTrace (prefixWord ++ tailWord_2752005) baseStart_2752005 baseEnd_2752005 := by
    simpa [prefixWord, tailWord_2752005, baseEnd_2752005] using wordTrace_append hprefix tailTrace_2752005
  have hstable : (prefixWord ++ tailWord_2752005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752005).length < 2 ^ (prefixWord ++ tailWord_2752005).sum := by decide
  have hdescent : baseEnd_2752005 < baseStart_2752005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752019 : List Nat := [1, 1, 1, 2, 1, 6, 3, 1, 2, 2, 3]
def baseStart_2752019 : Nat := 118140960795 + 2752019 * 2 ^ 59
def prefixEnd_2752019 : Nat := 4983230072969 + 3 ^ 40 * 2752019 * 2
def baseEnd_2752019 : Nat := 1413108517305773446706201

theorem tailTrace_2752019 : CollatzResearch.WordTrace tailWord_2752019 prefixEnd_2752019 1413108517305773446706201 := by
  unfold tailWord_2752019
  simp only [CollatzResearch.WordTrace]
  refine ⟨100374379016912645271107111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66916252677941763514071407 100374379016912645271107111)
  ·
    refine ⟨150561568525368967906660667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100374379016912645271107111 150561568525368967906660667)
    ·
      refine ⟨225842352788053451859991001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150561568525368967906660667 225842352788053451859991001)
      ·
        refine ⟨169381764591040088894993251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225842352788053451859991001 169381764591040088894993251)
        ·
          refine ⟨254072646886560133342489877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169381764591040088894993251 254072646886560133342489877)
          ·
            refine ⟨11909655322807506250429213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 254072646886560133342489877 11909655322807506250429213)
            ·
              refine ⟨4466120746052814843910955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11909655322807506250429213 4466120746052814843910955)
              ·
                refine ⟨6699181119079222265866433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4466120746052814843910955 6699181119079222265866433)
                ·
                  refine ⟨5024385839309416699399825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6699181119079222265866433 5024385839309416699399825)
                  ·
                    refine ⟨3768289379482062524549869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5024385839309416699399825 3768289379482062524549869)
                    ·
                      refine ⟨1413108517305773446706201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3768289379482062524549869 1413108517305773446706201)
                      ·
                        rfl

theorem cell23_2752019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 2, 2, 3].length) (baseStart_2752019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2752019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2752019 prefixEnd_2752019 := by exact prefixLift 2752019
  have htrace : WordTrace (prefixWord ++ tailWord_2752019) baseStart_2752019 baseEnd_2752019 := by
    simpa [prefixWord, tailWord_2752019, baseEnd_2752019] using wordTrace_append hprefix tailTrace_2752019
  have hstable : (prefixWord ++ tailWord_2752019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752019).length < 2 ^ (prefixWord ++ tailWord_2752019).sum := by decide
  have hdescent : baseEnd_2752019 < baseStart_2752019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752025 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 3, 1, 8]
def baseStart_2752025 : Nat := 118140960795 + 2752025 * 2 ^ 59
def prefixEnd_2752025 : Nat := 4983230072969 + 3 ^ 40 * 2752025 * 2
def baseEnd_2752025 : Nat := 1413111598189700423231173

theorem tailTrace_2752025 : CollatzResearch.WordTrace tailWord_2752025 prefixEnd_2752025 1413111598189700423231173 := by
  unfold tailWord_2752025
  simp only [CollatzResearch.WordTrace]
  refine ⟨100374597854890908295825529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66916398569927272197217019 100374597854890908295825529)
  ·
    refine ⟨75280948391168181221869147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100374597854890908295825529 75280948391168181221869147)
    ·
      refine ⟨112921422586752271832803721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75280948391168181221869147 112921422586752271832803721)
      ·
        refine ⟨84691066940064203874602791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112921422586752271832803721 84691066940064203874602791)
        ·
          refine ⟨127036600410096305811904187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84691066940064203874602791 127036600410096305811904187)
          ·
            refine ⟨190554900615144458717856281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127036600410096305811904187 190554900615144458717856281)
            ·
              refine ⟨142916175461358344038392211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190554900615144458717856281 142916175461358344038392211)
              ·
                refine ⟨214374263192037516057588317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142916175461358344038392211 214374263192037516057588317)
                ·
                  refine ⟨80390348697014068521595619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 214374263192037516057588317 80390348697014068521595619)
                  ·
                    refine ⟨120585523045521102782393429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 80390348697014068521595619 120585523045521102782393429)
                    ·
                      refine ⟨1413111598189700423231173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 120585523045521102782393429 1413111598189700423231173)
                      ·
                        rfl

theorem cell23_2752025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 1, 8].length) (baseStart_2752025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2752025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2752025 prefixEnd_2752025 := by exact prefixLift 2752025
  have htrace : WordTrace (prefixWord ++ tailWord_2752025) baseStart_2752025 baseEnd_2752025 := by
    simpa [prefixWord, tailWord_2752025, baseEnd_2752025] using wordTrace_append hprefix tailTrace_2752025
  have hstable : (prefixWord ++ tailWord_2752025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752025).length < 2 ^ (prefixWord ++ tailWord_2752025).sum := by decide
  have hdescent : baseEnd_2752025 < baseStart_2752025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752042 : List Nat := [3, 1, 4, 1, 1, 1, 1, 1, 1, 1, 8]
def baseStart_2752042 : Nat := 118140960795 + 2752042 * 2 ^ 59
def prefixEnd_2752042 : Nat := 4983230072969 + 3 ^ 40 * 2752042 * 2
def baseEnd_2752042 : Nat := 1413120327360826856718595

theorem tailTrace_2752042 : CollatzResearch.WordTrace tailWord_2752042 prefixEnd_2752042 1413120327360826856718595 := by
  unfold tailWord_2752042
  simp only [CollatzResearch.WordTrace]
  refine ⟨25093804473957330049798595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66916811930552880132796253 25093804473957330049798595)
  ·
    refine ⟨37640706710935995074697893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25093804473957330049798595 37640706710935995074697893)
    ·
      refine ⟨7057632508300499076505855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37640706710935995074697893 7057632508300499076505855)
      ·
        refine ⟨10586448762450748614758783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7057632508300499076505855 10586448762450748614758783)
        ·
          refine ⟨15879673143676122922138175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10586448762450748614758783 15879673143676122922138175)
          ·
            refine ⟨23819509715514184383207263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15879673143676122922138175 23819509715514184383207263)
            ·
              refine ⟨35729264573271276574810895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23819509715514184383207263 35729264573271276574810895)
              ·
                refine ⟨53593896859906914862216343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35729264573271276574810895 53593896859906914862216343)
                ·
                  refine ⟨80390845289860372293324515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53593896859906914862216343 80390845289860372293324515)
                  ·
                    refine ⟨120586267934790558439986773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 80390845289860372293324515 120586267934790558439986773)
                    ·
                      refine ⟨1413120327360826856718595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 120586267934790558439986773 1413120327360826856718595)
                      ·
                        rfl

theorem cell23_2752042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_2752042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2752042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2752042 prefixEnd_2752042 := by exact prefixLift 2752042
  have htrace : WordTrace (prefixWord ++ tailWord_2752042) baseStart_2752042 baseEnd_2752042 := by
    simpa [prefixWord, tailWord_2752042, baseEnd_2752042] using wordTrace_append hprefix tailTrace_2752042
  have hstable : (prefixWord ++ tailWord_2752042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752042).length < 2 ^ (prefixWord ++ tailWord_2752042).sum := by decide
  have hdescent : baseEnd_2752042 < baseStart_2752042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752069 : List Nat := [1, 3, 1, 1, 1, 4, 4, 2, 1, 5]
def baseStart_2752069 : Nat := 118140960795 + 2752069 * 2 ^ 59
def prefixEnd_2752069 : Nat := 4983230072969 + 3 ^ 40 * 2752069 * 2
def baseEnd_2752069 : Nat := 471044730446166083693657

theorem tailTrace_2752069 : CollatzResearch.WordTrace tailWord_2752069 prefixEnd_2752069 471044730446166083693657 := by
  unfold tailWord_2752069
  simp only [CollatzResearch.WordTrace]
  refine ⟨100376202666731503810427261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66917468444487669206951507 100376202666731503810427261)
  ·
    refine ⟨37641076000024313928910223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100376202666731503810427261 37641076000024313928910223)
    ·
      refine ⟨56461614000036470893365335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37641076000024313928910223 56461614000036470893365335)
      ·
        refine ⟨84692421000054706340048003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56461614000036470893365335 84692421000054706340048003)
        ·
          refine ⟨127038631500082059510072005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84692421000054706340048003 127038631500082059510072005)
          ·
            refine ⟨23819743406265386158138501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 127038631500082059510072005 23819743406265386158138501)
            ·
              refine ⟨4466201888674759904650969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23819743406265386158138501 4466201888674759904650969)
              ·
                refine ⟨3349651416506069928488227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4466201888674759904650969 3349651416506069928488227)
                ·
                  refine ⟨5024477124759104892732341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3349651416506069928488227 5024477124759104892732341)
                  ·
                    refine ⟨471044730446166083693657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5024477124759104892732341 471044730446166083693657)
                    ·
                      rfl

theorem cell23_2752069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 2, 1, 5].length) (baseStart_2752069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2752069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2752069 prefixEnd_2752069 := by exact prefixLift 2752069
  have htrace : WordTrace (prefixWord ++ tailWord_2752069) baseStart_2752069 baseEnd_2752069 := by
    simpa [prefixWord, tailWord_2752069, baseEnd_2752069] using wordTrace_append hprefix tailTrace_2752069
  have hstable : (prefixWord ++ tailWord_2752069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752069).length < 2 ^ (prefixWord ++ tailWord_2752069).sum := by decide
  have hdescent : baseEnd_2752069 < baseStart_2752069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752077 : List Nat := [1, 6, 1, 1, 4, 1, 1, 3, 1, 4]
def baseStart_2752077 : Nat := 118140960795 + 2752077 * 2 ^ 59
def prefixEnd_2752077 : Nat := 4983230072969 + 3 ^ 40 * 2752077 * 2
def baseEnd_2752077 : Nat := 471046099727911406593645

theorem tailTrace_2752077 : CollatzResearch.WordTrace tailWord_2752077 prefixEnd_2752077 471046099727911406593645 := by
  unfold tailWord_2752077
  simp only [CollatzResearch.WordTrace]
  refine ⟨100376494450702521176718485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66917662967135014117812323 100376494450702521176718485)
  ·
    refine ⟨4705148177376680680158679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 100376494450702521176718485 4705148177376680680158679)
    ·
      refine ⟨7057722266065021020238019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4705148177376680680158679 7057722266065021020238019)
      ·
        refine ⟨10586583399097531530357029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7057722266065021020238019 10586583399097531530357029)
        ·
          refine ⟨1984984387330787161941943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10586583399097531530357029 1984984387330787161941943)
          ·
            refine ⟨2977476580996180742912915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1984984387330787161941943 2977476580996180742912915)
            ·
              refine ⟨4466214871494271114369373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2977476580996180742912915 4466214871494271114369373)
              ·
                refine ⟨1674830576810351667888515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4466214871494271114369373 1674830576810351667888515)
                ·
                  refine ⟨2512245865215527501832773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1674830576810351667888515 2512245865215527501832773)
                  ·
                    refine ⟨471046099727911406593645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2512245865215527501832773 471046099727911406593645)
                    ·
                      rfl

theorem cell23_2752077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_2752077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2752077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2752077 prefixEnd_2752077 := by exact prefixLift 2752077
  have htrace : WordTrace (prefixWord ++ tailWord_2752077) baseStart_2752077 baseEnd_2752077 := by
    simpa [prefixWord, tailWord_2752077, baseEnd_2752077] using wordTrace_append hprefix tailTrace_2752077
  have hstable : (prefixWord ++ tailWord_2752077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752077).length < 2 ^ (prefixWord ++ tailWord_2752077).sum := by decide
  have hdescent : baseEnd_2752077 < baseStart_2752077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752099 : List Nat := [1, 1, 1, 5, 1, 3, 2, 1, 4, 4]
def baseStart_2752099 : Nat := 118140960795 + 2752099 * 2 ^ 59
def prefixEnd_2752099 : Nat := 4983230072969 + 3 ^ 40 * 2752099 * 2
def baseEnd_2752099 : Nat := 471049865252711044568611

theorem tailTrace_2752099 : CollatzResearch.WordTrace tailWord_2752099 prefixEnd_2752099 471049865252711044568611 := by
  unfold tailWord_2752099
  simp only [CollatzResearch.WordTrace]
  refine ⟨100377296856622818934019351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66918197904415212622679567 100377296856622818934019351)
  ·
    refine ⟨150565945284934228401029027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100377296856622818934019351 150565945284934228401029027)
    ·
      refine ⟨225848917927401342601543541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150565945284934228401029027 225848917927401342601543541)
      ·
        refine ⟨21173336055693875868894707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 225848917927401342601543541 21173336055693875868894707)
        ·
          refine ⟨31760004083540813803342061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21173336055693875868894707 31760004083540813803342061)
          ·
            refine ⟨11910001531327805176253273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31760004083540813803342061 11910001531327805176253273)
            ·
              refine ⟨8932501148495853882189955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11910001531327805176253273 8932501148495853882189955)
              ·
                refine ⟨13398751722743780823284933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8932501148495853882189955 13398751722743780823284933)
                ·
                  refine ⟨2512265948014458904365925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13398751722743780823284933 2512265948014458904365925)
                  ·
                    refine ⟨471049865252711044568611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2512265948014458904365925 471049865252711044568611)
                    ·
                      rfl

theorem cell23_2752099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 4, 4].length) (baseStart_2752099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2752099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2752099 prefixEnd_2752099 := by exact prefixLift 2752099
  have htrace : WordTrace (prefixWord ++ tailWord_2752099) baseStart_2752099 baseEnd_2752099 := by
    simpa [prefixWord, tailWord_2752099, baseEnd_2752099] using wordTrace_append hprefix tailTrace_2752099
  have hstable : (prefixWord ++ tailWord_2752099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752099).length < 2 ^ (prefixWord ++ tailWord_2752099).sum := by decide
  have hdescent : baseEnd_2752099 < baseStart_2752099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752100 : List Nat := [2, 3, 1, 1, 2, 4, 3, 2, 1, 1, 3]
def baseStart_2752100 : Nat := 118140960795 + 2752100 * 2 ^ 59
def prefixEnd_2752100 : Nat := 4983230072969 + 3 ^ 40 * 2752100 * 2
def baseEnd_2752100 : Nat := 1413150109238787629793329

theorem tailTrace_2752100 : CollatzResearch.WordTrace tailWord_2752100 prefixEnd_2752100 1413150109238787629793329 := by
  unfold tailWord_2752100
  simp only [CollatzResearch.WordTrace]
  refine ⟨50188666664809598052402877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66918222219746130736537169 50188666664809598052402877)
  ·
    refine ⟨18820749999303599269651079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50188666664809598052402877 18820749999303599269651079)
    ·
      refine ⟨28231124998955398904476619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18820749999303599269651079 28231124998955398904476619)
      ·
        refine ⟨42346687498433098356714929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28231124998955398904476619 42346687498433098356714929)
        ·
          refine ⟨31760015623824823767536197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42346687498433098356714929 31760015623824823767536197)
          ·
            refine ⟨5955002929467154456413037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31760015623824823767536197 5955002929467154456413037)
            ·
              refine ⟨2233126098550182921154889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5955002929467154456413037 2233126098550182921154889)
              ·
                refine ⟨1674844573912637190866167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2233126098550182921154889 1674844573912637190866167)
                ·
                  refine ⟨2512266860868955786299251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1674844573912637190866167 2512266860868955786299251)
                  ·
                    refine ⟨3768400291303433679448877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2512266860868955786299251 3768400291303433679448877)
                    ·
                      refine ⟨1413150109238787629793329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3768400291303433679448877 1413150109238787629793329)
                      ·
                        rfl

theorem cell23_2752100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 2, 1, 1, 3].length) (baseStart_2752100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2752100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2752100 prefixEnd_2752100 := by exact prefixLift 2752100
  have htrace : WordTrace (prefixWord ++ tailWord_2752100) baseStart_2752100 baseEnd_2752100 := by
    simpa [prefixWord, tailWord_2752100, baseEnd_2752100] using wordTrace_append hprefix tailTrace_2752100
  have hstable : (prefixWord ++ tailWord_2752100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752100).length < 2 ^ (prefixWord ++ tailWord_2752100).sum := by decide
  have hdescent : baseEnd_2752100 < baseStart_2752100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752112 : List Nat := [2, 1, 1, 1, 6, 1, 1, 10]
def baseStart_2752112 : Nat := 118140960795 + 2752112 * 2 ^ 59
def prefixEnd_2752112 : Nat := 4983230072969 + 3 ^ 40 * 2752112 * 2
def baseEnd_2752112 : Nat := 52339121148394132697899

theorem tailTrace_2752112 : CollatzResearch.WordTrace tailWord_2752112 prefixEnd_2752112 52339121148394132697899 := by
  unfold tailWord_2752112
  simp only [CollatzResearch.WordTrace]
  refine ⟨50188885502787861077121295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66918514003717148102828393 50188885502787861077121295)
  ·
    refine ⟨75283328254181791615681943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50188885502787861077121295 75283328254181791615681943)
    ·
      refine ⟨112924992381272687423522915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75283328254181791615681943 112924992381272687423522915)
      ·
        refine ⟨169387488571909031135284373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112924992381272687423522915 169387488571909031135284373)
        ·
          refine ⟨7940038526808235834466455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 169387488571909031135284373 7940038526808235834466455)
          ·
            refine ⟨11910057790212353751699683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7940038526808235834466455 11910057790212353751699683)
            ·
              refine ⟨17865086685318530627549525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11910057790212353751699683 17865086685318530627549525)
              ·
                refine ⟨52339121148394132697899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 17865086685318530627549525 52339121148394132697899)
                ·
                  rfl

theorem cell23_2752112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 10].length) (baseStart_2752112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2752112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2752112 prefixEnd_2752112 := by exact prefixLift 2752112
  have htrace : WordTrace (prefixWord ++ tailWord_2752112) baseStart_2752112 baseEnd_2752112 := by
    simpa [prefixWord, tailWord_2752112, baseEnd_2752112] using wordTrace_append hprefix tailTrace_2752112
  have hstable : (prefixWord ++ tailWord_2752112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752112).length < 2 ^ (prefixWord ++ tailWord_2752112).sum := by decide
  have hdescent : baseEnd_2752112 < baseStart_2752112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752139 : List Nat := [1, 1, 1, 1, 4, 1, 5, 2, 1, 3, 3]
def baseStart_2752139 : Nat := 118140960795 + 2752139 * 2 ^ 59
def prefixEnd_2752139 : Nat := 4983230072969 + 3 ^ 40 * 2752139 * 2
def baseEnd_2752139 : Nat := 1413170134984312977205649

theorem tailTrace_2752139 : CollatzResearch.WordTrace tailWord_2752139 prefixEnd_2752139 1413170134984312977205649 := by
  unfold tailWord_2752139
  simp only [CollatzResearch.WordTrace]
  refine ⟨100378755776477905765475471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66919170517651937176983647 100378755776477905765475471)
  ·
    refine ⟨150568133664716858648213207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100378755776477905765475471 150568133664716858648213207)
    ·
      refine ⟨225852200497075287972319811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150568133664716858648213207 225852200497075287972319811)
      ·
        refine ⟨338778300745612931958479717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225852200497075287972319811 338778300745612931958479717)
        ·
          refine ⟨63520931389802424742214947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 338778300745612931958479717 63520931389802424742214947)
          ·
            refine ⟨95281397084703637113322421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63520931389802424742214947 95281397084703637113322421)
            ·
              refine ⟨8932630976690965979373977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 95281397084703637113322421 8932630976690965979373977)
              ·
                refine ⟨6699473232518224484530483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8932630976690965979373977 6699473232518224484530483)
                ·
                  refine ⟨10049209848777336726795725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6699473232518224484530483 10049209848777336726795725)
                  ·
                    refine ⟨3768453693291501272548397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10049209848777336726795725 3768453693291501272548397)
                    ·
                      refine ⟨1413170134984312977205649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3768453693291501272548397 1413170134984312977205649)
                      ·
                        rfl

theorem cell23_2752139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 3, 3].length) (baseStart_2752139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2752139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2752139 prefixEnd_2752139 := by exact prefixLift 2752139
  have htrace : WordTrace (prefixWord ++ tailWord_2752139) baseStart_2752139 baseEnd_2752139 := by
    simpa [prefixWord, tailWord_2752139, baseEnd_2752139] using wordTrace_append hprefix tailTrace_2752139
  have hstable : (prefixWord ++ tailWord_2752139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752139).length < 2 ^ (prefixWord ++ tailWord_2752139).sum := by decide
  have hdescent : baseEnd_2752139 < baseStart_2752139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752173 : List Nat := [1, 5, 2, 1, 1, 1, 1, 5, 2, 1, 3]
def baseStart_2752173 : Nat := 118140960795 + 2752173 * 2 ^ 59
def prefixEnd_2752173 : Nat := 4983230072969 + 3 ^ 40 * 2752173 * 2
def baseEnd_2752173 : Nat := 1413187593326565844180493

theorem tailTrace_2752173 : CollatzResearch.WordTrace tailWord_2752173 prefixEnd_2752173 1413187593326565844180493 := by
  unfold tailWord_2752173
  simp only [CollatzResearch.WordTrace]
  refine ⟨100379995858354729572213173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66919997238903153048142115 100379995858354729572213173)
  ·
    refine ⟨9410624611720755897394985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 100379995858354729572213173 9410624611720755897394985)
    ·
      refine ⟨7057968458790566923046239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9410624611720755897394985 7057968458790566923046239)
      ·
        refine ⟨10586952688185850384569359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7057968458790566923046239 10586952688185850384569359)
        ·
          refine ⟨15880429032278775576854039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10586952688185850384569359 15880429032278775576854039)
          ·
            refine ⟨23820643548418163365281059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15880429032278775576854039 23820643548418163365281059)
            ·
              refine ⟨35730965322627245047921589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23820643548418163365281059 35730965322627245047921589)
              ·
                refine ⟨3349777998996304223242649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35730965322627245047921589 3349777998996304223242649)
                ·
                  refine ⟨2512333499247228167431987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3349777998996304223242649 2512333499247228167431987)
                  ·
                    refine ⟨3768500248870842251147981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2512333499247228167431987 3768500248870842251147981)
                    ·
                      refine ⟨1413187593326565844180493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3768500248870842251147981 1413187593326565844180493)
                      ·
                        rfl

theorem cell23_2752173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_2752173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2752173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2752173 prefixEnd_2752173 := by exact prefixLift 2752173
  have htrace : WordTrace (prefixWord ++ tailWord_2752173) baseStart_2752173 baseEnd_2752173 := by
    simpa [prefixWord, tailWord_2752173, baseEnd_2752173] using wordTrace_append hprefix tailTrace_2752173
  have hstable : (prefixWord ++ tailWord_2752173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752173).length < 2 ^ (prefixWord ++ tailWord_2752173).sum := by decide
  have hdescent : baseEnd_2752173 < baseStart_2752173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752209 : List Nat := [1, 2, 2, 1, 2, 4, 1, 2, 2, 2, 4]
def baseStart_2752209 : Nat := 118140960795 + 2752209 * 2 ^ 59
def prefixEnd_2752209 : Nat := 4983230072969 + 3 ^ 40 * 2752209 * 2
def baseEnd_2752209 : Nat := 1413206078630127703330327

theorem tailTrace_2752209 : CollatzResearch.WordTrace tailWord_2752209 prefixEnd_2752209 1413206078630127703330327 := by
  unfold tailWord_2752209
  simp only [CollatzResearch.WordTrace]
  refine ⟨100381308886224307720523681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66920872590816205147015787 100381308886224307720523681)
  ·
    refine ⟨75285981664668230790392761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100381308886224307720523681 75285981664668230790392761)
    ·
      refine ⟨56464486248501173092794571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75285981664668230790392761 56464486248501173092794571)
      ·
        refine ⟨84696729372751759639191857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56464486248501173092794571 84696729372751759639191857)
        ·
          refine ⟨63522547029563819729393893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84696729372751759639191857 63522547029563819729393893)
          ·
            refine ⟨11910477568043216199261355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63522547029563819729393893 11910477568043216199261355)
            ·
              refine ⟨17865716352064824298892033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11910477568043216199261355 17865716352064824298892033)
              ·
                refine ⟨13399287264048618224169025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17865716352064824298892033 13399287264048618224169025)
                ·
                  refine ⟨10049465448036463668126769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13399287264048618224169025 10049465448036463668126769)
                  ·
                    refine ⟨7537099086027347751095077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10049465448036463668126769 7537099086027347751095077)
                    ·
                      refine ⟨1413206078630127703330327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7537099086027347751095077 1413206078630127703330327)
                      ·
                        rfl

theorem cell23_2752209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 2, 4].length) (baseStart_2752209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2752209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2752209 prefixEnd_2752209 := by exact prefixLift 2752209
  have htrace : WordTrace (prefixWord ++ tailWord_2752209) baseStart_2752209 baseEnd_2752209 := by
    simpa [prefixWord, tailWord_2752209, baseEnd_2752209] using wordTrace_append hprefix tailTrace_2752209
  have hstable : (prefixWord ++ tailWord_2752209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752209).length < 2 ^ (prefixWord ++ tailWord_2752209).sum := by decide
  have hdescent : baseEnd_2752209 < baseStart_2752209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752266 : List Nat := [3, 1, 2, 2, 1, 4, 1, 2, 2, 5]
def baseStart_2752266 : Nat := 118140960795 + 2752266 * 2 ^ 59
def prefixEnd_2752266 : Nat := 4983230072969 + 3 ^ 40 * 2752266 * 2
def baseEnd_2752266 : Nat := 471078449009144660105855

theorem tailTrace_2752266 : CollatzResearch.WordTrace tailWord_2752266 prefixEnd_2752266 471078449009144660105855 := by
  unfold tailWord_2752266
  simp only [CollatzResearch.WordTrace]
  refine ⟨25095846961754451613837163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66922258564678537636899101 25095846961754451613837163)
  ·
    refine ⟨37643770442631677420755745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25095846961754451613837163 37643770442631677420755745)
    ·
      refine ⟨28232827831973758065566809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37643770442631677420755745 28232827831973758065566809)
      ·
        refine ⟨21174620873980318549175107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28232827831973758065566809 21174620873980318549175107)
        ·
          refine ⟨31761931310970477823762661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21174620873980318549175107 31761931310970477823762661)
          ·
            refine ⟨5955362120806964591955499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31761931310970477823762661 5955362120806964591955499)
            ·
              refine ⟨8933043181210446887933249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5955362120806964591955499 8933043181210446887933249)
              ·
                refine ⟨6699782385907835165949937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8933043181210446887933249 6699782385907835165949937)
                ·
                  refine ⟨5024836789430876374462453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6699782385907835165949937 5024836789430876374462453)
                  ·
                    refine ⟨471078449009144660105855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5024836789430876374462453 471078449009144660105855)
                    ·
                      rfl

theorem cell23_2752266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 2, 5].length) (baseStart_2752266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2752266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2752266 prefixEnd_2752266 := by exact prefixLift 2752266
  have htrace : WordTrace (prefixWord ++ tailWord_2752266) baseStart_2752266 baseEnd_2752266 := by
    simpa [prefixWord, tailWord_2752266, baseEnd_2752266] using wordTrace_append hprefix tailTrace_2752266
  have hstable : (prefixWord ++ tailWord_2752266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752266).length < 2 ^ (prefixWord ++ tailWord_2752266).sum := by decide
  have hdescent : baseEnd_2752266 < baseStart_2752266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752329 : List Nat := [1, 2, 1, 1, 2, 4, 2, 1, 1, 2, 6]
def baseStart_2752329 : Nat := 118140960795 + 2752329 * 2 ^ 59
def prefixEnd_2752329 : Nat := 4983230072969 + 3 ^ 40 * 2752329 * 2
def baseEnd_2752329 : Nat := 1413267696308667233829775

theorem tailTrace_2752329 : CollatzResearch.WordTrace tailWord_2752329 prefixEnd_2752329 1413267696308667233829775 := by
  unfold tailWord_2752329
  simp only [CollatzResearch.WordTrace]
  refine ⟨100385685645789568214892041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66923790430526378809928027 100385685645789568214892041)
  ·
    refine ⟨75289264234342176161169031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100385685645789568214892041 75289264234342176161169031)
    ·
      refine ⟨112933896351513264241753547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75289264234342176161169031 112933896351513264241753547)
      ·
        refine ⟨169400844527269896362630321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112933896351513264241753547 169400844527269896362630321)
        ·
          refine ⟨127050633395452422271972741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169400844527269896362630321 127050633395452422271972741)
          ·
            refine ⟨23821993761647329175994889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 127050633395452422271972741 23821993761647329175994889)
            ·
              refine ⟨17866495321235496881996167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23821993761647329175994889 17866495321235496881996167)
              ·
                refine ⟨26799742981853245322994251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17866495321235496881996167 26799742981853245322994251)
                ·
                  refine ⟨40199614472779867984491377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26799742981853245322994251 40199614472779867984491377)
                  ·
                    refine ⟨30149710854584900988368533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40199614472779867984491377 30149710854584900988368533)
                    ·
                      refine ⟨1413267696308667233829775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30149710854584900988368533 1413267696308667233829775)
                      ·
                        rfl

theorem cell23_2752329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 2, 6].length) (baseStart_2752329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2752329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2752329 prefixEnd_2752329 := by exact prefixLift 2752329
  have htrace : WordTrace (prefixWord ++ tailWord_2752329) baseStart_2752329 baseEnd_2752329 := by
    simpa [prefixWord, tailWord_2752329, baseEnd_2752329] using wordTrace_append hprefix tailTrace_2752329
  have hstable : (prefixWord ++ tailWord_2752329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752329).length < 2 ^ (prefixWord ++ tailWord_2752329).sum := by decide
  have hdescent : baseEnd_2752329 < baseStart_2752329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752353 : List Nat := [1, 2, 3, 1, 1, 1, 5, 2, 3, 1, 3]
def baseStart_2752353 : Nat := 118140960795 + 2752353 * 2 ^ 59
def prefixEnd_2752353 : Nat := 4983230072969 + 3 ^ 40 * 2752353 * 2
def baseEnd_2752353 : Nat := 1413280019844375139929665

theorem tailTrace_2752353 : CollatzResearch.WordTrace tailWord_2752353 prefixEnd_2752353 1413280019844375139929665 := by
  unfold tailWord_2752353
  simp only [CollatzResearch.WordTrace]
  refine ⟨100386560997702620313765713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66924373998468413542510475 100386560997702620313765713)
  ·
    refine ⟨75289920748276965235324285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100386560997702620313765713 75289920748276965235324285)
    ·
      refine ⟨28233720280603861963246607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75289920748276965235324285 28233720280603861963246607)
      ·
        refine ⟨42350580420905792944869911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28233720280603861963246607 42350580420905792944869911)
        ·
          refine ⟨63525870631358689417304867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42350580420905792944869911 63525870631358689417304867)
          ·
            refine ⟨95288805947038034125957301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63525870631358689417304867 95288805947038034125957301)
            ·
              refine ⟨8933325557534815699308497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 95288805947038034125957301 8933325557534815699308497)
              ·
                refine ⟨6699994168151111774481373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8933325557534815699308497 6699994168151111774481373)
                ·
                  refine ⟨2512497813056666915430515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6699994168151111774481373 2512497813056666915430515)
                  ·
                    refine ⟨3768746719585000373145773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2512497813056666915430515 3768746719585000373145773)
                    ·
                      refine ⟨1413280019844375139929665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3768746719585000373145773 1413280019844375139929665)
                      ·
                        rfl

theorem cell23_2752353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 3, 1, 3].length) (baseStart_2752353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2752353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2752353 prefixEnd_2752353 := by exact prefixLift 2752353
  have htrace : WordTrace (prefixWord ++ tailWord_2752353) baseStart_2752353 baseEnd_2752353 := by
    simpa [prefixWord, tailWord_2752353, baseEnd_2752353] using wordTrace_append hprefix tailTrace_2752353
  have hstable : (prefixWord ++ tailWord_2752353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752353).length < 2 ^ (prefixWord ++ tailWord_2752353).sum := by decide
  have hdescent : baseEnd_2752353 < baseStart_2752353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752373 : List Nat := [1, 3, 4, 1, 1, 1, 3, 3, 1, 5]
def baseStart_2752373 : Nat := 118140960795 + 2752373 * 2 ^ 59
def prefixEnd_2752373 : Nat := 4983230072969 + 3 ^ 40 * 2752373 * 2
def baseEnd_2752373 : Nat := 471096763152488353893191

theorem tailTrace_2752373 : CollatzResearch.WordTrace tailWord_2752373 prefixEnd_2752373 471096763152488353893191 := by
  unfold tailWord_2752373
  simp only [CollatzResearch.WordTrace]
  refine ⟨100387290457630163729493773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66924860305086775819662515 100387290457630163729493773)
  ·
    refine ⟨37645233921611311398560165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100387290457630163729493773 37645233921611311398560165)
    ·
      refine ⟨7058481360302120887230031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37645233921611311398560165 7058481360302120887230031)
      ·
        refine ⟨10587722040453181330845047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7058481360302120887230031 10587722040453181330845047)
        ·
          refine ⟨15881583060679771996267571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10587722040453181330845047 15881583060679771996267571)
          ·
            refine ⟨23822374591019657994401357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15881583060679771996267571 23822374591019657994401357)
            ·
              refine ⟨8933390471632371747900509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23822374591019657994401357 8933390471632371747900509)
              ·
                refine ⟨3350021426862139405462691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8933390471632371747900509 3350021426862139405462691)
                ·
                  refine ⟨5025032140293209108194037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3350021426862139405462691 5025032140293209108194037)
                  ·
                    refine ⟨471096763152488353893191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5025032140293209108194037 471096763152488353893191)
                    ·
                      rfl

theorem cell23_2752373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_2752373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2752373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2752373 prefixEnd_2752373 := by exact prefixLift 2752373
  have htrace : WordTrace (prefixWord ++ tailWord_2752373) baseStart_2752373 baseEnd_2752373 := by
    simpa [prefixWord, tailWord_2752373, baseEnd_2752373] using wordTrace_append hprefix tailTrace_2752373
  have hstable : (prefixWord ++ tailWord_2752373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752373).length < 2 ^ (prefixWord ++ tailWord_2752373).sum := by decide
  have hdescent : baseEnd_2752373 < baseStart_2752373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752410 : List Nat := [3, 1, 1, 4, 2, 2, 2, 2, 1, 1, 4]
def baseStart_2752410 : Nat := 118140960795 + 2752410 * 2 ^ 59
def prefixEnd_2752410 : Nat := 4983230072969 + 3 ^ 40 * 2752410 * 2
def baseEnd_2752410 : Nat := 1413309288241681416916903

theorem tailTrace_2752410 : CollatzResearch.WordTrace tailWord_2752410 prefixEnd_2752410 1413309288241681416916903 := by
  unfold tailWord_2752410
  simp only [CollatzResearch.WordTrace]
  refine ⟨25097159989624029762147671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66925759972330746032393789 25097159989624029762147671)
  ·
    refine ⟨37645739984436044643221507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25097159989624029762147671 37645739984436044643221507)
    ·
      refine ⟨56468609976654066964832261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37645739984436044643221507 56468609976654066964832261)
      ·
        refine ⟨10587864370622637555906049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56468609976654066964832261 10587864370622637555906049)
        ·
          refine ⟨7940898277966978166929537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10587864370622637555906049 7940898277966978166929537)
          ·
            refine ⟨5955673708475233625197153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7940898277966978166929537 5955673708475233625197153)
            ·
              refine ⟨4466755281356425218897865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5955673708475233625197153 4466755281356425218897865)
              ·
                refine ⟨3350066461017318914173399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4466755281356425218897865 3350066461017318914173399)
                ·
                  refine ⟨5025099691525978371260099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3350066461017318914173399 5025099691525978371260099)
                  ·
                    refine ⟨7537649537288967556890149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5025099691525978371260099 7537649537288967556890149)
                    ·
                      refine ⟨1413309288241681416916903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7537649537288967556890149 1413309288241681416916903)
                      ·
                        rfl

theorem cell23_2752410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_2752410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2752410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2752410 prefixEnd_2752410 := by exact prefixLift 2752410
  have htrace : WordTrace (prefixWord ++ tailWord_2752410) baseStart_2752410 baseEnd_2752410 := by
    simpa [prefixWord, tailWord_2752410, baseEnd_2752410] using wordTrace_append hprefix tailTrace_2752410
  have hstable : (prefixWord ++ tailWord_2752410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752410).length < 2 ^ (prefixWord ++ tailWord_2752410).sum := by decide
  have hdescent : baseEnd_2752410 < baseStart_2752410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752510 : List Nat := [4, 2, 2, 2, 1, 2, 1, 1, 2, 6]
def baseStart_2752510 : Nat := 118140960795 + 2752510 * 2 ^ 59
def prefixEnd_2752510 : Nat := 4983230072969 + 3 ^ 40 * 2752510 * 2
def baseEnd_2752510 : Nat := 471120212102377008555481

theorem tailTrace_2752510 : CollatzResearch.WordTrace tailWord_2752510 prefixEnd_2752510 471120212102377008555481 := by
  unfold tailWord_2752510
  simp only [CollatzResearch.WordTrace]
  refine ⟨12549035907266729515903873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66928191505422557418153989 12549035907266729515903873)
  ·
    refine ⟨9411776930450047136927905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12549035907266729515903873 9411776930450047136927905)
    ·
      refine ⟨7058832697837535352695929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9411776930450047136927905 7058832697837535352695929)
      ·
        refine ⟨5294124523378151514521947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7058832697837535352695929 5294124523378151514521947)
        ·
          refine ⟨7941186785067227271782921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5294124523378151514521947 7941186785067227271782921)
          ·
            refine ⟨5955890088800420453837191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7941186785067227271782921 5955890088800420453837191)
            ·
              refine ⟨8933835133200630680755787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5955890088800420453837191 8933835133200630680755787)
              ·
                refine ⟨13400752699800946021133681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8933835133200630680755787 13400752699800946021133681)
                ·
                  refine ⟨10050564524850709515850261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13400752699800946021133681 10050564524850709515850261)
                  ·
                    refine ⟨471120212102377008555481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10050564524850709515850261 471120212102377008555481)
                    ·
                      rfl

theorem cell23_2752510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_2752510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2752510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2752510 prefixEnd_2752510 := by exact prefixLift 2752510
  have htrace : WordTrace (prefixWord ++ tailWord_2752510) baseStart_2752510 baseEnd_2752510 := by
    simpa [prefixWord, tailWord_2752510, baseEnd_2752510] using wordTrace_append hprefix tailTrace_2752510
  have hstable : (prefixWord ++ tailWord_2752510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752510).length < 2 ^ (prefixWord ++ tailWord_2752510).sum := by decide
  have hdescent : baseEnd_2752510 < baseStart_2752510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752513 : List Nat := [1, 2, 4, 1, 2, 1, 3, 1, 2, 2, 4]
def baseStart_2752513 : Nat := 118140960795 + 2752513 * 2 ^ 59
def prefixEnd_2752513 : Nat := 4983230072969 + 3 ^ 40 * 2752513 * 2
def baseEnd_2752513 : Nat := 1413362176749094513928929

theorem tailTrace_2752513 : CollatzResearch.WordTrace tailWord_2752513 prefixEnd_2752513 1413362176749094513928929 := by
  unfold tailWord_2752513
  simp only [CollatzResearch.WordTrace]
  refine ⟨100392396677122967639590193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66928264451415311759726795 100392396677122967639590193)
  ·
    refine ⟨75294297507842225729692645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100392396677122967639590193 75294297507842225729692645)
    ·
      refine ⟨14117680782720417324317371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75294297507842225729692645 14117680782720417324317371)
      ·
        refine ⟨21176521174080625986476057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14117680782720417324317371 21176521174080625986476057)
        ·
          refine ⟨15882390880560469489857043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21176521174080625986476057 15882390880560469489857043)
          ·
            refine ⟨23823586320840704234785565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15882390880560469489857043 23823586320840704234785565)
            ·
              refine ⟨8933844870315264088044587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23823586320840704234785565 8933844870315264088044587)
              ·
                refine ⟨13400767305472896132066881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8933844870315264088044587 13400767305472896132066881)
                ·
                  refine ⟨10050575479104672099050161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13400767305472896132066881 10050575479104672099050161)
                  ·
                    refine ⟨7537931609328504074287621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10050575479104672099050161 7537931609328504074287621)
                    ·
                      refine ⟨1413362176749094513928929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7537931609328504074287621 1413362176749094513928929)
                      ·
                        rfl

theorem cell23_2752513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_2752513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2752513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2752513 prefixEnd_2752513 := by exact prefixLift 2752513
  have htrace : WordTrace (prefixWord ++ tailWord_2752513) baseStart_2752513 baseEnd_2752513 := by
    simpa [prefixWord, tailWord_2752513, baseEnd_2752513] using wordTrace_append hprefix tailTrace_2752513
  have hstable : (prefixWord ++ tailWord_2752513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752513).length < 2 ^ (prefixWord ++ tailWord_2752513).sum := by decide
  have hdescent : baseEnd_2752513 < baseStart_2752513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752517 : List Nat := [1, 3, 1, 1, 2, 4, 2, 3, 2, 2, 2]
def baseStart_2752517 : Nat := 118140960795 + 2752517 * 2 ^ 59
def prefixEnd_2752517 : Nat := 4983230072969 + 3 ^ 40 * 2752517 * 2
def baseEnd_2752517 : Nat := 1413364230671712498278911

theorem tailTrace_2752517 : CollatzResearch.WordTrace tailWord_2752517 prefixEnd_2752517 1413364230671712498278911 := by
  unfold tailWord_2752517
  simp only [CollatzResearch.WordTrace]
  refine ⟨100392542569108476322735805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66928361712738984215157203 100392542569108476322735805)
  ·
    refine ⟨37647203463415678621025927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100392542569108476322735805 37647203463415678621025927)
    ·
      refine ⟨56470805195123517931538891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37647203463415678621025927 56470805195123517931538891)
      ·
        refine ⟨84706207792685276897308337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56470805195123517931538891 84706207792685276897308337)
        ·
          refine ⟨63529655844513957672981253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84706207792685276897308337 63529655844513957672981253)
          ·
            refine ⟨11911810470846367063683985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63529655844513957672981253 11911810470846367063683985)
            ·
              refine ⟨8933857853134775297762989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11911810470846367063683985 8933857853134775297762989)
              ·
                refine ⟨3350196694925540736661121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8933857853134775297762989 3350196694925540736661121)
                ·
                  refine ⟨2512647521194155552495841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3350196694925540736661121 2512647521194155552495841)
                  ·
                    refine ⟨1884485640895616664371881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2512647521194155552495841 1884485640895616664371881)
                    ·
                      refine ⟨1413364230671712498278911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1884485640895616664371881 1413364230671712498278911)
                      ·
                        rfl

theorem cell23_2752517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 3, 2, 2, 2].length) (baseStart_2752517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2752517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2752517 prefixEnd_2752517 := by exact prefixLift 2752517
  have htrace : WordTrace (prefixWord ++ tailWord_2752517) baseStart_2752517 baseEnd_2752517 := by
    simpa [prefixWord, tailWord_2752517, baseEnd_2752517] using wordTrace_append hprefix tailTrace_2752517
  have hstable : (prefixWord ++ tailWord_2752517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752517).length < 2 ^ (prefixWord ++ tailWord_2752517).sum := by decide
  have hdescent : baseEnd_2752517 < baseStart_2752517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752540 : List Nat := [2, 2, 3, 1, 3, 1, 1, 5, 5]
def baseStart_2752540 : Nat := 118140960795 + 2752540 * 2 ^ 59
def prefixEnd_2752540 : Nat := 4983230072969 + 3 ^ 40 * 2752540 * 2
def baseEnd_2752540 : Nat := 157041782302973989810145

theorem tailTrace_2752540 : CollatzResearch.WordTrace tailWord_2752540 prefixEnd_2752540 157041782302973989810145 := by
  unfold tailWord_2752540
  simp only [CollatzResearch.WordTrace]
  refine ⟨50196690724012575625411537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66928920965350100833882049 50196690724012575625411537)
  ·
    refine ⟨37647518043009431719058653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50196690724012575625411537 37647518043009431719058653)
    ·
      refine ⟨14117819266128536894646995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37647518043009431719058653 14117819266128536894646995)
      ·
        refine ⟨21176728899192805341970493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14117819266128536894646995 21176728899192805341970493)
        ·
          refine ⟨7941273337197302003238935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21176728899192805341970493 7941273337197302003238935)
          ·
            refine ⟨11911910005795953004858403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7941273337197302003238935 11911910005795953004858403)
            ·
              refine ⟨17867865008693929507287605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11911910005795953004858403 17867865008693929507287605)
              ·
                refine ⟨1675112344565055891308213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17867865008693929507287605 1675112344565055891308213)
                ·
                  refine ⟨157041782302973989810145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1675112344565055891308213 157041782302973989810145)
                  ·
                    rfl

theorem cell23_2752540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 5, 5].length) (baseStart_2752540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2752540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2752540 prefixEnd_2752540 := by exact prefixLift 2752540
  have htrace : WordTrace (prefixWord ++ tailWord_2752540) baseStart_2752540 baseEnd_2752540 := by
    simpa [prefixWord, tailWord_2752540, baseEnd_2752540] using wordTrace_append hprefix tailTrace_2752540
  have hstable : (prefixWord ++ tailWord_2752540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752540).length < 2 ^ (prefixWord ++ tailWord_2752540).sum := by decide
  have hdescent : baseEnd_2752540 < baseStart_2752540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752573 : List Nat := [1, 4, 1, 3, 1, 1, 1, 1, 3, 3, 4]
def baseStart_2752573 : Nat := 118140960795 + 2752573 * 2 ^ 59
def prefixEnd_2752573 : Nat := 4983230072969 + 3 ^ 40 * 2752573 * 2
def baseEnd_2752573 : Nat := 1413392985588364279178653

theorem tailTrace_2752573 : CollatzResearch.WordTrace tailWord_2752573 prefixEnd_2752573 1413392985588364279178653 := by
  unfold tailWord_2752573
  simp only [CollatzResearch.WordTrace]
  refine ⟨100394585056905597886774373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66929723371270398591182915 100394585056905597886774373)
  ·
    refine ⟨18823984698169799603770195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100394585056905597886774373 18823984698169799603770195)
    ·
      refine ⟨28235977047254699405655293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18823984698169799603770195 28235977047254699405655293)
      ·
        refine ⟨10588491392720512277120735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28235977047254699405655293 10588491392720512277120735)
        ·
          refine ⟨15882737089080768415681103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10588491392720512277120735 15882737089080768415681103)
          ·
            refine ⟨23824105633621152623521655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15882737089080768415681103 23824105633621152623521655)
            ·
              refine ⟨35736158450431728935282483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23824105633621152623521655 35736158450431728935282483)
              ·
                refine ⟨53604237675647593402923725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35736158450431728935282483 53604237675647593402923725)
                ·
                  refine ⟨20101589128367847526096397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53604237675647593402923725 20101589128367847526096397)
                  ·
                    refine ⟨7538095923137942822286149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20101589128367847526096397 7538095923137942822286149)
                    ·
                      refine ⟨1413392985588364279178653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7538095923137942822286149 1413392985588364279178653)
                      ·
                        rfl

theorem cell23_2752573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_2752573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2752573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2752573 prefixEnd_2752573 := by exact prefixLift 2752573
  have htrace : WordTrace (prefixWord ++ tailWord_2752573) baseStart_2752573 baseEnd_2752573 := by
    simpa [prefixWord, tailWord_2752573, baseEnd_2752573] using wordTrace_append hprefix tailTrace_2752573
  have hstable : (prefixWord ++ tailWord_2752573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752573).length < 2 ^ (prefixWord ++ tailWord_2752573).sum := by decide
  have hdescent : baseEnd_2752573 < baseStart_2752573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752613 : List Nat := [1, 3, 1, 3, 2, 2, 2, 1, 8]
def baseStart_2752613 : Nat := 118140960795 + 2752613 * 2 ^ 59
def prefixEnd_2752613 : Nat := 4983230072969 + 3 ^ 40 * 2752613 * 2
def baseEnd_2752613 : Nat := 157045947201616013630941

theorem tailTrace_2752613 : CollatzResearch.WordTrace tailWord_2752613 prefixEnd_2752613 157045947201616013630941 := by
  unfold tailWord_2752613
  simp only [CollatzResearch.WordTrace]
  refine ⟨100396043976760684718230493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66930695984507123145486995 100396043976760684718230493)
  ·
    refine ⟨37648516491285256769336435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100396043976760684718230493 37648516491285256769336435)
    ·
      refine ⟨56472774736927885154004653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37648516491285256769336435 56472774736927885154004653)
      ·
        refine ⟨21177290526347956932751745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56472774736927885154004653 21177290526347956932751745)
        ·
          refine ⟨15882967894760967699563809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21177290526347956932751745 15882967894760967699563809)
          ·
            refine ⟨11912225921070725774672857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15882967894760967699563809 11912225921070725774672857)
            ·
              refine ⟨8934169440803044331004643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11912225921070725774672857 8934169440803044331004643)
              ·
                refine ⟨13401254161204566496506965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8934169440803044331004643 13401254161204566496506965)
                ·
                  refine ⟨157045947201616013630941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13401254161204566496506965 157045947201616013630941)
                  ·
                    rfl

theorem cell23_2752613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 8].length) (baseStart_2752613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2752613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2752613 prefixEnd_2752613 := by exact prefixLift 2752613
  have htrace : WordTrace (prefixWord ++ tailWord_2752613) baseStart_2752613 baseEnd_2752613 := by
    simpa [prefixWord, tailWord_2752613, baseEnd_2752613] using wordTrace_append hprefix tailTrace_2752613
  have hstable : (prefixWord ++ tailWord_2752613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752613).length < 2 ^ (prefixWord ++ tailWord_2752613).sum := by decide
  have hdescent : baseEnd_2752613 < baseStart_2752613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752640 : List Nat := [2, 1, 1, 2, 1, 3, 1, 3, 5, 1, 3]
def baseStart_2752640 : Nat := 118140960795 + 2752640 * 2 ^ 59
def prefixEnd_2752640 : Nat := 4983230072969 + 3 ^ 40 * 2752640 * 2
def baseEnd_2752640 : Nat := 1413427388792215517040845

theorem tailTrace_2752640 : CollatzResearch.WordTrace tailWord_2752640 prefixEnd_2752640 1413427388792215517040845 := by
  unfold tailWord_2752640
  simp only [CollatzResearch.WordTrace]
  refine ⟨50198514373831434164731687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66931352498441912219642249 50198514373831434164731687)
  ·
    refine ⟨75297771560747151247097531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50198514373831434164731687 75297771560747151247097531)
    ·
      refine ⟨112946657341120726870646297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75297771560747151247097531 112946657341120726870646297)
      ·
        refine ⟨84709993005840545152984723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112946657341120726870646297 84709993005840545152984723)
        ·
          refine ⟨127064989508760817729477085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84709993005840545152984723 127064989508760817729477085)
          ·
            refine ⟨47649371065785306648553907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127064989508760817729477085 47649371065785306648553907)
            ·
              refine ⟨71474056598677959972830861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47649371065785306648553907 71474056598677959972830861)
              ·
                refine ⟨26802771224504234989811573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71474056598677959972830861 26802771224504234989811573)
                ·
                  refine ⟨2512759802297272030294835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26802771224504234989811573 2512759802297272030294835)
                  ·
                    refine ⟨3769139703445908045442253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2512759802297272030294835 3769139703445908045442253)
                    ·
                      refine ⟨1413427388792215517040845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3769139703445908045442253 1413427388792215517040845)
                      ·
                        rfl

theorem cell23_2752640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 5, 1, 3].length) (baseStart_2752640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2752640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2752640 prefixEnd_2752640 := by exact prefixLift 2752640
  have htrace : WordTrace (prefixWord ++ tailWord_2752640) baseStart_2752640 baseEnd_2752640 := by
    simpa [prefixWord, tailWord_2752640, baseEnd_2752640] using wordTrace_append hprefix tailTrace_2752640
  have hstable : (prefixWord ++ tailWord_2752640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752640).length < 2 ^ (prefixWord ++ tailWord_2752640).sum := by decide
  have hdescent : baseEnd_2752640 < baseStart_2752640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752690 : List Nat := [3, 2, 1, 1, 1, 3, 4, 1, 1, 6]
def baseStart_2752690 : Nat := 118140960795 + 2752690 * 2 ^ 59
def prefixEnd_2752690 : Nat := 4983230072969 + 3 ^ 40 * 2752690 * 2
def baseEnd_2752690 : Nat := 471151020941646773805205

theorem tailTrace_2752690 : CollatzResearch.WordTrace tailWord_2752690 prefixEnd_2752690 471151020941646773805205 := by
  unfold tailWord_2752690
  simp only [CollatzResearch.WordTrace]
  refine ⟨25099713099370431717195881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66932568264987817912522349 25099713099370431717195881)
  ·
    refine ⟨18824784824527823787896911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25099713099370431717195881 18824784824527823787896911)
    ·
      refine ⟨28237177236791735681845367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18824784824527823787896911 28237177236791735681845367)
      ·
        refine ⟨42355765855187603522768051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28237177236791735681845367 42355765855187603522768051)
        ·
          refine ⟨63533648782781405284152077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42355765855187603522768051 63533648782781405284152077)
          ·
            refine ⟨23825118293543026981557029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63533648782781405284152077 23825118293543026981557029)
            ·
              refine ⟨4467209680039317559041943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23825118293543026981557029 4467209680039317559041943)
              ·
                refine ⟨6700814520058976338562915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4467209680039317559041943 6700814520058976338562915)
                ·
                  refine ⟨10051221780088464507844373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6700814520058976338562915 10051221780088464507844373)
                  ·
                    refine ⟨471151020941646773805205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10051221780088464507844373 471151020941646773805205)
                    ·
                      rfl

theorem cell23_2752690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 1, 6].length) (baseStart_2752690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2752690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2752690 prefixEnd_2752690 := by exact prefixLift 2752690
  have htrace : WordTrace (prefixWord ++ tailWord_2752690) baseStart_2752690 baseEnd_2752690 := by
    simpa [prefixWord, tailWord_2752690, baseEnd_2752690] using wordTrace_append hprefix tailTrace_2752690
  have hstable : (prefixWord ++ tailWord_2752690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752690).length < 2 ^ (prefixWord ++ tailWord_2752690).sum := by decide
  have hdescent : baseEnd_2752690 < baseStart_2752690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752730 : List Nat := [3, 1, 1, 2, 2, 1, 2, 2, 3, 3, 3]
def baseStart_2752730 : Nat := 118140960795 + 2752730 * 2 ^ 59
def prefixEnd_2752730 : Nat := 4983230072969 + 3 ^ 40 * 2752730 * 2
def baseEnd_2752730 : Nat := 1413473602051120164915431

theorem tailTrace_2752730 : CollatzResearch.WordTrace tailWord_2752730 prefixEnd_2752730 1413473602051120164915431 := by
  unfold tailWord_2752730
  simp only [CollatzResearch.WordTrace]
  refine ⟨25100077829334203425059911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66933540878224542466826429 25100077829334203425059911)
  ·
    refine ⟨37650116744001305137589867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25100077829334203425059911 37650116744001305137589867)
    ·
      refine ⟨56475175116001957706384801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37650116744001305137589867 56475175116001957706384801)
      ·
        refine ⟨42356381337001468279788601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56475175116001957706384801 42356381337001468279788601)
        ·
          refine ⟨31767286002751101209841451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42356381337001468279788601 31767286002751101209841451)
          ·
            refine ⟨47650929004126651814762177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31767286002751101209841451 47650929004126651814762177)
            ·
              refine ⟨35738196753094988861071633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47650929004126651814762177 35738196753094988861071633)
              ·
                refine ⟨26803647564821241645803725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35738196753094988861071633 26803647564821241645803725)
                ·
                  refine ⟨10051367836807965617176397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26803647564821241645803725 10051367836807965617176397)
                  ·
                    refine ⟨3769262938802987106441149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10051367836807965617176397 3769262938802987106441149)
                    ·
                      refine ⟨1413473602051120164915431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3769262938802987106441149 1413473602051120164915431)
                      ·
                        rfl

theorem cell23_2752730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 3, 3, 3].length) (baseStart_2752730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2752730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2752730 prefixEnd_2752730 := by exact prefixLift 2752730
  have htrace : WordTrace (prefixWord ++ tailWord_2752730) baseStart_2752730 baseEnd_2752730 := by
    simpa [prefixWord, tailWord_2752730, baseEnd_2752730] using wordTrace_append hprefix tailTrace_2752730
  have hstable : (prefixWord ++ tailWord_2752730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752730).length < 2 ^ (prefixWord ++ tailWord_2752730).sum := by decide
  have hdescent : baseEnd_2752730 < baseStart_2752730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752798 : List Nat := [4, 3, 2, 1, 1, 2, 1, 3, 2, 1, 3]
def baseStart_2752798 : Nat := 118140960795 + 2752798 * 2 ^ 59
def prefixEnd_2752798 : Nat := 4983230072969 + 3 ^ 40 * 2752798 * 2
def baseEnd_2752798 : Nat := 1413508518735625898865119

theorem tailTrace_2752798 : CollatzResearch.WordTrace tailWord_2752798 prefixEnd_2752798 1413508518735625898865119 := by
  unfold tailWord_2752798
  simp only [CollatzResearch.WordTrace]
  refine ⟨12550348935136307664214381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66935194320726974209143365 12550348935136307664214381)
  ·
    refine ⟨4706380850676115374080393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12550348935136307664214381 4706380850676115374080393)
    ·
      refine ⟨3529785638007086530560295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4706380850676115374080393 3529785638007086530560295)
      ·
        refine ⟨5294678457010629795840443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3529785638007086530560295 5294678457010629795840443)
        ·
          refine ⟨7942017685515944693760665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5294678457010629795840443 7942017685515944693760665)
          ·
            refine ⟨5956513264136958520320499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7942017685515944693760665 5956513264136958520320499)
            ·
              refine ⟨8934769896205437780480749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5956513264136958520320499 8934769896205437780480749)
              ·
                refine ⟨3350538711077039167680281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8934769896205437780480749 3350538711077039167680281)
                ·
                  refine ⟨2512904033307779375760211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3350538711077039167680281 2512904033307779375760211)
                  ·
                    refine ⟨3769356049961669063640317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2512904033307779375760211 3769356049961669063640317)
                    ·
                      refine ⟨1413508518735625898865119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3769356049961669063640317 1413508518735625898865119)
                      ·
                        rfl

theorem cell23_2752798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_2752798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2752798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2752798 prefixEnd_2752798 := by exact prefixLift 2752798
  have htrace : WordTrace (prefixWord ++ tailWord_2752798) baseStart_2752798 baseEnd_2752798 := by
    simpa [prefixWord, tailWord_2752798, baseEnd_2752798] using wordTrace_append hprefix tailTrace_2752798
  have hstable : (prefixWord ++ tailWord_2752798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752798).length < 2 ^ (prefixWord ++ tailWord_2752798).sum := by decide
  have hdescent : baseEnd_2752798 < baseStart_2752798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752808 : List Nat := [2, 1, 5, 1, 3, 2, 1, 2, 1, 3, 2]
def baseStart_2752808 : Nat := 118140960795 + 2752808 * 2 ^ 59
def prefixEnd_2752808 : Nat := 4983230072969 + 3 ^ 40 * 2752808 * 2
def baseEnd_2752808 : Nat := 1413513653542170859740073

theorem tailTrace_2752808 : CollatzResearch.WordTrace tailWord_2752808 prefixEnd_2752808 1413513653542170859740073 := by
  unfold tailWord_2752808
  simp only [CollatzResearch.WordTrace]
  refine ⟨50201578105527116510789539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66935437474036155347719385 50201578105527116510789539)
  ·
    refine ⟨75302367158290674766184309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50201578105527116510789539 75302367158290674766184309)
    ·
      refine ⟨7059596921089750759329779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 75302367158290674766184309 7059596921089750759329779)
      ·
        refine ⟨10589395381634626138994669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7059596921089750759329779 10589395381634626138994669)
        ·
          refine ⟨3971023268112984802123001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10589395381634626138994669 3971023268112984802123001)
          ·
            refine ⟨2978267451084738601592251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3971023268112984802123001 2978267451084738601592251)
            ·
              refine ⟨4467401176627107902388377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2978267451084738601592251 4467401176627107902388377)
              ·
                refine ⟨3350550882470330926791283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4467401176627107902388377 3350550882470330926791283)
                ·
                  refine ⟨5025826323705496390186925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3350550882470330926791283 5025826323705496390186925)
                  ·
                    refine ⟨1884684871389561146320097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5025826323705496390186925 1884684871389561146320097)
                    ·
                      refine ⟨1413513653542170859740073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1884684871389561146320097 1413513653542170859740073)
                      ·
                        rfl

theorem cell23_2752808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_2752808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2752808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2752808 prefixEnd_2752808 := by exact prefixLift 2752808
  have htrace : WordTrace (prefixWord ++ tailWord_2752808) baseStart_2752808 baseEnd_2752808 := by
    simpa [prefixWord, tailWord_2752808, baseEnd_2752808] using wordTrace_append hprefix tailTrace_2752808
  have hstable : (prefixWord ++ tailWord_2752808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752808).length < 2 ^ (prefixWord ++ tailWord_2752808).sum := by decide
  have hdescent : baseEnd_2752808 < baseStart_2752808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752874 : List Nat := [3, 1, 3, 3, 1, 1, 3, 1, 2, 5]
def baseStart_2752874 : Nat := 118140960795 + 2752874 * 2 ^ 59
def prefixEnd_2752874 : Nat := 4983230072969 + 3 ^ 40 * 2752874 * 2
def baseEnd_2752874 : Nat := 471182514421789200504923

theorem tailTrace_2752874 : CollatzResearch.WordTrace tailWord_2752874 prefixEnd_2752874 471182514421789200504923 := by
  unfold tailWord_2752874
  simp only [CollatzResearch.WordTrace]
  refine ⟨25101390857203781573370419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66937042285876750862321117 25101390857203781573370419)
  ·
    refine ⟨37652086285805672360055629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25101390857203781573370419 37652086285805672360055629)
    ·
      refine ⟨14119532357177127135020861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37652086285805672360055629 14119532357177127135020861)
      ·
        refine ⟨5294824633941422675632823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14119532357177127135020861 5294824633941422675632823)
        ·
          refine ⟨7942236950912134013449235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5294824633941422675632823 7942236950912134013449235)
          ·
            refine ⟨11913355426368201020173853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7942236950912134013449235 11913355426368201020173853)
            ·
              refine ⟨4467508284888075382565195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11913355426368201020173853 4467508284888075382565195)
              ·
                refine ⟨6701262427332113073847793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4467508284888075382565195 6701262427332113073847793)
                ·
                  refine ⟨5025946820499084805385845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6701262427332113073847793 5025946820499084805385845)
                  ·
                    refine ⟨471182514421789200504923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5025946820499084805385845 471182514421789200504923)
                    ·
                      rfl

theorem cell23_2752874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_2752874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2752874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2752874 prefixEnd_2752874 := by exact prefixLift 2752874
  have htrace : WordTrace (prefixWord ++ tailWord_2752874) baseStart_2752874 baseEnd_2752874 := by
    simpa [prefixWord, tailWord_2752874, baseEnd_2752874] using wordTrace_append hprefix tailTrace_2752874
  have hstable : (prefixWord ++ tailWord_2752874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752874).length < 2 ^ (prefixWord ++ tailWord_2752874).sum := by decide
  have hdescent : baseEnd_2752874 < baseStart_2752874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752877 : List Nat := [1, 5, 1, 1, 1, 2, 3, 1, 1, 3, 4]
def baseStart_2752877 : Nat := 118140960795 + 2752877 * 2 ^ 59
def prefixEnd_2752877 : Nat := 4983230072969 + 3 ^ 40 * 2752877 * 2
def baseEnd_2752877 : Nat := 1413549083707331089777255

theorem tailTrace_2752877 : CollatzResearch.WordTrace tailWord_2752877 prefixEnd_2752877 1413549083707331089777255 := by
  unfold tailWord_2752877
  simp only [CollatzResearch.WordTrace]
  refine ⟨100405672847804257805840885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66937115231869505203893923 100405672847804257805840885)
  ·
    refine ⟨9413031829481649169297583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 100405672847804257805840885 9413031829481649169297583)
    ·
      refine ⟨14119547744222473753946375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9413031829481649169297583 14119547744222473753946375)
      ·
        refine ⟨21179321616333710630919563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14119547744222473753946375 21179321616333710630919563)
        ·
          refine ⟨31768982424500565946379345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21179321616333710630919563 31768982424500565946379345)
          ·
            refine ⟨23826736818375424459784509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31768982424500565946379345 23826736818375424459784509)
            ·
              refine ⟨8935026306890784172419191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23826736818375424459784509 8935026306890784172419191)
              ·
                refine ⟨13402539460336176258628787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8935026306890784172419191 13402539460336176258628787)
                ·
                  refine ⟨20103809190504264387943181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13402539460336176258628787 20103809190504264387943181)
                  ·
                    refine ⟨7538928446439099145478693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20103809190504264387943181 7538928446439099145478693)
                    ·
                      refine ⟨1413549083707331089777255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7538928446439099145478693 1413549083707331089777255)
                      ·
                        rfl

theorem cell23_2752877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_2752877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2752877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2752877 prefixEnd_2752877 := by exact prefixLift 2752877
  have htrace : WordTrace (prefixWord ++ tailWord_2752877) baseStart_2752877 baseEnd_2752877 := by
    simpa [prefixWord, tailWord_2752877, baseEnd_2752877] using wordTrace_append hprefix tailTrace_2752877
  have hstable : (prefixWord ++ tailWord_2752877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752877).length < 2 ^ (prefixWord ++ tailWord_2752877).sum := by decide
  have hdescent : baseEnd_2752877 < baseStart_2752877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752904 : List Nat := [2, 1, 3, 3, 1, 1, 4, 1, 3, 4]
def baseStart_2752904 : Nat := 118140960795 + 2752904 * 2 ^ 59
def prefixEnd_2752904 : Nat := 4983230072969 + 3 ^ 40 * 2752904 * 2
def baseEnd_2752904 : Nat := 471187649228334161379877

theorem tailTrace_2752904 : CollatzResearch.WordTrace tailWord_2752904 prefixEnd_2752904 471187649228334161379877 := by
  unfold tailWord_2752904
  simp only [CollatzResearch.WordTrace]
  refine ⟨50203328809353220708536883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66937771745804294278049177 50203328809353220708536883)
  ·
    refine ⟨75304993214029831062805325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50203328809353220708536883 75304993214029831062805325)
    ·
      refine ⟨28239372455261186648551997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75304993214029831062805325 28239372455261186648551997)
      ·
        refine ⟨10589764670722944993206999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28239372455261186648551997 10589764670722944993206999)
        ·
          refine ⟨15884647006084417489810499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10589764670722944993206999 15884647006084417489810499)
          ·
            refine ⟨23826970509126626234715749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15884647006084417489810499 23826970509126626234715749)
            ·
              refine ⟨4467556970461242419009203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23826970509126626234715749 4467556970461242419009203)
              ·
                refine ⟨6701335455691863628513805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4467556970461242419009203 6701335455691863628513805)
                ·
                  refine ⟨2513000795884448860692677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6701335455691863628513805 2513000795884448860692677)
                  ·
                    refine ⟨471187649228334161379877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2513000795884448860692677 471187649228334161379877)
                    ·
                      rfl

theorem cell23_2752904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 3, 4].length) (baseStart_2752904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2752904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2752904 prefixEnd_2752904 := by exact prefixLift 2752904
  have htrace : WordTrace (prefixWord ++ tailWord_2752904) baseStart_2752904 baseEnd_2752904 := by
    simpa [prefixWord, tailWord_2752904, baseEnd_2752904] using wordTrace_append hprefix tailTrace_2752904
  have hstable : (prefixWord ++ tailWord_2752904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752904).length < 2 ^ (prefixWord ++ tailWord_2752904).sum := by decide
  have hdescent : baseEnd_2752904 < baseStart_2752904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752927 : List Nat := [1, 1, 2, 5, 1, 1, 1, 1, 2, 5, 3]
def baseStart_2752927 : Nat := 118140960795 + 2752927 * 2 ^ 59
def prefixEnd_2752927 : Nat := 4983230072969 + 3 ^ 40 * 2752927 * 2
def baseEnd_2752927 : Nat := 1413574757740055894152025

theorem tailTrace_2752927 : CollatzResearch.WordTrace tailWord_2752927 prefixEnd_2752927 1413574757740055894152025 := by
  unfold tailWord_2752927
  simp only [CollatzResearch.WordTrace]
  refine ⟨100407496497623116345161035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66938330998415410896774023 100407496497623116345161035)
  ·
    refine ⟨150611244746434674517741553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100407496497623116345161035 150611244746434674517741553)
    ·
      refine ⟨112958433559826005888306165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150611244746434674517741553 112958433559826005888306165)
      ·
        refine ⟨10589853146233688052028703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 112958433559826005888306165 10589853146233688052028703)
        ·
          refine ⟨15884779719350532078043055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10589853146233688052028703 15884779719350532078043055)
          ·
            refine ⟨23827169579025798117064583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15884779719350532078043055 23827169579025798117064583)
            ·
              refine ⟨35740754368538697175596875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23827169579025798117064583 35740754368538697175596875)
              ·
                refine ⟨53611131552808045763395313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35740754368538697175596875 53611131552808045763395313)
                ·
                  refine ⟨40208348664606034322546485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53611131552808045763395313 40208348664606034322546485)
                  ·
                    refine ⟨3769532687306815717738733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40208348664606034322546485 3769532687306815717738733)
                    ·
                      refine ⟨1413574757740055894152025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3769532687306815717738733 1413574757740055894152025)
                      ·
                        rfl

theorem cell23_2752927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_2752927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2752927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2752927 prefixEnd_2752927 := by exact prefixLift 2752927
  have htrace : WordTrace (prefixWord ++ tailWord_2752927) baseStart_2752927 baseEnd_2752927 := by
    simpa [prefixWord, tailWord_2752927, baseEnd_2752927] using wordTrace_append hprefix tailTrace_2752927
  have hstable : (prefixWord ++ tailWord_2752927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752927).length < 2 ^ (prefixWord ++ tailWord_2752927).sum := by decide
  have hdescent : baseEnd_2752927 < baseStart_2752927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752981 : List Nat := [1, 3, 2, 3, 1, 4, 1, 2, 1, 5]
def baseStart_2752981 : Nat := 118140960795 + 2752981 * 2 ^ 59
def prefixEnd_2752981 : Nat := 4983230072969 + 3 ^ 40 * 2752981 * 2
def baseEnd_2752981 : Nat := 471200828565132894292259

theorem tailTrace_2752981 : CollatzResearch.WordTrace tailWord_2752981 prefixEnd_2752981 471200828565132894292259 := by
  unfold tailWord_2752981
  simp only [CollatzResearch.WordTrace]
  refine ⟨100409466039427483567626797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66939644026284989045084531 100409466039427483567626797)
  ·
    refine ⟨37653549764785306337860049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100409466039427483567626797 37653549764785306337860049)
    ·
      refine ⟨28240162323588979753395037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37653549764785306337860049 28240162323588979753395037)
      ·
        refine ⟨10590060871345867407523139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28240162323588979753395037 10590060871345867407523139)
        ·
          refine ⟨15885091307018801111284709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10590060871345867407523139 15885091307018801111284709)
          ·
            refine ⟨2978454620066025208365883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15885091307018801111284709 2978454620066025208365883)
            ·
              refine ⟨4467681930099037812548825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2978454620066025208365883 4467681930099037812548825)
              ·
                refine ⟨3350761447574278359411619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4467681930099037812548825 3350761447574278359411619)
                ·
                  refine ⟨5026142171361417539117429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3350761447574278359411619 5026142171361417539117429)
                  ·
                    refine ⟨471200828565132894292259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5026142171361417539117429 471200828565132894292259)
                    ·
                      rfl

theorem cell23_2752981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 2, 1, 5].length) (baseStart_2752981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2752981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2752981 prefixEnd_2752981 := by exact prefixLift 2752981
  have htrace : WordTrace (prefixWord ++ tailWord_2752981) baseStart_2752981 baseEnd_2752981 := by
    simpa [prefixWord, tailWord_2752981, baseEnd_2752981] using wordTrace_append hprefix tailTrace_2752981
  have hstable : (prefixWord ++ tailWord_2752981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752981).length < 2 ^ (prefixWord ++ tailWord_2752981).sum := by decide
  have hdescent : baseEnd_2752981 < baseStart_2752981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753014 : List Nat := [5, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4]
def baseStart_2753014 : Nat := 118140960795 + 2753014 * 2 ^ 59
def prefixEnd_2753014 : Nat := 4983230072969 + 3 ^ 40 * 2753014 * 2
def baseEnd_2753014 : Nat := 1413619430556997053764125

theorem tailTrace_2753014 : CollatzResearch.WordTrace tailWord_2753014 prefixEnd_2753014 1413619430556997053764125 := by
  unfold tailWord_2753014
  simp only [CollatzResearch.WordTrace]
  refine ⟨6275666853019245637723631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66940446432205286802385397 6275666853019245637723631)
  ·
    refine ⟨9413500279528868456585447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6275666853019245637723631 9413500279528868456585447)
    ·
      refine ⟨14120250419293302684878171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9413500279528868456585447 14120250419293302684878171)
      ·
        refine ⟨21180375628939954027317257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14120250419293302684878171 21180375628939954027317257)
        ·
          refine ⟨15885281721704965520487943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21180375628939954027317257 15885281721704965520487943)
          ·
            refine ⟨23827922582557448280731915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15885281721704965520487943 23827922582557448280731915)
            ·
              refine ⟨35741883873836172421097873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23827922582557448280731915 35741883873836172421097873)
              ·
                refine ⟨26806412905377129315823405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35741883873836172421097873 26806412905377129315823405)
                ·
                  refine ⟨10052404839516423493433777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26806412905377129315823405 10052404839516423493433777)
                  ·
                    refine ⟨7539303629637317620075333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10052404839516423493433777 7539303629637317620075333)
                    ·
                      refine ⟨1413619430556997053764125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7539303629637317620075333 1413619430556997053764125)
                      ·
                        rfl

theorem cell23_2753014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_2753014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2753014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2753014 prefixEnd_2753014 := by exact prefixLift 2753014
  have htrace : WordTrace (prefixWord ++ tailWord_2753014) baseStart_2753014 baseEnd_2753014 := by
    simpa [prefixWord, tailWord_2753014, baseEnd_2753014] using wordTrace_append hprefix tailTrace_2753014
  have hstable : (prefixWord ++ tailWord_2753014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753014).length < 2 ^ (prefixWord ++ tailWord_2753014).sum := by decide
  have hdescent : baseEnd_2753014 < baseStart_2753014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753031 : List Nat := [1, 1, 4, 3, 3, 1, 2, 1, 1, 2, 4]
def baseStart_2753031 : Nat := 118140960795 + 2753031 * 2 ^ 59
def prefixEnd_2753031 : Nat := 4983230072969 + 3 ^ 40 * 2753031 * 2
def baseEnd_2753031 : Nat := 1413628159728123487251547

theorem tailTrace_2753031 : CollatzResearch.WordTrace tailWord_2753031 prefixEnd_2753031 1413628159728123487251547 := by
  unfold tailWord_2753031
  simp only [CollatzResearch.WordTrace]
  refine ⟨100411289689246342106946947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66940859792830894737964631 100411289689246342106946947)
  ·
    refine ⟨150616934533869513160420421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100411289689246342106946947 150616934533869513160420421)
    ·
      refine ⟨28240675225100533717578829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150616934533869513160420421 28240675225100533717578829)
      ·
        refine ⟨10590253209412700144092061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28240675225100533717578829 10590253209412700144092061)
        ·
          refine ⟨3971344953529762554034523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10590253209412700144092061 3971344953529762554034523)
          ·
            refine ⟨5957017430294643831051785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3971344953529762554034523 5957017430294643831051785)
            ·
              refine ⟨4467763072720982873288839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5957017430294643831051785 4467763072720982873288839)
              ·
                refine ⟨6701644609081474309933259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4467763072720982873288839 6701644609081474309933259)
                ·
                  refine ⟨10052466913622211464899889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6701644609081474309933259 10052466913622211464899889)
                  ·
                    refine ⟨7539350185216658598674917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10052466913622211464899889 7539350185216658598674917)
                    ·
                      refine ⟨1413628159728123487251547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7539350185216658598674917 1413628159728123487251547)
                      ·
                        rfl

theorem cell23_2753031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_2753031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2753031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2753031 prefixEnd_2753031 := by exact prefixLift 2753031
  have htrace : WordTrace (prefixWord ++ tailWord_2753031) baseStart_2753031 baseEnd_2753031 := by
    simpa [prefixWord, tailWord_2753031, baseEnd_2753031] using wordTrace_append hprefix tailTrace_2753031
  have hstable : (prefixWord ++ tailWord_2753031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753031).length < 2 ^ (prefixWord ++ tailWord_2753031).sum := by decide
  have hdescent : baseEnd_2753031 < baseStart_2753031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753069 : List Nat := [1, 5, 4, 1, 1, 1, 2, 1, 3, 2, 2]
def baseStart_2753069 : Nat := 118140960795 + 2753069 * 2 ^ 59
def prefixEnd_2753069 : Nat := 4983230072969 + 3 ^ 40 * 2753069 * 2
def baseEnd_2753069 : Nat := 1413647671992994338576373

theorem tailTrace_2753069 : CollatzResearch.WordTrace tailWord_2753069 prefixEnd_2753069 1413647671992994338576373 := by
  unfold tailWord_2753069
  simp only [CollatzResearch.WordTrace]
  refine ⟨100412675663108674596830261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66941783775405783064553507 100412675663108674596830261)
  ·
    refine ⟨9413688343416438243452837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 100412675663108674596830261 9413688343416438243452837)
    ·
      refine ⟨1765066564390582170647407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9413688343416438243452837 1765066564390582170647407)
      ·
        refine ⟨2647599846585873255971111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1765066564390582170647407 2647599846585873255971111)
        ·
          refine ⟨3971399769878809883956667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2647599846585873255971111 3971399769878809883956667)
          ·
            refine ⟨5957099654818214825935001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3971399769878809883956667 5957099654818214825935001)
            ·
              refine ⟨4467824741113661119451251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5957099654818214825935001 4467824741113661119451251)
              ·
                refine ⟨6701737111670491679176877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4467824741113661119451251 6701737111670491679176877)
                ·
                  refine ⟨2513151416876434379691329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6701737111670491679176877 2513151416876434379691329)
                  ·
                    refine ⟨1884863562657325784768497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2513151416876434379691329 1884863562657325784768497)
                    ·
                      refine ⟨1413647671992994338576373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1884863562657325784768497 1413647671992994338576373)
                      ·
                        rfl

theorem cell23_2753069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_2753069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2753069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2753069 prefixEnd_2753069 := by exact prefixLift 2753069
  have htrace : WordTrace (prefixWord ++ tailWord_2753069) baseStart_2753069 baseEnd_2753069 := by
    simpa [prefixWord, tailWord_2753069, baseEnd_2753069] using wordTrace_append hprefix tailTrace_2753069
  have hstable : (prefixWord ++ tailWord_2753069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753069).length < 2 ^ (prefixWord ++ tailWord_2753069).sum := by decide
  have hdescent : baseEnd_2753069 < baseStart_2753069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753084 : List Nat := [2, 2, 2, 2, 3, 1, 2, 1, 2, 6]
def baseStart_2753084 : Nat := 118140960795 + 2753084 * 2 ^ 59
def prefixEnd_2753084 : Nat := 4983230072969 + 3 ^ 40 * 2753084 * 2
def baseEnd_2753084 : Nat := 471218458067603926629601

theorem tailTrace_2753084 : CollatzResearch.WordTrace tailWord_2753084 prefixEnd_2753084 471218458067603926629601 := by
  unfold tailWord_2753084
  simp only [CollatzResearch.WordTrace]
  refine ⟨50206611379027166079313153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66942148505369554772417537 50206611379027166079313153)
  ·
    refine ⟨37654958534270374559484865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50206611379027166079313153 37654958534270374559484865)
    ·
      refine ⟨28241218900702780919613649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37654958534270374559484865 28241218900702780919613649)
      ·
        refine ⟨21180914175527085689710237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28241218900702780919613649 21180914175527085689710237)
        ·
          refine ⟨7942842815822657133641339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21180914175527085689710237 7942842815822657133641339)
          ·
            refine ⟨11914264223733985700462009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7942842815822657133641339 11914264223733985700462009)
            ·
              refine ⟨8935698167800489275346507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11914264223733985700462009 8935698167800489275346507)
              ·
                refine ⟨13403547251700733913019761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8935698167800489275346507 13403547251700733913019761)
                ·
                  refine ⟨10052660438775550434764821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13403547251700733913019761 10052660438775550434764821)
                  ·
                    refine ⟨471218458067603926629601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10052660438775550434764821 471218458067603926629601)
                    ·
                      rfl

theorem cell23_2753084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 2, 6].length) (baseStart_2753084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2753084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2753084 prefixEnd_2753084 := by exact prefixLift 2753084
  have htrace : WordTrace (prefixWord ++ tailWord_2753084) baseStart_2753084 baseEnd_2753084 := by
    simpa [prefixWord, tailWord_2753084, baseEnd_2753084] using wordTrace_append hprefix tailTrace_2753084
  have hstable : (prefixWord ++ tailWord_2753084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753084).length < 2 ^ (prefixWord ++ tailWord_2753084).sum := by decide
  have hdescent : baseEnd_2753084 < baseStart_2753084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753085 : List Nat := [1, 4, 1, 3, 2, 2, 3, 1, 2, 1, 3]
def baseStart_2753085 : Nat := 118140960795 + 2753085 * 2 ^ 59
def prefixEnd_2753085 : Nat := 4983230072969 + 3 ^ 40 * 2753085 * 2
def baseEnd_2753085 : Nat := 1413655887683466275976299

theorem tailTrace_2753085 : CollatzResearch.WordTrace tailWord_2753085 prefixEnd_2753085 1413655887683466275976299 := by
  unfold tailWord_2753085
  simp only [CollatzResearch.WordTrace]
  refine ⟨100413259231050709329412709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66942172820700472886275139 100413259231050709329412709)
  ·
    refine ⟨18827486105822007999264883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100413259231050709329412709 18827486105822007999264883)
    ·
      refine ⟨28241229158733011998897325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18827486105822007999264883 28241229158733011998897325)
      ·
        refine ⟨10590460934524879499586497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28241229158733011998897325 10590460934524879499586497)
        ·
          refine ⟨7942845700893659624689873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10590460934524879499586497 7942845700893659624689873)
          ·
            refine ⟨5957134275670244718517405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7942845700893659624689873 5957134275670244718517405)
            ·
              refine ⟨2233925353376341769444027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5957134275670244718517405 2233925353376341769444027)
              ·
                refine ⟨3350888030064512654166041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2233925353376341769444027 3350888030064512654166041)
                ·
                  refine ⟨2513166022548384490624531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3350888030064512654166041 2513166022548384490624531)
                  ·
                    refine ⟨3769749033822576735936797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2513166022548384490624531 3769749033822576735936797)
                    ·
                      refine ⟨1413655887683466275976299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3769749033822576735936797 1413655887683466275976299)
                      ·
                        rfl

theorem cell23_2753085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_2753085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2753085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2753085 prefixEnd_2753085 := by exact prefixLift 2753085
  have htrace : WordTrace (prefixWord ++ tailWord_2753085) baseStart_2753085 baseEnd_2753085 := by
    simpa [prefixWord, tailWord_2753085, baseEnd_2753085] using wordTrace_append hprefix tailTrace_2753085
  have hstable : (prefixWord ++ tailWord_2753085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753085).length < 2 ^ (prefixWord ++ tailWord_2753085).sum := by decide
  have hdescent : baseEnd_2753085 < baseStart_2753085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753092 : List Nat := [2, 3, 5, 1, 2, 1, 2, 7]
def baseStart_2753092 : Nat := 118140960795 + 2753092 * 2 ^ 59
def prefixEnd_2753092 : Nat := 4983230072969 + 3 ^ 40 * 2753092 * 2
def baseEnd_2753092 : Nat := 52357758594372138836621

theorem tailTrace_2753092 : CollatzResearch.WordTrace tailWord_2753092 prefixEnd_2753092 52357758594372138836621 := by
  unfold tailWord_2753092
  simp only [CollatzResearch.WordTrace]
  refine ⟨50206757271012674762458765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66942343028016899683278353 50206757271012674762458765)
  ·
    refine ⟨18827533976629753035922037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50206757271012674762458765 18827533976629753035922037)
    ·
      refine ⟨1765081310309039347117691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18827533976629753035922037 1765081310309039347117691)
      ·
        refine ⟨2647621965463559020676537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1765081310309039347117691 2647621965463559020676537)
        ·
          refine ⟨1985716474097669265507403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2647621965463559020676537 1985716474097669265507403)
          ·
            refine ⟨2978574711146503898261105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1985716474097669265507403 2978574711146503898261105)
            ·
              refine ⟨2233931033359877923695829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2978574711146503898261105 2233931033359877923695829)
              ·
                refine ⟨52357758594372138836621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2233931033359877923695829 52357758594372138836621)
                ·
                  rfl

theorem cell23_2753092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 7].length) (baseStart_2753092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2753092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2753092 prefixEnd_2753092 := by exact prefixLift 2753092
  have htrace : WordTrace (prefixWord ++ tailWord_2753092) baseStart_2753092 baseEnd_2753092 := by
    simpa [prefixWord, tailWord_2753092, baseEnd_2753092] using wordTrace_append hprefix tailTrace_2753092
  have hstable : (prefixWord ++ tailWord_2753092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753092).length < 2 ^ (prefixWord ++ tailWord_2753092).sum := by decide
  have hdescent : baseEnd_2753092 < baseStart_2753092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753108 : List Nat := [2, 4, 1, 1, 1, 3, 1, 2, 4, 2, 2]
def baseStart_2753108 : Nat := 118140960795 + 2753108 * 2 ^ 59
def prefixEnd_2753108 : Nat := 4983230072969 + 3 ^ 40 * 2753108 * 2
def baseEnd_2753108 : Nat := 1413667697738519685988693

theorem tailTrace_2753108 : CollatzResearch.WordTrace tailWord_2753108 prefixEnd_2753108 1413667697738519685988693 := by
  unfold tailWord_2753108
  simp only [CollatzResearch.WordTrace]
  refine ⟨50207049054983692128749989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66942732073311589504999985 50207049054983692128749989)
  ·
    refine ⟨9413821697809442274140623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50207049054983692128749989 9413821697809442274140623)
    ·
      refine ⟨14120732546714163411210935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9413821697809442274140623 14120732546714163411210935)
      ·
        refine ⟨21181098820071245116816403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14120732546714163411210935 21181098820071245116816403)
        ·
          refine ⟨31771648230106867675224605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21181098820071245116816403 31771648230106867675224605)
          ·
            refine ⟨11914368086290075378209227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31771648230106867675224605 11914368086290075378209227)
            ·
              refine ⟨17871552129435113067313841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11914368086290075378209227 17871552129435113067313841)
              ·
                refine ⟨13403664097076334800485381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17871552129435113067313841 13403664097076334800485381)
                ·
                  refine ⟨2513187018201812775091009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13403664097076334800485381 2513187018201812775091009)
                  ·
                    refine ⟨1884890263651359581318257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2513187018201812775091009 1884890263651359581318257)
                    ·
                      refine ⟨1413667697738519685988693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1884890263651359581318257 1413667697738519685988693)
                      ·
                        rfl

theorem cell23_2753108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 4, 2, 2].length) (baseStart_2753108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2753108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2753108 prefixEnd_2753108 := by exact prefixLift 2753108
  have htrace : WordTrace (prefixWord ++ tailWord_2753108) baseStart_2753108 baseEnd_2753108 := by
    simpa [prefixWord, tailWord_2753108, baseEnd_2753108] using wordTrace_append hprefix tailTrace_2753108
  have hstable : (prefixWord ++ tailWord_2753108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753108).length < 2 ^ (prefixWord ++ tailWord_2753108).sum := by decide
  have hdescent : baseEnd_2753108 < baseStart_2753108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753142 : List Nat := [5, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2]
def baseStart_2753142 : Nat := 118140960795 + 2753142 * 2 ^ 59
def prefixEnd_2753142 : Nat := 4983230072969 + 3 ^ 40 * 2753142 * 2
def baseEnd_2753142 : Nat := 1413685156080772552963537

theorem tailTrace_2753142 : CollatzResearch.WordTrace tailWord_2753142 prefixEnd_2753142 1413685156080772552963537 := by
  unfold tailWord_2753142
  simp only [CollatzResearch.WordTrace]
  refine ⟨6275958636990263004014855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66943558794562805376158453 6275958636990263004014855)
  ·
    refine ⟨9413937955485394506022283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6275958636990263004014855 9413937955485394506022283)
    ·
      refine ⟨14120906933228091759033425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9413937955485394506022283 14120906933228091759033425)
      ·
        refine ⟨10590680199921068819275069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14120906933228091759033425 10590680199921068819275069)
        ·
          refine ⟨3971505074970400807228151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10590680199921068819275069 3971505074970400807228151)
          ·
            refine ⟨5957257612455601210842227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3971505074970400807228151 5957257612455601210842227)
            ·
              refine ⟨8935886418683401816263341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5957257612455601210842227 8935886418683401816263341)
              ·
                refine ⟨3350957407006275681098753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8935886418683401816263341 3350957407006275681098753)
                ·
                  refine ⟨2513218055254706760824065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3350957407006275681098753 2513218055254706760824065)
                  ·
                    refine ⟨1884913541441030070618049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2513218055254706760824065 1884913541441030070618049)
                    ·
                      refine ⟨1413685156080772552963537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1884913541441030070618049 1413685156080772552963537)
                      ·
                        rfl

theorem cell23_2753142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_2753142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2753142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2753142 prefixEnd_2753142 := by exact prefixLift 2753142
  have htrace : WordTrace (prefixWord ++ tailWord_2753142) baseStart_2753142 baseEnd_2753142 := by
    simpa [prefixWord, tailWord_2753142, baseEnd_2753142] using wordTrace_append hprefix tailTrace_2753142
  have hstable : (prefixWord ++ tailWord_2753142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753142).length < 2 ^ (prefixWord ++ tailWord_2753142).sum := by decide
  have hdescent : baseEnd_2753142 < baseStart_2753142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753181 : List Nat := [1, 4, 2, 1, 1, 1, 4, 2, 2, 1, 4]
def baseStart_2753181 : Nat := 118140960795 + 2753181 * 2 ^ 59
def prefixEnd_2753181 : Nat := 4983230072969 + 3 ^ 40 * 2753181 * 2
def baseEnd_2753181 : Nat := 1413705181826297900375857

theorem tailTrace_2753181 : CollatzResearch.WordTrace tailWord_2753181 prefixEnd_2753181 1413705181826297900375857 := by
  unfold tailWord_2753181
  simp only [CollatzResearch.WordTrace]
  refine ⟨100416760638702917724907397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66944507092468611816604931 100416760638702917724907397)
  ·
    refine ⟨18828142619756797073420137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100416760638702917724907397 18828142619756797073420137)
    ·
      refine ⟨14121106964817597805065103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18828142619756797073420137 14121106964817597805065103)
      ·
        refine ⟨21181660447226396707597655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14121106964817597805065103 21181660447226396707597655)
        ·
          refine ⟨31772490670839595061396483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21181660447226396707597655 31772490670839595061396483)
          ·
            refine ⟨47658736006259392592094725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31772490670839595061396483 47658736006259392592094725)
            ·
              refine ⟨8936013001173636111017761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47658736006259392592094725 8936013001173636111017761)
              ·
                refine ⟨6702009750880227083263321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8936013001173636111017761 6702009750880227083263321)
                ·
                  refine ⟨5026507313160170312447491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6702009750880227083263321 5026507313160170312447491)
                  ·
                    refine ⟨7539760969740255468671237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5026507313160170312447491 7539760969740255468671237)
                    ·
                      refine ⟨1413705181826297900375857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7539760969740255468671237 1413705181826297900375857)
                      ·
                        rfl

theorem cell23_2753181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_2753181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2753181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2753181 prefixEnd_2753181 := by exact prefixLift 2753181
  have htrace : WordTrace (prefixWord ++ tailWord_2753181) baseStart_2753181 baseEnd_2753181 := by
    simpa [prefixWord, tailWord_2753181, baseEnd_2753181] using wordTrace_append hprefix tailTrace_2753181
  have hstable : (prefixWord ++ tailWord_2753181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753181).length < 2 ^ (prefixWord ++ tailWord_2753181).sum := by decide
  have hdescent : baseEnd_2753181 < baseStart_2753181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753271 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 1, 8, 2]
def baseStart_2753271 : Nat := 118140960795 + 2753271 * 2 ^ 59
def prefixEnd_2753271 : Nat := 4983230072969 + 3 ^ 40 * 2753271 * 2
def baseEnd_2753271 : Nat := 1413751395085202548250443

theorem tailTrace_2753271 : CollatzResearch.WordTrace tailWord_2753271 prefixEnd_2753271 1413751395085202548250443 := by
  unfold tailWord_2753271
  simp only [CollatzResearch.WordTrace]
  refine ⟨100420043208376863095683667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66946695472251242063789111 100420043208376863095683667)
  ·
    refine ⟨150630064812565294643525501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100420043208376863095683667 150630064812565294643525501)
    ·
      refine ⟨56486274304711985491322063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150630064812565294643525501 56486274304711985491322063)
      ·
        refine ⟨84729411457067978236983095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56486274304711985491322063 84729411457067978236983095)
        ·
          refine ⟨127094117185601967355474643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84729411457067978236983095 127094117185601967355474643)
          ·
            refine ⟨190641175778402951033211965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127094117185601967355474643 190641175778402951033211965)
            ·
              refine ⟨71490440916901106637454487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 190641175778402951033211965 71490440916901106637454487)
              ·
                refine ⟨107235661375351659956181731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71490440916901106637454487 107235661375351659956181731)
                ·
                  refine ⟨160853492063027489934272597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107235661375351659956181731 160853492063027489934272597)
                  ·
                    refine ⟨1885001860113603397667257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 160853492063027489934272597 1885001860113603397667257)
                    ·
                      refine ⟨1413751395085202548250443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1885001860113603397667257 1413751395085202548250443)
                      ·
                        rfl

theorem cell23_2753271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 8, 2].length) (baseStart_2753271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2753271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2753271 prefixEnd_2753271 := by exact prefixLift 2753271
  have htrace : WordTrace (prefixWord ++ tailWord_2753271) baseStart_2753271 baseEnd_2753271 := by
    simpa [prefixWord, tailWord_2753271, baseEnd_2753271] using wordTrace_append hprefix tailTrace_2753271
  have hstable : (prefixWord ++ tailWord_2753271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753271).length < 2 ^ (prefixWord ++ tailWord_2753271).sum := by decide
  have hdescent : baseEnd_2753271 < baseStart_2753271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753288 : List Nat := [2, 1, 3, 2, 2, 2, 2, 3, 1, 1, 4]
def baseStart_2753288 : Nat := 118140960795 + 2753288 * 2 ^ 59
def prefixEnd_2753288 : Nat := 4983230072969 + 3 ^ 40 * 2753288 * 2
def baseEnd_2753288 : Nat := 1413760124256328981737865

theorem tailTrace_2753288 : CollatzResearch.WordTrace tailWord_2753288 prefixEnd_2753288 1413760124256328981737865 := by
  unfold tailWord_2753288
  simp only [CollatzResearch.WordTrace]
  refine ⟨50210331624657637499526259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66947108832876849999368345 50210331624657637499526259)
  ·
    refine ⟨75315497436986456249289389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50210331624657637499526259 75315497436986456249289389)
    ·
      refine ⟨28243311538869921093483521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75315497436986456249289389 28243311538869921093483521)
      ·
        refine ⟨21182483654152440820112641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28243311538869921093483521 21182483654152440820112641)
        ·
          refine ⟨15886862740614330615084481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21182483654152440820112641 15886862740614330615084481)
          ·
            refine ⟨11915147055460747961313361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15886862740614330615084481 11915147055460747961313361)
            ·
              refine ⟨8936360291595560970985021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11915147055460747961313361 8936360291595560970985021)
              ·
                refine ⟨3351135109348335364119383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8936360291595560970985021 3351135109348335364119383)
                ·
                  refine ⟨5026702664022503046179075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3351135109348335364119383 5026702664022503046179075)
                  ·
                    refine ⟨7540053996033754569268613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5026702664022503046179075 7540053996033754569268613)
                    ·
                      refine ⟨1413760124256328981737865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7540053996033754569268613 1413760124256328981737865)
                      ·
                        rfl

theorem cell23_2753288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_2753288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2753288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2753288 prefixEnd_2753288 := by exact prefixLift 2753288
  have htrace : WordTrace (prefixWord ++ tailWord_2753288) baseStart_2753288 baseEnd_2753288 := by
    simpa [prefixWord, tailWord_2753288, baseEnd_2753288] using wordTrace_append hprefix tailTrace_2753288
  have hstable : (prefixWord ++ tailWord_2753288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753288).length < 2 ^ (prefixWord ++ tailWord_2753288).sum := by decide
  have hdescent : baseEnd_2753288 < baseStart_2753288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753291 : List Nat := [1, 1, 1, 1, 5, 1, 1, 2, 5, 2, 3]
def baseStart_2753291 : Nat := 118140960795 + 2753291 * 2 ^ 59
def prefixEnd_2753291 : Nat := 4983230072969 + 3 ^ 40 * 2753291 * 2
def baseEnd_2753291 : Nat := 1413761664698292470000351

theorem tailTrace_2753291 : CollatzResearch.WordTrace tailWord_2753291 prefixEnd_2753291 1413761664698292470000351 := by
  unfold tailWord_2753291
  simp only [CollatzResearch.WordTrace]
  refine ⟨100420772668304406511411727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66947181778869604340941151 100420772668304406511411727)
  ·
    refine ⟨150631159002456609767117591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100420772668304406511411727 150631159002456609767117591)
    ·
      refine ⟨225946738503684914650676387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150631159002456609767117591 225946738503684914650676387)
      ·
        refine ⟨338920107755527371976014581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225946738503684914650676387 338920107755527371976014581)
        ·
          refine ⟨31773760102080691122751367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 338920107755527371976014581 31773760102080691122751367)
          ·
            refine ⟨47660640153121036684127051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31773760102080691122751367 47660640153121036684127051)
            ·
              refine ⟨71490960229681555026190577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47660640153121036684127051 71490960229681555026190577)
              ·
                refine ⟨53618220172261166269642933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71490960229681555026190577 53618220172261166269642933)
                ·
                  refine ⟨5026708141149484337779025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53618220172261166269642933 5026708141149484337779025)
                  ·
                    refine ⟨3770031105862113253334269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5026708141149484337779025 3770031105862113253334269)
                    ·
                      refine ⟨1413761664698292470000351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3770031105862113253334269 1413761664698292470000351)
                      ·
                        rfl

theorem cell23_2753291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 5, 2, 3].length) (baseStart_2753291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2753291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2753291 prefixEnd_2753291 := by exact prefixLift 2753291
  have htrace : WordTrace (prefixWord ++ tailWord_2753291) baseStart_2753291 baseEnd_2753291 := by
    simpa [prefixWord, tailWord_2753291, baseEnd_2753291] using wordTrace_append hprefix tailTrace_2753291
  have hstable : (prefixWord ++ tailWord_2753291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753291).length < 2 ^ (prefixWord ++ tailWord_2753291).sum := by decide
  have hdescent : baseEnd_2753291 < baseStart_2753291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753311 : List Nat := [1, 1, 2, 4, 2, 3, 2, 8]
def baseStart_2753311 : Nat := 118140960795 + 2753311 * 2 ^ 59
def prefixEnd_2753311 : Nat := 4983230072969 + 3 ^ 40 * 2753311 * 2
def baseEnd_2753311 : Nat := 52361923493014162657417

theorem tailTrace_2753311 : CollatzResearch.WordTrace tailWord_2753311 prefixEnd_2753311 52361923493014162657417 := by
  unfold tailWord_2753311
  simp only [CollatzResearch.WordTrace]
  refine ⟨100421502128231949927139787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66947668085487966618093191 100421502128231949927139787)
  ·
    refine ⟨150632253192347924890709681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100421502128231949927139787 150632253192347924890709681)
    ·
      refine ⟨112974189894260943668032261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150632253192347924890709681 112974189894260943668032261)
      ·
        refine ⟨21182660605173926937756049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112974189894260943668032261 21182660605173926937756049)
        ·
          refine ⟨15886995453880445203317037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21182660605173926937756049 15886995453880445203317037)
          ·
            refine ⟨5957623295205166951243889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15886995453880445203317037 5957623295205166951243889)
            ·
              refine ⟨4468217471403875213432917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5957623295205166951243889 4468217471403875213432917)
              ·
                refine ⟨52361923493014162657417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4468217471403875213432917 52361923493014162657417)
                ·
                  rfl

theorem cell23_2753311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 8].length) (baseStart_2753311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2753311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2753311 prefixEnd_2753311 := by exact prefixLift 2753311
  have htrace : WordTrace (prefixWord ++ tailWord_2753311) baseStart_2753311 baseEnd_2753311 := by
    simpa [prefixWord, tailWord_2753311, baseEnd_2753311] using wordTrace_append hprefix tailTrace_2753311
  have hstable : (prefixWord ++ tailWord_2753311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753311).length < 2 ^ (prefixWord ++ tailWord_2753311).sum := by decide
  have hdescent : baseEnd_2753311 < baseStart_2753311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753342 : List Nat := [4, 2, 1, 2, 4, 1, 1, 1, 1, 1, 5]
def baseStart_2753342 : Nat := 118140960795 + 2753342 * 2 ^ 59
def prefixEnd_2753342 : Nat := 4983230072969 + 3 ^ 40 * 2753342 * 2
def baseEnd_2753342 : Nat := 1413787852211671770462617

theorem tailTrace_2753342 : CollatzResearch.WordTrace tailWord_2753342 prefixEnd_2753342 1413787852211671770462617 := by
  unfold tailWord_2753342
  simp only [CollatzResearch.WordTrace]
  refine ⟨12552829098889955277689785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66948421860746428147678853 12552829098889955277689785)
  ·
    refine ⟨9414621824167466458267339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12552829098889955277689785 9414621824167466458267339)
    ·
      refine ⟨14121932736251199687401009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9414621824167466458267339 14121932736251199687401009)
      ·
        refine ⟨10591449552188399765550757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14121932736251199687401009 10591449552188399765550757)
        ·
          refine ⟨1985896791035324956040767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10591449552188399765550757 1985896791035324956040767)
          ·
            refine ⟨2978845186552987434061151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1985896791035324956040767 2978845186552987434061151)
            ·
              refine ⟨4468267779829481151091727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2978845186552987434061151 4468267779829481151091727)
              ·
                refine ⟨6702401669744221726637591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4468267779829481151091727 6702401669744221726637591)
                ·
                  refine ⟨10053602504616332589956387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6702401669744221726637591 10053602504616332589956387)
                  ·
                    refine ⟨15080403756924498884934581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10053602504616332589956387 15080403756924498884934581)
                    ·
                      refine ⟨1413787852211671770462617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15080403756924498884934581 1413787852211671770462617)
                      ·
                        rfl

theorem cell23_2753342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_2753342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2753342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2753342 prefixEnd_2753342 := by exact prefixLift 2753342
  have htrace : WordTrace (prefixWord ++ tailWord_2753342) baseStart_2753342 baseEnd_2753342 := by
    simpa [prefixWord, tailWord_2753342, baseEnd_2753342] using wordTrace_append hprefix tailTrace_2753342
  have hstable : (prefixWord ++ tailWord_2753342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753342).length < 2 ^ (prefixWord ++ tailWord_2753342).sum := by decide
  have hdescent : baseEnd_2753342 < baseStart_2753342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753350 : List Nat := [6, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3]
def baseStart_2753350 : Nat := 118140960795 + 2753350 * 2 ^ 59
def prefixEnd_2753350 : Nat := 4983230072969 + 3 ^ 40 * 2753350 * 2
def baseEnd_2753350 : Nat := 1413791960056907739162581

theorem tailTrace_2753350 : CollatzResearch.WordTrace tailWord_2753350 prefixEnd_2753350 1413791960056907739162581 := by
  unfold tailWord_2753350
  simp only [CollatzResearch.WordTrace]
  refine ⟨3138216392971583112119047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 66948616383393773058539669 3138216392971583112119047)
  ·
    refine ⟨4707324589457374668178571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3138216392971583112119047 4707324589457374668178571)
    ·
      refine ⟨7060986884186062002267857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4707324589457374668178571 7060986884186062002267857)
      ·
        refine ⟨5295740163139546501700893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7060986884186062002267857 5295740163139546501700893)
        ·
          refine ⟨1985902561177329938137835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5295740163139546501700893 1985902561177329938137835)
          ·
            refine ⟨2978853841765994907206753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1985902561177329938137835 2978853841765994907206753)
            ·
              refine ⟨2234140381324496180405065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2978853841765994907206753 2234140381324496180405065)
              ·
                refine ⟨1675605285993372135303799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2234140381324496180405065 1675605285993372135303799)
                ·
                  refine ⟨2513407928990058202955699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1675605285993372135303799 2513407928990058202955699)
                  ·
                    refine ⟨3770111893485087304433549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2513407928990058202955699 3770111893485087304433549)
                    ·
                      refine ⟨1413791960056907739162581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3770111893485087304433549 1413791960056907739162581)
                      ·
                        rfl

theorem cell23_2753350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_2753350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2753350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2753350 prefixEnd_2753350 := by exact prefixLift 2753350
  have htrace : WordTrace (prefixWord ++ tailWord_2753350) baseStart_2753350 baseEnd_2753350 := by
    simpa [prefixWord, tailWord_2753350, baseEnd_2753350] using wordTrace_append hprefix tailTrace_2753350
  have hstable : (prefixWord ++ tailWord_2753350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753350).length < 2 ^ (prefixWord ++ tailWord_2753350).sum := by decide
  have hdescent : baseEnd_2753350 < baseStart_2753350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753356 : List Nat := [2, 2, 1, 3, 3, 3, 2, 2, 1, 2, 2]
def baseStart_2753356 : Nat := 118140960795 + 2753356 * 2 ^ 59
def prefixEnd_2753356 : Nat := 4983230072969 + 3 ^ 40 * 2753356 * 2
def baseEnd_2753356 : Nat := 1413795040940834715687553

theorem tailTrace_2753356 : CollatzResearch.WordTrace tailWord_2753356 prefixEnd_2753356 1413795040940834715687553 := by
  unfold tailWord_2753356
  simp only [CollatzResearch.WordTrace]
  refine ⟨50211571706534461306263961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66948762275379281741685281 50211571706534461306263961)
  ·
    refine ⟨37658678779900845979697971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50211571706534461306263961 37658678779900845979697971)
    ·
      refine ⟨56488018169851268969546957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37658678779900845979697971 56488018169851268969546957)
      ·
        refine ⟨21183006813694225863580109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56488018169851268969546957 21183006813694225863580109)
        ·
          refine ⟨7943627555135334698842541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21183006813694225863580109 7943627555135334698842541)
          ·
            refine ⟨2978860333175750512065953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7943627555135334698842541 2978860333175750512065953)
            ·
              refine ⟨2234145249881812884049465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2978860333175750512065953 2234145249881812884049465)
              ·
                refine ⟨1675608937411359663037099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2234145249881812884049465 1675608937411359663037099)
                ·
                  refine ⟨2513413406117039494555649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1675608937411359663037099 2513413406117039494555649)
                  ·
                    refine ⟨1885060054587779620916737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2513413406117039494555649 1885060054587779620916737)
                    ·
                      refine ⟨1413795040940834715687553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1885060054587779620916737 1413795040940834715687553)
                      ·
                        rfl

theorem cell23_2753356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 2, 1, 2, 2].length) (baseStart_2753356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2753356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2753356 prefixEnd_2753356 := by exact prefixLift 2753356
  have htrace : WordTrace (prefixWord ++ tailWord_2753356) baseStart_2753356 baseEnd_2753356 := by
    simpa [prefixWord, tailWord_2753356, baseEnd_2753356] using wordTrace_append hprefix tailTrace_2753356
  have hstable : (prefixWord ++ tailWord_2753356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753356).length < 2 ^ (prefixWord ++ tailWord_2753356).sum := by decide
  have hdescent : baseEnd_2753356 < baseStart_2753356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753372 : List Nat := [2, 2, 4, 2, 1, 1, 2, 3, 2, 1, 3]
def baseStart_2753372 : Nat := 118140960795 + 2753372 * 2 ^ 59
def prefixEnd_2753372 : Nat := 4983230072969 + 3 ^ 40 * 2753372 * 2
def baseEnd_2753372 : Nat := 1413803256631306653087479

theorem tailTrace_2753372 : CollatzResearch.WordTrace tailWord_2753372 prefixEnd_2753372 1413803256631306653087479 := by
  unfold tailWord_2753372
  simp only [CollatzResearch.WordTrace]
  refine ⟨50211863490505478672555185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66949151320673971563406913 50211863490505478672555185)
  ·
    refine ⟨37658897617879109004416389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50211863490505478672555185 37658897617879109004416389)
    ·
      refine ⟨7061043303352332938328073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37658897617879109004416389 7061043303352332938328073)
      ·
        refine ⟨5295782477514249703746055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7061043303352332938328073 5295782477514249703746055)
        ·
          refine ⟨7943673716271374555619083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5295782477514249703746055 7943673716271374555619083)
          ·
            refine ⟨11915510574407061833428625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7943673716271374555619083 11915510574407061833428625)
            ·
              refine ⟨8936632930805296375071469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11915510574407061833428625 8936632930805296375071469)
              ·
                refine ⟨3351237349051986140651801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8936632930805296375071469 3351237349051986140651801)
                ·
                  refine ⟨2513428011788989605488851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3351237349051986140651801 2513428011788989605488851)
                  ·
                    refine ⟨3770142017683484408233277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2513428011788989605488851 3770142017683484408233277)
                    ·
                      refine ⟨1413803256631306653087479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3770142017683484408233277 1413803256631306653087479)
                      ·
                        rfl

theorem cell23_2753372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_2753372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2753372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2753372 prefixEnd_2753372 := by exact prefixLift 2753372
  have htrace : WordTrace (prefixWord ++ tailWord_2753372) baseStart_2753372 baseEnd_2753372 := by
    simpa [prefixWord, tailWord_2753372, baseEnd_2753372] using wordTrace_append hprefix tailTrace_2753372
  have hstable : (prefixWord ++ tailWord_2753372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753372).length < 2 ^ (prefixWord ++ tailWord_2753372).sum := by decide
  have hdescent : baseEnd_2753372 < baseStart_2753372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753381 : List Nat := [1, 3, 1, 3, 1, 1, 2, 1, 4, 1, 5]
def baseStart_2753381 : Nat := 118140960795 + 2753381 * 2 ^ 59
def prefixEnd_2753381 : Nat := 4983230072969 + 3 ^ 40 * 2753381 * 2
def baseEnd_2753381 : Nat := 1413807877957197117874937

theorem tailTrace_2753381 : CollatzResearch.WordTrace tailWord_2753381 prefixEnd_2753381 1413807877957197117874937 := by
  unfold tailWord_2753381
  simp only [CollatzResearch.WordTrace]
  refine ⟨100424055237978351882187997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66949370158652234588125331 100424055237978351882187997)
  ·
    refine ⟨37659020714241881955820499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100424055237978351882187997 37659020714241881955820499)
    ·
      refine ⟨56488531071362822933730749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37659020714241881955820499 56488531071362822933730749)
      ·
        refine ⟨21183199151761058600149031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56488531071362822933730749 21183199151761058600149031)
        ·
          refine ⟨31774798727641587900223547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21183199151761058600149031 31774798727641587900223547)
          ·
            refine ⟨47662198091462381850335321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31774798727641587900223547 47662198091462381850335321)
            ·
              refine ⟨35746648568596786387751491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47662198091462381850335321 35746648568596786387751491)
              ·
                refine ⟨53619972852895179581627237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35746648568596786387751491 53619972852895179581627237)
                ·
                  refine ⟨10053744909917846171555107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53619972852895179581627237 10053744909917846171555107)
                  ·
                    refine ⟨15080617364876769257332661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10053744909917846171555107 15080617364876769257332661)
                    ·
                      refine ⟨1413807877957197117874937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15080617364876769257332661 1413807877957197117874937)
                      ·
                        rfl

theorem cell23_2753381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_2753381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2753381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2753381 prefixEnd_2753381 := by exact prefixLift 2753381
  have htrace : WordTrace (prefixWord ++ tailWord_2753381) baseStart_2753381 baseEnd_2753381 := by
    simpa [prefixWord, tailWord_2753381, baseEnd_2753381] using wordTrace_append hprefix tailTrace_2753381
  have hstable : (prefixWord ++ tailWord_2753381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753381).length < 2 ^ (prefixWord ++ tailWord_2753381).sum := by decide
  have hdescent : baseEnd_2753381 < baseStart_2753381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753406 : List Nat := [4, 2, 3, 1, 2, 2, 1, 2, 2, 1, 3]
def baseStart_2753406 : Nat := 118140960795 + 2753406 * 2 ^ 59
def prefixEnd_2753406 : Nat := 4983230072969 + 3 ^ 40 * 2753406 * 2
def baseEnd_2753406 : Nat := 1413820714973559520062323

theorem tailTrace_2753406 : CollatzResearch.WordTrace tailWord_2753406 prefixEnd_2753406 1413820714973559520062323 := by
  unfold tailWord_2753406
  simp only [CollatzResearch.WordTrace]
  refine ⟨12553120882860972643981009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66949978041925187434565381 12553120882860972643981009)
  ·
    refine ⟨9414840662145729482985757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12553120882860972643981009 9414840662145729482985757)
    ·
      refine ⟨3530565248304648556119659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9414840662145729482985757 3530565248304648556119659)
      ·
        refine ⟨5295847872456972834179489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3530565248304648556119659 5295847872456972834179489)
        ·
          refine ⟨3971885904342729625634617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5295847872456972834179489 3971885904342729625634617)
          ·
            refine ⟨2978914428257047219225963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3971885904342729625634617 2978914428257047219225963)
            ·
              refine ⟨4468371642385570828838945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2978914428257047219225963 4468371642385570828838945)
              ·
                refine ⟨3351278731789178121629209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4468371642385570828838945 3351278731789178121629209)
                ·
                  refine ⟨2513459048841883591221907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3351278731789178121629209 2513459048841883591221907)
                  ·
                    refine ⟨3770188573262825386832861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2513459048841883591221907 3770188573262825386832861)
                    ·
                      refine ⟨1413820714973559520062323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3770188573262825386832861 1413820714973559520062323)
                      ·
                        rfl

theorem cell23_2753406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_2753406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2753406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2753406 prefixEnd_2753406 := by exact prefixLift 2753406
  have htrace : WordTrace (prefixWord ++ tailWord_2753406) baseStart_2753406 baseEnd_2753406 := by
    simpa [prefixWord, tailWord_2753406, baseEnd_2753406] using wordTrace_append hprefix tailTrace_2753406
  have hstable : (prefixWord ++ tailWord_2753406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753406).length < 2 ^ (prefixWord ++ tailWord_2753406).sum := by decide
  have hdescent : baseEnd_2753406 < baseStart_2753406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753418 : List Nat := [3, 1, 2, 4, 1, 1, 1, 3, 7]
def baseStart_2753418 : Nat := 118140960795 + 2753418 * 2 ^ 59
def prefixEnd_2753418 : Nat := 4983230072969 + 3 ^ 40 * 2753418 * 2
def baseEnd_2753418 : Nat := 157091875193490385901363

theorem tailTrace_2753418 : CollatzResearch.WordTrace tailWord_2753418 prefixEnd_2753418 157091875193490385901363 := by
  unfold tailWord_2753418
  simp only [CollatzResearch.WordTrace]
  refine ⟨25106351184711076800321227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66950269825896204800856605 25106351184711076800321227)
  ·
    refine ⟨37659526777066615200481841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25106351184711076800321227 37659526777066615200481841)
    ·
      refine ⟨28244645082799961400361381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37659526777066615200481841 28244645082799961400361381)
      ·
        refine ⟨5295870953024992762567759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28244645082799961400361381 5295870953024992762567759)
        ·
          refine ⟨7943806429537489143851639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5295870953024992762567759 7943806429537489143851639)
          ·
            refine ⟨11915709644306233715777459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7943806429537489143851639 11915709644306233715777459)
            ·
              refine ⟨17873564466459350573666189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11915709644306233715777459 17873564466459350573666189)
              ·
                refine ⟨6702586674922256465124821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17873564466459350573666189 6702586674922256465124821)
                ·
                  refine ⟨157091875193490385901363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6702586674922256465124821 157091875193490385901363)
                  ·
                    rfl

theorem cell23_2753418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 7].length) (baseStart_2753418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2753418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2753418 prefixEnd_2753418 := by exact prefixLift 2753418
  have htrace : WordTrace (prefixWord ++ tailWord_2753418) baseStart_2753418 baseEnd_2753418 := by
    simpa [prefixWord, tailWord_2753418, baseEnd_2753418] using wordTrace_append hprefix tailTrace_2753418
  have hstable : (prefixWord ++ tailWord_2753418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753418).length < 2 ^ (prefixWord ++ tailWord_2753418).sum := by decide
  have hdescent : baseEnd_2753418 < baseStart_2753418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753429 : List Nat := [1, 3, 2, 1, 1, 5, 3, 1, 2, 2, 2]
def baseStart_2753429 : Nat := 118140960795 + 2753429 * 2 ^ 59
def prefixEnd_2753429 : Nat := 4983230072969 + 3 ^ 40 * 2753429 * 2
def baseEnd_2753429 : Nat := 1413832525028612930074717

theorem tailTrace_2753429 : CollatzResearch.WordTrace tailWord_2753429 prefixEnd_2753429 1413832525028612930074717 := by
  unfold tailWord_2753429
  simp only [CollatzResearch.WordTrace]
  refine ⟨100425805941804456079935341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66950537294536304053290227 100425805941804456079935341)
  ·
    refine ⟨37659677228176671029975753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100425805941804456079935341 37659677228176671029975753)
    ·
      refine ⟨28244757921132503272481815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37659677228176671029975753 28244757921132503272481815)
      ·
        refine ⟨42367136881698754908722723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28244757921132503272481815 42367136881698754908722723)
        ·
          refine ⟨63550705322548132363084085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42367136881698754908722723 63550705322548132363084085)
          ·
            refine ⟨5957878623988887409039133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63550705322548132363084085 5957878623988887409039133)
            ·
              refine ⟨2234204483995832778389675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5957878623988887409039133 2234204483995832778389675)
              ·
                refine ⟨3351306725993749167584513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2234204483995832778389675 3351306725993749167584513)
                ·
                  refine ⟨2513480044495311875688385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3351306725993749167584513 2513480044495311875688385)
                  ·
                    refine ⟨1885110033371483906766289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2513480044495311875688385 1885110033371483906766289)
                    ·
                      refine ⟨1413832525028612930074717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1885110033371483906766289 1413832525028612930074717)
                      ·
                        rfl

theorem cell23_2753429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 1, 2, 2, 2].length) (baseStart_2753429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2753429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2753429 prefixEnd_2753429 := by exact prefixLift 2753429
  have htrace : WordTrace (prefixWord ++ tailWord_2753429) baseStart_2753429 baseEnd_2753429 := by
    simpa [prefixWord, tailWord_2753429, baseEnd_2753429] using wordTrace_append hprefix tailTrace_2753429
  have hstable : (prefixWord ++ tailWord_2753429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753429).length < 2 ^ (prefixWord ++ tailWord_2753429).sum := by decide
  have hdescent : baseEnd_2753429 < baseStart_2753429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753431 : List Nat := [1, 1, 3, 3, 1, 2, 1, 1, 3, 7]
def baseStart_2753431 : Nat := 118140960795 + 2753431 * 2 ^ 59
def prefixEnd_2753431 : Nat := 4983230072969 + 3 ^ 40 * 2753431 * 2
def baseEnd_2753431 : Nat := 471277850663307307416569

theorem tailTrace_2753431 : CollatzResearch.WordTrace tailWord_2753431 prefixEnd_2753431 471277850663307307416569 := by
  unfold tailWord_2753431
  simp only [CollatzResearch.WordTrace]
  refine ⟨100425878887797210421508147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66950585925198140281005431 100425878887797210421508147)
  ·
    refine ⟨150638818331695815632262221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100425878887797210421508147 150638818331695815632262221)
    ·
      refine ⟨56489556874385930862098333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150638818331695815632262221 56489556874385930862098333)
      ·
        refine ⟨21183583827894724073286875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56489556874385930862098333 21183583827894724073286875)
        ·
          refine ⟨31775375741842086109930313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21183583827894724073286875 31775375741842086109930313)
          ·
            refine ⟨23831531806381564582447735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31775375741842086109930313 23831531806381564582447735)
            ·
              refine ⟨35747297709572346873671603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23831531806381564582447735 35747297709572346873671603)
              ·
                refine ⟨53620946564358520310507405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35747297709572346873671603 53620946564358520310507405)
                ·
                  refine ⟨20107854961634445116440277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53620946564358520310507405 20107854961634445116440277)
                  ·
                    refine ⟨471277850663307307416569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20107854961634445116440277 471277850663307307416569)
                    ·
                      rfl

theorem cell23_2753431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 7].length) (baseStart_2753431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2753431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2753431 prefixEnd_2753431 := by exact prefixLift 2753431
  have htrace : WordTrace (prefixWord ++ tailWord_2753431) baseStart_2753431 baseEnd_2753431 := by
    simpa [prefixWord, tailWord_2753431, baseEnd_2753431] using wordTrace_append hprefix tailTrace_2753431
  have hstable : (prefixWord ++ tailWord_2753431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753431).length < 2 ^ (prefixWord ++ tailWord_2753431).sum := by decide
  have hdescent : baseEnd_2753431 < baseStart_2753431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753471 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 5]
def baseStart_2753471 : Nat := 118140960795 + 2753471 * 2 ^ 59
def prefixEnd_2753471 : Nat := 4983230072969 + 3 ^ 40 * 2753471 * 2
def baseEnd_2753471 : Nat := 1413854091216101765749523

theorem tailTrace_2753471 : CollatzResearch.WordTrace tailWord_2753471 prefixEnd_2753471 1413854091216101765749523 := by
  unfold tailWord_2753471
  simp only [CollatzResearch.WordTrace]
  refine ⟨100427337807652297252964267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66951558538434864835309511 100427337807652297252964267)
  ·
    refine ⟨150641006711478445879446401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100427337807652297252964267 150641006711478445879446401)
    ·
      refine ⟨112980755033608834409584801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150641006711478445879446401 112980755033608834409584801)
      ·
        refine ⟨84735566275206625807188601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112980755033608834409584801 84735566275206625807188601)
        ·
          refine ⟨63551674706404969355391451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84735566275206625807188601 63551674706404969355391451)
          ·
            refine ⟨95327512059607454033087177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63551674706404969355391451 95327512059607454033087177)
            ·
              refine ⟨71495634044705590524815383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95327512059607454033087177 71495634044705590524815383)
              ·
                refine ⟨107243451067058385787223075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71495634044705590524815383 107243451067058385787223075)
                ·
                  refine ⟨160865176600587578680834613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107243451067058385787223075 160865176600587578680834613)
                  ·
                    refine ⟨15081110306305085501328245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 160865176600587578680834613 15081110306305085501328245)
                    ·
                      refine ⟨1413854091216101765749523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15081110306305085501328245 1413854091216101765749523)
                      ·
                        rfl

theorem cell23_2753471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 5].length) (baseStart_2753471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2753471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2753471 prefixEnd_2753471 := by exact prefixLift 2753471
  have htrace : WordTrace (prefixWord ++ tailWord_2753471) baseStart_2753471 baseEnd_2753471 := by
    simpa [prefixWord, tailWord_2753471, baseEnd_2753471] using wordTrace_append hprefix tailTrace_2753471
  have hstable : (prefixWord ++ tailWord_2753471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753471).length < 2 ^ (prefixWord ++ tailWord_2753471).sum := by decide
  have hdescent : baseEnd_2753471 < baseStart_2753471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753488 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 3]
def baseStart_2753488 : Nat := 118140960795 + 2753488 * 2 ^ 59
def prefixEnd_2753488 : Nat := 4983230072969 + 3 ^ 40 * 2753488 * 2
def baseEnd_2753488 : Nat := 1413862820387228199236945

theorem tailTrace_2753488 : CollatzResearch.WordTrace tailWord_2753488 prefixEnd_2753488 1413862820387228199236945 := by
  unfold tailWord_2753488
  simp only [CollatzResearch.WordTrace]
  refine ⟨50213978924295354578166559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66951971899060472770888745 50213978924295354578166559)
  ·
    refine ⟨75320968386443031867249839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50213978924295354578166559 75320968386443031867249839)
    ·
      refine ⟨112981452579664547800874759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75320968386443031867249839 112981452579664547800874759)
      ·
        refine ⟨169472178869496821701312139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112981452579664547800874759 169472178869496821701312139)
        ·
          refine ⟨254208268304245232551968209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169472178869496821701312139 254208268304245232551968209)
          ·
            refine ⟨190656201228183924413976157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 254208268304245232551968209 190656201228183924413976157)
            ·
              refine ⟨71496075460568971655241059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 190656201228183924413976157 71496075460568971655241059)
              ·
                refine ⟨107244113190853457482861589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71496075460568971655241059 107244113190853457482861589)
                ·
                  refine ⟨5027067805821255819509137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 107244113190853457482861589 5027067805821255819509137)
                  ·
                    refine ⟨3770300854365941864631853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5027067805821255819509137 3770300854365941864631853)
                    ·
                      refine ⟨1413862820387228199236945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3770300854365941864631853 1413862820387228199236945)
                      ·
                        rfl

theorem cell23_2753488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 3].length) (baseStart_2753488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2753488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2753488 prefixEnd_2753488 := by exact prefixLift 2753488
  have htrace : WordTrace (prefixWord ++ tailWord_2753488) baseStart_2753488 baseEnd_2753488 := by
    simpa [prefixWord, tailWord_2753488, baseEnd_2753488] using wordTrace_append hprefix tailTrace_2753488
  have hstable : (prefixWord ++ tailWord_2753488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753488).length < 2 ^ (prefixWord ++ tailWord_2753488).sum := by decide
  have hdescent : baseEnd_2753488 < baseStart_2753488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753545 : List Nat := [1, 2, 1, 1, 3, 1, 1, 4, 4, 3, 2]
def baseStart_2753545 : Nat := 118140960795 + 2753545 * 2 ^ 59
def prefixEnd_2753545 : Nat := 4983230072969 + 3 ^ 40 * 2753545 * 2
def baseEnd_2753545 : Nat := 1413892088784534476224183

theorem tailTrace_2753545 : CollatzResearch.WordTrace tailWord_2753545 prefixEnd_2753545 1413892088784534476224183 := by
  unfold tailWord_2753545
  simp only [CollatzResearch.WordTrace]
  refine ⟨100430036809384207891158089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66953357872922805260772059 100430036809384207891158089)
  ·
    refine ⟨75322527607038155918368567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100430036809384207891158089 75322527607038155918368567)
    ·
      refine ⟨112983791410557233877552851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75322527607038155918368567 112983791410557233877552851)
      ·
        refine ⟨169475687115835850816329277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112983791410557233877552851 169475687115835850816329277)
        ·
          refine ⟨63553382668438444056123479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169475687115835850816329277 63553382668438444056123479)
          ·
            refine ⟨95330074002657666084185219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63553382668438444056123479 95330074002657666084185219)
            ·
              refine ⟨142995111003986499126277829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95330074002657666084185219 142995111003986499126277829)
              ·
                refine ⟨26811583313247468586177093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 142995111003986499126277829 26811583313247468586177093)
                ·
                  refine ⟨5027171871233900359908205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26811583313247468586177093 5027171871233900359908205)
                  ·
                    refine ⟨1885189451712712634965577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5027171871233900359908205 1885189451712712634965577)
                    ·
                      refine ⟨1413892088784534476224183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1885189451712712634965577 1413892088784534476224183)
                      ·
                        rfl

theorem cell23_2753545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 4, 3, 2].length) (baseStart_2753545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2753545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2753545 prefixEnd_2753545 := by exact prefixLift 2753545
  have htrace : WordTrace (prefixWord ++ tailWord_2753545) baseStart_2753545 baseEnd_2753545 := by
    simpa [prefixWord, tailWord_2753545, baseEnd_2753545] using wordTrace_append hprefix tailTrace_2753545
  have hstable : (prefixWord ++ tailWord_2753545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753545).length < 2 ^ (prefixWord ++ tailWord_2753545).sum := by decide
  have hdescent : baseEnd_2753545 < baseStart_2753545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753569 : List Nat := [1, 2, 3, 2, 3, 1, 1, 5, 1, 1, 3]
def baseStart_2753569 : Nat := 118140960795 + 2753569 * 2 ^ 59
def prefixEnd_2753569 : Nat := 4983230072969 + 3 ^ 40 * 2753569 * 2
def baseEnd_2753569 : Nat := 1413904412320242382324073

theorem tailTrace_2753569 : CollatzResearch.WordTrace tailWord_2753569 prefixEnd_2753569 1413904412320242382324073 := by
  unfold tailWord_2753569
  simp only [CollatzResearch.WordTrace]
  refine ⟨100430912161297259990031761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66953941440864839993354507 100430912161297259990031761)
  ·
    refine ⟨75323184120972944992523821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100430912161297259990031761 75323184120972944992523821)
    ·
      refine ⟨28246194045364854372196433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75323184120972944992523821 28246194045364854372196433)
      ·
        refine ⟨21184645534023640779147325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28246194045364854372196433 21184645534023640779147325)
        ·
          refine ⟨7944242075258865292180247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21184645534023640779147325 7944242075258865292180247)
          ·
            refine ⟨11916363112888297938270371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7944242075258865292180247 11916363112888297938270371)
            ·
              refine ⟨17874544669332446907405557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11916363112888297938270371 17874544669332446907405557)
              ·
                refine ⟨1675738562749916897569271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17874544669332446907405557 1675738562749916897569271)
                ·
                  refine ⟨2513607844124875346353907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1675738562749916897569271 2513607844124875346353907)
                  ·
                    refine ⟨3770411766187313019530861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2513607844124875346353907 3770411766187313019530861)
                    ·
                      refine ⟨1413904412320242382324073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3770411766187313019530861 1413904412320242382324073)
                      ·
                        rfl

theorem cell23_2753569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 5, 1, 1, 3].length) (baseStart_2753569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2753569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2753569 prefixEnd_2753569 := by exact prefixLift 2753569
  have htrace : WordTrace (prefixWord ++ tailWord_2753569) baseStart_2753569 baseEnd_2753569 := by
    simpa [prefixWord, tailWord_2753569, baseEnd_2753569] using wordTrace_append hprefix tailTrace_2753569
  have hstable : (prefixWord ++ tailWord_2753569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753569).length < 2 ^ (prefixWord ++ tailWord_2753569).sum := by decide
  have hdescent : baseEnd_2753569 < baseStart_2753569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753572 : List Nat := [2, 3, 1, 4, 1, 2, 1, 3, 1, 5]
def baseStart_2753572 : Nat := 118140960795 + 2753572 * 2 ^ 59
def prefixEnd_2753572 : Nat := 4983230072969 + 3 ^ 40 * 2753572 * 2
def baseEnd_2753572 : Nat := 471301984254068623528853

theorem tailTrace_2753572 : CollatzResearch.WordTrace tailWord_2753572 prefixEnd_2753572 471301984254068623528853 := by
  unfold tailWord_2753572
  simp only [CollatzResearch.WordTrace]
  refine ⟨50215510790143195751195485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66954014386857594334927313 50215510790143195751195485)
  ·
    refine ⟨18830816546303698406698307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50215510790143195751195485 18830816546303698406698307)
    ·
      refine ⟨28246224819455547610047461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18830816546303698406698307 28246224819455547610047461)
      ·
        refine ⟨5296167153647915176883899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28246224819455547610047461 5296167153647915176883899)
        ·
          refine ⟨7944250730471872765325849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5296167153647915176883899 7944250730471872765325849)
          ·
            refine ⟨5958188047853904573994387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7944250730471872765325849 5958188047853904573994387)
            ·
              refine ⟨8937282071780856860991581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5958188047853904573994387 8937282071780856860991581)
              ·
                refine ⟨3351480776917821322871843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8937282071780856860991581 3351480776917821322871843)
                ·
                  refine ⟨5027221165376731984307765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3351480776917821322871843 5027221165376731984307765)
                  ·
                    refine ⟨471301984254068623528853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5027221165376731984307765 471301984254068623528853)
                    ·
                      rfl

theorem cell23_2753572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 3, 1, 5].length) (baseStart_2753572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2753572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2753572 prefixEnd_2753572 := by exact prefixLift 2753572
  have htrace : WordTrace (prefixWord ++ tailWord_2753572) baseStart_2753572 baseEnd_2753572 := by
    simpa [prefixWord, tailWord_2753572, baseEnd_2753572] using wordTrace_append hprefix tailTrace_2753572
  have hstable : (prefixWord ++ tailWord_2753572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753572).length < 2 ^ (prefixWord ++ tailWord_2753572).sum := by decide
  have hdescent : baseEnd_2753572 < baseStart_2753572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753585 : List Nat := [1, 2, 2, 3, 1, 2, 3, 1, 4, 4]
def baseStart_2753585 : Nat := 118140960795 + 2753585 * 2 ^ 59
def prefixEnd_2753585 : Nat := 4983230072969 + 3 ^ 40 * 2753585 * 2
def baseEnd_2753585 : Nat := 471304209336904773241333

theorem tailTrace_2753585 : CollatzResearch.WordTrace tailWord_2753585 prefixEnd_2753585 471304209336904773241333 := by
  unfold tailWord_2753585
  simp only [CollatzResearch.WordTrace]
  refine ⟨100431495729239294722614209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66954330486159529815076139 100431495729239294722614209)
  ·
    refine ⟨75323621796929471041960657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100431495729239294722614209 75323621796929471041960657)
    ·
      refine ⟨56492716347697103281470493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75323621796929471041960657 56492716347697103281470493)
      ·
        refine ⟨21184768630386413730551435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56492716347697103281470493 21184768630386413730551435)
        ·
          refine ⟨31777152945579620595827153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21184768630386413730551435 31777152945579620595827153)
          ·
            refine ⟨23832864709184715446870365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31777152945579620595827153 23832864709184715446870365)
            ·
              refine ⟨8937324265944268292576387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23832864709184715446870365 8937324265944268292576387)
              ·
                refine ⟨13405986398916402438864581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8937324265944268292576387 13405986398916402438864581)
                ·
                  refine ⟨2513622449796825457287109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13405986398916402438864581 2513622449796825457287109)
                  ·
                    refine ⟨471304209336904773241333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2513622449796825457287109 471304209336904773241333)
                    ·
                      rfl

theorem cell23_2753585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 4, 4].length) (baseStart_2753585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2753585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2753585 prefixEnd_2753585 := by exact prefixLift 2753585
  have htrace : WordTrace (prefixWord ++ tailWord_2753585) baseStart_2753585 baseEnd_2753585 := by
    simpa [prefixWord, tailWord_2753585, baseEnd_2753585] using wordTrace_append hprefix tailTrace_2753585
  have hstable : (prefixWord ++ tailWord_2753585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753585).length < 2 ^ (prefixWord ++ tailWord_2753585).sum := by decide
  have hdescent : baseEnd_2753585 < baseStart_2753585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753605 : List Nat := [1, 3, 1, 1, 1, 3, 5, 1, 1, 2, 4]
def baseStart_2753605 : Nat := 118140960795 + 2753605 * 2 ^ 59
def prefixEnd_2753605 : Nat := 4983230072969 + 3 ^ 40 * 2753605 * 2
def baseEnd_2753605 : Nat := 1413922897623804241473907

theorem tailTrace_2753605 : CollatzResearch.WordTrace tailWord_2753605 prefixEnd_2753605 1413922897623804241473907 := by
  unfold tailWord_2753605
  simp only [CollatzResearch.WordTrace]
  refine ⟨100432225189166838138342269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66954816792777892092228179 100432225189166838138342269)
  ·
    refine ⟨37662084445937564301878351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100432225189166838138342269 37662084445937564301878351)
    ·
      refine ⟨56493126668906346452817527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37662084445937564301878351 56493126668906346452817527)
      ·
        refine ⟨84739690003359519679226291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56493126668906346452817527 84739690003359519679226291)
        ·
          refine ⟨127109535005039279518839437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84739690003359519679226291 127109535005039279518839437)
          ·
            refine ⟨47666075626889729819564789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127109535005039279518839437 47666075626889729819564789)
            ·
              refine ⟨4468694590020912170584199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47666075626889729819564789 4468694590020912170584199)
              ·
                refine ⟨6703041885031368255876299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4468694590020912170584199 6703041885031368255876299)
                ·
                  refine ⟨10054562827547052383814449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6703041885031368255876299 10054562827547052383814449)
                  ·
                    refine ⟨7540922120660289287860837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10054562827547052383814449 7540922120660289287860837)
                    ·
                      refine ⟨1413922897623804241473907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7540922120660289287860837 1413922897623804241473907)
                      ·
                        rfl

theorem cell23_2753605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 2, 4].length) (baseStart_2753605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2753605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2753605 prefixEnd_2753605 := by exact prefixLift 2753605
  have htrace : WordTrace (prefixWord ++ tailWord_2753605) baseStart_2753605 baseEnd_2753605 := by
    simpa [prefixWord, tailWord_2753605, baseEnd_2753605] using wordTrace_append hprefix tailTrace_2753605
  have hstable : (prefixWord ++ tailWord_2753605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753605).length < 2 ^ (prefixWord ++ tailWord_2753605).sum := by decide
  have hdescent : baseEnd_2753605 < baseStart_2753605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753629 : List Nat := [1, 4, 4, 1, 2, 1, 2, 1, 1, 1, 5]
def baseStart_2753629 : Nat := 118140960795 + 2753629 * 2 ^ 59
def prefixEnd_2753629 : Nat := 4983230072969 + 3 ^ 40 * 2753629 * 2
def baseEnd_2753629 : Nat := 1413935221159512147573797

theorem tailTrace_2753629 : CollatzResearch.WordTrace tailWord_2753629 prefixEnd_2753629 1413935221159512147573797 := by
  unfold tailWord_2753629
  simp only [CollatzResearch.WordTrace]
  refine ⟨100433100541079890237215941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66955400360719926824810627 100433100541079890237215941)
  ·
    refine ⟨18831206351452479419477989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100433100541079890237215941 18831206351452479419477989)
    ·
      refine ⟨3530851190897339891152123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18831206351452479419477989 3530851190897339891152123)
      ·
        refine ⟨5296276786346009836728185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3530851190897339891152123 5296276786346009836728185)
        ·
          refine ⟨3972207589759507377546139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5296276786346009836728185 3972207589759507377546139)
          ·
            refine ⟨5958311384639261066319209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3972207589759507377546139 5958311384639261066319209)
            ·
              refine ⟨4468733538479445799739407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5958311384639261066319209 4468733538479445799739407)
              ·
                refine ⟨6703100307719168699609111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4468733538479445799739407 6703100307719168699609111)
                ·
                  refine ⟨10054650461578753049413667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6703100307719168699609111 10054650461578753049413667)
                  ·
                    refine ⟨15081975692368129574120501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10054650461578753049413667 15081975692368129574120501)
                    ·
                      refine ⟨1413935221159512147573797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15081975692368129574120501 1413935221159512147573797)
                      ·
                        rfl

theorem cell23_2753629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_2753629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2753629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2753629 prefixEnd_2753629 := by exact prefixLift 2753629
  have htrace : WordTrace (prefixWord ++ tailWord_2753629) baseStart_2753629 baseEnd_2753629 := by
    simpa [prefixWord, tailWord_2753629, baseEnd_2753629] using wordTrace_append hprefix tailTrace_2753629
  have hstable : (prefixWord ++ tailWord_2753629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753629).length < 2 ^ (prefixWord ++ tailWord_2753629).sum := by decide
  have hdescent : baseEnd_2753629 < baseStart_2753629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753653 : List Nat := [1, 3, 4, 3, 1, 2, 2, 1, 2, 4]
def baseStart_2753653 : Nat := 118140960795 + 2753653 * 2 ^ 59
def prefixEnd_2753653 : Nat := 4983230072969 + 3 ^ 40 * 2753653 * 2
def baseEnd_2753653 : Nat := 471315848231740017891229

theorem tailTrace_2753653 : CollatzResearch.WordTrace tailWord_2753653 prefixEnd_2753653 471315848231740017891229 := by
  unfold tailWord_2753653
  simp only [CollatzResearch.WordTrace]
  refine ⟨100433975892992942336089613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66955983928661961557393075 100433975892992942336089613)
  ·
    refine ⟨37662740959872353376033605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100433975892992942336089613 37662740959872353376033605)
    ·
      refine ⟨7061763929976066258006301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37662740959872353376033605 7061763929976066258006301)
      ·
        refine ⟨2648161473741024846752363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7061763929976066258006301 2648161473741024846752363)
        ·
          refine ⟨3972242210611537270128545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2648161473741024846752363 3972242210611537270128545)
          ·
            refine ⟨2979181657958652952596409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3972242210611537270128545 2979181657958652952596409)
            ·
              refine ⟨2234386243468989714447307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2979181657958652952596409 2234386243468989714447307)
              ·
                refine ⟨3351579365203484571670961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2234386243468989714447307 3351579365203484571670961)
                ·
                  refine ⟨2513684523902613428753221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3351579365203484571670961 2513684523902613428753221)
                  ·
                    refine ⟨471315848231740017891229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2513684523902613428753221 471315848231740017891229)
                    ·
                      rfl

theorem cell23_2753653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_2753653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2753653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2753653 prefixEnd_2753653 := by exact prefixLift 2753653
  have htrace : WordTrace (prefixWord ++ tailWord_2753653) baseStart_2753653 baseEnd_2753653 := by
    simpa [prefixWord, tailWord_2753653, baseEnd_2753653] using wordTrace_append hprefix tailTrace_2753653
  have hstable : (prefixWord ++ tailWord_2753653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753653).length < 2 ^ (prefixWord ++ tailWord_2753653).sum := by decide
  have hdescent : baseEnd_2753653 < baseStart_2753653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753669 : List Nat := [1, 3, 1, 1, 6, 1, 1, 1, 3, 3, 2]
def baseStart_2753669 : Nat := 118140960795 + 2753669 * 2 ^ 59
def prefixEnd_2753669 : Nat := 4983230072969 + 3 ^ 40 * 2753669 * 2
def baseEnd_2753669 : Nat := 1413955760385691991073613

theorem tailTrace_2753669 : CollatzResearch.WordTrace tailWord_2753669 prefixEnd_2753669 1413955760385691991073613 := by
  unfold tailWord_2753669
  simp only [CollatzResearch.WordTrace]
  refine ⟨100434559460934977068672061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66956372973956651379114707 100434559460934977068672061)
  ·
    refine ⟨37662959797850616400752023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100434559460934977068672061 37662959797850616400752023)
    ·
      refine ⟨56494439696775924601128035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37662959797850616400752023 56494439696775924601128035)
      ·
        refine ⟨84741659545163886901692053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56494439696775924601128035 84741659545163886901692053)
        ·
          refine ⟨3972265291179557198516815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 84741659545163886901692053 3972265291179557198516815)
          ·
            refine ⟨5958397936769335797775223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3972265291179557198516815 5958397936769335797775223)
            ·
              refine ⟨8937596905154003696662835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5958397936769335797775223 8937596905154003696662835)
              ·
                refine ⟨13406395357731005544994253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8937596905154003696662835 13406395357731005544994253)
                ·
                  refine ⟨5027398259149127079372845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13406395357731005544994253 5027398259149127079372845)
                  ·
                    refine ⟨1885274347180922654764817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5027398259149127079372845 1885274347180922654764817)
                    ·
                      refine ⟨1413955760385691991073613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1885274347180922654764817 1413955760385691991073613)
                      ·
                        rfl

theorem cell23_2753669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 3, 3, 2].length) (baseStart_2753669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2753669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2753669 prefixEnd_2753669 := by exact prefixLift 2753669
  have htrace : WordTrace (prefixWord ++ tailWord_2753669) baseStart_2753669 baseEnd_2753669 := by
    simpa [prefixWord, tailWord_2753669, baseEnd_2753669] using wordTrace_append hprefix tailTrace_2753669
  have hstable : (prefixWord ++ tailWord_2753669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753669).length < 2 ^ (prefixWord ++ tailWord_2753669).sum := by decide
  have hdescent : baseEnd_2753669 < baseStart_2753669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753715 : List Nat := [1, 1, 1, 2, 3, 2, 3, 1, 1, 5, 3]
def baseStart_2753715 : Nat := 118140960795 + 2753715 * 2 ^ 59
def prefixEnd_2753715 : Nat := 4983230072969 + 3 ^ 40 * 2753715 * 2
def baseEnd_2753715 : Nat := 1413979380495798811098401

theorem tailTrace_2753715 : CollatzResearch.WordTrace tailWord_2753715 prefixEnd_2753715 1413979380495798811098401 := by
  unfold tailWord_2753715
  simp only [CollatzResearch.WordTrace]
  refine ⟨100436237218768326924846599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66957491479178884616564399 100436237218768326924846599)
  ·
    refine ⟨150654355828152490387269899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100436237218768326924846599 150654355828152490387269899)
    ·
      refine ⟨225981533742228735580904849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150654355828152490387269899 225981533742228735580904849)
      ·
        refine ⟨169486150306671551685678637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225981533742228735580904849 169486150306671551685678637)
        ·
          refine ⟨63557306365001831882129489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169486150306671551685678637 63557306365001831882129489)
          ·
            refine ⟨47667979773751373911597117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63557306365001831882129489 47667979773751373911597117)
            ·
              refine ⟨17875492415156765216848919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47667979773751373911597117 17875492415156765216848919)
              ·
                refine ⟨26813238622735147825273379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17875492415156765216848919 26813238622735147825273379)
                ·
                  refine ⟨40219857934102721737910069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26813238622735147825273379 40219857934102721737910069)
                  ·
                    refine ⟨3770611681322130162929069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40219857934102721737910069 3770611681322130162929069)
                    ·
                      refine ⟨1413979380495798811098401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3770611681322130162929069 1413979380495798811098401)
                      ·
                        rfl

theorem cell23_2753715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 5, 3].length) (baseStart_2753715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2753715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2753715 prefixEnd_2753715 := by exact prefixLift 2753715
  have htrace : WordTrace (prefixWord ++ tailWord_2753715) baseStart_2753715 baseEnd_2753715 := by
    simpa [prefixWord, tailWord_2753715, baseEnd_2753715] using wordTrace_append hprefix tailTrace_2753715
  have hstable : (prefixWord ++ tailWord_2753715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753715).length < 2 ^ (prefixWord ++ tailWord_2753715).sum := by decide
  have hdescent : baseEnd_2753715 < baseStart_2753715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753785 : List Nat := [1, 2, 1, 3, 1, 1, 3, 1, 2, 4, 4]
def baseStart_2753785 : Nat := 118140960795 + 2753785 * 2 ^ 59
def prefixEnd_2753785 : Nat := 4983230072969 + 3 ^ 40 * 2753785 * 2
def baseEnd_2753785 : Nat := 1414015324141613537223079

theorem tailTrace_2753785 : CollatzResearch.WordTrace tailWord_2753785 prefixEnd_2753785 1414015324141613537223079 := by
  unfold tailWord_2753785
  simp only [CollatzResearch.WordTrace]
  refine ⟨100438790328514728879894809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66959193552343152586596539 100438790328514728879894809)
  ·
    refine ⟨75329092746386046659921107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100438790328514728879894809 75329092746386046659921107)
    ·
      refine ⟨112993639119579069989881661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75329092746386046659921107 112993639119579069989881661)
      ·
        refine ⟨42372614669842151246205623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112993639119579069989881661 42372614669842151246205623)
        ·
          refine ⟨63558922004763226869308435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42372614669842151246205623 63558922004763226869308435)
          ·
            refine ⟨95338383007144840303962653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63558922004763226869308435 95338383007144840303962653)
            ·
              refine ⟨35751893627679315113985995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95338383007144840303962653 35751893627679315113985995)
              ·
                refine ⟨53627840441518972670978993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35751893627679315113985995 53627840441518972670978993)
                ·
                  refine ⟨40220880331139229503234245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53627840441518972670978993 40220880331139229503234245)
                  ·
                    refine ⟨7541415062088605531856421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40220880331139229503234245 7541415062088605531856421)
                    ·
                      refine ⟨1414015324141613537223079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7541415062088605531856421 1414015324141613537223079)
                      ·
                        rfl

theorem cell23_2753785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_2753785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2753785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2753785 prefixEnd_2753785 := by exact prefixLift 2753785
  have htrace : WordTrace (prefixWord ++ tailWord_2753785) baseStart_2753785 baseEnd_2753785 := by
    simpa [prefixWord, tailWord_2753785, baseEnd_2753785] using wordTrace_append hprefix tailTrace_2753785
  have hstable : (prefixWord ++ tailWord_2753785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753785).length < 2 ^ (prefixWord ++ tailWord_2753785).sum := by decide
  have hdescent : baseEnd_2753785 < baseStart_2753785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753792 : List Nat := [2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 3]
def baseStart_2753792 : Nat := 118140960795 + 2753792 * 2 ^ 59
def prefixEnd_2753792 : Nat := 4983230072969 + 3 ^ 40 * 2753792 * 2
def baseEnd_2753792 : Nat := 1414018918506195009835547

theorem tailTrace_2753792 : CollatzResearch.WordTrace tailWord_2753792 prefixEnd_2753792 1414018918506195009835547 := by
  unfold tailWord_2753792
  simp only [CollatzResearch.WordTrace]
  refine ⟨50219522819744684537699815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66959363759659579383599753 50219522819744684537699815)
  ·
    refine ⟨75329284229617026806549723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50219522819744684537699815 75329284229617026806549723)
    ·
      refine ⟨112993926344425540209824585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75329284229617026806549723 112993926344425540209824585)
      ·
        refine ⟨84745444758319155157368439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112993926344425540209824585 84745444758319155157368439)
        ·
          refine ⟨127118167137478732736052659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84745444758319155157368439 127118167137478732736052659)
          ·
            refine ⟨190677250706218099104078989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127118167137478732736052659 190677250706218099104078989)
            ·
              refine ⟨71503969014831787164029621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 190677250706218099104078989 71503969014831787164029621)
              ·
                refine ⟨6703497095140480046627777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71503969014831787164029621 6703497095140480046627777)
                ·
                  refine ⟨5027622821355360034970833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6703497095140480046627777 5027622821355360034970833)
                  ·
                    refine ⟨3770717116016520026228125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5027622821355360034970833 3770717116016520026228125)
                    ·
                      refine ⟨1414018918506195009835547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3770717116016520026228125 1414018918506195009835547)
                      ·
                        rfl

theorem cell23_2753792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 3].length) (baseStart_2753792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2753792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2753792 prefixEnd_2753792 := by exact prefixLift 2753792
  have htrace : WordTrace (prefixWord ++ tailWord_2753792) baseStart_2753792 baseEnd_2753792 := by
    simpa [prefixWord, tailWord_2753792, baseEnd_2753792] using wordTrace_append hprefix tailTrace_2753792
  have hstable : (prefixWord ++ tailWord_2753792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753792).length < 2 ^ (prefixWord ++ tailWord_2753792).sum := by decide
  have hdescent : baseEnd_2753792 < baseStart_2753792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753795 : List Nat := [1, 1, 1, 3, 2, 4, 1, 2, 8]
def baseStart_2753795 : Nat := 118140960795 + 2753795 * 2 ^ 59
def prefixEnd_2753795 : Nat := 4983230072969 + 3 ^ 40 * 2753795 * 2
def baseEnd_2753795 : Nat := 157113384327573166455337

theorem tailTrace_2753795 : CollatzResearch.WordTrace tailWord_2753795 prefixEnd_2753795 157113384327573166455337 := by
  unfold tailWord_2753795
  simp only [CollatzResearch.WordTrace]
  refine ⟨100439155058478500587758839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66959436705652333725172559 100439155058478500587758839)
  ·
    refine ⟨150658732587717750881638259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100439155058478500587758839 150658732587717750881638259)
    ·
      refine ⟨225988098881576626322457389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150658732587717750881638259 225988098881576626322457389)
      ·
        refine ⟨84745537080591234870921521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 225988098881576626322457389 84745537080591234870921521)
        ·
          refine ⟨63559152810443426153191141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84745537080591234870921521 63559152810443426153191141)
          ·
            refine ⟨11917341151958142403723339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63559152810443426153191141 11917341151958142403723339)
            ·
              refine ⟨17876011727937213605585009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11917341151958142403723339 17876011727937213605585009)
              ·
                refine ⟨13407008795952910204188757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17876011727937213605585009 13407008795952910204188757)
                ·
                  refine ⟨157113384327573166455337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13407008795952910204188757 157113384327573166455337)
                  ·
                    rfl

theorem cell23_2753795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 8].length) (baseStart_2753795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2753795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2753795 prefixEnd_2753795 := by exact prefixLift 2753795
  have htrace : WordTrace (prefixWord ++ tailWord_2753795) baseStart_2753795 baseEnd_2753795 := by
    simpa [prefixWord, tailWord_2753795, baseEnd_2753795] using wordTrace_append hprefix tailTrace_2753795
  have hstable : (prefixWord ++ tailWord_2753795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753795).length < 2 ^ (prefixWord ++ tailWord_2753795).sum := by decide
  have hdescent : baseEnd_2753795 < baseStart_2753795 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753825 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 2, 9]
def baseStart_2753825 : Nat := 118140960795 + 2753825 * 2 ^ 59
def prefixEnd_2753825 : Nat := 4983230072969 + 3 ^ 40 * 2753825 * 2
def baseEnd_2753825 : Nat := 471345287789264460240965

theorem tailTrace_2753825 : CollatzResearch.WordTrace tailWord_2753825 prefixEnd_2753825 471345287789264460240965 := by
  unfold tailWord_2753825
  simp only [CollatzResearch.WordTrace]
  refine ⟨100440249248369815711350929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66960166165579877140900619 100440249248369815711350929)
  ·
    refine ⟨75330186936277361783513197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100440249248369815711350929 75330186936277361783513197)
    ·
      refine ⟨28248820101104010668817449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75330186936277361783513197 28248820101104010668817449)
      ·
        refine ⟨21186615075828008001613087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28248820101104010668817449 21186615075828008001613087)
        ·
          refine ⟨31779922613742012002419631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21186615075828008001613087 31779922613742012002419631)
          ·
            refine ⟨47669883920613018003629447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31779922613742012002419631 47669883920613018003629447)
            ·
              refine ⟨71504825880919527005444171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47669883920613018003629447 71504825880919527005444171)
              ·
                refine ⟨107257238821379290508166257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71504825880919527005444171 107257238821379290508166257)
                ·
                  refine ⟨80442929116034467881124693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107257238821379290508166257 80442929116034467881124693)
                  ·
                    refine ⟨471345287789264460240965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 80442929116034467881124693 471345287789264460240965)
                    ·
                      rfl

theorem cell23_2753825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 9].length) (baseStart_2753825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2753825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2753825 prefixEnd_2753825 := by exact prefixLift 2753825
  have htrace : WordTrace (prefixWord ++ tailWord_2753825) baseStart_2753825 baseEnd_2753825 := by
    simpa [prefixWord, tailWord_2753825, baseEnd_2753825] using wordTrace_append hprefix tailTrace_2753825
  have hstable : (prefixWord ++ tailWord_2753825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753825).length < 2 ^ (prefixWord ++ tailWord_2753825).sum := by decide
  have hdescent : baseEnd_2753825 < baseStart_2753825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753829 : List Nat := [1, 3, 1, 2, 4, 1, 4, 1, 6]
def baseStart_2753829 : Nat := 118140960795 + 2753829 * 2 ^ 59
def prefixEnd_2753829 : Nat := 4983230072969 + 3 ^ 40 * 2753829 * 2
def baseEnd_2753829 : Nat := 157115324143379040563653

theorem tailTrace_2753829 : CollatzResearch.WordTrace tailWord_2753829 prefixEnd_2753829 157115324143379040563653 := by
  unfold tailWord_2753829
  simp only [CollatzResearch.WordTrace]
  refine ⟨100440395140355324394496541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66960263426903549596331027 100440395140355324394496541)
  ·
    refine ⟨37665148177633246647936203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100440395140355324394496541 37665148177633246647936203)
    ·
      refine ⟨56497722266449869971904305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37665148177633246647936203 56497722266449869971904305)
      ·
        refine ⟨42373291699837402478928229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56497722266449869971904305 42373291699837402478928229)
        ·
          refine ⟨7944992193719512964799043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42373291699837402478928229 7944992193719512964799043)
          ·
            refine ⟨11917488290579269447198565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7944992193719512964799043 11917488290579269447198565)
            ·
              refine ⟨2234529054483613021349731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11917488290579269447198565 2234529054483613021349731)
              ·
                refine ⟨3351793581725419532024597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2234529054483613021349731 3351793581725419532024597)
                ·
                  refine ⟨157115324143379040563653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3351793581725419532024597 157115324143379040563653)
                  ·
                    rfl

theorem cell23_2753829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 1, 6].length) (baseStart_2753829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2753829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2753829 prefixEnd_2753829 := by exact prefixLift 2753829
  have htrace : WordTrace (prefixWord ++ tailWord_2753829) baseStart_2753829 baseEnd_2753829 := by
    simpa [prefixWord, tailWord_2753829, baseEnd_2753829] using wordTrace_append hprefix tailTrace_2753829
  have hstable : (prefixWord ++ tailWord_2753829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753829).length < 2 ^ (prefixWord ++ tailWord_2753829).sum := by decide
  have hdescent : baseEnd_2753829 < baseStart_2753829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753856 : List Nat := [2, 1, 1, 2, 2, 1, 4, 5, 1, 1, 3]
def baseStart_2753856 : Nat := 118140960795 + 2753856 * 2 ^ 59
def prefixEnd_2753856 : Nat := 4983230072969 + 3 ^ 40 * 2753856 * 2
def baseEnd_2753856 : Nat := 1414051781268082759435253

theorem tailTrace_2753856 : CollatzResearch.WordTrace tailWord_2753856 prefixEnd_2753856 1414051781268082759435253 := by
  unfold tailWord_2753856
  simp only [CollatzResearch.WordTrace]
  refine ⟨50220689955628754002864711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66960919940838338670486281 50220689955628754002864711)
  ·
    refine ⟨75331034933443131004297067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50220689955628754002864711 75331034933443131004297067)
    ·
      refine ⟨112996552400164696506445601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75331034933443131004297067 112996552400164696506445601)
      ·
        refine ⟨84747414300123522379834201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112996552400164696506445601 84747414300123522379834201)
        ·
          refine ⟨63560560725092641784875651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84747414300123522379834201 63560560725092641784875651)
          ·
            refine ⟨95340841087638962677313477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63560560725092641784875651 95340841087638962677313477)
            ·
              refine ⟨17876407703932305501996277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95340841087638962677313477 17876407703932305501996277)
              ·
                refine ⟨1675913222243653640812151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17876407703932305501996277 1675913222243653640812151)
                ·
                  refine ⟨2513869833365480461218227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1675913222243653640812151 2513869833365480461218227)
                  ·
                    refine ⟨3770804750048220691827341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2513869833365480461218227 3770804750048220691827341)
                    ·
                      refine ⟨1414051781268082759435253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3770804750048220691827341 1414051781268082759435253)
                      ·
                        rfl

theorem cell23_2753856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 5, 1, 1, 3].length) (baseStart_2753856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2753856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2753856 prefixEnd_2753856 := by exact prefixLift 2753856
  have htrace : WordTrace (prefixWord ++ tailWord_2753856) baseStart_2753856 baseEnd_2753856 := by
    simpa [prefixWord, tailWord_2753856, baseEnd_2753856] using wordTrace_append hprefix tailTrace_2753856
  have hstable : (prefixWord ++ tailWord_2753856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753856).length < 2 ^ (prefixWord ++ tailWord_2753856).sum := by decide
  have hdescent : baseEnd_2753856 < baseStart_2753856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753882 : List Nat := [3, 1, 1, 2, 1, 2, 2, 4, 1, 1, 5]
def baseStart_2753882 : Nat := 118140960795 + 2753882 * 2 ^ 59
def prefixEnd_2753882 : Nat := 4983230072969 + 3 ^ 40 * 2753882 * 2
def baseEnd_2753882 : Nat := 1414065131765099657710133

theorem tailTrace_2753882 : CollatzResearch.WordTrace tailWord_2753882 prefixEnd_2753882 1414065131765099657710133 := by
  unfold tailWord_2753882
  simp only [CollatzResearch.WordTrace]
  refine ⟨25110582052290828611543975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66961552139442209630783933 25110582052290828611543975)
  ·
    refine ⟨37665873078436242917315963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25110582052290828611543975 37665873078436242917315963)
    ·
      refine ⟨56498809617654364375973945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37665873078436242917315963 56498809617654364375973945)
      ·
        refine ⟨42374107213240773281980459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56498809617654364375973945 42374107213240773281980459)
        ·
          refine ⟨63561160819861159922970689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42374107213240773281980459 63561160819861159922970689)
          ·
            refine ⟨47670870614895869942228017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63561160819861159922970689 47670870614895869942228017)
            ·
              refine ⟨35753152961171902456671013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47670870614895869942228017 35753152961171902456671013)
              ·
                refine ⟨6703716180219731710625815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35753152961171902456671013 6703716180219731710625815)
                ·
                  refine ⟨10055574270329597565938723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6703716180219731710625815 10055574270329597565938723)
                  ·
                    refine ⟨15083361405494396348908085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10055574270329597565938723 15083361405494396348908085)
                    ·
                      refine ⟨1414065131765099657710133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15083361405494396348908085 1414065131765099657710133)
                      ·
                        rfl

theorem cell23_2753882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_2753882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2753882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2753882 prefixEnd_2753882 := by exact prefixLift 2753882
  have htrace : WordTrace (prefixWord ++ tailWord_2753882) baseStart_2753882 baseEnd_2753882 := by
    simpa [prefixWord, tailWord_2753882, baseEnd_2753882] using wordTrace_append hprefix tailTrace_2753882
  have hstable : (prefixWord ++ tailWord_2753882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753882).length < 2 ^ (prefixWord ++ tailWord_2753882).sum := by decide
  have hdescent : baseEnd_2753882 < baseStart_2753882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753913 : List Nat := [1, 2, 1, 3, 2, 1, 3, 5, 1, 2, 2]
def baseStart_2753913 : Nat := 118140960795 + 2753913 * 2 ^ 59
def prefixEnd_2753913 : Nat := 4983230072969 + 3 ^ 40 * 2753913 * 2
def baseEnd_2753913 : Nat := 1414081049665389036422491

theorem tailTrace_2753913 : CollatzResearch.WordTrace tailWord_2753913 prefixEnd_2753913 1414081049665389036422491 := by
  unfold tailWord_2753913
  simp only [CollatzResearch.WordTrace]
  refine ⟨100443458872051006740554393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66962305914700671160369595 100443458872051006740554393)
  ·
    refine ⟨75332594154038255055415795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100443458872051006740554393 75332594154038255055415795)
    ·
      refine ⟨112998891231057382583123693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75332594154038255055415795 112998891231057382583123693)
      ·
        refine ⟨42374584211646518468671385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112998891231057382583123693 42374584211646518468671385)
        ·
          refine ⟨31780938158734888851503539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42374584211646518468671385 31780938158734888851503539)
          ·
            refine ⟨47671407238102333277255309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31780938158734888851503539 47671407238102333277255309)
            ·
              refine ⟨17876777714288374978970741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47671407238102333277255309 17876777714288374978970741)
              ·
                refine ⟨1675947910714535154278507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17876777714288374978970741 1675947910714535154278507)
                ·
                  refine ⟨2513921866071802731417761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1675947910714535154278507 2513921866071802731417761)
                  ·
                    refine ⟨1885441399553852048563321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2513921866071802731417761 1885441399553852048563321)
                    ·
                      refine ⟨1414081049665389036422491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1885441399553852048563321 1414081049665389036422491)
                      ·
                        rfl

theorem cell23_2753913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 5, 1, 2, 2].length) (baseStart_2753913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2753913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2753913 prefixEnd_2753913 := by exact prefixLift 2753913
  have htrace : WordTrace (prefixWord ++ tailWord_2753913) baseStart_2753913 baseEnd_2753913 := by
    simpa [prefixWord, tailWord_2753913, baseEnd_2753913] using wordTrace_append hprefix tailTrace_2753913
  have hstable : (prefixWord ++ tailWord_2753913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753913).length < 2 ^ (prefixWord ++ tailWord_2753913).sum := by decide
  have hdescent : baseEnd_2753913 < baseStart_2753913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753950 : List Nat := [4, 3, 1, 2, 2, 1, 2, 2, 1, 2, 3]
def baseStart_2753950 : Nat := 118140960795 + 2753950 * 2 ^ 59
def prefixEnd_2753950 : Nat := 4983230072969 + 3 ^ 40 * 2753950 * 2
def baseEnd_2753950 : Nat := 1414100048449605391659821

theorem tailTrace_2753950 : CollatzResearch.WordTrace tailWord_2753950 prefixEnd_2753950 1414100048449605391659821 := by
  unfold tailWord_2753950
  simp only [CollatzResearch.WordTrace]
  refine ⟨12555601046614620257456413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66963205581944641373100869 12555601046614620257456413)
  ·
    refine ⟨4708350392480482596546155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12555601046614620257456413 4708350392480482596546155)
    ·
      refine ⟨7062525588720723894819233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4708350392480482596546155 7062525588720723894819233)
      ·
        refine ⟨5296894191540542921114425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7062525588720723894819233 5296894191540542921114425)
        ·
          refine ⟨3972670643655407190835819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5296894191540542921114425 3972670643655407190835819)
          ·
            refine ⟨5959005965483110786253729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3972670643655407190835819 5959005965483110786253729)
            ·
              refine ⟨4469254474112333089690297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5959005965483110786253729 4469254474112333089690297)
              ·
                refine ⟨3351940855584249817267723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4469254474112333089690297 3351940855584249817267723)
                ·
                  refine ⟨5027911283376374725901585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3351940855584249817267723 5027911283376374725901585)
                  ·
                    refine ⟨3770933462532281044426189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5027911283376374725901585 3770933462532281044426189)
                    ·
                      refine ⟨1414100048449605391659821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3770933462532281044426189 1414100048449605391659821)
                      ·
                        rfl

theorem cell23_2753950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_2753950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2753950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2753950 prefixEnd_2753950 := by exact prefixLift 2753950
  have htrace : WordTrace (prefixWord ++ tailWord_2753950) baseStart_2753950 baseEnd_2753950 := by
    simpa [prefixWord, tailWord_2753950, baseEnd_2753950] using wordTrace_append hprefix tailTrace_2753950
  have hstable : (prefixWord ++ tailWord_2753950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753950).length < 2 ^ (prefixWord ++ tailWord_2753950).sum := by decide
  have hdescent : baseEnd_2753950 < baseStart_2753950 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753973 : List Nat := [1, 3, 3, 2, 2, 1, 2, 3, 1, 3, 2]
def baseStart_2753973 : Nat := 118140960795 + 2753973 * 2 ^ 59
def prefixEnd_2753973 : Nat := 4983230072969 + 3 ^ 40 * 2753973 * 2
def baseEnd_2753973 : Nat := 1414111858504658801672215

theorem tailTrace_2753973 : CollatzResearch.WordTrace tailWord_2753973 prefixEnd_2753973 1414111858504658801672215 := by
  unfold tailWord_2753973
  simp only [CollatzResearch.WordTrace]
  refine ⟨100445647251833636987738573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66963764834555757991825715 100445647251833636987738573)
  ·
    refine ⟨37667117719437613870401965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100445647251833636987738573 37667117719437613870401965)
    ·
      refine ⟨14125169144789105201400737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37667117719437613870401965 14125169144789105201400737)
      ·
        refine ⟨10593876858591828901050553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14125169144789105201400737 10593876858591828901050553)
        ·
          refine ⟨7945407643943871675787915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10593876858591828901050553 7945407643943871675787915)
          ·
            refine ⟨11918111465915807513681873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7945407643943871675787915 11918111465915807513681873)
            ·
              refine ⟨8938583599436855635261405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11918111465915807513681873 8938583599436855635261405)
              ·
                refine ⟨3351968849788820863223027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8938583599436855635261405 3351968849788820863223027)
                ·
                  refine ⟨5027953274683231294834541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3351968849788820863223027 5027953274683231294834541)
                  ·
                    refine ⟨1885482478006211735562953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5027953274683231294834541 1885482478006211735562953)
                    ·
                      refine ⟨1414111858504658801672215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1885482478006211735562953 1414111858504658801672215)
                      ·
                        rfl

theorem cell23_2753973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_2753973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2753973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2753973 prefixEnd_2753973 := by exact prefixLift 2753973
  have htrace : WordTrace (prefixWord ++ tailWord_2753973) baseStart_2753973 baseEnd_2753973 := by
    simpa [prefixWord, tailWord_2753973, baseEnd_2753973] using wordTrace_append hprefix tailTrace_2753973
  have hstable : (prefixWord ++ tailWord_2753973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753973).length < 2 ^ (prefixWord ++ tailWord_2753973).sum := by decide
  have hdescent : baseEnd_2753973 < baseStart_2753973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754006 : List Nat := [5, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5]
def baseStart_2754006 : Nat := 118140960795 + 2754006 * 2 ^ 59
def prefixEnd_2754006 : Nat := 4983230072969 + 3 ^ 40 * 2754006 * 2
def baseEnd_2754006 : Nat := 1414128803366257172559563

theorem tailTrace_2754006 : CollatzResearch.WordTrace tailWord_2754006 prefixEnd_2754006 1414128803366257172559563 := by
  unfold tailWord_2754006
  simp only [CollatzResearch.WordTrace]
  refine ⟨6277928178794630226480617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66964567240476055749126581 6277928178794630226480617)
  ·
    refine ⟨4708446134095972669860463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6277928178794630226480617 4708446134095972669860463)
    ·
      refine ⟨7062669201143959004790695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4708446134095972669860463 7062669201143959004790695)
      ·
        refine ⟨10594003801715938507186043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7062669201143959004790695 10594003801715938507186043)
        ·
          refine ⟨15891005702573907760779065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10594003801715938507186043 15891005702573907760779065)
          ·
            refine ⟨11918254276930430820584299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15891005702573907760779065 11918254276930430820584299)
            ·
              refine ⟨17877381415395646230876449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11918254276930430820584299 17877381415395646230876449)
              ·
                refine ⟨13408036061546734673157337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17877381415395646230876449 13408036061546734673157337)
                ·
                  refine ⟨10056027046160051004868003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13408036061546734673157337 10056027046160051004868003)
                  ·
                    refine ⟨15084040569240076507302005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10056027046160051004868003 15084040569240076507302005)
                    ·
                      refine ⟨1414128803366257172559563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15084040569240076507302005 1414128803366257172559563)
                      ·
                        rfl

theorem cell23_2754006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_2754006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2754006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2754006 prefixEnd_2754006 := by exact prefixLift 2754006
  have htrace : WordTrace (prefixWord ++ tailWord_2754006) baseStart_2754006 baseEnd_2754006 := by
    simpa [prefixWord, tailWord_2754006, baseEnd_2754006] using wordTrace_append hprefix tailTrace_2754006
  have hstable : (prefixWord ++ tailWord_2754006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754006).length < 2 ^ (prefixWord ++ tailWord_2754006).sum := by decide
  have hdescent : baseEnd_2754006 < baseStart_2754006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754037 : List Nat := [1, 3, 5, 1, 1, 2, 2, 2, 2, 2, 2]
def baseStart_2754037 : Nat := 118140960795 + 2754037 * 2 ^ 59
def prefixEnd_2754037 : Nat := 4983230072969 + 3 ^ 40 * 2754037 * 2
def baseEnd_2754037 : Nat := 1414144721266546551271921

theorem tailTrace_2754037 : CollatzResearch.WordTrace tailWord_2754037 prefixEnd_2754037 1414144721266546551271921 := by
  unfold tailWord_2754037
  simp only [CollatzResearch.WordTrace]
  refine ⟨100447981523601775918068365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66965321015734517278712243 100447981523601775918068365)
  ·
    refine ⟨37667993071350665969275637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100447981523601775918068365 37667993071350665969275637)
    ·
      refine ⟨3531374350439124934619591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37667993071350665969275637 3531374350439124934619591)
      ·
        refine ⟨5297061525658687401929387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3531374350439124934619591 5297061525658687401929387)
        ·
          refine ⟨7945592288488031102894081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5297061525658687401929387 7945592288488031102894081)
          ·
            refine ⟨5959194216366023327170561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7945592288488031102894081 5959194216366023327170561)
            ·
              refine ⟨4469395662274517495377921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5959194216366023327170561 4469395662274517495377921)
              ·
                refine ⟨3352046746705888121533441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4469395662274517495377921 3352046746705888121533441)
                ·
                  refine ⟨2514035060029416091150081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3352046746705888121533441 2514035060029416091150081)
                  ·
                    refine ⟨1885526295022062068362561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2514035060029416091150081 1885526295022062068362561)
                    ·
                      refine ⟨1414144721266546551271921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1885526295022062068362561 1414144721266546551271921)
                      ·
                        rfl

theorem cell23_2754037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_2754037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2754037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2754037 prefixEnd_2754037 := by exact prefixLift 2754037
  have htrace : WordTrace (prefixWord ++ tailWord_2754037) baseStart_2754037 baseEnd_2754037 := by
    simpa [prefixWord, tailWord_2754037, baseEnd_2754037] using wordTrace_append hprefix tailTrace_2754037
  have hstable : (prefixWord ++ tailWord_2754037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754037).length < 2 ^ (prefixWord ++ tailWord_2754037).sum := by decide
  have hdescent : baseEnd_2754037 < baseStart_2754037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754054 : List Nat := [6, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2]
def baseStart_2754054 : Nat := 118140960795 + 2754054 * 2 ^ 59
def prefixEnd_2754054 : Nat := 4983230072969 + 3 ^ 40 * 2754054 * 2
def baseEnd_2754054 : Nat := 1414153450437672984759343

theorem tailTrace_2754054 : CollatzResearch.WordTrace tailWord_2754054 prefixEnd_2754054 1414153450437672984759343 := by
  unfold tailWord_2754054
  simp only [CollatzResearch.WordTrace]
  refine ⟨3139018798891880869419913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 66965734376360125214291477 3139018798891880869419913)
  ·
    refine ⟨2354264099168910652064935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3139018798891880869419913 2354264099168910652064935)
    ·
      refine ⟨3531396148753365978097403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2354264099168910652064935 3531396148753365978097403)
      ·
        refine ⟨5297094223130048967146105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3531396148753365978097403 5297094223130048967146105)
        ·
          refine ⟨3972820667347536725359579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5297094223130048967146105 3972820667347536725359579)
          ·
            refine ⟨5959231001021305088039369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3972820667347536725359579 5959231001021305088039369)
            ·
              refine ⟨4469423250765978816029527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5959231001021305088039369 4469423250765978816029527)
              ·
                refine ⟨6704134876148968224044291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4469423250765978816029527 6704134876148968224044291)
                ·
                  refine ⟨10056202314223452336066437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6704134876148968224044291 10056202314223452336066437)
                  ·
                    refine ⟨1885537933916897313012457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10056202314223452336066437 1885537933916897313012457)
                    ·
                      refine ⟨1414153450437672984759343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1885537933916897313012457 1414153450437672984759343)
                      ·
                        rfl

theorem cell23_2754054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_2754054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2754054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2754054 prefixEnd_2754054 := by exact prefixLift 2754054
  have htrace : WordTrace (prefixWord ++ tailWord_2754054) baseStart_2754054 baseEnd_2754054 := by
    simpa [prefixWord, tailWord_2754054, baseEnd_2754054] using wordTrace_append hprefix tailTrace_2754054
  have hstable : (prefixWord ++ tailWord_2754054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754054).length < 2 ^ (prefixWord ++ tailWord_2754054).sum := by decide
  have hdescent : baseEnd_2754054 < baseStart_2754054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754076 : List Nat := [2, 2, 3, 1, 2, 1, 1, 2, 1, 6, 2]
def baseStart_2754076 : Nat := 118140960795 + 2754076 * 2 ^ 59
def prefixEnd_2754076 : Nat := 4983230072969 + 3 ^ 40 * 2754076 * 2
def baseEnd_2754076 : Nat := 1414164747012071898684241

theorem tailTrace_2754076 : CollatzResearch.WordTrace tailWord_2754076 prefixEnd_2754076 1414164747012071898684241 := by
  unfold tailWord_2754076
  simp only [CollatzResearch.WordTrace]
  refine ⟨50224701985230242789369041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66966269313640323719158721 50224701985230242789369041)
  ·
    refine ⟨37668526488922682092026781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50224701985230242789369041 37668526488922682092026781)
    ·
      refine ⟨14125697433346005784510043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37668526488922682092026781 14125697433346005784510043)
      ·
        refine ⟨21188546150019008676765065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14125697433346005784510043 21188546150019008676765065)
        ·
          refine ⟨15891409612514256507573799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21188546150019008676765065 15891409612514256507573799)
          ·
            refine ⟨23837114418771384761360699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15891409612514256507573799 23837114418771384761360699)
            ·
              refine ⟨35755671628157077142041049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23837114418771384761360699 35755671628157077142041049)
              ·
                refine ⟨26816753721117807856530787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35755671628157077142041049 26816753721117807856530787)
                ·
                  refine ⟨40225130581676711784796181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26816753721117807856530787 40225130581676711784796181)
                  ·
                    refine ⟨1885552996016095864912321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 40225130581676711784796181 1885552996016095864912321)
                    ·
                      refine ⟨1414164747012071898684241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1885552996016095864912321 1414164747012071898684241)
                      ·
                        rfl

theorem cell23_2754076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 1, 6, 2].length) (baseStart_2754076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2754076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2754076 prefixEnd_2754076 := by exact prefixLift 2754076
  have htrace : WordTrace (prefixWord ++ tailWord_2754076) baseStart_2754076 baseEnd_2754076 := by
    simpa [prefixWord, tailWord_2754076, baseEnd_2754076] using wordTrace_append hprefix tailTrace_2754076
  have hstable : (prefixWord ++ tailWord_2754076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754076).length < 2 ^ (prefixWord ++ tailWord_2754076).sum := by decide
  have hdescent : baseEnd_2754076 < baseStart_2754076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754099 : List Nat := [1, 1, 1, 2, 4, 4, 1, 1, 8]
def baseStart_2754099 : Nat := 118140960795 + 2754099 * 2 ^ 59
def prefixEnd_2754099 : Nat := 4983230072969 + 3 ^ 40 * 2754099 * 2
def baseEnd_2754099 : Nat := 157130728563013923188515

theorem tailTrace_2754099 : CollatzResearch.WordTrace tailWord_2754099 prefixEnd_2754099 157130728563013923188515 := by
  unfold tailWord_2754099
  simp only [CollatzResearch.WordTrace]
  refine ⟨100450242849377160506825351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66966828566251440337883567 100450242849377160506825351)
  ·
    refine ⟨150675364274065740760238027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100450242849377160506825351 150675364274065740760238027)
    ·
      refine ⟨226013046411098611140357041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150675364274065740760238027 226013046411098611140357041)
      ·
        refine ⟨169509784808323958355267781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226013046411098611140357041 169509784808323958355267781)
        ·
          refine ⟨31783084651560742191612709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 169509784808323958355267781 31783084651560742191612709)
          ·
            refine ⟨5959328372167639160927383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31783084651560742191612709 5959328372167639160927383)
            ·
              refine ⟨8938992558251458741391075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5959328372167639160927383 8938992558251458741391075)
              ·
                refine ⟨13408488837377188112086613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8938992558251458741391075 13408488837377188112086613)
                ·
                  refine ⟨157130728563013923188515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13408488837377188112086613 157130728563013923188515)
                  ·
                    rfl

theorem cell23_2754099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 8].length) (baseStart_2754099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2754099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2754099 prefixEnd_2754099 := by exact prefixLift 2754099
  have htrace : WordTrace (prefixWord ++ tailWord_2754099) baseStart_2754099 baseEnd_2754099 := by
    simpa [prefixWord, tailWord_2754099, baseEnd_2754099] using wordTrace_append hprefix tailTrace_2754099
  have hstable : (prefixWord ++ tailWord_2754099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754099).length < 2 ^ (prefixWord ++ tailWord_2754099).sum := by decide
  have hdescent : baseEnd_2754099 < baseStart_2754099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754103 : List Nat := [1, 1, 3, 1, 2, 4, 2, 4, 1, 4]
def baseStart_2754103 : Nat := 118140960795 + 2754103 * 2 ^ 59
def prefixEnd_2754103 : Nat := 4983230072969 + 3 ^ 40 * 2754103 * 2
def baseEnd_2754103 : Nat := 471392870329914431015539

theorem tailTrace_2754103 : CollatzResearch.WordTrace tailWord_2754103 prefixEnd_2754103 471392870329914431015539 := by
  unfold tailWord_2754103
  simp only [CollatzResearch.WordTrace]
  refine ⟨100450388741362669189970963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66966925827575112793313975 100450388741362669189970963)
  ·
    refine ⟨150675583112044003784956445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100450388741362669189970963 150675583112044003784956445)
    ·
      refine ⟨56503343667016501419358667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150675583112044003784956445 56503343667016501419358667)
      ·
        refine ⟨84755015500524752129038001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56503343667016501419358667 84755015500524752129038001)
        ·
          refine ⟨63566261625393564096778501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84755015500524752129038001 63566261625393564096778501)
          ·
            refine ⟨11918674054761293268145969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63566261625393564096778501 11918674054761293268145969)
            ·
              refine ⟨8939005541070969951109477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11918674054761293268145969 8939005541070969951109477)
              ·
                refine ⟨1676063538950806865833027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8939005541070969951109477 1676063538950806865833027)
                ·
                  refine ⟨2514095308426210298749541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1676063538950806865833027 2514095308426210298749541)
                  ·
                    refine ⟨471392870329914431015539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2514095308426210298749541 471392870329914431015539)
                    ·
                      rfl

theorem cell23_2754103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 4, 1, 4].length) (baseStart_2754103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2754103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2754103 prefixEnd_2754103 := by exact prefixLift 2754103
  have htrace : WordTrace (prefixWord ++ tailWord_2754103) baseStart_2754103 baseEnd_2754103 := by
    simpa [prefixWord, tailWord_2754103, baseEnd_2754103] using wordTrace_append hprefix tailTrace_2754103
  have hstable : (prefixWord ++ tailWord_2754103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754103).length < 2 ^ (prefixWord ++ tailWord_2754103).sum := by decide
  have hdescent : baseEnd_2754103 < baseStart_2754103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754160 : List Nat := [2, 1, 1, 1, 6, 3, 1, 1, 3, 1, 3]
def baseStart_2754160 : Nat := 118140960795 + 2754160 * 2 ^ 59
def prefixEnd_2754160 : Nat := 4983230072969 + 3 ^ 40 * 2754160 * 2
def baseEnd_2754160 : Nat := 1414207879387049570033855

theorem tailTrace_2754160 : CollatzResearch.WordTrace tailWord_2754160 prefixEnd_2754160 1414207879387049570033855 := by
  unfold tailWord_2754160
  simp only [CollatzResearch.WordTrace]
  refine ⟨50226233851078083962397967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66968311801437445283197289 50226233851078083962397967)
  ·
    refine ⟨75339350776617125943596951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50226233851078083962397967 75339350776617125943596951)
    ·
      refine ⟨113009026164925688915395427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75339350776617125943596951 113009026164925688915395427)
      ·
        refine ⟨169513539247388533373093141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113009026164925688915395427 169513539247388533373093141)
        ·
          refine ⟨7945947152221337501863741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 169513539247388533373093141 7945947152221337501863741)
          ·
            refine ⟨2979730182083001563198903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7945947152221337501863741 2979730182083001563198903)
            ·
              refine ⟨4469595273124502344798355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2979730182083001563198903 4469595273124502344798355)
              ·
                refine ⟨6704392909686753517197533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4469595273124502344798355 6704392909686753517197533)
                ·
                  refine ⟨2514147341132532568949075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6704392909686753517197533 2514147341132532568949075)
                  ·
                    refine ⟨3771221011698798853423613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2514147341132532568949075 3771221011698798853423613)
                    ·
                      refine ⟨1414207879387049570033855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3771221011698798853423613 1414207879387049570033855)
                      ·
                        rfl

theorem cell23_2754160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 3, 1, 3].length) (baseStart_2754160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2754160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2754160 prefixEnd_2754160 := by exact prefixLift 2754160
  have htrace : WordTrace (prefixWord ++ tailWord_2754160) baseStart_2754160 baseEnd_2754160 := by
    simpa [prefixWord, tailWord_2754160, baseEnd_2754160] using wordTrace_append hprefix tailTrace_2754160
  have hstable : (prefixWord ++ tailWord_2754160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754160).length < 2 ^ (prefixWord ++ tailWord_2754160).sum := by decide
  have hdescent : baseEnd_2754160 < baseStart_2754160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754180 : List Nat := [2, 3, 2, 1, 4, 2, 1, 2, 1, 5]
def baseStart_2754180 : Nat := 118140960795 + 2754180 * 2 ^ 59
def prefixEnd_2754180 : Nat := 4983230072969 + 3 ^ 40 * 2754180 * 2
def baseEnd_2754180 : Nat := 471406049666713163927921

theorem tailTrace_2754180 : CollatzResearch.WordTrace tailWord_2754180 prefixEnd_2754180 471406049666713163927921 := by
  unfold tailWord_2754180
  simp only [CollatzResearch.WordTrace]
  refine ⟨50226598581041855670261997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66968798108055807560349329 50226598581041855670261997)
  ·
    refine ⟨18834974467890695876348249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50226598581041855670261997 18834974467890695876348249)
    ·
      refine ⟨14126230850918021907261187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18834974467890695876348249 14126230850918021907261187)
      ·
        refine ⟨21189346276377032860891781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14126230850918021907261187 21189346276377032860891781)
        ·
          refine ⟨3973002426820693661417209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21189346276377032860891781 3973002426820693661417209)
          ·
            refine ⟨2979751820115520246062907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3973002426820693661417209 2979751820115520246062907)
            ·
              refine ⟨4469627730173280369094361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2979751820115520246062907 4469627730173280369094361)
              ·
                refine ⟨3352220797629960276820771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4469627730173280369094361 3352220797629960276820771)
                ·
                  refine ⟨5028331196444940415231157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3352220797629960276820771 5028331196444940415231157)
                  ·
                    refine ⟨471406049666713163927921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5028331196444940415231157 471406049666713163927921)
                    ·
                      rfl

theorem cell23_2754180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_2754180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2754180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2754180 prefixEnd_2754180 := by exact prefixLift 2754180
  have htrace : WordTrace (prefixWord ++ tailWord_2754180) baseStart_2754180 baseEnd_2754180 := by
    simpa [prefixWord, tailWord_2754180, baseEnd_2754180] using wordTrace_append hprefix tailTrace_2754180
  have hstable : (prefixWord ++ tailWord_2754180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754180).length < 2 ^ (prefixWord ++ tailWord_2754180).sum := by decide
  have hdescent : baseEnd_2754180 < baseStart_2754180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754183 : List Nat := [1, 1, 4, 2, 1, 3, 3, 2, 1, 1, 4]
def baseStart_2754183 : Nat := 118140960795 + 2754183 * 2 ^ 59
def prefixEnd_2754183 : Nat := 4983230072969 + 3 ^ 40 * 2754183 * 2
def baseEnd_2754183 : Nat := 1414219689442102980046249

theorem tailTrace_2754183 : CollatzResearch.WordTrace tailWord_2754183 prefixEnd_2754183 1414219689442102980046249 := by
  unfold tailWord_2754183
  simp only [CollatzResearch.WordTrace]
  refine ⟨100453306581072842852883203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66968871054048561901922135 100453306581072842852883203)
  ·
    refine ⟨150679959871609264279324805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100453306581072842852883203 150679959871609264279324805)
    ·
      refine ⟨28252492475926737052373401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150679959871609264279324805 28252492475926737052373401)
      ·
        refine ⟨21189369356945052789280051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28252492475926737052373401 21189369356945052789280051)
        ·
          refine ⟨31784054035417579183920077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21189369356945052789280051 31784054035417579183920077)
          ·
            refine ⟨11919020263281592193970029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31784054035417579183920077 11919020263281592193970029)
            ·
              refine ⟨4469632598730597072738761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11919020263281592193970029 4469632598730597072738761)
              ·
                refine ⟨3352224449047947804554071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4469632598730597072738761 3352224449047947804554071)
                ·
                  refine ⟨5028336673571921706831107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3352224449047947804554071 5028336673571921706831107)
                  ·
                    refine ⟨7542505010357882560246661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5028336673571921706831107 7542505010357882560246661)
                    ·
                      refine ⟨1414219689442102980046249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7542505010357882560246661 1414219689442102980046249)
                      ·
                        rfl

theorem cell23_2754183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_2754183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2754183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2754183 prefixEnd_2754183 := by exact prefixLift 2754183
  have htrace : WordTrace (prefixWord ++ tailWord_2754183) baseStart_2754183 baseEnd_2754183 := by
    simpa [prefixWord, tailWord_2754183, baseEnd_2754183] using wordTrace_append hprefix tailTrace_2754183
  have hstable : (prefixWord ++ tailWord_2754183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754183).length < 2 ^ (prefixWord ++ tailWord_2754183).sum := by decide
  have hdescent : baseEnd_2754183 < baseStart_2754183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754200 : List Nat := [2, 1, 2, 4, 1, 3, 3, 1, 1, 1, 4]
def baseStart_2754200 : Nat := 118140960795 + 2754200 * 2 ^ 59
def prefixEnd_2754200 : Nat := 4983230072969 + 3 ^ 40 * 2754200 * 2
def baseEnd_2754200 : Nat := 1414228418613229413533671

theorem tailTrace_2754200 : CollatzResearch.WordTrace tailWord_2754200 prefixEnd_2754200 1414228418613229413533671 := by
  unfold tailWord_2754200
  simp only [CollatzResearch.WordTrace]
  refine ⟨50226963311005627378126027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66969284414674169837501369 50226963311005627378126027)
  ·
    refine ⟨75340444966508441067189041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50226963311005627378126027 75340444966508441067189041)
    ·
      refine ⟨56505333724881330800391781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75340444966508441067189041 56505333724881330800391781)
      ·
        refine ⟨10594750073415249525073459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56505333724881330800391781 10594750073415249525073459)
        ·
          refine ⟨15892125110122874287610189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10594750073415249525073459 15892125110122874287610189)
          ·
            refine ⟨5959546916296077857853821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15892125110122874287610189 5959546916296077857853821)
            ·
              refine ⟨2234830093611029196695183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5959546916296077857853821 2234830093611029196695183)
              ·
                refine ⟨3352245140416543795042775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2234830093611029196695183 3352245140416543795042775)
                ·
                  refine ⟨5028367710624815692564163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3352245140416543795042775 5028367710624815692564163)
                  ·
                    refine ⟨7542551565937223538846245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5028367710624815692564163 7542551565937223538846245)
                    ·
                      refine ⟨1414228418613229413533671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7542551565937223538846245 1414228418613229413533671)
                      ·
                        rfl

theorem cell23_2754200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_2754200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2754200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2754200 prefixEnd_2754200 := by exact prefixLift 2754200
  have htrace : WordTrace (prefixWord ++ tailWord_2754200) baseStart_2754200 baseEnd_2754200 := by
    simpa [prefixWord, tailWord_2754200, baseEnd_2754200] using wordTrace_append hprefix tailTrace_2754200
  have hstable : (prefixWord ++ tailWord_2754200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754200).length < 2 ^ (prefixWord ++ tailWord_2754200).sum := by decide
  have hdescent : baseEnd_2754200 < baseStart_2754200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754206 : List Nat := [4, 3, 1, 1, 1, 13]
def baseStart_2754206 : Nat := 118140960795 + 2754206 * 2 ^ 59
def prefixEnd_2754206 : Nat := 4983230072969 + 3 ^ 40 * 2754206 * 2
def baseEnd_2754206 : Nat := 5819882713980067448801

theorem tailTrace_2754206 : CollatzResearch.WordTrace tailWord_2754206 prefixEnd_2754206 5819882713980067448801 := by
  unfold tailWord_2754206
  simp only [CollatzResearch.WordTrace]
  refine ⟨12556768182498689722621309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66969430306659678520646981 12556768182498689722621309)
  ·
    refine ⟨4708788068437008645982991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12556768182498689722621309 4708788068437008645982991)
    ·
      refine ⟨7063182102655512968974487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4708788068437008645982991 7063182102655512968974487)
      ·
        refine ⟨10594773153983269453461731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7063182102655512968974487 10594773153983269453461731)
        ·
          refine ⟨15892159730974904180192597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10594773153983269453461731 15892159730974904180192597)
          ·
            refine ⟨5819882713980067448801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 15892159730974904180192597 5819882713980067448801)
            ·
              rfl

theorem cell23_2754206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 13].length) (baseStart_2754206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2754206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2754206 prefixEnd_2754206 := by exact prefixLift 2754206
  have htrace : WordTrace (prefixWord ++ tailWord_2754206) baseStart_2754206 baseEnd_2754206 := by
    simpa [prefixWord, tailWord_2754206, baseEnd_2754206] using wordTrace_append hprefix tailTrace_2754206
  have hstable : (prefixWord ++ tailWord_2754206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754206).length < 2 ^ (prefixWord ++ tailWord_2754206).sum := by decide
  have hdescent : baseEnd_2754206 < baseStart_2754206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754230 : List Nat := [5, 1, 3, 1, 1, 1, 1, 3, 1, 2, 4]
def baseStart_2754230 : Nat := 118140960795 + 2754230 * 2 ^ 59
def prefixEnd_2754230 : Nat := 4983230072969 + 3 ^ 40 * 2754230 * 2
def baseEnd_2754230 : Nat := 1414243823032864296158533

theorem tailTrace_2754230 : CollatzResearch.WordTrace tailWord_2754230 prefixEnd_2754230 1414243823032864296158533 := by
  unfold tailWord_2754230
  simp only [CollatzResearch.WordTrace]
  refine ⟨6278438800743910617490259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66970013874601713253229429 6278438800743910617490259)
  ·
    refine ⟨9417658201115865926235389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6278438800743910617490259 9417658201115865926235389)
    ·
      refine ⟨3531621825418449722338271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9417658201115865926235389 3531621825418449722338271)
      ·
        refine ⟨5297432738127674583507407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3531621825418449722338271 5297432738127674583507407)
        ·
          refine ⟨7946149107191511875261111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5297432738127674583507407 7946149107191511875261111)
          ·
            refine ⟨11919223660787267812891667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7946149107191511875261111 11919223660787267812891667)
            ·
              refine ⟨17878835491180901719337501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11919223660787267812891667 17878835491180901719337501)
              ·
                refine ⟨6704563309192838144751563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17878835491180901719337501 6704563309192838144751563)
                ·
                  refine ⟨10056844963789257217127345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6704563309192838144751563 10056844963789257217127345)
                  ·
                    refine ⟨7542633722841942912845509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10056844963789257217127345 7542633722841942912845509)
                    ·
                      refine ⟨1414243823032864296158533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7542633722841942912845509 1414243823032864296158533)
                      ·
                        rfl

theorem cell23_2754230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_2754230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2754230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2754230 prefixEnd_2754230 := by exact prefixLift 2754230
  have htrace : WordTrace (prefixWord ++ tailWord_2754230) baseStart_2754230 baseEnd_2754230 := by
    simpa [prefixWord, tailWord_2754230, baseEnd_2754230] using wordTrace_append hprefix tailTrace_2754230
  have hstable : (prefixWord ++ tailWord_2754230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754230).length < 2 ^ (prefixWord ++ tailWord_2754230).sum := by decide
  have hdescent : baseEnd_2754230 < baseStart_2754230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754259 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 9]
def baseStart_2754259 : Nat := 118140960795 + 2754259 * 2 ^ 59
def prefixEnd_2754259 : Nat := 4983230072969 + 3 ^ 40 * 2754259 * 2
def baseEnd_2754259 : Nat := 1414258713971844682695899

theorem tailTrace_2754259 : CollatzResearch.WordTrace tailWord_2754259 prefixEnd_2754259 1414258713971844682695899 := by
  unfold tailWord_2754259
  simp only [CollatzResearch.WordTrace]
  refine ⟨100456078528797507832649831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66970719019198338555099887 100456078528797507832649831)
  ·
    refine ⟨150684117793196261748974747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100456078528797507832649831 150684117793196261748974747)
    ·
      refine ⟨226026176689794392623462121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150684117793196261748974747 226026176689794392623462121)
      ·
        refine ⟨169519632517345794467596591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226026176689794392623462121 169519632517345794467596591)
        ·
          refine ⟨254279448776018691701394887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169519632517345794467596591 254279448776018691701394887)
          ·
            refine ⟨381419173164028037552092331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254279448776018691701394887 381419173164028037552092331)
            ·
              refine ⟨572128759746042056328138497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 381419173164028037552092331 572128759746042056328138497)
              ·
                refine ⟨429096569809531542246103873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 572128759746042056328138497 429096569809531542246103873)
                ·
                  refine ⟨321822427357148656684577905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 429096569809531542246103873 321822427357148656684577905)
                  ·
                    refine ⟨241366820517861492513433429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 321822427357148656684577905 241366820517861492513433429)
                    ·
                      refine ⟨1414258713971844682695899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 241366820517861492513433429 1414258713971844682695899)
                      ·
                        rfl

theorem cell23_2754259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 9].length) (baseStart_2754259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2754259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2754259 prefixEnd_2754259 := by exact prefixLift 2754259
  have htrace : WordTrace (prefixWord ++ tailWord_2754259) baseStart_2754259 baseEnd_2754259 := by
    simpa [prefixWord, tailWord_2754259, baseEnd_2754259] using wordTrace_append hprefix tailTrace_2754259
  have hstable : (prefixWord ++ tailWord_2754259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754259).length < 2 ^ (prefixWord ++ tailWord_2754259).sum := by decide
  have hdescent : baseEnd_2754259 < baseStart_2754259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754266 : List Nat := [3, 1, 1, 2, 2, 3, 1, 2, 2, 6]
def baseStart_2754266 : Nat := 118140960795 + 2754266 * 2 ^ 59
def prefixEnd_2754266 : Nat := 4983230072969 + 3 ^ 40 * 2754266 * 2
def baseEnd_2754266 : Nat := 471420769445475385102789

theorem tailTrace_2754266 : CollatzResearch.WordTrace tailWord_2754266 prefixEnd_2754266 471420769445475385102789 := by
  unfold tailWord_2754266
  simp only [CollatzResearch.WordTrace]
  refine ⟨25114083459943037007038663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66970889226514765352103101 25114083459943037007038663)
  ·
    refine ⟨37671125189914555510557995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25114083459943037007038663 37671125189914555510557995)
    ·
      refine ⟨56506687784871833265836993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37671125189914555510557995 56506687784871833265836993)
      ·
        refine ⟨42380015838653874949377745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56506687784871833265836993 42380015838653874949377745)
        ·
          refine ⟨31785011878990406212033309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42380015838653874949377745 31785011878990406212033309)
          ·
            refine ⟨11919379454621402329512491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31785011878990406212033309 11919379454621402329512491)
            ·
              refine ⟨17879069181932103494268737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11919379454621402329512491 17879069181932103494268737)
              ·
                refine ⟨13409301886449077620701553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17879069181932103494268737 13409301886449077620701553)
                ·
                  refine ⟨10056976414836808215526165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13409301886449077620701553 10056976414836808215526165)
                  ·
                    refine ⟨471420769445475385102789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10056976414836808215526165 471420769445475385102789)
                    ·
                      rfl

theorem cell23_2754266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 2, 6].length) (baseStart_2754266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2754266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2754266 prefixEnd_2754266 := by exact prefixLift 2754266
  have htrace : WordTrace (prefixWord ++ tailWord_2754266) baseStart_2754266 baseEnd_2754266 := by
    simpa [prefixWord, tailWord_2754266, baseEnd_2754266] using wordTrace_append hprefix tailTrace_2754266
  have hstable : (prefixWord ++ tailWord_2754266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754266).length < 2 ^ (prefixWord ++ tailWord_2754266).sum := by decide
  have hdescent : baseEnd_2754266 < baseStart_2754266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754481 : List Nat := [1, 2, 2, 4, 2, 3, 1, 3, 1, 1, 3]
def baseStart_2754481 : Nat := 118140960795 + 2754481 * 2 ^ 59
def prefixEnd_2754481 : Nat := 4983230072969 + 3 ^ 40 * 2754481 * 2
def baseEnd_2754481 : Nat := 1414372706677142814119879

theorem tailTrace_2754481 : CollatzResearch.WordTrace tailWord_2754481 prefixEnd_2754481 1414372706677142814119879 := by
  unfold tailWord_2754481
  simp only [CollatzResearch.WordTrace]
  refine ⟨100464175533993239747231297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66976117022662159831487531 100464175533993239747231297)
  ·
    refine ⟨75348131650494929810423473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100464175533993239747231297 75348131650494929810423473)
    ·
      refine ⟨56511098737871197357817605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75348131650494929810423473 56511098737871197357817605)
      ·
        refine ⟨10595831013350849504590801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56511098737871197357817605 10595831013350849504590801)
        ·
          refine ⟨7946873260013137128443101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10595831013350849504590801 7946873260013137128443101)
          ·
            refine ⟨2980077472504926423166163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7946873260013137128443101 2980077472504926423166163)
            ·
              refine ⟨4470116208757389634749245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2980077472504926423166163 4470116208757389634749245)
              ·
                refine ⟨1676293578284021113030967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4470116208757389634749245 1676293578284021113030967)
                ·
                  refine ⟨2514440367426031669546451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1676293578284021113030967 2514440367426031669546451)
                  ·
                    refine ⟨3771660551139047504319677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2514440367426031669546451 3771660551139047504319677)
                    ·
                      refine ⟨1414372706677142814119879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3771660551139047504319677 1414372706677142814119879)
                      ·
                        rfl

theorem cell23_2754481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_2754481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2754481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2754481 prefixEnd_2754481 := by exact prefixLift 2754481
  have htrace : WordTrace (prefixWord ++ tailWord_2754481) baseStart_2754481 baseEnd_2754481 := by
    simpa [prefixWord, tailWord_2754481, baseEnd_2754481] using wordTrace_append hprefix tailTrace_2754481
  have hstable : (prefixWord ++ tailWord_2754481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754481).length < 2 ^ (prefixWord ++ tailWord_2754481).sum := by decide
  have hdescent : baseEnd_2754481 < baseStart_2754481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754483 : List Nat := [1, 1, 1, 2, 3, 1, 4, 1, 3, 2, 4]
def baseStart_2754483 : Nat := 118140960795 + 2754483 * 2 ^ 59
def prefixEnd_2754483 : Nat := 4983230072969 + 3 ^ 40 * 2754483 * 2
def baseEnd_2754483 : Nat := 1414373733638451806294869

theorem tailTrace_2754483 : CollatzResearch.WordTrace tailWord_2754483 prefixEnd_2754483 1414373733638451806294869 := by
  unfold tailWord_2754483
  simp only [CollatzResearch.WordTrace]
  refine ⟨100464248479985994088804103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66976165653323996059202735 100464248479985994088804103)
  ·
    refine ⟨150696372719978991133206155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100464248479985994088804103 150696372719978991133206155)
    ·
      refine ⟨226044559079968486699809233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150696372719978991133206155 226044559079968486699809233)
      ·
        refine ⟨169533419309976365024856925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226044559079968486699809233 169533419309976365024856925)
        ·
          refine ⟨63575032241241136884321347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169533419309976365024856925 63575032241241136884321347)
          ·
            refine ⟨95362548361861705326482021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63575032241241136884321347 95362548361861705326482021)
            ·
              refine ⟨17880477817849069748715379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95362548361861705326482021 17880477817849069748715379)
              ·
                refine ⟨26820716726773604623073069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17880477817849069748715379 26820716726773604623073069)
                ·
                  refine ⟨10057768772540101733652401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26820716726773604623073069 10057768772540101733652401)
                  ·
                    refine ⟨7543326579405076300239301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10057768772540101733652401 7543326579405076300239301)
                    ·
                      refine ⟨1414373733638451806294869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7543326579405076300239301 1414373733638451806294869)
                      ·
                        rfl

theorem cell23_2754483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 2, 4].length) (baseStart_2754483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2754483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2754483 prefixEnd_2754483 := by exact prefixLift 2754483
  have htrace : WordTrace (prefixWord ++ tailWord_2754483) baseStart_2754483 baseEnd_2754483 := by
    simpa [prefixWord, tailWord_2754483, baseEnd_2754483] using wordTrace_append hprefix tailTrace_2754483
  have hstable : (prefixWord ++ tailWord_2754483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754483).length < 2 ^ (prefixWord ++ tailWord_2754483).sum := by decide
  have hdescent : baseEnd_2754483 < baseStart_2754483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754493 : List Nat := [1, 4, 1, 2, 3, 1, 11]
def baseStart_2754493 : Nat := 118140960795 + 2754493 * 2 ^ 59
def prefixEnd_2754493 : Nat := 4983230072969 + 3 ^ 40 * 2754493 * 2
def baseEnd_2754493 : Nat := 17461467511666626755183

theorem tailTrace_2754493 : CollatzResearch.WordTrace tailWord_2754493 prefixEnd_2754493 17461467511666626755183 := by
  unfold tailWord_2754493
  simp only [CollatzResearch.WordTrace]
  refine ⟨100464613209949765796668133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66976408806633177197778755 100464613209949765796668133)
  ·
    refine ⟨18837114976865581086875275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100464613209949765796668133 18837114976865581086875275)
    ·
      refine ⟨28255672465298371630312913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18837114976865581086875275 28255672465298371630312913)
      ·
        refine ⟨21191754348973778722734685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28255672465298371630312913 21191754348973778722734685)
        ·
          refine ⟨7946907880865167021025507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21191754348973778722734685 7946907880865167021025507)
          ·
            refine ⟨11920361821297750531538261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7946907880865167021025507 11920361821297750531538261)
            ·
              refine ⟨17461467511666626755183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 11920361821297750531538261 17461467511666626755183)
              ·
                rfl

theorem cell23_2754493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 11].length) (baseStart_2754493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2754493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2754493 prefixEnd_2754493 := by exact prefixLift 2754493
  have htrace : WordTrace (prefixWord ++ tailWord_2754493) baseStart_2754493 baseEnd_2754493 := by
    simpa [prefixWord, tailWord_2754493, baseEnd_2754493] using wordTrace_append hprefix tailTrace_2754493
  have hstable : (prefixWord ++ tailWord_2754493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754493).length < 2 ^ (prefixWord ++ tailWord_2754493).sum := by decide
  have hdescent : baseEnd_2754493 < baseStart_2754493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754504 : List Nat := [2, 1, 3, 1, 4, 1, 3, 1, 3, 2, 2]
def baseStart_2754504 : Nat := 118140960795 + 2754504 * 2 ^ 59
def prefixEnd_2754504 : Nat := 4983230072969 + 3 ^ 40 * 2754504 * 2
def baseEnd_2754504 : Nat := 1414384516732196224132273

theorem tailTrace_2754504 : CollatzResearch.WordTrace tailWord_2754504 prefixEnd_2754504 1414384516732196224132273 := by
  unfold tailWord_2754504
  simp only [CollatzResearch.WordTrace]
  refine ⟨50232507206454957337659283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66976676275273276450212377 50232507206454957337659283)
  ·
    refine ⟨75348760809682436006488925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50232507206454957337659283 75348760809682436006488925)
    ·
      refine ⟨28255785303630913502433347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75348760809682436006488925 28255785303630913502433347)
      ·
        refine ⟨42383677955446370253650021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28255785303630913502433347 42383677955446370253650021)
        ·
          refine ⟨7946939616646194422559379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42383677955446370253650021 7946939616646194422559379)
          ·
            refine ⟨11920409424969291633839069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7946939616646194422559379 11920409424969291633839069)
            ·
              refine ⟨4470153534363484362689651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11920409424969291633839069 4470153534363484362689651)
              ·
                refine ⟨6705230301545226544034477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4470153534363484362689651 6705230301545226544034477)
                ·
                  refine ⟨2514461363079459954012929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6705230301545226544034477 2514461363079459954012929)
                  ·
                    refine ⟨1885846022309594965509697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2514461363079459954012929 1885846022309594965509697)
                    ·
                      refine ⟨1414384516732196224132273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1885846022309594965509697 1414384516732196224132273)
                      ·
                        rfl

theorem cell23_2754504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 3, 2, 2].length) (baseStart_2754504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2754504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2754504 prefixEnd_2754504 := by exact prefixLift 2754504
  have htrace : WordTrace (prefixWord ++ tailWord_2754504) baseStart_2754504 baseEnd_2754504 := by
    simpa [prefixWord, tailWord_2754504, baseEnd_2754504] using wordTrace_append hprefix tailTrace_2754504
  have hstable : (prefixWord ++ tailWord_2754504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754504).length < 2 ^ (prefixWord ++ tailWord_2754504).sum := by decide
  have hdescent : baseEnd_2754504 < baseStart_2754504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754514 : List Nat := [3, 2, 2, 3, 2, 1, 1, 3, 2, 4]
def baseStart_2754514 : Nat := 118140960795 + 2754514 * 2 ^ 59
def prefixEnd_2754514 : Nat := 4983230072969 + 3 ^ 40 * 2754514 * 2
def baseEnd_2754514 : Nat := 471463217179580395002409

theorem tailTrace_2754514 : CollatzResearch.WordTrace tailWord_2754514 prefixEnd_2754514 471463217179580395002409 := by
  unfold tailWord_2754514
  simp only [CollatzResearch.WordTrace]
  refine ⟨25116344785718421595795649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66976919428582457588788397 25116344785718421595795649)
  ·
    refine ⟨18837258589288816196846737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25116344785718421595795649 18837258589288816196846737)
    ·
      refine ⟨14127943941966612147635053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18837258589288816196846737 14127943941966612147635053)
      ·
        refine ⟨5297978978237479555363145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14127943941966612147635053 5297978978237479555363145)
        ·
          refine ⟨3973484233678109666522359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5297978978237479555363145 3973484233678109666522359)
          ·
            refine ⟨5960226350517164499783539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3973484233678109666522359 5960226350517164499783539)
            ·
              refine ⟨8940339525775746749675309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5960226350517164499783539 8940339525775746749675309)
              ·
                refine ⟨3352627322165905031128241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8940339525775746749675309 3352627322165905031128241)
                ·
                  refine ⟨2514470491624428773346181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3352627322165905031128241 2514470491624428773346181)
                  ·
                    refine ⟨471463217179580395002409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2514470491624428773346181 471463217179580395002409)
                    ·
                      rfl

theorem cell23_2754514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_2754514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2754514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2754514 prefixEnd_2754514 := by exact prefixLift 2754514
  have htrace : WordTrace (prefixWord ++ tailWord_2754514) baseStart_2754514 baseEnd_2754514 := by
    simpa [prefixWord, tailWord_2754514, baseEnd_2754514] using wordTrace_append hprefix tailTrace_2754514
  have hstable : (prefixWord ++ tailWord_2754514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754514).length < 2 ^ (prefixWord ++ tailWord_2754514).sum := by decide
  have hdescent : baseEnd_2754514 < baseStart_2754514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754520 : List Nat := [2, 1, 2, 2, 2, 2, 2, 3, 1, 3, 3]
def baseStart_2754520 : Nat := 118140960795 + 2754520 * 2 ^ 59
def prefixEnd_2754520 : Nat := 4983230072969 + 3 ^ 40 * 2754520 * 2
def baseEnd_2754520 : Nat := 1414392732422668161532199

theorem tailTrace_2754520 : CollatzResearch.WordTrace tailWord_2754520 prefixEnd_2754520 1414392732422668161532199 := by
  unfold tailWord_2754520
  simp only [CollatzResearch.WordTrace]
  refine ⟨50232798990425974703950507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66977065320567966271934009 50232798990425974703950507)
  ·
    refine ⟨75349198485638962055925761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50232798990425974703950507 75349198485638962055925761)
    ·
      refine ⟨56511898864229221541944321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75349198485638962055925761 56511898864229221541944321)
      ·
        refine ⟨42383924148171916156458241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56511898864229221541944321 42383924148171916156458241)
        ·
          refine ⟨31787943111128937117343681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42383924148171916156458241 31787943111128937117343681)
          ·
            refine ⟨23840957333346702838007761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31787943111128937117343681 23840957333346702838007761)
            ·
              refine ⟨17880718000010027128505821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23840957333346702838007761 17880718000010027128505821)
              ·
                refine ⟨6705269250003760173189683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17880718000010027128505821 6705269250003760173189683)
                ·
                  refine ⟨10057903875005640259784525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6705269250003760173189683 10057903875005640259784525)
                  ·
                    refine ⟨3771713953127115097419197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10057903875005640259784525 3771713953127115097419197)
                    ·
                      refine ⟨1414392732422668161532199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3771713953127115097419197 1414392732422668161532199)
                      ·
                        rfl

theorem cell23_2754520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 1, 3, 3].length) (baseStart_2754520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2754520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2754520 prefixEnd_2754520 := by exact prefixLift 2754520
  have htrace : WordTrace (prefixWord ++ tailWord_2754520) baseStart_2754520 baseEnd_2754520 := by
    simpa [prefixWord, tailWord_2754520, baseEnd_2754520] using wordTrace_append hprefix tailTrace_2754520
  have hstable : (prefixWord ++ tailWord_2754520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754520).length < 2 ^ (prefixWord ++ tailWord_2754520).sum := by decide
  have hdescent : baseEnd_2754520 < baseStart_2754520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754541 : List Nat := [1, 5, 1, 4, 2, 1, 1, 1, 1, 1, 5]
def baseStart_2754541 : Nat := 118140960795 + 2754541 * 2 ^ 59
def prefixEnd_2754541 : Nat := 4983230072969 + 3 ^ 40 * 2754541 * 2
def baseEnd_2754541 : Nat := 1414403515516412579369603

theorem tailTrace_2754541 : CollatzResearch.WordTrace tailWord_2754541 prefixEnd_2754541 1414403515516412579369603 := by
  unfold tailWord_2754541
  simp only [CollatzResearch.WordTrace]
  refine ⟨100466363913775869994415477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66977575942517246662943651 100466363913775869994415477)
  ·
    refine ⟨9418721616916487811976451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 100466363913775869994415477 9418721616916487811976451)
    ·
      refine ⟨14128082425374731717964677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9418721616916487811976451 14128082425374731717964677)
      ·
        refine ⟨2649015454757762197118377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14128082425374731717964677 2649015454757762197118377)
        ·
          refine ⟨1986761591068321647838783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2649015454757762197118377 1986761591068321647838783)
          ·
            refine ⟨2980142386602482471758175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1986761591068321647838783 2980142386602482471758175)
            ·
              refine ⟨4470213579903723707637263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2980142386602482471758175 4470213579903723707637263)
              ·
                refine ⟨6705320369855585561455895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4470213579903723707637263 6705320369855585561455895)
                ·
                  refine ⟨10057980554783378342183843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6705320369855585561455895 10057980554783378342183843)
                  ·
                    refine ⟨15086970832175067513275765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10057980554783378342183843 15086970832175067513275765)
                    ·
                      refine ⟨1414403515516412579369603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15086970832175067513275765 1414403515516412579369603)
                      ·
                        rfl

theorem cell23_2754541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_2754541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2754541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2754541 prefixEnd_2754541 := by exact prefixLift 2754541
  have htrace : WordTrace (prefixWord ++ tailWord_2754541) baseStart_2754541 baseEnd_2754541 := by
    simpa [prefixWord, tailWord_2754541, baseEnd_2754541] using wordTrace_append hprefix tailTrace_2754541
  have hstable : (prefixWord ++ tailWord_2754541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754541).length < 2 ^ (prefixWord ++ tailWord_2754541).sum := by decide
  have hdescent : baseEnd_2754541 < baseStart_2754541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754547 : List Nat := [1, 1, 1, 2, 2, 2, 1, 7, 1, 3, 2]
def baseStart_2754547 : Nat := 118140960795 + 2754547 * 2 ^ 59
def prefixEnd_2754547 : Nat := 4983230072969 + 3 ^ 40 * 2754547 * 2
def baseEnd_2754547 : Nat := 1414406596400339555894575

theorem tailTrace_2754547 : CollatzResearch.WordTrace tailWord_2754547 prefixEnd_2754547 1414406596400339555894575 := by
  unfold tailWord_2754547
  simp only [CollatzResearch.WordTrace]
  refine ⟨100466582751754133019133895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66977721834502755346089263 100466582751754133019133895)
  ·
    refine ⟨150699874127631199528700843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100466582751754133019133895 150699874127631199528700843)
    ·
      refine ⟨226049811191446799293051265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150699874127631199528700843 226049811191446799293051265)
      ·
        refine ⟨169537358393585099469788449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226049811191446799293051265 169537358393585099469788449)
        ·
          refine ⟨127153018795188824602341337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169537358393585099469788449 127153018795188824602341337)
          ·
            refine ⟨95364764096391618451756003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127153018795188824602341337 95364764096391618451756003)
            ·
              refine ⟨143047146144587427677634005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95364764096391618451756003 143047146144587427677634005)
              ·
                refine ⟨3352667487763767836194547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 143047146144587427677634005 3352667487763767836194547)
                ·
                  refine ⟨5029001231645651754291821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3352667487763767836194547 5029001231645651754291821)
                  ·
                    refine ⟨1885875461867119407859433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5029001231645651754291821 1885875461867119407859433)
                    ·
                      refine ⟨1414406596400339555894575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1885875461867119407859433 1414406596400339555894575)
                      ·
                        rfl

theorem cell23_2754547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 7, 1, 3, 2].length) (baseStart_2754547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2754547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2754547 prefixEnd_2754547 := by exact prefixLift 2754547
  have htrace : WordTrace (prefixWord ++ tailWord_2754547) baseStart_2754547 baseEnd_2754547 := by
    simpa [prefixWord, tailWord_2754547, baseEnd_2754547] using wordTrace_append hprefix tailTrace_2754547
  have hstable : (prefixWord ++ tailWord_2754547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754547).length < 2 ^ (prefixWord ++ tailWord_2754547).sum := by decide
  have hdescent : baseEnd_2754547 < baseStart_2754547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754563 : List Nat := [1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 5]
def baseStart_2754563 : Nat := 118140960795 + 2754563 * 2 ^ 59
def prefixEnd_2754563 : Nat := 4983230072969 + 3 ^ 40 * 2754563 * 2
def baseEnd_2754563 : Nat := 1414414812090811493294501

theorem tailTrace_2754563 : CollatzResearch.WordTrace tailWord_2754563 prefixEnd_2754563 1414414812090811493294501 := by
  unfold tailWord_2754563
  simp only [CollatzResearch.WordTrace]
  refine ⟨100467166319696167751716343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66978110879797445167810895 100467166319696167751716343)
  ·
    refine ⟨150700749479544251627574515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100467166319696167751716343 150700749479544251627574515)
    ·
      refine ⟨226051124219316377441361773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150700749479544251627574515 226051124219316377441361773)
      ·
        refine ⟨84769171582243641540510665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 226051124219316377441361773 84769171582243641540510665)
        ·
          refine ⟨63576878686682731155382999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84769171582243641540510665 63576878686682731155382999)
          ·
            refine ⟨95365318030024096733074499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63576878686682731155382999 95365318030024096733074499)
            ·
              refine ⟨143047977045036145099611749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95365318030024096733074499 143047977045036145099611749)
              ·
                refine ⟨26821495695944277206177203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 143047977045036145099611749 26821495695944277206177203)
                ·
                  refine ⟨40232243543916415809265805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26821495695944277206177203 40232243543916415809265805)
                  ·
                    refine ⟨15087091328968655928474677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40232243543916415809265805 15087091328968655928474677)
                    ·
                      refine ⟨1414414812090811493294501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15087091328968655928474677 1414414812090811493294501)
                      ·
                        rfl

theorem cell23_2754563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 5].length) (baseStart_2754563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2754563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2754563 prefixEnd_2754563 := by exact prefixLift 2754563
  have htrace : WordTrace (prefixWord ++ tailWord_2754563) baseStart_2754563 baseEnd_2754563 := by
    simpa [prefixWord, tailWord_2754563, baseEnd_2754563] using wordTrace_append hprefix tailTrace_2754563
  have hstable : (prefixWord ++ tailWord_2754563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754563).length < 2 ^ (prefixWord ++ tailWord_2754563).sum := by decide
  have hdescent : baseEnd_2754563 < baseStart_2754563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754577 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 8, 2, 2]
def baseStart_2754577 : Nat := 118140960795 + 2754577 * 2 ^ 59
def prefixEnd_2754577 : Nat := 4983230072969 + 3 ^ 40 * 2754577 * 2
def baseEnd_2754577 : Nat := 1414422000819974438519437

theorem tailTrace_2754577 : CollatzResearch.WordTrace tailWord_2754577 prefixEnd_2754577 1414422000819974438519437 := by
  unfold tailWord_2754577
  simp only [CollatzResearch.WordTrace]
  refine ⟨100467676941645448142725985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66978451294430298761817323 100467676941645448142725985)
  ·
    refine ⟨75350757706234086107044489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100467676941645448142725985 75350757706234086107044489)
    ·
      refine ⟨56513068279675564580283367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75350757706234086107044489 56513068279675564580283367)
      ·
        refine ⟨84769602419513346870425051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56513068279675564580283367 84769602419513346870425051)
        ·
          refine ⟨127154403629270020305637577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84769602419513346870425051 127154403629270020305637577)
          ·
            refine ⟨95365802721952515229228183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127154403629270020305637577 95365802721952515229228183)
            ·
              refine ⟨143048704082928772843842275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95365802721952515229228183 143048704082928772843842275)
              ·
                refine ⟨214573056124393159265763413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143048704082928772843842275 214573056124393159265763413)
                ·
                  refine ⟨2514528001457732335145665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 214573056124393159265763413 2514528001457732335145665)
                  ·
                    refine ⟨1885896001093299251359249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2514528001457732335145665 1885896001093299251359249)
                    ·
                      refine ⟨1414422000819974438519437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1885896001093299251359249 1414422000819974438519437)
                      ·
                        rfl

theorem cell23_2754577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 8, 2, 2].length) (baseStart_2754577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2754577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2754577 prefixEnd_2754577 := by exact prefixLift 2754577
  have htrace : WordTrace (prefixWord ++ tailWord_2754577) baseStart_2754577 baseEnd_2754577 := by
    simpa [prefixWord, tailWord_2754577, baseEnd_2754577] using wordTrace_append hprefix tailTrace_2754577
  have hstable : (prefixWord ++ tailWord_2754577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754577).length < 2 ^ (prefixWord ++ tailWord_2754577).sum := by decide
  have hdescent : baseEnd_2754577 < baseStart_2754577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754594 : List Nat := [3, 3, 1, 1, 1, 2, 2, 2, 4, 2, 2]
def baseStart_2754594 : Nat := 118140960795 + 2754594 * 2 ^ 59
def prefixEnd_2754594 : Nat := 4983230072969 + 3 ^ 40 * 2754594 * 2
def baseEnd_2754594 : Nat := 1414430729991100872006859

theorem tailTrace_2754594 : CollatzResearch.WordTrace tailWord_2754594 prefixEnd_2754594 1414430729991100872006859 := by
  unfold tailWord_2754594
  simp only [CollatzResearch.WordTrace]
  refine ⟨25117074245645965011523709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66978864655055906697396557 25117074245645965011523709)
  ·
    refine ⟨9418902842117236879321391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25117074245645965011523709 9418902842117236879321391)
    ·
      refine ⟨14128354263175855318982087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9418902842117236879321391 14128354263175855318982087)
      ·
        refine ⟨21192531394763782978473131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14128354263175855318982087 21192531394763782978473131)
        ·
          refine ⟨31788797092145674467709697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21192531394763782978473131 31788797092145674467709697)
          ·
            refine ⟨23841597819109255850782273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31788797092145674467709697 23841597819109255850782273)
            ·
              refine ⟨17881198364331941888086705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23841597819109255850782273 17881198364331941888086705)
              ·
                refine ⟨13410898773248956416065029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17881198364331941888086705 13410898773248956416065029)
                ·
                  refine ⟨2514543519984179328012193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13410898773248956416065029 2514543519984179328012193)
                  ·
                    refine ⟨1885907639988134496009145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2514543519984179328012193 1885907639988134496009145)
                    ·
                      refine ⟨1414430729991100872006859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1885907639988134496009145 1414430729991100872006859)
                      ·
                        rfl

theorem cell23_2754594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 4, 2, 2].length) (baseStart_2754594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2754594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2754594 prefixEnd_2754594 := by exact prefixLift 2754594
  have htrace : WordTrace (prefixWord ++ tailWord_2754594) baseStart_2754594 baseEnd_2754594 := by
    simpa [prefixWord, tailWord_2754594, baseEnd_2754594] using wordTrace_append hprefix tailTrace_2754594
  have hstable : (prefixWord ++ tailWord_2754594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754594).length < 2 ^ (prefixWord ++ tailWord_2754594).sum := by decide
  have hdescent : baseEnd_2754594 < baseStart_2754594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754617 : List Nat := [1, 2, 1, 5, 3, 1, 2, 1, 7]
def baseStart_2754617 : Nat := 118140960795 + 2754617 * 2 ^ 59
def prefixEnd_2754617 : Nat := 4983230072969 + 3 ^ 40 * 2754617 * 2
def baseEnd_2754617 : Nat := 157160282227350475779917

theorem tailTrace_2754617 : CollatzResearch.WordTrace tailWord_2754617 prefixEnd_2754617 157160282227350475779917 := by
  unfold tailWord_2754617
  simp only [CollatzResearch.WordTrace]
  refine ⟨100469135861500534974182105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66979423907667023316121403 100469135861500534974182105)
  ·
    refine ⟨75351851896125401230636579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100469135861500534974182105 75351851896125401230636579)
    ·
      refine ⟨113027777844188101845954869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75351851896125401230636579 113027777844188101845954869)
      ·
        refine ⟨10596354172892634548058269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 113027777844188101845954869 10596354172892634548058269)
        ·
          refine ⟨3973632814834737955521851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10596354172892634548058269 3973632814834737955521851)
          ·
            refine ⟨5960449222252106933282777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3973632814834737955521851 5960449222252106933282777)
            ·
              refine ⟨4470336916689080199962083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5960449222252106933282777 4470336916689080199962083)
              ·
                refine ⟨6705505375033620299943125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4470336916689080199962083 6705505375033620299943125)
                ·
                  refine ⟨157160282227350475779917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6705505375033620299943125 157160282227350475779917)
                  ·
                    rfl

theorem cell23_2754617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 7].length) (baseStart_2754617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2754617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2754617 prefixEnd_2754617 := by exact prefixLift 2754617
  have htrace : WordTrace (prefixWord ++ tailWord_2754617) baseStart_2754617 baseEnd_2754617 := by
    simpa [prefixWord, tailWord_2754617, baseEnd_2754617] using wordTrace_append hprefix tailTrace_2754617
  have hstable : (prefixWord ++ tailWord_2754617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754617).length < 2 ^ (prefixWord ++ tailWord_2754617).sum := by decide
  have hdescent : baseEnd_2754617 < baseStart_2754617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754650 : List Nat := [3, 1, 1, 2, 1, 1, 3, 3, 1, 3, 4]
def baseStart_2754650 : Nat := 118140960795 + 2754650 * 2 ^ 59
def prefixEnd_2754650 : Nat := 4983230072969 + 3 ^ 40 * 2754650 * 2
def baseEnd_2754650 : Nat := 1414459484907752652906601

theorem tailTrace_2754650 : CollatzResearch.WordTrace tailWord_2754650 prefixEnd_2754650 1414459484907752652906601 := by
  unfold tailWord_2754650
  simp only [CollatzResearch.WordTrace]
  refine ⟨25117584867595245402533351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66980226313587321073422269 25117584867595245402533351)
  ·
    refine ⟨37676377301392868103800027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25117584867595245402533351 37676377301392868103800027)
    ·
      refine ⟨56514565952089302155700041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37676377301392868103800027 56514565952089302155700041)
      ·
        refine ⟨42385924464066976616775031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56514565952089302155700041 42385924464066976616775031)
        ·
          refine ⟨63578886696100464925162547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42385924464066976616775031 63578886696100464925162547)
          ·
            refine ⟨95368330044150697387743821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63578886696100464925162547 95368330044150697387743821)
            ·
              refine ⟨35763123766556511520403933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95368330044150697387743821 35763123766556511520403933)
              ·
                refine ⟨13411171412458691820151475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35763123766556511520403933 13411171412458691820151475)
                ·
                  refine ⟨20116757118688037730227213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13411171412458691820151475 20116757118688037730227213)
                  ·
                    refine ⟨7543783919508014148835205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20116757118688037730227213 7543783919508014148835205)
                    ·
                      refine ⟨1414459484907752652906601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7543783919508014148835205 1414459484907752652906601)
                      ·
                        rfl

theorem cell23_2754650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_2754650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2754650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2754650 prefixEnd_2754650 := by exact prefixLift 2754650
  have htrace : WordTrace (prefixWord ++ tailWord_2754650) baseStart_2754650 baseEnd_2754650 := by
    simpa [prefixWord, tailWord_2754650, baseEnd_2754650] using wordTrace_append hprefix tailTrace_2754650
  have hstable : (prefixWord ++ tailWord_2754650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754650).length < 2 ^ (prefixWord ++ tailWord_2754650).sum := by decide
  have hdescent : baseEnd_2754650 < baseStart_2754650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754724 : List Nat := [2, 3, 1, 2, 4, 1, 2, 2, 6]
def baseStart_2754724 : Nat := 118140960795 + 2754724 * 2 ^ 59
def prefixEnd_2754724 : Nat := 4983230072969 + 3 ^ 40 * 2754724 * 2
def baseEnd_2754724 : Nat := 157166386941798373709029

theorem tailTrace_2754724 : CollatzResearch.WordTrace tailWord_2754724 prefixEnd_2754724 157166386941798373709029 := by
  unfold tailWord_2754724
  simp only [CollatzResearch.WordTrace]
  refine ⟨50236519236056446124163613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66982025648075261498884817 50236519236056446124163613)
  ·
    refine ⟨18838694713521167296561355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50236519236056446124163613 18838694713521167296561355)
    ·
      refine ⟨28258042070281750944842033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18838694713521167296561355 28258042070281750944842033)
      ·
        refine ⟨21193531552711313208631525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28258042070281750944842033 21193531552711313208631525)
        ·
          refine ⟨3973787166133371226618411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21193531552711313208631525 3973787166133371226618411)
          ·
            refine ⟨5960680749200056839927617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3973787166133371226618411 5960680749200056839927617)
            ·
              refine ⟨4470510561900042629945713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5960680749200056839927617 4470510561900042629945713)
              ·
                refine ⟨3352882921425031972459285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4470510561900042629945713 3352882921425031972459285)
                ·
                  refine ⟨157166386941798373709029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3352882921425031972459285 157166386941798373709029)
                  ·
                    rfl

theorem cell23_2754724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 2, 6].length) (baseStart_2754724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2754724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2754724 prefixEnd_2754724 := by exact prefixLift 2754724
  have htrace : WordTrace (prefixWord ++ tailWord_2754724) baseStart_2754724 baseEnd_2754724 := by
    simpa [prefixWord, tailWord_2754724, baseEnd_2754724] using wordTrace_append hprefix tailTrace_2754724
  have hstable : (prefixWord ++ tailWord_2754724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754724).length < 2 ^ (prefixWord ++ tailWord_2754724).sum := by decide
  have hdescent : baseEnd_2754724 < baseStart_2754724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754757 : List Nat := [1, 3, 1, 1, 1, 1, 6, 1, 3, 1, 4]
def baseStart_2754757 : Nat := 118140960795 + 2754757 * 2 ^ 59
def prefixEnd_2754757 : Nat := 4983230072969 + 3 ^ 40 * 2754757 * 2
def baseEnd_2754757 : Nat := 1414514427337783734268609

theorem tailTrace_2754757 : CollatzResearch.WordTrace tailWord_2754757 prefixEnd_2754757 1414514427337783734268609 := by
  unfold tailWord_2754757
  simp only [CollatzResearch.WordTrace]
  refine ⟨100474242080993338884278525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66982828053995559256185683 100474242080993338884278525)
  ·
    refine ⟨37677840780372502081604447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100474242080993338884278525 37677840780372502081604447)
    ·
      refine ⟨56516761170558753122406671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37677840780372502081604447 56516761170558753122406671)
      ·
        refine ⟨84775141755838129683610007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56516761170558753122406671 84775141755838129683610007)
        ·
          refine ⟨127162712633757194525415011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84775141755838129683610007 127162712633757194525415011)
          ·
            refine ⟨190744068950635791788122517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127162712633757194525415011 190744068950635791788122517)
            ·
              refine ⟨8941128232061052740068243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 190744068950635791788122517 8941128232061052740068243)
              ·
                refine ⟨13411692348091579110102365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8941128232061052740068243 13411692348091579110102365)
                ·
                  refine ⟨5029384630534342166288387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13411692348091579110102365 5029384630534342166288387)
                  ·
                    refine ⟨7544076945801513249432581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5029384630534342166288387 7544076945801513249432581)
                    ·
                      refine ⟨1414514427337783734268609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7544076945801513249432581 1414514427337783734268609)
                      ·
                        rfl

theorem cell23_2754757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 3, 1, 4].length) (baseStart_2754757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2754757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2754757 prefixEnd_2754757 := by exact prefixLift 2754757
  have htrace : WordTrace (prefixWord ++ tailWord_2754757) baseStart_2754757 baseEnd_2754757 := by
    simpa [prefixWord, tailWord_2754757, baseEnd_2754757] using wordTrace_append hprefix tailTrace_2754757
  have hstable : (prefixWord ++ tailWord_2754757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754757).length < 2 ^ (prefixWord ++ tailWord_2754757).sum := by decide
  have hdescent : baseEnd_2754757 < baseStart_2754757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754767 : List Nat := [1, 1, 2, 1, 1, 3, 4, 2, 4, 4]
def baseStart_2754767 : Nat := 118140960795 + 2754767 * 2 ^ 59
def prefixEnd_2754767 : Nat := 4983230072969 + 3 ^ 40 * 2754767 * 2
def baseEnd_2754767 : Nat := 471506520714776231714521

theorem tailTrace_2754767 : CollatzResearch.WordTrace tailWord_2754767 prefixEnd_2754767 471506520714776231714521 := by
  unfold tailWord_2754767
  simp only [CollatzResearch.WordTrace]
  refine ⟨100474606810957110592142555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66983071207304740394761703 100474606810957110592142555)
  ·
    refine ⟨150711910216435665888213833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100474606810957110592142555 150711910216435665888213833)
    ·
      refine ⟨113033932662326749416160375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150711910216435665888213833 113033932662326749416160375)
      ·
        refine ⟨169550898993490124124240563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113033932662326749416160375 169550898993490124124240563)
        ·
          refine ⟨254326348490235186186360845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169550898993490124124240563 254326348490235186186360845)
          ·
            refine ⟨95372380683838194819885317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 254326348490235186186360845 95372380683838194819885317)
            ·
              refine ⟨17882321378219661528728497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95372380683838194819885317 17882321378219661528728497)
              ·
                refine ⟨13411741033664746146546373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17882321378219661528728497 13411741033664746146546373)
                ·
                  refine ⟨2514701443812139902477445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13411741033664746146546373 2514701443812139902477445)
                  ·
                    refine ⟨471506520714776231714521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2514701443812139902477445 471506520714776231714521)
                    ·
                      rfl

theorem cell23_2754767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 4, 4].length) (baseStart_2754767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2754767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2754767 prefixEnd_2754767 := by exact prefixLift 2754767
  have htrace : WordTrace (prefixWord ++ tailWord_2754767) baseStart_2754767 baseEnd_2754767 := by
    simpa [prefixWord, tailWord_2754767, baseEnd_2754767] using wordTrace_append hprefix tailTrace_2754767
  have hstable : (prefixWord ++ tailWord_2754767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754767).length < 2 ^ (prefixWord ++ tailWord_2754767).sum := by decide
  have hdescent : baseEnd_2754767 < baseStart_2754767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754825 : List Nat := [1, 2, 1, 1, 3, 6, 1, 3, 1, 2, 2]
def baseStart_2754825 : Nat := 118140960795 + 2754825 * 2 ^ 59
def prefixEnd_2754825 : Nat := 4983230072969 + 3 ^ 40 * 2754825 * 2
def baseEnd_2754825 : Nat := 1414549344022289468218297

theorem tailTrace_2754825 : CollatzResearch.WordTrace tailWord_2754825 prefixEnd_2754825 1414549344022289468218297 := by
  unfold tailWord_2754825
  simp only [CollatzResearch.WordTrace]
  refine ⟨100476722244746986497753929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66984481496497990998502619 100476722244746986497753929)
  ·
    refine ⟨75357541683560239873315447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100476722244746986497753929 75357541683560239873315447)
    ·
      refine ⟨113036312525340359809973171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75357541683560239873315447 113036312525340359809973171)
      ·
        refine ⟨169554468788010539714959757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113036312525340359809973171 169554468788010539714959757)
        ·
          refine ⟨63582925795503952393109909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169554468788010539714959757 63582925795503952393109909)
          ·
            refine ⟨2980449646664247768427027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 63582925795503952393109909 2980449646664247768427027)
            ·
              refine ⟨4470674469996371652640541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2980449646664247768427027 4470674469996371652640541)
              ·
                refine ⟨1676502926248639369740203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4470674469996371652640541 1676502926248639369740203)
                ·
                  refine ⟨2514754389372959054610305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1676502926248639369740203 2514754389372959054610305)
                  ·
                    refine ⟨1886065792029719290957729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2514754389372959054610305 1886065792029719290957729)
                    ·
                      refine ⟨1414549344022289468218297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1886065792029719290957729 1414549344022289468218297)
                      ·
                        rfl

theorem cell23_2754825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 3, 1, 2, 2].length) (baseStart_2754825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2754825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2754825 prefixEnd_2754825 := by exact prefixLift 2754825
  have htrace : WordTrace (prefixWord ++ tailWord_2754825) baseStart_2754825 baseEnd_2754825 := by
    simpa [prefixWord, tailWord_2754825, baseEnd_2754825] using wordTrace_append hprefix tailTrace_2754825
  have hstable : (prefixWord ++ tailWord_2754825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754825).length < 2 ^ (prefixWord ++ tailWord_2754825).sum := by decide
  have hdescent : baseEnd_2754825 < baseStart_2754825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754842 : List Nat := [3, 1, 1, 3, 4, 1, 3, 2, 1, 2, 2]
def baseStart_2754842 : Nat := 118140960795 + 2754842 * 2 ^ 59
def prefixEnd_2754842 : Nat := 4983230072969 + 3 ^ 40 * 2754842 * 2
def baseEnd_2754842 : Nat := 1414558073193415901705719

theorem tailTrace_2754842 : CollatzResearch.WordTrace tailWord_2754842 prefixEnd_2754842 1414558073193415901705719 := by
  unfold tailWord_2754842
  simp only [CollatzResearch.WordTrace]
  refine ⟨25119335571421349600280695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66984894857123598934081853 25119335571421349600280695)
  ·
    refine ⟨37679003357132024400421043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25119335571421349600280695 37679003357132024400421043)
    ·
      refine ⟨56518505035698036600631565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37679003357132024400421043 56518505035698036600631565)
      ·
        refine ⟨21194439388386763725236837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56518505035698036600631565 21194439388386763725236837)
        ·
          refine ⟨3973957385322518198481907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21194439388386763725236837 3973957385322518198481907)
          ·
            refine ⟨5960936077983777297722861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3973957385322518198481907 5960936077983777297722861)
            ·
              refine ⟨2235351029243916486646073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5960936077983777297722861 2235351029243916486646073)
              ·
                refine ⟨1676513271932937364984555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2235351029243916486646073 1676513271932937364984555)
                ·
                  refine ⟨2514769907899406047476833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1676513271932937364984555 2514769907899406047476833)
                  ·
                    refine ⟨1886077430924554535607625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2514769907899406047476833 1886077430924554535607625)
                    ·
                      refine ⟨1414558073193415901705719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1886077430924554535607625 1414558073193415901705719)
                      ·
                        rfl

theorem cell23_2754842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 2, 1, 2, 2].length) (baseStart_2754842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2754842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2754842 prefixEnd_2754842 := by exact prefixLift 2754842
  have htrace : WordTrace (prefixWord ++ tailWord_2754842) baseStart_2754842 baseEnd_2754842 := by
    simpa [prefixWord, tailWord_2754842, baseEnd_2754842] using wordTrace_append hprefix tailTrace_2754842
  have hstable : (prefixWord ++ tailWord_2754842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754842).length < 2 ^ (prefixWord ++ tailWord_2754842).sum := by decide
  have hdescent : baseEnd_2754842 < baseStart_2754842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754862 : List Nat := [4, 1, 3, 3, 2, 1, 1, 2, 1, 2, 3]
def baseStart_2754862 : Nat := 118140960795 + 2754862 * 2 ^ 59
def prefixEnd_2754862 : Nat := 4983230072969 + 3 ^ 40 * 2754862 * 2
def baseEnd_2754862 : Nat := 1414568342806505823455627

theorem tailTrace_2754862 : CollatzResearch.WordTrace tailWord_2754862 prefixEnd_2754862 1414568342806505823455627 := by
  unfold tailWord_2754862
  simp only [CollatzResearch.WordTrace]
  refine ⟨12559758968201617727106355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66985381163741961211233893 12559758968201617727106355)
  ·
    refine ⟨18839638452302426590659533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12559758968201617727106355 18839638452302426590659533)
    ·
      refine ⟨7064864419613409971497325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18839638452302426590659533 7064864419613409971497325)
      ·
        refine ⟨2649324157355028739311497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7064864419613409971497325 2649324157355028739311497)
        ·
          refine ⟨1986993118016271554483623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2649324157355028739311497 1986993118016271554483623)
          ·
            refine ⟨2980489677024407331725435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1986993118016271554483623 2980489677024407331725435)
            ·
              refine ⟨4470734515536610997588153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2980489677024407331725435 4470734515536610997588153)
              ·
                refine ⟨3353050886652458248191115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4470734515536610997588153 3353050886652458248191115)
                ·
                  refine ⟨5029576329978687372286673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3353050886652458248191115 5029576329978687372286673)
                  ·
                    refine ⟨3772182247484015529215005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5029576329978687372286673 3772182247484015529215005)
                    ·
                      refine ⟨1414568342806505823455627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3772182247484015529215005 1414568342806505823455627)
                      ·
                        rfl

theorem cell23_2754862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_2754862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2754862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2754862 prefixEnd_2754862 := by exact prefixLift 2754862
  have htrace : WordTrace (prefixWord ++ tailWord_2754862) baseStart_2754862 baseEnd_2754862 := by
    simpa [prefixWord, tailWord_2754862, baseEnd_2754862] using wordTrace_append hprefix tailTrace_2754862
  have hstable : (prefixWord ++ tailWord_2754862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754862).length < 2 ^ (prefixWord ++ tailWord_2754862).sum := by decide
  have hdescent : baseEnd_2754862 < baseStart_2754862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754867 : List Nat := [1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 5]
def baseStart_2754867 : Nat := 118140960795 + 2754867 * 2 ^ 59
def prefixEnd_2754867 : Nat := 4983230072969 + 3 ^ 40 * 2754867 * 2
def baseEnd_2754867 : Nat := 1414570910209778303893103

theorem tailTrace_2754867 : CollatzResearch.WordTrace tailWord_2754867 prefixEnd_2754867 1414570910209778303893103 := by
  unfold tailWord_2754867
  simp only [CollatzResearch.WordTrace]
  refine ⟨100478254110594827670782855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66985502740396551780521903 100478254110594827670782855)
  ·
    refine ⟨150717381165892241506174283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100478254110594827670782855 150717381165892241506174283)
    ·
      refine ⟨226076071748838362259261425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150717381165892241506174283 226076071748838362259261425)
      ·
        refine ⟨169557053811628771694446069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226076071748838362259261425 169557053811628771694446069)
        ·
          refine ⟨15895973794840197346354319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 169557053811628771694446069 15895973794840197346354319)
          ·
            refine ⟨23843960692260296019531479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15895973794840197346354319 23843960692260296019531479)
            ·
              refine ⟨35765941038390444029297219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23843960692260296019531479 35765941038390444029297219)
              ·
                refine ⟨53648911557585666043945829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35765941038390444029297219 53648911557585666043945829)
                ·
                  refine ⟨10059170917047312383239843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53648911557585666043945829 10059170917047312383239843)
                  ·
                    refine ⟨15088756375570968574859765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10059170917047312383239843 15088756375570968574859765)
                    ·
                      refine ⟨1414570910209778303893103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15088756375570968574859765 1414570910209778303893103)
                      ·
                        rfl

theorem cell23_2754867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 5].length) (baseStart_2754867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2754867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2754867 prefixEnd_2754867 := by exact prefixLift 2754867
  have htrace : WordTrace (prefixWord ++ tailWord_2754867) baseStart_2754867 baseEnd_2754867 := by
    simpa [prefixWord, tailWord_2754867, baseEnd_2754867] using wordTrace_append hprefix tailTrace_2754867
  have hstable : (prefixWord ++ tailWord_2754867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754867).length < 2 ^ (prefixWord ++ tailWord_2754867).sum := by decide
  have hdescent : baseEnd_2754867 < baseStart_2754867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754868 : List Nat := [2, 5, 1, 1, 1, 3, 1, 1, 3, 3, 2]
def baseStart_2754868 : Nat := 118140960795 + 2754868 * 2 ^ 59
def prefixEnd_2754868 : Nat := 4983230072969 + 3 ^ 40 * 2754868 * 2
def baseEnd_2754868 : Nat := 1414571423690432799980599

theorem tailTrace_2754868 : CollatzResearch.WordTrace tailWord_2754868 prefixEnd_2754868 1414571423690432799980599 := by
  unfold tailWord_2754868
  simp only [CollatzResearch.WordTrace]
  refine ⟨50239145291795602420784629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66985527055727469894379505 50239145291795602420784629)
  ·
    refine ⟨4709919871105837726948559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50239145291795602420784629 4709919871105837726948559)
    ·
      refine ⟨7064879806658756590422839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4709919871105837726948559 7064879806658756590422839)
      ·
        refine ⟨10597319709988134885634259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7064879806658756590422839 10597319709988134885634259)
        ·
          refine ⟨15895979564982202328451389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10597319709988134885634259 15895979564982202328451389)
          ·
            refine ⟨5960992336868325873169271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15895979564982202328451389 5960992336868325873169271)
            ·
              refine ⟨8941488505302488809753907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5960992336868325873169271 8941488505302488809753907)
              ·
                refine ⟨13412232757953733214630861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8941488505302488809753907 13412232757953733214630861)
                ·
                  refine ⟨5029587284232649955486573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13412232757953733214630861 5029587284232649955486573)
                  ·
                    refine ⟨1886095231587243733307465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5029587284232649955486573 1886095231587243733307465)
                    ·
                      refine ⟨1414571423690432799980599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1886095231587243733307465 1414571423690432799980599)
                      ·
                        rfl

theorem cell23_2754868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_2754868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2754868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2754868 prefixEnd_2754868 := by exact prefixLift 2754868
  have htrace : WordTrace (prefixWord ++ tailWord_2754868) baseStart_2754868 baseEnd_2754868 := by
    simpa [prefixWord, tailWord_2754868, baseEnd_2754868] using wordTrace_append hprefix tailTrace_2754868
  have hstable : (prefixWord ++ tailWord_2754868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754868).length < 2 ^ (prefixWord ++ tailWord_2754868).sum := by decide
  have hdescent : baseEnd_2754868 < baseStart_2754868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754898 : List Nat := [3, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2]
def baseStart_2754898 : Nat := 118140960795 + 2754898 * 2 ^ 59
def prefixEnd_2754898 : Nat := 4983230072969 + 3 ^ 40 * 2754898 * 2
def baseEnd_2754898 : Nat := 1414586828110067682605461

theorem tailTrace_2754898 : CollatzResearch.WordTrace tailWord_2754898 prefixEnd_2754898 1414586828110067682605461 := by
  unfold tailWord_2754898
  simp only [CollatzResearch.WordTrace]
  refine ⟨25119846193370629991290337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66986256515655013310107565 25119846193370629991290337)
  ·
    refine ⟨18839884645027972493467753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25119846193370629991290337 18839884645027972493467753)
    ·
      refine ⟨14129913483770979370100815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18839884645027972493467753 14129913483770979370100815)
      ·
        refine ⟨21194870225656469055151223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14129913483770979370100815 21194870225656469055151223)
        ·
          refine ⟨31792305338484703582726835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21194870225656469055151223 31792305338484703582726835)
          ·
            refine ⟨47688458007727055374090253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31792305338484703582726835 47688458007727055374090253)
            ·
              refine ⟨17883171752897645765283845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47688458007727055374090253 17883171752897645765283845)
              ·
                refine ⟨3353094703668308580990721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17883171752897645765283845 3353094703668308580990721)
                ·
                  refine ⟨2514821027751231435743041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3353094703668308580990721 2514821027751231435743041)
                  ·
                    refine ⟨1886115770813423576807281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2514821027751231435743041 1886115770813423576807281)
                    ·
                      refine ⟨1414586828110067682605461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1886115770813423576807281 1414586828110067682605461)
                      ·
                        rfl

theorem cell23_2754898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2].length) (baseStart_2754898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2754898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2754898 prefixEnd_2754898 := by exact prefixLift 2754898
  have htrace : WordTrace (prefixWord ++ tailWord_2754898) baseStart_2754898 baseEnd_2754898 := by
    simpa [prefixWord, tailWord_2754898, baseEnd_2754898] using wordTrace_append hprefix tailTrace_2754898
  have hstable : (prefixWord ++ tailWord_2754898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754898).length < 2 ^ (prefixWord ++ tailWord_2754898).sum := by decide
  have hdescent : baseEnd_2754898 < baseStart_2754898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754927 : List Nat := [1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 5]
def baseStart_2754927 : Nat := 118140960795 + 2754927 * 2 ^ 59
def prefixEnd_2754927 : Nat := 4983230072969 + 3 ^ 40 * 2754927 * 2
def baseEnd_2754927 : Nat := 1414601719049048069142827

theorem tailTrace_2754927 : CollatzResearch.WordTrace tailWord_2754927 prefixEnd_2754927 1414601719049048069142827 := by
  unfold tailWord_2754927
  simp only [CollatzResearch.WordTrace]
  refine ⟨100480442490377457917967035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66986961660251638611978023 100480442490377457917967035)
  ·
    refine ⟨150720663735566186876950553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100480442490377457917967035 150720663735566186876950553)
    ·
      refine ⟨113040497801674640157712915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150720663735566186876950553 113040497801674640157712915)
      ·
        refine ⟨169560746702511960236569373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113040497801674640157712915 169560746702511960236569373)
        ·
          refine ⟨63585280013441985088713515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169560746702511960236569373 63585280013441985088713515)
          ·
            refine ⟨95377920020162977633070273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63585280013441985088713515 95377920020162977633070273)
            ·
              refine ⟨71533440015122233224802705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95377920020162977633070273 71533440015122233224802705)
              ·
                refine ⟨53650080011341674918602029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71533440015122233224802705 53650080011341674918602029)
                ·
                  refine ⟨20118780004253128094475761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53650080011341674918602029 20118780004253128094475761)
                  ·
                    refine ⟨15089085003189846070856821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20118780004253128094475761 15089085003189846070856821)
                    ·
                      refine ⟨1414601719049048069142827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15089085003189846070856821 1414601719049048069142827)
                      ·
                        rfl

theorem cell23_2754927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 5].length) (baseStart_2754927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2754927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2754927 prefixEnd_2754927 := by exact prefixLift 2754927
  have htrace : WordTrace (prefixWord ++ tailWord_2754927) baseStart_2754927 baseEnd_2754927 := by
    simpa [prefixWord, tailWord_2754927, baseEnd_2754927] using wordTrace_append hprefix tailTrace_2754927
  have hstable : (prefixWord ++ tailWord_2754927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754927).length < 2 ^ (prefixWord ++ tailWord_2754927).sum := by decide
  have hdescent : baseEnd_2754927 < baseStart_2754927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754966 : List Nat := [5, 3, 1, 2, 2, 1, 1, 1, 1, 4, 2]
def baseStart_2754966 : Nat := 118140960795 + 2754966 * 2 ^ 59
def prefixEnd_2754966 : Nat := 4983230072969 + 3 ^ 40 * 2754966 * 2
def baseEnd_2754966 : Nat := 1414621744794573416555149

theorem tailTrace_2754966 : CollatzResearch.WordTrace tailWord_2754966 prefixEnd_2754966 1414621744794573416555149 := by
  unfold tailWord_2754966
  simp only [CollatzResearch.WordTrace]
  refine ⟨6280116558577260473664797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66987909958157445052424501 6280116558577260473664797)
  ·
    refine ⟨2355043709466472677624299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6280116558577260473664797 2355043709466472677624299)
    ·
      refine ⟨3532565564199709016436449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2355043709466472677624299 3532565564199709016436449)
      ·
        refine ⟨2649424173149781762327337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3532565564199709016436449 2649424173149781762327337)
        ·
          refine ⟨1987068129862336321745503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2649424173149781762327337 1987068129862336321745503)
          ·
            refine ⟨2980602194793504482618255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1987068129862336321745503 2980602194793504482618255)
            ·
              refine ⟨4470903292190256723927383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2980602194793504482618255 4470903292190256723927383)
              ·
                refine ⟨6706354938285385085891075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4470903292190256723927383 6706354938285385085891075)
                ·
                  refine ⟨10059532407428077628836613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6706354938285385085891075 10059532407428077628836613)
                  ·
                    refine ⟨1886162326392764555406865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10059532407428077628836613 1886162326392764555406865)
                    ·
                      refine ⟨1414621744794573416555149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1886162326392764555406865 1414621744794573416555149)
                      ·
                        rfl

theorem cell23_2754966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_2754966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2754966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2754966 prefixEnd_2754966 := by exact prefixLift 2754966
  have htrace : WordTrace (prefixWord ++ tailWord_2754966) baseStart_2754966 baseEnd_2754966 := by
    simpa [prefixWord, tailWord_2754966, baseEnd_2754966] using wordTrace_append hprefix tailTrace_2754966
  have hstable : (prefixWord ++ tailWord_2754966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754966).length < 2 ^ (prefixWord ++ tailWord_2754966).sum := by decide
  have hdescent : baseEnd_2754966 < baseStart_2754966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755015 : List Nat := [1, 1, 4, 1, 1, 5, 3, 2, 1, 4]
def baseStart_2755015 : Nat := 118140960795 + 2755015 * 2 ^ 59
def prefixEnd_2755015 : Nat := 4983230072969 + 3 ^ 40 * 2755015 * 2
def baseEnd_2755015 : Nat := 471548968448881241614141

theorem tailTrace_2755015 : CollatzResearch.WordTrace tailWord_2755015 prefixEnd_2755015 471548968448881241614141 := by
  unfold tailWord_2755015
  simp only [CollatzResearch.WordTrace]
  refine ⟨100483652114058648947170499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66989101409372432631446999 100483652114058648947170499)
  ·
    refine ⟨150725478171087973420755749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100483652114058648947170499 150725478171087973420755749)
    ·
      refine ⟨28261027157078995016391703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150725478171087973420755749 28261027157078995016391703)
      ·
        refine ⟨42391540735618492524587555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28261027157078995016391703 42391540735618492524587555)
        ·
          refine ⟨63587311103427738786881333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42391540735618492524587555 63587311103427738786881333)
          ·
            refine ⟨5961310415946350511270125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63587311103427738786881333 5961310415946350511270125)
            ·
              refine ⟨2235491405979881441726297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5961310415946350511270125 2235491405979881441726297)
              ·
                refine ⟨1676618554484911081294723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2235491405979881441726297 1676618554484911081294723)
                ·
                  refine ⟨2514927831727366621942085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1676618554484911081294723 2514927831727366621942085)
                  ·
                    refine ⟨471548968448881241614141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2514927831727366621942085 471548968448881241614141)
                    ·
                      rfl

theorem cell23_2755015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 2, 1, 4].length) (baseStart_2755015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2755015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2755015 prefixEnd_2755015 := by exact prefixLift 2755015
  have htrace : WordTrace (prefixWord ++ tailWord_2755015) baseStart_2755015 baseEnd_2755015 := by
    simpa [prefixWord, tailWord_2755015, baseEnd_2755015] using wordTrace_append hprefix tailTrace_2755015
  have hstable : (prefixWord ++ tailWord_2755015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755015).length < 2 ^ (prefixWord ++ tailWord_2755015).sum := by decide
  have hdescent : baseEnd_2755015 < baseStart_2755015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755028 : List Nat := [2, 4, 1, 2, 2, 1, 4, 1, 6]
def baseStart_2755028 : Nat := 118140960795 + 2755028 * 2 ^ 59
def prefixEnd_2755028 : Nat := 4983230072969 + 3 ^ 40 * 2755028 * 2
def baseEnd_2755028 : Nat := 157183731177239130442207

theorem tailTrace_2755028 : CollatzResearch.WordTrace tailWord_2755028 prefixEnd_2755028 157183731177239130442207 := by
  unfold tailWord_2755028
  simp only [CollatzResearch.WordTrace]
  refine ⟨50242063131505776083696869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66989417508674368111595825 50242063131505776083696869)
  ·
    refine ⟨9420386837157333015693163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50242063131505776083696869 9420386837157333015693163)
    ·
      refine ⟨14130580255735999523539745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9420386837157333015693163 14130580255735999523539745)
      ·
        refine ⟨10597935191801999642654809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14130580255735999523539745 10597935191801999642654809)
        ·
          refine ⟨7948451393851499731991107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10597935191801999642654809 7948451393851499731991107)
          ·
            refine ⟨11922677090777249597986661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7948451393851499731991107 11922677090777249597986661)
            ·
              refine ⟨2235501954520734299622499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11922677090777249597986661 2235501954520734299622499)
              ·
                refine ⟨3353252931781101449433749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2235501954520734299622499 3353252931781101449433749)
                ·
                  refine ⟨157183731177239130442207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3353252931781101449433749 157183731177239130442207)
                  ·
                    rfl

theorem cell23_2755028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 1, 6].length) (baseStart_2755028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2755028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2755028 prefixEnd_2755028 := by exact prefixLift 2755028
  have htrace : WordTrace (prefixWord ++ tailWord_2755028) baseStart_2755028 baseEnd_2755028 := by
    simpa [prefixWord, tailWord_2755028, baseEnd_2755028] using wordTrace_append hprefix tailTrace_2755028
  have hstable : (prefixWord ++ tailWord_2755028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755028).length < 2 ^ (prefixWord ++ tailWord_2755028).sum := by decide
  have hdescent : baseEnd_2755028 < baseStart_2755028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755042 : List Nat := [3, 3, 3, 2, 1, 1, 2, 1, 2, 2, 3]
def baseStart_2755042 : Nat := 118140960795 + 2755042 * 2 ^ 59
def prefixEnd_2755042 : Nat := 4983230072969 + 3 ^ 40 * 2755042 * 2
def baseEnd_2755042 : Nat := 1414660769324315119204799

theorem tailTrace_2755042 : CollatzResearch.WordTrace tailWord_2755042 prefixEnd_2755042 1414660769324315119204799 := by
  unfold tailWord_2755042
  simp only [CollatzResearch.WordTrace]
  refine ⟨25121159221240208139600845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66989757923307221705602253 25121159221240208139600845)
  ·
    refine ⟨9420434707965078052350317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25121159221240208139600845 9420434707965078052350317)
    ·
      refine ⟨3532663015486904269631369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9420434707965078052350317 3532663015486904269631369)
      ·
        refine ⟨2649497261615178202223527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3532663015486904269631369 2649497261615178202223527)
        ·
          refine ⟨3974245892422767303335291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2649497261615178202223527 3974245892422767303335291)
          ·
            refine ⟨5961368838634150955002937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3974245892422767303335291 5961368838634150955002937)
            ·
              refine ⟨4471026628975613216252203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5961368838634150955002937 4471026628975613216252203)
              ·
                refine ⟨6706539943463419824378305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4471026628975613216252203 6706539943463419824378305)
                ·
                  refine ⟨5029904957597564868283729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6706539943463419824378305 5029904957597564868283729)
                  ·
                    refine ⟨3772428718198173651212797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5029904957597564868283729 3772428718198173651212797)
                    ·
                      refine ⟨1414660769324315119204799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3772428718198173651212797 1414660769324315119204799)
                      ·
                        rfl

theorem cell23_2755042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_2755042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2755042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2755042 prefixEnd_2755042 := by exact prefixLift 2755042
  have htrace : WordTrace (prefixWord ++ tailWord_2755042) baseStart_2755042 baseEnd_2755042 := by
    simpa [prefixWord, tailWord_2755042, baseEnd_2755042] using wordTrace_append hprefix tailTrace_2755042
  have hstable : (prefixWord ++ tailWord_2755042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755042).length < 2 ^ (prefixWord ++ tailWord_2755042).sum := by decide
  have hdescent : baseEnd_2755042 < baseStart_2755042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755048 : List Nat := [2, 1, 4, 1, 1, 3, 1, 3, 2, 3, 2]
def baseStart_2755048 : Nat := 118140960795 + 2755048 * 2 ^ 59
def prefixEnd_2755048 : Nat := 4983230072969 + 3 ^ 40 * 2755048 * 2
def baseEnd_2755048 : Nat := 1414663850208242095729771

theorem tailTrace_2755048 : CollatzResearch.WordTrace tailWord_2755048 prefixEnd_2755048 1414663850208242095729771 := by
  unfold tailWord_2755048
  simp only [CollatzResearch.WordTrace]
  refine ⟨50242427861469547791560899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66989903815292730388747865 50242427861469547791560899)
  ·
    refine ⟨75363641792204321687341349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50242427861469547791560899 75363641792204321687341349)
    ·
      refine ⟨14130682836038310316376503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75363641792204321687341349 14130682836038310316376503)
      ·
        refine ⟨21196024254057465474564755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14130682836038310316376503 21196024254057465474564755)
        ·
          refine ⟨31794036381086198211847133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21196024254057465474564755 31794036381086198211847133)
          ·
            refine ⟨11922763642907324329442675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31794036381086198211847133 11922763642907324329442675)
            ·
              refine ⟨17884145464360986494164013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11922763642907324329442675 17884145464360986494164013)
              ·
                refine ⟨6706554549135369935311505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17884145464360986494164013 6706554549135369935311505)
                ·
                  refine ⟨5029915911851527451483629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6706554549135369935311505 5029915911851527451483629)
                  ·
                    refine ⟨1886218466944322794306361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5029915911851527451483629 1886218466944322794306361)
                    ·
                      refine ⟨1414663850208242095729771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1886218466944322794306361 1414663850208242095729771)
                      ·
                        rfl

theorem cell23_2755048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 2, 3, 2].length) (baseStart_2755048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2755048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2755048 prefixEnd_2755048 := by exact prefixLift 2755048
  have htrace : WordTrace (prefixWord ++ tailWord_2755048) baseStart_2755048 baseEnd_2755048 := by
    simpa [prefixWord, tailWord_2755048, baseEnd_2755048] using wordTrace_append hprefix tailTrace_2755048
  have hstable : (prefixWord ++ tailWord_2755048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755048).length < 2 ^ (prefixWord ++ tailWord_2755048).sum := by decide
  have hdescent : baseEnd_2755048 < baseStart_2755048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755091 : List Nat := [1, 1, 1, 2, 1, 5, 4, 1, 1, 2, 4]
def baseStart_2755091 : Nat := 118140960795 + 2755091 * 2 ^ 59
def prefixEnd_2755091 : Nat := 4983230072969 + 3 ^ 40 * 2755091 * 2
def baseEnd_2755091 : Nat := 1414685929876385427492073

theorem tailTrace_2755091 : CollatzResearch.WordTrace tailWord_2755091 prefixEnd_2755091 1414685929876385427492073 := by
  unfold tailWord_2755091
  simp only [CollatzResearch.WordTrace]
  refine ⟨100486424061783313926937127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66990949374522209284624751 100486424061783313926937127)
  ·
    refine ⟨150729636092674970890405691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100486424061783313926937127 150729636092674970890405691)
    ·
      refine ⟨226094454139012456335608537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150729636092674970890405691 226094454139012456335608537)
      ·
        refine ⟨169570840604259342251706403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226094454139012456335608537 169570840604259342251706403)
        ·
          refine ⟨254356260906389013377559605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169570840604259342251706403 254356260906389013377559605)
          ·
            refine ⟨23845899459973970004146213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 254356260906389013377559605 23845899459973970004146213)
            ·
              refine ⟨4471106148745119375777415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23845899459973970004146213 4471106148745119375777415)
              ·
                refine ⟨6706659223117679063666123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4471106148745119375777415 6706659223117679063666123)
                ·
                  refine ⟨10059988834676518595499185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6706659223117679063666123 10059988834676518595499185)
                  ·
                    refine ⟨7544991626007388946624389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10059988834676518595499185 7544991626007388946624389)
                    ·
                      refine ⟨1414685929876385427492073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7544991626007388946624389 1414685929876385427492073)
                      ·
                        rfl

theorem cell23_2755091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 2, 4].length) (baseStart_2755091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2755091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2755091 prefixEnd_2755091 := by exact prefixLift 2755091
  have htrace : WordTrace (prefixWord ++ tailWord_2755091) baseStart_2755091 baseEnd_2755091 := by
    simpa [prefixWord, tailWord_2755091, baseEnd_2755091] using wordTrace_append hprefix tailTrace_2755091
  have hstable : (prefixWord ++ tailWord_2755091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755091).length < 2 ^ (prefixWord ++ tailWord_2755091).sum := by decide
  have hdescent : baseEnd_2755091 < baseStart_2755091 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755112 : List Nat := [2, 1, 5, 2, 1, 3, 2, 1, 1, 1, 4]
def baseStart_2755112 : Nat := 118140960795 + 2755112 * 2 ^ 59
def prefixEnd_2755112 : Nat := 4983230072969 + 3 ^ 40 * 2755112 * 2
def baseEnd_2755112 : Nat := 1414696712970129845329477

theorem tailTrace_2755112 : CollatzResearch.WordTrace tailWord_2755112 prefixEnd_2755112 1414696712970129845329477 := by
  unfold tailWord_2755112
  simp only [CollatzResearch.WordTrace]
  refine ⟨50243594997353617256725795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66991459996471489675634393 50243594997353617256725795)
  ·
    refine ⟨75365392496030425885088693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50243594997353617256725795 75365392496030425885088693)
    ·
      refine ⟨7065505546502852426727065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 75365392496030425885088693 7065505546502852426727065)
      ·
        refine ⟨5299129159877139320045299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7065505546502852426727065 5299129159877139320045299)
        ·
          refine ⟨7948693739815708980067949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5299129159877139320045299 7948693739815708980067949)
          ·
            refine ⟨2980760152430890867525481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7948693739815708980067949 2980760152430890867525481)
            ·
              refine ⟨2235570114323168150644111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2980760152430890867525481 2235570114323168150644111)
              ·
                refine ⟨3353355171484752225966167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2235570114323168150644111 3353355171484752225966167)
                ·
                  refine ⟨5030032757227128338949251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3353355171484752225966167 5030032757227128338949251)
                  ·
                    refine ⟨7545049135840692508423877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5030032757227128338949251 7545049135840692508423877)
                    ·
                      refine ⟨1414696712970129845329477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7545049135840692508423877 1414696712970129845329477)
                      ·
                        rfl

theorem cell23_2755112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_2755112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2755112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2755112 prefixEnd_2755112 := by exact prefixLift 2755112
  have htrace : WordTrace (prefixWord ++ tailWord_2755112) baseStart_2755112 baseEnd_2755112 := by
    simpa [prefixWord, tailWord_2755112, baseEnd_2755112] using wordTrace_append hprefix tailTrace_2755112
  have hstable : (prefixWord ++ tailWord_2755112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755112).length < 2 ^ (prefixWord ++ tailWord_2755112).sum := by decide
  have hdescent : baseEnd_2755112 < baseStart_2755112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755128 : List Nat := [2, 1, 2, 1, 4, 1, 3, 1, 4, 1, 3]
def baseStart_2755128 : Nat := 118140960795 + 2755128 * 2 ^ 59
def prefixEnd_2755128 : Nat := 4983230072969 + 3 ^ 40 * 2755128 * 2
def baseEnd_2755128 : Nat := 1414704928660601782729403

theorem tailTrace_2755128 : CollatzResearch.WordTrace tailWord_2755128 prefixEnd_2755128 1414704928660601782729403 := by
  unfold tailWord_2755128
  simp only [CollatzResearch.WordTrace]
  refine ⟨50243886781324634623017019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66991849041766179497356025 50243886781324634623017019)
  ·
    refine ⟨75365830171986951934525529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50243886781324634623017019 75365830171986951934525529)
    ·
      refine ⟨56524372628990213950894147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75365830171986951934525529 56524372628990213950894147)
      ·
        refine ⟨84786558943485320926341221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56524372628990213950894147 84786558943485320926341221)
        ·
          refine ⟨15897479801903497673688979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84786558943485320926341221 15897479801903497673688979)
          ·
            refine ⟨23846219702855246510533469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15897479801903497673688979 23846219702855246510533469)
            ·
              refine ⟨8942332388570717441450051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23846219702855246510533469 8942332388570717441450051)
              ·
                refine ⟨13413498582856076162175077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8942332388570717441450051 13413498582856076162175077)
                ·
                  refine ⟨2515030984285514280407827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13413498582856076162175077 2515030984285514280407827)
                  ·
                    refine ⟨3772546476428271420611741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2515030984285514280407827 3772546476428271420611741)
                    ·
                      refine ⟨1414704928660601782729403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3772546476428271420611741 1414704928660601782729403)
                      ·
                        rfl

theorem cell23_2755128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 4, 1, 3].length) (baseStart_2755128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2755128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2755128 prefixEnd_2755128 := by exact prefixLift 2755128
  have htrace : WordTrace (prefixWord ++ tailWord_2755128) baseStart_2755128 baseEnd_2755128 := by
    simpa [prefixWord, tailWord_2755128, baseEnd_2755128] using wordTrace_append hprefix tailTrace_2755128
  have hstable : (prefixWord ++ tailWord_2755128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755128).length < 2 ^ (prefixWord ++ tailWord_2755128).sum := by decide
  have hdescent : baseEnd_2755128 < baseStart_2755128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755142 : List Nat := [6, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4]
def baseStart_2755142 : Nat := 118140960795 + 2755142 * 2 ^ 59
def prefixEnd_2755142 : Nat := 4983230072969 + 3 ^ 40 * 2755142 * 2
def baseEnd_2755142 : Nat := 1414712117389764727954339

theorem tailTrace_2755142 : CollatzResearch.WordTrace tailWord_2755142 prefixEnd_2755142 1414712117389764727954339 := by
  unfold tailWord_2755142
  simp only [CollatzResearch.WordTrace]
  refine ⟨3140258880768704676157615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 66992189456399033091362453 3140258880768704676157615)
  ·
    refine ⟨4710388321153057014236423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3140258880768704676157615 4710388321153057014236423)
    ·
      refine ⟨7065582481729585521354635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4710388321153057014236423 7065582481729585521354635)
      ·
        refine ⟨10598373722594378282031953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7065582481729585521354635 10598373722594378282031953)
        ·
          refine ⟨7948780291945783711523965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10598373722594378282031953 7948780291945783711523965)
          ·
            refine ⟨2980792609479668891821487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7948780291945783711523965 2980792609479668891821487)
            ·
              refine ⟨4471188914219503337732231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2980792609479668891821487 4471188914219503337732231)
              ·
                refine ⟨6706783371329255006598347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4471188914219503337732231 6706783371329255006598347)
                ·
                  refine ⟨10060175056993882509897521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6706783371329255006598347 10060175056993882509897521)
                  ·
                    refine ⟨7545131292745411882423141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10060175056993882509897521 7545131292745411882423141)
                    ·
                      refine ⟨1414712117389764727954339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7545131292745411882423141 1414712117389764727954339)
                      ·
                        rfl

theorem cell23_2755142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_2755142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2755142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2755142 prefixEnd_2755142 := by exact prefixLift 2755142
  have htrace : WordTrace (prefixWord ++ tailWord_2755142) baseStart_2755142 baseEnd_2755142 := by
    simpa [prefixWord, tailWord_2755142, baseEnd_2755142] using wordTrace_append hprefix tailTrace_2755142
  have hstable : (prefixWord ++ tailWord_2755142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755142).length < 2 ^ (prefixWord ++ tailWord_2755142).sum := by decide
  have hdescent : baseEnd_2755142 < baseStart_2755142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755168 : List Nat := [2, 1, 1, 3, 2, 1, 2, 4, 1, 4, 2]
def baseStart_2755168 : Nat := 118140960795 + 2755168 * 2 ^ 59
def prefixEnd_2755168 : Nat := 4983230072969 + 3 ^ 40 * 2755168 * 2
def baseEnd_2755168 : Nat := 1414725467886781626229219

theorem tailTrace_2755168 : CollatzResearch.WordTrace tailWord_2755168 prefixEnd_2755168 1414725467886781626229219 := by
  unfold tailWord_2755168
  simp only [CollatzResearch.WordTrace]
  refine ⟨50244616241252178038745079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66992821655002904051660105 50244616241252178038745079)
  ·
    refine ⟨75366924361878267058117619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50244616241252178038745079 75366924361878267058117619)
    ·
      refine ⟨113050386542817400587176429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75366924361878267058117619 113050386542817400587176429)
      ·
        refine ⟨42393894953556525220191161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113050386542817400587176429 42393894953556525220191161)
        ·
          refine ⟨31795421215167393915143371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42393894953556525220191161 31795421215167393915143371)
          ·
            refine ⟨47693131822751090872715057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31795421215167393915143371 47693131822751090872715057)
            ·
              refine ⟨35769848867063318154536293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47693131822751090872715057 35769848867063318154536293)
              ·
                refine ⟨6706846662574372153975555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35769848867063318154536293 6706846662574372153975555)
                ·
                  refine ⟨10060269993861558230963333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6706846662574372153975555 10060269993861558230963333)
                  ·
                    refine ⟨1886300623849042168305625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10060269993861558230963333 1886300623849042168305625)
                    ·
                      refine ⟨1414725467886781626229219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1886300623849042168305625 1414725467886781626229219)
                      ·
                        rfl

theorem cell23_2755168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 1, 4, 2].length) (baseStart_2755168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2755168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2755168 prefixEnd_2755168 := by exact prefixLift 2755168
  have htrace : WordTrace (prefixWord ++ tailWord_2755168) baseStart_2755168 baseEnd_2755168 := by
    simpa [prefixWord, tailWord_2755168, baseEnd_2755168] using wordTrace_append hprefix tailTrace_2755168
  have hstable : (prefixWord ++ tailWord_2755168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755168).length < 2 ^ (prefixWord ++ tailWord_2755168).sum := by decide
  have hdescent : baseEnd_2755168 < baseStart_2755168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755171 : List Nat := [1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 5]
def baseStart_2755171 : Nat := 118140960795 + 2755171 * 2 ^ 59
def prefixEnd_2755171 : Nat := 4983230072969 + 3 ^ 40 * 2755171 * 2
def baseEnd_2755171 : Nat := 1414727008328745114491705

theorem tailTrace_2755171 : CollatzResearch.WordTrace tailWord_2755171 prefixEnd_2755171 1414727008328745114491705 := by
  unfold tailWord_2755171
  simp only [CollatzResearch.WordTrace]
  refine ⟨100489341901493487589849367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66992894600995658393232911 100489341901493487589849367)
  ·
    refine ⟨150734012852240231384774051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100489341901493487589849367 150734012852240231384774051)
    ·
      refine ⟨226101019278360347077161077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150734012852240231384774051 226101019278360347077161077)
      ·
        refine ⟨21196970557346282538483851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 226101019278360347077161077 21196970557346282538483851)
        ·
          refine ⟨31795455836019423807725777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21196970557346282538483851 31795455836019423807725777)
          ·
            refine ⟨23846591877014567855794333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31795455836019423807725777 23846591877014567855794333)
            ·
              refine ⟨8942471953880462945922875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23846591877014567855794333 8942471953880462945922875)
              ·
                refine ⟨13413707930820694418884313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8942471953880462945922875 13413707930820694418884313)
                ·
                  refine ⟨10060280948115520814163235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13413707930820694418884313 10060280948115520814163235)
                  ·
                    refine ⟨15090421422173281221244853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10060280948115520814163235 15090421422173281221244853)
                    ·
                      refine ⟨1414727008328745114491705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15090421422173281221244853 1414727008328745114491705)
                      ·
                        rfl

theorem cell23_2755171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_2755171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2755171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2755171 prefixEnd_2755171 := by exact prefixLift 2755171
  have htrace : WordTrace (prefixWord ++ tailWord_2755171) baseStart_2755171 baseEnd_2755171 := by
    simpa [prefixWord, tailWord_2755171, baseEnd_2755171] using wordTrace_append hprefix tailTrace_2755171
  have hstable : (prefixWord ++ tailWord_2755171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755171).length < 2 ^ (prefixWord ++ tailWord_2755171).sum := by decide
  have hdescent : baseEnd_2755171 < baseStart_2755171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755191 : List Nat := [1, 1, 3, 1, 1, 3, 5, 1, 7]
def baseStart_2755191 : Nat := 118140960795 + 2755191 * 2 ^ 59
def prefixEnd_2755191 : Nat := 4983230072969 + 3 ^ 40 * 2755191 * 2
def baseEnd_2755191 : Nat := 157193030882426115137957

theorem tailTrace_2755191 : CollatzResearch.WordTrace tailWord_2755191 prefixEnd_2755191 157193030882426115137957 := by
  unfold tailWord_2755191
  simp only [CollatzResearch.WordTrace]
  refine ⟨100490071361421031005577427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66993380907614020670384951 100490071361421031005577427)
  ·
    refine ⟨150735107042131546508366141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100490071361421031005577427 150735107042131546508366141)
    ·
      refine ⟨56525665140799329940637303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150735107042131546508366141 56525665140799329940637303)
      ·
        refine ⟨84788497711198994910955955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56525665140799329940637303 84788497711198994910955955)
        ·
          refine ⟨127182746566798492366433933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84788497711198994910955955 127182746566798492366433933)
          ·
            refine ⟨47693529962549434637412725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127182746566798492366433933 47693529962549434637412725)
            ·
              refine ⟨4471268433989009497257443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47693529962549434637412725 4471268433989009497257443)
              ·
                refine ⟨6706902650983514245886165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4471268433989009497257443 6706902650983514245886165)
                ·
                  refine ⟨157193030882426115137957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6706902650983514245886165 157193030882426115137957)
                  ·
                    rfl

theorem cell23_2755191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 7].length) (baseStart_2755191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2755191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2755191 prefixEnd_2755191 := by exact prefixLift 2755191
  have htrace : WordTrace (prefixWord ++ tailWord_2755191) baseStart_2755191 baseEnd_2755191 := by
    simpa [prefixWord, tailWord_2755191, baseEnd_2755191] using wordTrace_append hprefix tailTrace_2755191
  have hstable : (prefixWord ++ tailWord_2755191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755191).length < 2 ^ (prefixWord ++ tailWord_2755191).sum := by decide
  have hdescent : baseEnd_2755191 < baseStart_2755191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755245 : List Nat := [1, 5, 2, 1, 1, 2, 1, 1, 2, 5, 2]
def baseStart_2755245 : Nat := 118140960795 + 2755245 * 2 ^ 59
def prefixEnd_2755245 : Nat := 4983230072969 + 3 ^ 40 * 2755245 * 2
def baseEnd_2755245 : Nat := 1414765005897177824966365

theorem tailTrace_2755245 : CollatzResearch.WordTrace tailWord_2755245 prefixEnd_2755245 1414765005897177824966365 := by
  unfold tailWord_2755245
  simp only [CollatzResearch.WordTrace]
  refine ⟨100492040903225398228043189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66994693935483598818695459 100492040903225398228043189)
  ·
    refine ⟨9421128834677381083879049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 100492040903225398228043189 9421128834677381083879049)
    ·
      refine ⟨7065846626008035812909287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9421128834677381083879049 7065846626008035812909287)
      ·
        refine ⟨10598769939012053719363931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7065846626008035812909287 10598769939012053719363931)
        ·
          refine ⟨15898154908518080579045897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10598769939012053719363931 15898154908518080579045897)
          ·
            refine ⟨11923616181388560434284423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15898154908518080579045897 11923616181388560434284423)
            ·
              refine ⟨17885424272082840651426635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11923616181388560434284423 17885424272082840651426635)
              ·
                refine ⟨26828136408124260977139953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17885424272082840651426635 26828136408124260977139953)
                ·
                  refine ⟨20121102306093195732854965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26828136408124260977139953 20121102306093195732854965)
                  ·
                    refine ⟨1886353341196237099955153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20121102306093195732854965 1886353341196237099955153)
                    ·
                      refine ⟨1414765005897177824966365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1886353341196237099955153 1414765005897177824966365)
                      ·
                        rfl

theorem cell23_2755245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_2755245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2755245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2755245 prefixEnd_2755245 := by exact prefixLift 2755245
  have htrace : WordTrace (prefixWord ++ tailWord_2755245) baseStart_2755245 baseEnd_2755245 := by
    simpa [prefixWord, tailWord_2755245, baseEnd_2755245] using wordTrace_append hprefix tailTrace_2755245
  have hstable : (prefixWord ++ tailWord_2755245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755245).length < 2 ^ (prefixWord ++ tailWord_2755245).sum := by decide
  have hdescent : baseEnd_2755245 < baseStart_2755245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755271 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 1, 6, 4]
def baseStart_2755271 : Nat := 118140960795 + 2755271 * 2 ^ 59
def prefixEnd_2755271 : Nat := 4983230072969 + 3 ^ 40 * 2755271 * 2
def baseEnd_2755271 : Nat := 1414778356394194723241245

theorem tailTrace_2755271 : CollatzResearch.WordTrace tailWord_2755271 prefixEnd_2755271 1414778356394194723241245 := by
  unfold tailWord_2755271
  simp only [CollatzResearch.WordTrace]
  refine ⟨100492989201131204668489667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66995326134087469778993111 100492989201131204668489667)
  ·
    refine ⟨150739483801696807002734501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100492989201131204668489667 150739483801696807002734501)
    ·
      refine ⟨28263653212818151313012719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150739483801696807002734501 28263653212818151313012719)
      ·
        refine ⟨42395479819227226969519079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28263653212818151313012719 42395479819227226969519079)
        ·
          refine ⟨63593219728840840454278619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42395479819227226969519079 63593219728840840454278619)
          ·
            refine ⟨95389829593261260681417929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63593219728840840454278619 95389829593261260681417929)
            ·
              refine ⟨71542372194945945511063447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95389829593261260681417929 71542372194945945511063447)
              ·
                refine ⟨107313558292418918266595171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71542372194945945511063447 107313558292418918266595171)
                ·
                  refine ⟨160970337438628377399892757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107313558292418918266595171 160970337438628377399892757)
                  ·
                    refine ⟨7545484567435705190619973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 160970337438628377399892757 7545484567435705190619973)
                    ·
                      refine ⟨1414778356394194723241245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7545484567435705190619973 1414778356394194723241245)
                      ·
                        rfl

theorem cell23_2755271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_2755271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2755271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2755271 prefixEnd_2755271 := by exact prefixLift 2755271
  have htrace : WordTrace (prefixWord ++ tailWord_2755271) baseStart_2755271 baseEnd_2755271 := by
    simpa [prefixWord, tailWord_2755271, baseEnd_2755271] using wordTrace_append hprefix tailTrace_2755271
  have hstable : (prefixWord ++ tailWord_2755271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755271).length < 2 ^ (prefixWord ++ tailWord_2755271).sum := by decide
  have hdescent : baseEnd_2755271 < baseStart_2755271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755281 : List Nat := [1, 2, 2, 1, 2, 3, 2, 2, 8]
def baseStart_2755281 : Nat := 118140960795 + 2755281 * 2 ^ 59
def prefixEnd_2755281 : Nat := 4983230072969 + 3 ^ 40 * 2755281 * 2
def baseEnd_2755281 : Nat := 157198165688971076012911

theorem tailTrace_2755281 : CollatzResearch.WordTrace tailWord_2755281 prefixEnd_2755281 157198165688971076012911 := by
  unfold tailWord_2755281
  simp only [CollatzResearch.WordTrace]
  refine ⟨100493353931094976376353697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66995569287396650917569131 100493353931094976376353697)
  ·
    refine ⟨75370015448321232282265273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100493353931094976376353697 75370015448321232282265273)
    ·
      refine ⟨56527511586240924211698955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75370015448321232282265273 56527511586240924211698955)
      ·
        refine ⟨84791267379361386317548433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56527511586240924211698955 84791267379361386317548433)
        ·
          refine ⟨63593450534521039738161325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84791267379361386317548433 63593450534521039738161325)
          ·
            refine ⟨23847543950445389901810497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63593450534521039738161325 23847543950445389901810497)
            ·
              refine ⟨17885657962834042426357873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23847543950445389901810497 17885657962834042426357873)
              ·
                refine ⟨13414243472125531819768405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17885657962834042426357873 13414243472125531819768405)
                ·
                  refine ⟨157198165688971076012911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13414243472125531819768405 157198165688971076012911)
                  ·
                    rfl

theorem cell23_2755281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 8].length) (baseStart_2755281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2755281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2755281 prefixEnd_2755281 := by exact prefixLift 2755281
  have htrace : WordTrace (prefixWord ++ tailWord_2755281) baseStart_2755281 baseEnd_2755281 := by
    simpa [prefixWord, tailWord_2755281, baseEnd_2755281] using wordTrace_append hprefix tailTrace_2755281
  have hstable : (prefixWord ++ tailWord_2755281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755281).length < 2 ^ (prefixWord ++ tailWord_2755281).sum := by decide
  have hdescent : baseEnd_2755281 < baseStart_2755281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755292 : List Nat := [2, 2, 5, 1, 1, 1, 1, 2, 2, 4, 2]
def baseStart_2755292 : Nat := 118140960795 + 2755292 * 2 ^ 59
def prefixEnd_2755292 : Nat := 4983230072969 + 3 ^ 40 * 2755292 * 2
def baseEnd_2755292 : Nat := 1414789139487939141078649

theorem tailTrace_2755292 : CollatzResearch.WordTrace tailWord_2755292 prefixEnd_2755292 1414789139487939141078649 := by
  unfold tailWord_2755292
  simp only [CollatzResearch.WordTrace]
  refine ⟨50246877567027562627502065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66995836756036750170002753 50246877567027562627502065)
  ·
    refine ⟨37685158175270671970626549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50246877567027562627502065 37685158175270671970626549)
    ·
      refine ⟨3532983578931625497246239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37685158175270671970626549 3532983578931625497246239)
      ·
        refine ⟨5299475368397438245869359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3532983578931625497246239 5299475368397438245869359)
        ·
          refine ⟨7949213052596157368804039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5299475368397438245869359 7949213052596157368804039)
          ·
            refine ⟨11923819578894236053206059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7949213052596157368804039 11923819578894236053206059)
            ·
              refine ⟨17885729368341354079809089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11923819578894236053206059 17885729368341354079809089)
              ·
                refine ⟨13414297026256015559856817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17885729368341354079809089 13414297026256015559856817)
                ·
                  refine ⟨10060722769692011669892613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13414297026256015559856817 10060722769692011669892613)
                  ·
                    refine ⟨1886385519317252188104865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10060722769692011669892613 1886385519317252188104865)
                    ·
                      refine ⟨1414789139487939141078649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1886385519317252188104865 1414789139487939141078649)
                      ·
                        rfl

theorem cell23_2755292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_2755292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2755292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2755292 prefixEnd_2755292 := by exact prefixLift 2755292
  have htrace : WordTrace (prefixWord ++ tailWord_2755292) baseStart_2755292 baseEnd_2755292 := by
    simpa [prefixWord, tailWord_2755292, baseEnd_2755292] using wordTrace_append hprefix tailTrace_2755292
  have hstable : (prefixWord ++ tailWord_2755292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755292).length < 2 ^ (prefixWord ++ tailWord_2755292).sum := by decide
  have hdescent : baseEnd_2755292 < baseStart_2755292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755318 : List Nat := [5, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6]
def baseStart_2755318 : Nat := 118140960795 + 2755318 * 2 ^ 59
def prefixEnd_2755318 : Nat := 4983230072969 + 3 ^ 40 * 2755318 * 2
def baseEnd_2755318 : Nat := 1414802489984956039353529

theorem tailTrace_2755318 : CollatzResearch.WordTrace tailWord_2755318 prefixEnd_2755318 1414802489984956039353529 := by
  unfold tailWord_2755318
  simp only [CollatzResearch.WordTrace]
  refine ⟨6280918964497558230965663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66996468954640621130300405 6280918964497558230965663)
  ·
    refine ⟨9421378446746337346448495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6280918964497558230965663 9421378446746337346448495)
    ·
      refine ⟨14132067670119506019672743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9421378446746337346448495 14132067670119506019672743)
      ·
        refine ⟨21198101505179259029509115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14132067670119506019672743 21198101505179259029509115)
        ·
          refine ⟨31797152257768888544263673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21198101505179259029509115 31797152257768888544263673)
          ·
            refine ⟨23847864193326666408197755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31797152257768888544263673 23847864193326666408197755)
            ·
              refine ⟨35771796289989999612296633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23847864193326666408197755 35771796289989999612296633)
              ·
                refine ⟨26828847217492499709222475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35771796289989999612296633 26828847217492499709222475)
                ·
                  refine ⟨40243270826238749563833713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26828847217492499709222475 40243270826238749563833713)
                  ·
                    refine ⟨30182453119679062172875285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40243270826238749563833713 30182453119679062172875285)
                    ·
                      refine ⟨1414802489984956039353529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30182453119679062172875285 1414802489984956039353529)
                      ·
                        rfl

theorem cell23_2755318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_2755318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2755318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2755318 prefixEnd_2755318 := by exact prefixLift 2755318
  have htrace : WordTrace (prefixWord ++ tailWord_2755318) baseStart_2755318 baseEnd_2755318 := by
    simpa [prefixWord, tailWord_2755318, baseEnd_2755318] using wordTrace_append hprefix tailTrace_2755318
  have hstable : (prefixWord ++ tailWord_2755318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755318).length < 2 ^ (prefixWord ++ tailWord_2755318).sum := by decide
  have hdescent : baseEnd_2755318 < baseStart_2755318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755321 : List Nat := [1, 2, 1, 3, 1, 1, 1, 3, 2, 1, 7]
def baseStart_2755321 : Nat := 118140960795 + 2755321 * 2 ^ 59
def prefixEnd_2755321 : Nat := 4983230072969 + 3 ^ 40 * 2755321 * 2
def baseEnd_2755321 : Nat := 1414804030426919527616015

theorem tailTrace_2755321 : CollatzResearch.WordTrace tailWord_2755321 prefixEnd_2755321 1414804030426919527616015 := by
  unfold tailWord_2755321
  simp only [CollatzResearch.WordTrace]
  refine ⟨100494812850950063207809817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66996541900633375471873211 100494812850950063207809817)
  ·
    refine ⟨75371109638212547405857363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100494812850950063207809817 75371109638212547405857363)
    ·
      refine ⟨113056664457318821108786045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75371109638212547405857363 113056664457318821108786045)
      ·
        refine ⟨42396249171494557915794767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113056664457318821108786045 42396249171494557915794767)
        ·
          refine ⟨63594373757241836873692151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42396249171494557915794767 63594373757241836873692151)
          ·
            refine ⟨95391560635862755310538227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63594373757241836873692151 95391560635862755310538227)
            ·
              refine ⟨143087340953794132965807341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95391560635862755310538227 143087340953794132965807341)
              ·
                refine ⟨53657752857672799862177753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143087340953794132965807341 53657752857672799862177753)
                ·
                  refine ⟨40243314643254599896633315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53657752857672799862177753 40243314643254599896633315)
                  ·
                    refine ⟨60364971964881899844949973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40243314643254599896633315 60364971964881899844949973)
                    ·
                      refine ⟨1414804030426919527616015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 60364971964881899844949973 1414804030426919527616015)
                      ·
                        rfl

theorem cell23_2755321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_2755321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2755321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2755321 prefixEnd_2755321 := by exact prefixLift 2755321
  have htrace : WordTrace (prefixWord ++ tailWord_2755321) baseStart_2755321 baseEnd_2755321 := by
    simpa [prefixWord, tailWord_2755321, baseEnd_2755321] using wordTrace_append hprefix tailTrace_2755321
  have hstable : (prefixWord ++ tailWord_2755321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755321).length < 2 ^ (prefixWord ++ tailWord_2755321).sum := by decide
  have hdescent : baseEnd_2755321 < baseStart_2755321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755325 : List Nat := [1, 4, 1, 1, 1, 1, 3, 4, 3, 1, 3]
def baseStart_2755325 : Nat := 118140960795 + 2755325 * 2 ^ 59
def prefixEnd_2755325 : Nat := 4983230072969 + 3 ^ 40 * 2755325 * 2
def baseEnd_2755325 : Nat := 1414806084349537511965997

theorem tailTrace_2755325 : CollatzResearch.WordTrace tailWord_2755325 prefixEnd_2755325 1414806084349537511965997 := by
  unfold tailWord_2755325
  simp only [CollatzResearch.WordTrace]
  refine ⟨100494958742935571890955429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66996639161957047927303619 100494958742935571890955429)
  ·
    refine ⟨18842804764300419729554143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100494958742935571890955429 18842804764300419729554143)
    ·
      refine ⟨28264207146450629594331215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18842804764300419729554143 28264207146450629594331215)
      ·
        refine ⟨42396310719675944391496823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28264207146450629594331215 42396310719675944391496823)
        ·
          refine ⟨63594466079513916587245235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42396310719675944391496823 63594466079513916587245235)
          ·
            refine ⟨95391699119270874880867853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63594466079513916587245235 95391699119270874880867853)
            ·
              refine ⟨35771887169726578080325445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95391699119270874880867853 35771887169726578080325445)
              ·
                refine ⟨6707228844323733390061021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35771887169726578080325445 6707228844323733390061021)
                ·
                  refine ⟨2515210816621400021272883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6707228844323733390061021 2515210816621400021272883)
                  ·
                    refine ⟨3772816224932100031909325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2515210816621400021272883 3772816224932100031909325)
                    ·
                      refine ⟨1414806084349537511965997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3772816224932100031909325 1414806084349537511965997)
                      ·
                        rfl

theorem cell23_2755325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 3, 1, 3].length) (baseStart_2755325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2755325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2755325 prefixEnd_2755325 := by exact prefixLift 2755325
  have htrace : WordTrace (prefixWord ++ tailWord_2755325) baseStart_2755325 baseEnd_2755325 := by
    simpa [prefixWord, tailWord_2755325, baseEnd_2755325] using wordTrace_append hprefix tailTrace_2755325
  have hstable : (prefixWord ++ tailWord_2755325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755325).length < 2 ^ (prefixWord ++ tailWord_2755325).sum := by decide
  have hdescent : baseEnd_2755325 < baseStart_2755325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755371 : List Nat := [1, 1, 1, 1, 2, 1, 2, 14]
def baseStart_2755371 : Nat := 118140960795 + 2755371 * 2 ^ 59
def prefixEnd_2755371 : Nat := 4983230072969 + 3 ^ 40 * 2755371 * 2
def baseEnd_2755371 : Nat := 52401100165172012295955

theorem tailTrace_2755371 : CollatzResearch.WordTrace tailWord_2755371 prefixEnd_2755371 52401100165172012295955 := by
  unfold tailWord_2755371
  simp only [CollatzResearch.WordTrace]
  refine ⟨100496636500768921747129967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66997757667179281164753311 100496636500768921747129967)
  ·
    refine ⟨150744954751153382620694951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100496636500768921747129967 150744954751153382620694951)
    ·
      refine ⟨226117432126730073931042427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150744954751153382620694951 226117432126730073931042427)
      ·
        refine ⟨339176148190095110896563641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226117432126730073931042427 339176148190095110896563641)
        ·
          refine ⟨254382111142571333172422731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 339176148190095110896563641 254382111142571333172422731)
          ·
            refine ⟨381573166713856999758634097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254382111142571333172422731 381573166713856999758634097)
            ·
              refine ⟨286179875035392749818975573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 381573166713856999758634097 286179875035392749818975573)
              ·
                refine ⟨52401100165172012295955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 14 286179875035392749818975573 52401100165172012295955)
                ·
                  rfl

theorem cell23_2755371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 14].length) (baseStart_2755371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2755371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2755371 prefixEnd_2755371 := by exact prefixLift 2755371
  have htrace : WordTrace (prefixWord ++ tailWord_2755371) baseStart_2755371 baseEnd_2755371 := by
    simpa [prefixWord, tailWord_2755371, baseEnd_2755371] using wordTrace_append hprefix tailTrace_2755371
  have hstable : (prefixWord ++ tailWord_2755371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755371).length < 2 ^ (prefixWord ++ tailWord_2755371).sum := by decide
  have hdescent : baseEnd_2755371 < baseStart_2755371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755378 : List Nat := [3, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6]
def baseStart_2755378 : Nat := 118140960795 + 2755378 * 2 ^ 59
def prefixEnd_2755378 : Nat := 4983230072969 + 3 ^ 40 * 2755378 * 2
def baseEnd_2755378 : Nat := 1414833298824225804603253

theorem tailTrace_2755378 : CollatzResearch.WordTrace tailWord_2755378 prefixEnd_2755378 1414833298824225804603253 := by
  unfold tailWord_2755378
  simp only [CollatzResearch.WordTrace]
  refine ⟨25124222952935890485658697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66997927874495707961756525 25124222952935890485658697)
  ·
    refine ⟨18843167214701917864244023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25124222952935890485658697 18843167214701917864244023)
    ·
      refine ⟨28264750822052876796366035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18843167214701917864244023 28264750822052876796366035)
      ·
        refine ⟨42397126233079315194549053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28264750822052876796366035 42397126233079315194549053)
        ·
          refine ⟨15898922337404743197955895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42397126233079315194549053 15898922337404743197955895)
          ·
            refine ⟨23848383506107114796933843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15898922337404743197955895 23848383506107114796933843)
            ·
              refine ⟨35772575259160672195400765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23848383506107114796933843 35772575259160672195400765)
              ·
                refine ⟨13414715722185252073275287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35772575259160672195400765 13414715722185252073275287)
                ·
                  refine ⟨20122073583277878109912931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13414715722185252073275287 20122073583277878109912931)
                  ·
                    refine ⟨30183110374916817164869397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20122073583277878109912931 30183110374916817164869397)
                    ·
                      refine ⟨1414833298824225804603253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30183110374916817164869397 1414833298824225804603253)
                      ·
                        rfl

theorem cell23_2755378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_2755378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2755378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2755378 prefixEnd_2755378 := by exact prefixLift 2755378
  have htrace : WordTrace (prefixWord ++ tailWord_2755378) baseStart_2755378 baseEnd_2755378 := by
    simpa [prefixWord, tailWord_2755378, baseEnd_2755378] using wordTrace_append hprefix tailTrace_2755378
  have hstable : (prefixWord ++ tailWord_2755378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755378).length < 2 ^ (prefixWord ++ tailWord_2755378).sum := by decide
  have hdescent : baseEnd_2755378 < baseStart_2755378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755396 : List Nat := [2, 3, 4, 2, 1, 1, 3, 1, 1, 5]
def baseStart_2755396 : Nat := 118140960795 + 2755396 * 2 ^ 59
def prefixEnd_2755396 : Nat := 4983230072969 + 3 ^ 40 * 2755396 * 2
def baseEnd_2755396 : Nat := 471614180492002244726057

theorem tailTrace_2755396 : CollatzResearch.WordTrace tailWord_2755396 prefixEnd_2755396 471614180492002244726057 := by
  unfold tailWord_2755396
  simp only [CollatzResearch.WordTrace]
  refine ⟨50248774162839175508395021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66998365550452234011193361 50248774162839175508395021)
  ·
    refine ⟨18843290311064690815648133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50248774162839175508395021 18843290311064690815648133)
    ·
      refine ⟨3533116933324629527934025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18843290311064690815648133 3533116933324629527934025)
      ·
        refine ⟨2649837699993472145950519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3533116933324629527934025 2649837699993472145950519)
        ·
          refine ⟨3974756549990208218925779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2649837699993472145950519 3974756549990208218925779)
          ·
            refine ⟨5962134824985312328388669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3974756549990208218925779 5962134824985312328388669)
            ·
              refine ⟨2235800559369492123145751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5962134824985312328388669 2235800559369492123145751)
              ·
                refine ⟨3353700839054238184718627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2235800559369492123145751 3353700839054238184718627)
                ·
                  refine ⟨5030551258581357277077941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3353700839054238184718627 5030551258581357277077941)
                  ·
                    refine ⟨471614180492002244726057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5030551258581357277077941 471614180492002244726057)
                    ·
                      rfl

theorem cell23_2755396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_2755396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2755396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2755396 prefixEnd_2755396 := by exact prefixLift 2755396
  have htrace : WordTrace (prefixWord ++ tailWord_2755396) baseStart_2755396 baseEnd_2755396 := by
    simpa [prefixWord, tailWord_2755396, baseEnd_2755396] using wordTrace_append hprefix tailTrace_2755396
  have hstable : (prefixWord ++ tailWord_2755396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755396).length < 2 ^ (prefixWord ++ tailWord_2755396).sum := by decide
  have hdescent : baseEnd_2755396 < baseStart_2755396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755399 : List Nat := [1, 1, 4, 1, 2, 1, 1, 7, 1, 2, 2]
def baseStart_2755399 : Nat := 118140960795 + 2755399 * 2 ^ 59
def prefixEnd_2755399 : Nat := 4983230072969 + 3 ^ 40 * 2755399 * 2
def baseEnd_2755399 : Nat := 1414844081917970222440657

theorem tailTrace_2755399 : CollatzResearch.WordTrace tailWord_2755399 prefixEnd_2755399 1414844081917970222440657 := by
  unfold tailWord_2755399
  simp only [CollatzResearch.WordTrace]
  refine ⟨100497657744667482529149251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66998438496444988352766167 100497657744667482529149251)
  ·
    refine ⟨150746486617001223793723877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100497657744667482529149251 150746486617001223793723877)
    ·
      refine ⟨28264966240687729461323227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150746486617001223793723877 28264966240687729461323227)
      ·
        refine ⟨42397449361031594191984841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28264966240687729461323227 42397449361031594191984841)
        ·
          refine ⟨31798087020773695643988631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42397449361031594191984841 31798087020773695643988631)
          ·
            refine ⟨47697130531160543465982947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31798087020773695643988631 47697130531160543465982947)
            ·
              refine ⟨71545695796740815198974421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47697130531160543465982947 71545695796740815198974421)
              ·
                refine ⟨1676852245236112856225963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 71545695796740815198974421 1676852245236112856225963)
                ·
                  refine ⟨2515278367854169284338945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1676852245236112856225963 2515278367854169284338945)
                  ·
                    refine ⟨1886458775890626963254209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2515278367854169284338945 1886458775890626963254209)
                    ·
                      refine ⟨1414844081917970222440657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1886458775890626963254209 1414844081917970222440657)
                      ·
                        rfl

theorem cell23_2755399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 7, 1, 2, 2].length) (baseStart_2755399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2755399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2755399 prefixEnd_2755399 := by exact prefixLift 2755399
  have htrace : WordTrace (prefixWord ++ tailWord_2755399) baseStart_2755399 baseEnd_2755399 := by
    simpa [prefixWord, tailWord_2755399, baseEnd_2755399] using wordTrace_append hprefix tailTrace_2755399
  have hstable : (prefixWord ++ tailWord_2755399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755399).length < 2 ^ (prefixWord ++ tailWord_2755399).sum := by decide
  have hdescent : baseEnd_2755399 < baseStart_2755399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755405 : List Nat := [1, 6, 1, 2, 2, 11]
def baseStart_2755405 : Nat := 118140960795 + 2755405 * 2 ^ 59
def prefixEnd_2755405 : Nat := 4983230072969 + 3 ^ 40 * 2755405 * 2
def baseEnd_2755405 : Nat := 5822416307826737444303

theorem tailTrace_2755405 : CollatzResearch.WordTrace tailWord_2755405 prefixEnd_2755405 5822416307826737444303 := by
  unfold tailWord_2755405
  simp only [CollatzResearch.WordTrace]
  refine ⟨100497876582645745553867669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66998584388430497035911779 100497876582645745553867669)
  ·
    refine ⟨4710837964811519322837547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 100497876582645745553867669 4710837964811519322837547)
    ·
      refine ⟨7066256947217278984256321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4710837964811519322837547 7066256947217278984256321)
      ·
        refine ⟨5299692710412959238192241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7066256947217278984256321 5299692710412959238192241)
        ·
          refine ⟨3974769532809719428644181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5299692710412959238192241 3974769532809719428644181)
          ·
            refine ⟨5822416307826737444303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3974769532809719428644181 5822416307826737444303)
            ·
              rfl

theorem cell23_2755405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 11].length) (baseStart_2755405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2755405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2755405 prefixEnd_2755405 := by exact prefixLift 2755405
  have htrace : WordTrace (prefixWord ++ tailWord_2755405) baseStart_2755405 baseEnd_2755405 := by
    simpa [prefixWord, tailWord_2755405, baseEnd_2755405] using wordTrace_append hprefix tailTrace_2755405
  have hstable : (prefixWord ++ tailWord_2755405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755405).length < 2 ^ (prefixWord ++ tailWord_2755405).sum := by decide
  have hdescent : baseEnd_2755405 < baseStart_2755405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755418 : List Nat := [3, 1, 1, 2, 1, 4, 1, 1, 2, 7]
def baseStart_2755418 : Nat := 118140960795 + 2755418 * 2 ^ 59
def prefixEnd_2755418 : Nat := 4983230072969 + 3 ^ 40 * 2755418 * 2
def baseEnd_2755418 : Nat := 471617946016801882701023

theorem tailTrace_2755418 : CollatzResearch.WordTrace tailWord_2755418 prefixEnd_2755418 471617946016801882701023 := by
  unfold tailWord_2755418
  simp only [CollatzResearch.WordTrace]
  refine ⟨25124587682899662193522727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66998900487732432516060605 25124587682899662193522727)
  ·
    refine ⟨37686881524349493290284091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25124587682899662193522727 37686881524349493290284091)
    ·
      refine ⟨56530322286524239935426137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37686881524349493290284091 56530322286524239935426137)
      ·
        refine ⟨42397741714893179951569603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56530322286524239935426137 42397741714893179951569603)
        ·
          refine ⟨63596612572339769927354405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42397741714893179951569603 63596612572339769927354405)
          ·
            refine ⟨11924364857313706861378951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63596612572339769927354405 11924364857313706861378951)
            ·
              refine ⟨17886547285970560292068427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11924364857313706861378951 17886547285970560292068427)
              ·
                refine ⟨26829820928955840438102641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17886547285970560292068427 26829820928955840438102641)
                ·
                  refine ⟨20122365696716880328576981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26829820928955840438102641 20122365696716880328576981)
                  ·
                    refine ⟨471617946016801882701023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20122365696716880328576981 471617946016801882701023)
                    ·
                      rfl

theorem cell23_2755418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 2, 7].length) (baseStart_2755418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2755418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2755418 prefixEnd_2755418 := by exact prefixLift 2755418
  have htrace : WordTrace (prefixWord ++ tailWord_2755418) baseStart_2755418 baseEnd_2755418 := by
    simpa [prefixWord, tailWord_2755418, baseEnd_2755418] using wordTrace_append hprefix tailTrace_2755418
  have hstable : (prefixWord ++ tailWord_2755418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755418).length < 2 ^ (prefixWord ++ tailWord_2755418).sum := by decide
  have hdescent : baseEnd_2755418 < baseStart_2755418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755432 : List Nat := [2, 1, 4, 2, 1, 3, 2, 1, 1, 3, 3]
def baseStart_2755432 : Nat := 118140960795 + 2755432 * 2 ^ 59
def prefixEnd_2755432 : Nat := 4983230072969 + 3 ^ 40 * 2755432 * 2
def baseEnd_2755432 : Nat := 1414861026779568593328005

theorem tailTrace_2755432 : CollatzResearch.WordTrace tailWord_2755432 prefixEnd_2755432 1414861026779568593328005 := by
  unfold tailWord_2755432
  simp only [CollatzResearch.WordTrace]
  refine ⟨50249430676773964582550275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66999240902365286110067033 50249430676773964582550275)
  ·
    refine ⟨75374146015160946873825413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50249430676773964582550275 75374146015160946873825413)
    ·
      refine ⟨14132652377842677538842265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75374146015160946873825413 14132652377842677538842265)
      ·
        refine ⟨10599489283382008154131699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14132652377842677538842265 10599489283382008154131699)
        ·
          refine ⟨15899233925073012231197549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10599489283382008154131699 15899233925073012231197549)
          ·
            refine ⟨5962212721902379586699081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15899233925073012231197549 5962212721902379586699081)
            ·
              refine ⟨4471659541426784690024311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5962212721902379586699081 4471659541426784690024311)
              ·
                refine ⟨6707489312140177035036467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4471659541426784690024311 6707489312140177035036467)
                ·
                  refine ⟨10061233968210265552554701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6707489312140177035036467 10061233968210265552554701)
                  ·
                    refine ⟨3772962738078849582208013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10061233968210265552554701 3772962738078849582208013)
                    ·
                      refine ⟨1414861026779568593328005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3772962738078849582208013 1414861026779568593328005)
                      ·
                        rfl

theorem cell23_2755432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_2755432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2755432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2755432 prefixEnd_2755432 := by exact prefixLift 2755432
  have htrace : WordTrace (prefixWord ++ tailWord_2755432) baseStart_2755432 baseEnd_2755432 := by
    simpa [prefixWord, tailWord_2755432, baseEnd_2755432] using wordTrace_append hprefix tailTrace_2755432
  have hstable : (prefixWord ++ tailWord_2755432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755432).length < 2 ^ (prefixWord ++ tailWord_2755432).sum := by decide
  have hdescent : baseEnd_2755432 < baseStart_2755432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755442 : List Nat := [3, 2, 1, 2, 1, 1, 4, 1, 3, 3, 2]
def baseStart_2755442 : Nat := 118140960795 + 2755442 * 2 ^ 59
def prefixEnd_2755442 : Nat := 4983230072969 + 3 ^ 40 * 2755442 * 2
def baseEnd_2755442 : Nat := 1414866161586113554202959

theorem tailTrace_2755442 : CollatzResearch.WordTrace tailWord_2755442 prefixEnd_2755442 1414866161586113554202959 := by
  unfold tailWord_2755442
  simp only [CollatzResearch.WordTrace]
  refine ⟨25124806520877925218241145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66999484055674467248643053 25124806520877925218241145)
  ·
    refine ⟨18843604890658443913680859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25124806520877925218241145 18843604890658443913680859)
    ·
      refine ⟨28265407335987665870521289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18843604890658443913680859 28265407335987665870521289)
      ·
        refine ⟨21199055501990749402890967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28265407335987665870521289 21199055501990749402890967)
        ·
          refine ⟨31798583252986124104336451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21199055501990749402890967 31798583252986124104336451)
          ·
            refine ⟨47697874879479186156504677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31798583252986124104336451 47697874879479186156504677)
            ·
              refine ⟨8943351539902347404344627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47697874879479186156504677 8943351539902347404344627)
              ·
                refine ⟨13415027309853521106516941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8943351539902347404344627 13415027309853521106516941)
                ·
                  refine ⟨5030635241195070414943853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13415027309853521106516941 5030635241195070414943853)
                  ·
                    refine ⟨1886488215448151405603945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5030635241195070414943853 1886488215448151405603945)
                    ·
                      refine ⟨1414866161586113554202959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1886488215448151405603945 1414866161586113554202959)
                      ·
                        rfl

theorem cell23_2755442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 3, 3, 2].length) (baseStart_2755442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2755442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2755442 prefixEnd_2755442 := by exact prefixLift 2755442
  have htrace : WordTrace (prefixWord ++ tailWord_2755442) baseStart_2755442 baseEnd_2755442 := by
    simpa [prefixWord, tailWord_2755442, baseEnd_2755442] using wordTrace_append hprefix tailTrace_2755442
  have hstable : (prefixWord ++ tailWord_2755442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755442).length < 2 ^ (prefixWord ++ tailWord_2755442).sum := by decide
  have hdescent : baseEnd_2755442 < baseStart_2755442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755466 : List Nat := [3, 1, 2, 4, 1, 3, 1, 2, 2, 1, 3]
def baseStart_2755466 : Nat := 118140960795 + 2755466 * 2 ^ 59
def prefixEnd_2755466 : Nat := 4983230072969 + 3 ^ 40 * 2755466 * 2
def baseEnd_2755466 : Nat := 1414878485121821460302849

theorem tailTrace_2755466 : CollatzResearch.WordTrace tailWord_2755466 prefixEnd_2755466 1414878485121821460302849 := by
  unfold tailWord_2755466
  simp only [CollatzResearch.WordTrace]
  refine ⟨25125025358856188242959563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67000067623616501981225501 25125025358856188242959563)
  ·
    refine ⟨37687538038284282364439345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25125025358856188242959563 37687538038284282364439345)
    ·
      refine ⟨28265653528713211773329509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37687538038284282364439345 28265653528713211773329509)
      ·
        refine ⟨5299810036633727207499283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28265653528713211773329509 5299810036633727207499283)
        ·
          refine ⟨7949715054950590811248925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5299810036633727207499283 7949715054950590811248925)
          ·
            refine ⟨2981143145606471554218347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7949715054950590811248925 2981143145606471554218347)
            ·
              refine ⟨4471714718409707331327521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2981143145606471554218347 4471714718409707331327521)
              ·
                refine ⟨3353786038807280498495641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4471714718409707331327521 3353786038807280498495641)
                ·
                  refine ⟨2515339529105460373871731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3353786038807280498495641 2515339529105460373871731)
                  ·
                    refine ⟨3773009293658190560807597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2515339529105460373871731 3773009293658190560807597)
                    ·
                      refine ⟨1414878485121821460302849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3773009293658190560807597 1414878485121821460302849)
                      ·
                        rfl

theorem cell23_2755466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_2755466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2755466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2755466 prefixEnd_2755466 := by exact prefixLift 2755466
  have htrace : WordTrace (prefixWord ++ tailWord_2755466) baseStart_2755466 baseEnd_2755466 := by
    simpa [prefixWord, tailWord_2755466, baseEnd_2755466] using wordTrace_append hprefix tailTrace_2755466
  have hstable : (prefixWord ++ tailWord_2755466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755466).length < 2 ^ (prefixWord ++ tailWord_2755466).sum := by decide
  have hdescent : baseEnd_2755466 < baseStart_2755466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755485 : List Nat := [1, 4, 2, 1, 2, 1, 1, 3, 2, 2, 4]
def baseStart_2755485 : Nat := 118140960795 + 2755485 * 2 ^ 59
def prefixEnd_2755485 : Nat := 4983230072969 + 3 ^ 40 * 2755485 * 2
def baseEnd_2755485 : Nat := 1414888241254256885965261

theorem tailTrace_2755485 : CollatzResearch.WordTrace tailWord_2755485 prefixEnd_2755485 1414888241254256885965261 := by
  unfold tailWord_2755485
  simp only [CollatzResearch.WordTrace]
  refine ⟨100500794422355919216779909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67000529614903946144519939 100500794422355919216779909)
  ·
    refine ⟨18843898954191734853146233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100500794422355919216779909 18843898954191734853146233)
    ·
      refine ⟨14132924215643801139859675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18843898954191734853146233 14132924215643801139859675)
      ·
        refine ⟨21199386323465701709789513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14132924215643801139859675 21199386323465701709789513)
        ·
          refine ⟨15899539742599276282342135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21199386323465701709789513 15899539742599276282342135)
          ·
            refine ⟨23849309613898914423513203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15899539742599276282342135 23849309613898914423513203)
            ·
              refine ⟨35773964420848371635269805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23849309613898914423513203 35773964420848371635269805)
              ·
                refine ⟨13415236657818139363226177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35773964420848371635269805 13415236657818139363226177)
                ·
                  refine ⟨10061427493363604522419633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13415236657818139363226177 10061427493363604522419633)
                  ·
                    refine ⟨7546070620022703391814725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10061427493363604522419633 7546070620022703391814725)
                    ·
                      refine ⟨1414888241254256885965261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7546070620022703391814725 1414888241254256885965261)
                      ·
                        rfl

theorem cell23_2755485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_2755485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2755485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2755485 prefixEnd_2755485 := by exact prefixLift 2755485
  have htrace : WordTrace (prefixWord ++ tailWord_2755485) baseStart_2755485 baseEnd_2755485 := by
    simpa [prefixWord, tailWord_2755485, baseEnd_2755485] using wordTrace_append hprefix tailTrace_2755485
  have hstable : (prefixWord ++ tailWord_2755485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755485).length < 2 ^ (prefixWord ++ tailWord_2755485).sum := by decide
  have hdescent : baseEnd_2755485 < baseStart_2755485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755489 : List Nat := [1, 2, 3, 4, 1, 1, 3, 1, 1, 4, 2]
def baseStart_2755489 : Nat := 118140960795 + 2755489 * 2 ^ 59
def prefixEnd_2755489 : Nat := 4983230072969 + 3 ^ 40 * 2755489 * 2
def baseEnd_2755489 : Nat := 1414890295176874870315243

theorem tailTrace_2755489 : CollatzResearch.WordTrace tailWord_2755489 prefixEnd_2755489 1414890295176874870315243 := by
  unfold tailWord_2755489
  simp only [CollatzResearch.WordTrace]
  refine ⟨100500940314341427899925521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67000626876227618599950347 100500940314341427899925521)
  ·
    refine ⟨75375705235756070924944141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100500940314341427899925521 75375705235756070924944141)
    ·
      refine ⟨28265889463408526596854053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75375705235756070924944141 28265889463408526596854053)
      ·
        refine ⟨5299854274389098736910135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28265889463408526596854053 5299854274389098736910135)
        ·
          refine ⟨7949781411583648105365203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5299854274389098736910135 7949781411583648105365203)
          ·
            refine ⟨11924672117375472158047805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7949781411583648105365203 11924672117375472158047805)
            ·
              refine ⟨4471752044015802059267927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11924672117375472158047805 4471752044015802059267927)
              ·
                refine ⟨6707628066023703088901891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4471752044015802059267927 6707628066023703088901891)
                ·
                  refine ⟨10061442099035554633352837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6707628066023703088901891 10061442099035554633352837)
                  ·
                    refine ⟨1886520393569166493753657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10061442099035554633352837 1886520393569166493753657)
                    ·
                      refine ⟨1414890295176874870315243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1886520393569166493753657 1414890295176874870315243)
                      ·
                        rfl

theorem cell23_2755489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_2755489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2755489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2755489 prefixEnd_2755489 := by exact prefixLift 2755489
  have htrace : WordTrace (prefixWord ++ tailWord_2755489) baseStart_2755489 baseEnd_2755489 := by
    simpa [prefixWord, tailWord_2755489, baseEnd_2755489] using wordTrace_append hprefix tailTrace_2755489
  have hstable : (prefixWord ++ tailWord_2755489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755489).length < 2 ^ (prefixWord ++ tailWord_2755489).sum := by decide
  have hdescent : baseEnd_2755489 < baseStart_2755489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755512 : List Nat := [2, 1, 2, 1, 2, 4, 3, 3, 5]
def baseStart_2755512 : Nat := 118140960795 + 2755512 * 2 ^ 59
def prefixEnd_2755512 : Nat := 4983230072969 + 3 ^ 40 * 2755512 * 2
def baseEnd_2755512 : Nat := 157211345025769808925293

theorem tailTrace_2755512 : CollatzResearch.WordTrace tailWord_2755512 prefixEnd_2755512 157211345025769808925293 := by
  unfold tailWord_2755512
  simp only [CollatzResearch.WordTrace]
  refine ⟨50250889596629051414006395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67001186128838735218675193 50250889596629051414006395)
  ·
    refine ⟨75376334394943577121009593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50250889596629051414006395 75376334394943577121009593)
    ·
      refine ⟨56532250796207682840757195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75376334394943577121009593 56532250796207682840757195)
      ·
        refine ⟨84798376194311524261135793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56532250796207682840757195 84798376194311524261135793)
        ·
          refine ⟨63598782145733643195851845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84798376194311524261135793 63598782145733643195851845)
          ·
            refine ⟨11924771652325058099222221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63598782145733643195851845 11924771652325058099222221)
            ·
              refine ⟨4471789369621896787208333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11924771652325058099222221 4471789369621896787208333)
              ·
                refine ⟨1676921013608211295203125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4471789369621896787208333 1676921013608211295203125)
                ·
                  refine ⟨157211345025769808925293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1676921013608211295203125 157211345025769808925293)
                  ·
                    rfl

theorem cell23_2755512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 3, 5].length) (baseStart_2755512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2755512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2755512 prefixEnd_2755512 := by exact prefixLift 2755512
  have htrace : WordTrace (prefixWord ++ tailWord_2755512) baseStart_2755512 baseEnd_2755512 := by
    simpa [prefixWord, tailWord_2755512, baseEnd_2755512] using wordTrace_append hprefix tailTrace_2755512
  have hstable : (prefixWord ++ tailWord_2755512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755512).length < 2 ^ (prefixWord ++ tailWord_2755512).sum := by decide
  have hdescent : baseEnd_2755512 < baseStart_2755512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755532 : List Nat := [2, 2, 1, 4, 1, 1, 2, 1, 2, 5, 2]
def baseStart_2755532 : Nat := 118140960795 + 2755532 * 2 ^ 59
def prefixEnd_2755532 : Nat := 4983230072969 + 3 ^ 40 * 2755532 * 2
def baseEnd_2755532 : Nat := 1414912374845018202077545

theorem tailTrace_2755532 : CollatzResearch.WordTrace tailWord_2755532 prefixEnd_2755532 1414912374845018202077545 := by
  unfold tailWord_2755532
  simp only [CollatzResearch.WordTrace]
  refine ⟨50251254326592823121870425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67001672435457097495827233 50251254326592823121870425)
  ·
    refine ⟨37688440744944617341402819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50251254326592823121870425 37688440744944617341402819)
    ·
      refine ⟨56532661117416926012104229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37688440744944617341402819 56532661117416926012104229)
      ·
        refine ⟨10599873959515673627269543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56532661117416926012104229 10599873959515673627269543)
        ·
          refine ⟨15899810939273510440904315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10599873959515673627269543 15899810939273510440904315)
          ·
            refine ⟨23849716408910265661356473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15899810939273510440904315 23849716408910265661356473)
            ·
              refine ⟨17887287306682699246017355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23849716408910265661356473 17887287306682699246017355)
              ·
                refine ⟨26830930960024048869026033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17887287306682699246017355 26830930960024048869026033)
                ·
                  refine ⟨20123198220018036651769525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26830930960024048869026033 20123198220018036651769525)
                  ·
                    refine ⟨1886549833126690936103393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20123198220018036651769525 1886549833126690936103393)
                    ·
                      refine ⟨1414912374845018202077545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1886549833126690936103393 1414912374845018202077545)
                      ·
                        rfl

theorem cell23_2755532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_2755532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2755532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2755532 prefixEnd_2755532 := by exact prefixLift 2755532
  have htrace : WordTrace (prefixWord ++ tailWord_2755532) baseStart_2755532 baseEnd_2755532 := by
    simpa [prefixWord, tailWord_2755532, baseEnd_2755532] using wordTrace_append hprefix tailTrace_2755532
  have hstable : (prefixWord ++ tailWord_2755532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755532).length < 2 ^ (prefixWord ++ tailWord_2755532).sum := by decide
  have hdescent : baseEnd_2755532 < baseStart_2755532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755535 : List Nat := [1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 5]
def baseStart_2755535 : Nat := 118140960795 + 2755535 * 2 ^ 59
def prefixEnd_2755535 : Nat := 4983230072969 + 3 ^ 40 * 2755535 * 2
def baseEnd_2755535 : Nat := 1414913915286981690340031

theorem tailTrace_2755535 : CollatzResearch.WordTrace tailWord_2755535 prefixEnd_2755535 1414913915286981690340031 := by
  unfold tailWord_2755535
  simp only [CollatzResearch.WordTrace]
  refine ⟨100502618072174777756100059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67001745381449851837400039 100502618072174777756100059)
  ·
    refine ⟨150753927108262166634150089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100502618072174777756100059 150753927108262166634150089)
    ·
      refine ⟨113065445331196624975612567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150753927108262166634150089 113065445331196624975612567)
      ·
        refine ⟨169598167996794937463418851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113065445331196624975612567 169598167996794937463418851)
        ·
          refine ⟨254397251995192406195128277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169598167996794937463418851 254397251995192406195128277)
          ·
            refine ⟨5962435593637322020198319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 254397251995192406195128277 5962435593637322020198319)
            ·
              refine ⟨8943653390455983030297479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5962435593637322020198319 8943653390455983030297479)
              ·
                refine ⟨13415480085683974545446219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8943653390455983030297479 13415480085683974545446219)
                ·
                  refine ⟨20123220128525961818169329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13415480085683974545446219 20123220128525961818169329)
                  ·
                    refine ⟨15092415096394471363626997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20123220128525961818169329 15092415096394471363626997)
                    ·
                      refine ⟨1414913915286981690340031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15092415096394471363626997 1414913915286981690340031)
                      ·
                        rfl

theorem cell23_2755535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 5].length) (baseStart_2755535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2755535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2755535 prefixEnd_2755535 := by exact prefixLift 2755535
  have htrace : WordTrace (prefixWord ++ tailWord_2755535) baseStart_2755535 baseEnd_2755535 := by
    simpa [prefixWord, tailWord_2755535, baseEnd_2755535] using wordTrace_append hprefix tailTrace_2755535
  have hstable : (prefixWord ++ tailWord_2755535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755535).length < 2 ^ (prefixWord ++ tailWord_2755535).sum := by decide
  have hdescent : baseEnd_2755535 < baseStart_2755535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755562 : List Nat := [3, 1, 3, 1, 2, 2, 1, 3, 2, 1, 4]
def baseStart_2755562 : Nat := 118140960795 + 2755562 * 2 ^ 59
def prefixEnd_2755562 : Nat := 4983230072969 + 3 ^ 40 * 2755562 * 2
def baseEnd_2755562 : Nat := 1414927779264653084702407

theorem tailTrace_2755562 : CollatzResearch.WordTrace tailWord_2755562 prefixEnd_2755562 1414927779264653084702407 := by
  unfold tailWord_2755562
  simp only [CollatzResearch.WordTrace]
  refine ⟨25125900710769240341833235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67002401895384640911555293 25125900710769240341833235)
  ·
    refine ⟨37688851066153860512749853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25125900710769240341833235 37688851066153860512749853)
    ·
      refine ⟨14133319149807697692281195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37688851066153860512749853 14133319149807697692281195)
      ·
        refine ⟨21199978724711546538421793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14133319149807697692281195 21199978724711546538421793)
        ·
          refine ⟨15899984043533659903816345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21199978724711546538421793 15899984043533659903816345)
          ·
            refine ⟨11924988032650244927862259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15899984043533659903816345 11924988032650244927862259)
            ·
              refine ⟨17887482048975367391793389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11924988032650244927862259 17887482048975367391793389)
              ·
                refine ⟨6707805768365762771922521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17887482048975367391793389 6707805768365762771922521)
                ·
                  refine ⟨5030854326274322078941891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6707805768365762771922521 5030854326274322078941891)
                  ·
                    refine ⟨7546281489411483118412837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5030854326274322078941891 7546281489411483118412837)
                    ·
                      refine ⟨1414927779264653084702407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7546281489411483118412837 1414927779264653084702407)
                      ·
                        rfl

theorem cell23_2755562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_2755562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2755562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2755562 prefixEnd_2755562 := by exact prefixLift 2755562
  have htrace : WordTrace (prefixWord ++ tailWord_2755562) baseStart_2755562 baseEnd_2755562 := by
    simpa [prefixWord, tailWord_2755562, baseEnd_2755562] using wordTrace_append hprefix tailTrace_2755562
  have hstable : (prefixWord ++ tailWord_2755562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755562).length < 2 ^ (prefixWord ++ tailWord_2755562).sum := by decide
  have hdescent : baseEnd_2755562 < baseStart_2755562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755589 : List Nat := [1, 3, 1, 1, 2, 3, 3, 4, 1, 4]
def baseStart_2755589 : Nat := 118140960795 + 2755589 * 2 ^ 59
def prefixEnd_2755589 : Nat := 4983230072969 + 3 ^ 40 * 2755589 * 2
def baseEnd_2755589 : Nat := 471647214414108159688261

theorem tailTrace_2755589 : CollatzResearch.WordTrace tailWord_2755589 prefixEnd_2755589 471647214414108159688261 := by
  unfold tailWord_2755589
  simp only [CollatzResearch.WordTrace]
  refine ⟨100504587613979144978565821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67003058409319429985710547 100504587613979144978565821)
  ·
    refine ⟨37689220355242179366962183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100504587613979144978565821 37689220355242179366962183)
    ·
      refine ⟨56533830532863269050443275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37689220355242179366962183 56533830532863269050443275)
      ·
        refine ⟨84800745799294903575664913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56533830532863269050443275 84800745799294903575664913)
        ·
          refine ⟨63600559349471177681748685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84800745799294903575664913 63600559349471177681748685)
          ·
            refine ⟨23850209756051691630655757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63600559349471177681748685 23850209756051691630655757)
            ·
              refine ⟨8943828658519384361495909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23850209756051691630655757 8943828658519384361495909)
              ·
                refine ⟨1676967873472384567780483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8943828658519384361495909 1676967873472384567780483)
                ·
                  refine ⟨2515451810208576851670725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1676967873472384567780483 2515451810208576851670725)
                  ·
                    refine ⟨471647214414108159688261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2515451810208576851670725 471647214414108159688261)
                    ·
                      rfl

theorem cell23_2755589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 4, 1, 4].length) (baseStart_2755589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2755589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2755589 prefixEnd_2755589 := by exact prefixLift 2755589
  have htrace : WordTrace (prefixWord ++ tailWord_2755589) baseStart_2755589 baseEnd_2755589 := by
    simpa [prefixWord, tailWord_2755589, baseEnd_2755589] using wordTrace_append hprefix tailTrace_2755589
  have hstable : (prefixWord ++ tailWord_2755589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755589).length < 2 ^ (prefixWord ++ tailWord_2755589).sum := by decide
  have hdescent : baseEnd_2755589 < baseStart_2755589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755623 : List Nat := [1, 1, 7, 1, 1, 2, 2, 3, 1, 4]
def baseStart_2755623 : Nat := 118140960795 + 2755623 * 2 ^ 59
def prefixEnd_2755623 : Nat := 4983230072969 + 3 ^ 40 * 2755623 * 2
def baseEnd_2755623 : Nat := 471653033861525782013209

theorem tailTrace_2755623 : CollatzResearch.WordTrace tailWord_2755623 prefixEnd_2755623 471653033861525782013209 := by
  unfold tailWord_2755623
  simp only [CollatzResearch.WordTrace]
  refine ⟨100505827695855968785303523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67003885130570645856869015 100505827695855968785303523)
  ·
    refine ⟨150758741543783953177955285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100505827695855968785303523 150758741543783953177955285)
    ·
      refine ⟨3533408004932436402608327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 150758741543783953177955285 3533408004932436402608327)
      ·
        refine ⟨5300112007398654603912491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3533408004932436402608327 5300112007398654603912491)
        ·
          refine ⟨7950168011097981905868737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5300112007398654603912491 7950168011097981905868737)
          ·
            refine ⟨5962626008323486429401553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7950168011097981905868737 5962626008323486429401553)
            ·
              refine ⟨4471969506242614822051165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5962626008323486429401553 4471969506242614822051165)
              ·
                refine ⟨1676988564840980558269187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4471969506242614822051165 1676988564840980558269187)
                ·
                  refine ⟨2515482847261470837403781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1676988564840980558269187 2515482847261470837403781)
                  ·
                    refine ⟨471653033861525782013209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2515482847261470837403781 471653033861525782013209)
                    ·
                      rfl

theorem cell23_2755623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_2755623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2755623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2755623 prefixEnd_2755623 := by exact prefixLift 2755623
  have htrace : WordTrace (prefixWord ++ tailWord_2755623) baseStart_2755623 baseEnd_2755623 := by
    simpa [prefixWord, tailWord_2755623, baseEnd_2755623] using wordTrace_append hprefix tailTrace_2755623
  have hstable : (prefixWord ++ tailWord_2755623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755623).length < 2 ^ (prefixWord ++ tailWord_2755623).sum := by decide
  have hdescent : baseEnd_2755623 < baseStart_2755623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755632 : List Nat := [2, 1, 1, 1, 2, 4, 3, 3, 1, 5]
def baseStart_2755632 : Nat := 118140960795 + 2755632 * 2 ^ 59
def prefixEnd_2755632 : Nat := 4983230072969 + 3 ^ 40 * 2755632 * 2
def baseEnd_2755632 : Nat := 471654574303489270275695

theorem tailTrace_2755632 : CollatzResearch.WordTrace tailWord_2755632 prefixEnd_2755632 471654574303489270275695 := by
  unfold tailWord_2755632
  simp only [CollatzResearch.WordTrace]
  refine ⟨50253077976411681661190575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67004103968548908881587433 50253077976411681661190575)
  ·
    refine ⟨75379616964617522491785863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50253077976411681661190575 75379616964617522491785863)
    ·
      refine ⟨113069425446926283737678795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75379616964617522491785863 113069425446926283737678795)
      ·
        refine ⟨169604138170389425606518193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113069425446926283737678795 169604138170389425606518193)
        ·
          refine ⟨127203103627792069204888645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169604138170389425606518193 127203103627792069204888645)
          ·
            refine ⟨23850581930211012975916621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 127203103627792069204888645 23850581930211012975916621)
            ·
              refine ⟨8943968223829129865968733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23850581930211012975916621 8943968223829129865968733)
              ·
                refine ⟨3353988083935923699738275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8943968223829129865968733 3353988083935923699738275)
                ·
                  refine ⟨5030982125903885549607413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3353988083935923699738275 5030982125903885549607413)
                  ·
                    refine ⟨471654574303489270275695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5030982125903885549607413 471654574303489270275695)
                    ·
                      rfl

theorem cell23_2755632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 3, 1, 5].length) (baseStart_2755632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2755632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2755632 prefixEnd_2755632 := by exact prefixLift 2755632
  have htrace : WordTrace (prefixWord ++ tailWord_2755632) baseStart_2755632 baseEnd_2755632 := by
    simpa [prefixWord, tailWord_2755632, baseEnd_2755632] using wordTrace_append hprefix tailTrace_2755632
  have hstable : (prefixWord ++ tailWord_2755632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755632).length < 2 ^ (prefixWord ++ tailWord_2755632).sum := by decide
  have hdescent : baseEnd_2755632 < baseStart_2755632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755636 : List Nat := [2, 5, 1, 2, 1, 3, 1, 2, 6]
def baseStart_2755636 : Nat := 118140960795 + 2755636 * 2 ^ 59
def prefixEnd_2755636 : Nat := 4983230072969 + 3 ^ 40 * 2755636 * 2
def baseEnd_2755636 : Nat := 157218419648120643908563

theorem tailTrace_2755636 : CollatzResearch.WordTrace tailWord_2755636 prefixEnd_2755636 157218419648120643908563 := by
  unfold tailWord_2755636
  simp only [CollatzResearch.WordTrace]
  refine ⟨50253150922404436002763381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67004201229872581337017841 50253150922404436002763381)
  ·
    refine ⟨4711232898975415875259067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50253150922404436002763381 4711232898975415875259067)
    ·
      refine ⟨7066849348463123812888601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4711232898975415875259067 7066849348463123812888601)
      ·
        refine ⟨5300137011347342859666451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7066849348463123812888601 5300137011347342859666451)
        ·
          refine ⟨7950205517021014289499677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5300137011347342859666451 7950205517021014289499677)
          ·
            refine ⟨2981327068882880358562379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7950205517021014289499677 2981327068882880358562379)
            ·
              refine ⟨4471990603324320537843569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2981327068882880358562379 4471990603324320537843569)
              ·
                refine ⟨3353992952493240403382677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4471990603324320537843569 3353992952493240403382677)
                ·
                  refine ⟨157218419648120643908563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3353992952493240403382677 157218419648120643908563)
                  ·
                    rfl

theorem cell23_2755636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_2755636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2755636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2755636 prefixEnd_2755636 := by exact prefixLift 2755636
  have htrace : WordTrace (prefixWord ++ tailWord_2755636) baseStart_2755636 baseEnd_2755636 := by
    simpa [prefixWord, tailWord_2755636, baseEnd_2755636] using wordTrace_append hprefix tailTrace_2755636
  have hstable : (prefixWord ++ tailWord_2755636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755636).length < 2 ^ (prefixWord ++ tailWord_2755636).sum := by decide
  have hdescent : baseEnd_2755636 < baseStart_2755636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755646 : List Nat := [4, 2, 1, 3, 1, 1, 1, 3, 3, 1, 3]
def baseStart_2755646 : Nat := 118140960795 + 2755646 * 2 ^ 59
def prefixEnd_2755646 : Nat := 4983230072969 + 3 ^ 40 * 2755646 * 2
def baseEnd_2755646 : Nat := 1414970911639630756052021

theorem tailTrace_2755646 : CollatzResearch.WordTrace tailWord_2755646 prefixEnd_2755646 1414970911639630756052021 := by
  unfold tailWord_2755646
  simp only [CollatzResearch.WordTrace]
  refine ⟨12563333321846580464173849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67004444383181762475593861 12563333321846580464173849)
  ·
    refine ⟨9422499991384935348130387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12563333321846580464173849 9422499991384935348130387)
    ·
      refine ⟨14133749987077403022195581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9422499991384935348130387 14133749987077403022195581)
      ·
        refine ⟨5300156245154026133323343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14133749987077403022195581 5300156245154026133323343)
        ·
          refine ⟨7950234367731039199985015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5300156245154026133323343 7950234367731039199985015)
          ·
            refine ⟨11925351551596558799977523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7950234367731039199985015 11925351551596558799977523)
            ·
              refine ⟨17888027327394838199966285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11925351551596558799977523 17888027327394838199966285)
              ·
                refine ⟨6708010247773064324987357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17888027327394838199966285 6708010247773064324987357)
                ·
                  refine ⟨2515503842914899121870259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6708010247773064324987357 2515503842914899121870259)
                  ·
                    refine ⟨3773255764372348682805389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2515503842914899121870259 3773255764372348682805389)
                    ·
                      refine ⟨1414970911639630756052021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3773255764372348682805389 1414970911639630756052021)
                      ·
                        rfl

theorem cell23_2755646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_2755646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2755646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2755646 prefixEnd_2755646 := by exact prefixLift 2755646
  have htrace : WordTrace (prefixWord ++ tailWord_2755646) baseStart_2755646 baseEnd_2755646 := by
    simpa [prefixWord, tailWord_2755646, baseEnd_2755646] using wordTrace_append hprefix tailTrace_2755646
  have hstable : (prefixWord ++ tailWord_2755646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755646).length < 2 ^ (prefixWord ++ tailWord_2755646).sum := by decide
  have hdescent : baseEnd_2755646 < baseStart_2755646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755669 : List Nat := [1, 3, 2, 2, 1, 2, 4, 2, 1, 1, 4]
def baseStart_2755669 : Nat := 118140960795 + 2755669 * 2 ^ 59
def prefixEnd_2755669 : Nat := 4983230072969 + 3 ^ 40 * 2755669 * 2
def baseEnd_2755669 : Nat := 1414982721694684166064415

theorem tailTrace_2755669 : CollatzResearch.WordTrace tailWord_2755669 prefixEnd_2755669 1414982721694684166064415 := by
  unfold tailWord_2755669
  simp only [CollatzResearch.WordTrace]
  refine ⟨100507505453689318641478061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67005003635792879094318707 100507505453689318641478061)
  ·
    refine ⟨37690314545133494490554273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100507505453689318641478061 37690314545133494490554273)
    ·
      refine ⟨28267735908850120867915705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37690314545133494490554273 28267735908850120867915705)
      ·
        refine ⟨21200801931637590650936779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28267735908850120867915705 21200801931637590650936779)
        ·
          refine ⟨31801202897456385976405169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21200801931637590650936779 31801202897456385976405169)
          ·
            refine ⟨23850902173092289482303877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31801202897456385976405169 23850902173092289482303877)
            ·
              refine ⟨4472044157454804277931977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23850902173092289482303877 4472044157454804277931977)
              ·
                refine ⟨3354033118091103208448983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4472044157454804277931977 3354033118091103208448983)
                ·
                  refine ⟨5031049677136654812673475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3354033118091103208448983 5031049677136654812673475)
                  ·
                    refine ⟨7546574515704982219010213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5031049677136654812673475 7546574515704982219010213)
                    ·
                      refine ⟨1414982721694684166064415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7546574515704982219010213 1414982721694684166064415)
                      ·
                        rfl

theorem cell23_2755669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_2755669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2755669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2755669 prefixEnd_2755669 := by exact prefixLift 2755669
  have htrace : WordTrace (prefixWord ++ tailWord_2755669) baseStart_2755669 baseEnd_2755669 := by
    simpa [prefixWord, tailWord_2755669, baseEnd_2755669] using wordTrace_append hprefix tailTrace_2755669
  have hstable : (prefixWord ++ tailWord_2755669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755669).length < 2 ^ (prefixWord ++ tailWord_2755669).sum := by decide
  have hdescent : baseEnd_2755669 < baseStart_2755669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755689 : List Nat := [1, 2, 1, 1, 1, 6, 2, 3, 1, 2, 3]
def baseStart_2755689 : Nat := 118140960795 + 2755689 * 2 ^ 59
def prefixEnd_2755689 : Nat := 4983230072969 + 3 ^ 40 * 2755689 * 2
def baseEnd_2755689 : Nat := 1414992991307774087814323

theorem tailTrace_2755689 : CollatzResearch.WordTrace tailWord_2755689 prefixEnd_2755689 1414992991307774087814323 := by
  unfold tailWord_2755689
  simp only [CollatzResearch.WordTrace]
  refine ⟨100508234913616862057206121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67005489942411241371470747 100508234913616862057206121)
  ·
    refine ⟨75381176185212646542904591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100508234913616862057206121 75381176185212646542904591)
    ·
      refine ⟨113071764277818969814356887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75381176185212646542904591 113071764277818969814356887)
      ·
        refine ⟨169607646416728454721535331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113071764277818969814356887 169607646416728454721535331)
        ·
          refine ⟨254411469625092682082302997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169607646416728454721535331 254411469625092682082302997)
          ·
            refine ⟨11925537638676219472607953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 254411469625092682082302997 11925537638676219472607953)
            ·
              refine ⟨8944153229007164604455965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11925537638676219472607953 8944153229007164604455965)
              ·
                refine ⟨3354057460877686726670987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8944153229007164604455965 3354057460877686726670987)
                ·
                  refine ⟨5031086191316530090006481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3354057460877686726670987 5031086191316530090006481)
                  ·
                    refine ⟨3773314643487397567504861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5031086191316530090006481 3773314643487397567504861)
                    ·
                      refine ⟨1414992991307774087814323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3773314643487397567504861 1414992991307774087814323)
                      ·
                        rfl

theorem cell23_2755689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 3, 1, 2, 3].length) (baseStart_2755689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2755689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2755689 prefixEnd_2755689 := by exact prefixLift 2755689
  have htrace : WordTrace (prefixWord ++ tailWord_2755689) baseStart_2755689 baseEnd_2755689 := by
    simpa [prefixWord, tailWord_2755689, baseEnd_2755689] using wordTrace_append hprefix tailTrace_2755689
  have hstable : (prefixWord ++ tailWord_2755689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755689).length < 2 ^ (prefixWord ++ tailWord_2755689).sum := by decide
  have hdescent : baseEnd_2755689 < baseStart_2755689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755713 : List Nat := [1, 2, 4, 2, 2, 3, 2, 1, 2, 4]
def baseStart_2755713 : Nat := 118140960795 + 2755713 * 2 ^ 59
def prefixEnd_2755713 : Nat := 4983230072969 + 3 ^ 40 * 2755713 * 2
def baseEnd_2755713 : Nat := 471668438281160664638071

theorem tailTrace_2755713 : CollatzResearch.WordTrace tailWord_2755713 prefixEnd_2755713 471668438281160664638071 := by
  unfold tailWord_2755713
  simp only [CollatzResearch.WordTrace]
  refine ⟨100509110265529914156079793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67006073510353276104053195 100509110265529914156079793)
  ·
    refine ⟨75381832699147435617059845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100509110265529914156079793 75381832699147435617059845)
    ·
      refine ⟨14134093631090144178198721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75381832699147435617059845 14134093631090144178198721)
      ·
        refine ⟨10600570223317608133649041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14134093631090144178198721 10600570223317608133649041)
        ·
          refine ⟨7950427667488206100236781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10600570223317608133649041 7950427667488206100236781)
          ·
            refine ⟨2981410375308077287588793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7950427667488206100236781 2981410375308077287588793)
            ·
              refine ⟨2236057781481057965691595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2981410375308077287588793 2236057781481057965691595)
              ·
                refine ⟨3354086672221586948537393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2236057781481057965691595 3354086672221586948537393)
                ·
                  refine ⟨2515565004166190211403045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3354086672221586948537393 2515565004166190211403045)
                  ·
                    refine ⟨471668438281160664638071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2515565004166190211403045 471668438281160664638071)
                    ·
                      rfl

theorem cell23_2755713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_2755713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2755713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2755713 prefixEnd_2755713 := by exact prefixLift 2755713
  have htrace : WordTrace (prefixWord ++ tailWord_2755713) baseStart_2755713 baseEnd_2755713 := by
    simpa [prefixWord, tailWord_2755713, baseEnd_2755713] using wordTrace_append hprefix tailTrace_2755713
  have hstable : (prefixWord ++ tailWord_2755713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755713).length < 2 ^ (prefixWord ++ tailWord_2755713).sum := by decide
  have hdescent : baseEnd_2755713 < baseStart_2755713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755754 : List Nat := [3, 1, 5, 1, 1, 3, 2, 2, 1, 2, 2]
def baseStart_2755754 : Nat := 118140960795 + 2755754 * 2 ^ 59
def prefixEnd_2755754 : Nat := 4983230072969 + 3 ^ 40 * 2755754 * 2
def baseEnd_2755754 : Nat := 1415026367550316333501525

theorem tailTrace_2755754 : CollatzResearch.WordTrace tailWord_2755754 prefixEnd_2755754 1415026367550316333501525 := by
  unfold tailWord_2755754
  simp only [CollatzResearch.WordTrace]
  refine ⟨25127651414595344539580579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67007070438920918772214877 25127651414595344539580579)
  ·
    refine ⟨37691477121893016809370869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25127651414595344539580579 37691477121893016809370869)
    ·
      refine ⟨3533575980177470325878519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37691477121893016809370869 3533575980177470325878519)
      ·
        refine ⟨5300363970266205488817779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3533575980177470325878519 5300363970266205488817779)
        ·
          refine ⟨7950545955399308233226669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5300363970266205488817779 7950545955399308233226669)
          ·
            refine ⟨2981454733274740587460001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7950545955399308233226669 2981454733274740587460001)
            ·
              refine ⟨2236091049956055440595001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2981454733274740587460001 2236091049956055440595001)
              ·
                refine ⟨1677068287467041580446251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2236091049956055440595001 1677068287467041580446251)
                ·
                  refine ⟨2515602431200562370669377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1677068287467041580446251 2515602431200562370669377)
                  ·
                    refine ⟨1886701823400421778002033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2515602431200562370669377 1886701823400421778002033)
                    ·
                      refine ⟨1415026367550316333501525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1886701823400421778002033 1415026367550316333501525)
                      ·
                        rfl

theorem cell23_2755754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_2755754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2755754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2755754 prefixEnd_2755754 := by exact prefixLift 2755754
  have htrace : WordTrace (prefixWord ++ tailWord_2755754) baseStart_2755754 baseEnd_2755754 := by
    simpa [prefixWord, tailWord_2755754, baseEnd_2755754] using wordTrace_append hprefix tailTrace_2755754
  have hstable : (prefixWord ++ tailWord_2755754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755754).length < 2 ^ (prefixWord ++ tailWord_2755754).sum := by decide
  have hdescent : baseEnd_2755754 < baseStart_2755754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755799 : List Nat := [1, 1, 3, 2, 1, 2, 3, 5, 5]
def baseStart_2755799 : Nat := 118140960795 + 2755799 * 2 ^ 59
def prefixEnd_2755799 : Nat := 4983230072969 + 3 ^ 40 * 2755799 * 2
def baseEnd_2755799 : Nat := 157227719353307628604313

theorem tailTrace_2755799 : CollatzResearch.WordTrace tailWord_2755799 prefixEnd_2755799 157227719353307628604313 := by
  unfold tailWord_2755799
  simp only [CollatzResearch.WordTrace]
  refine ⟨100512246943218350843710451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67008164628812233895806967 100512246943218350843710451)
  ·
    refine ⟨150768370414827526265565677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100512246943218350843710451 150768370414827526265565677)
    ·
      refine ⟨56538138905560322349587129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150768370414827526265565677 56538138905560322349587129)
      ·
        refine ⟨42403604179170241762190347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56538138905560322349587129 42403604179170241762190347)
        ·
          refine ⟨63605406268755362643285521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42403604179170241762190347 63605406268755362643285521)
          ·
            refine ⟨47704054701566521982464141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63605406268755362643285521 47704054701566521982464141)
            ·
              refine ⟨17889020513087445743424053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47704054701566521982464141 17889020513087445743424053)
              ·
                refine ⟨1677095673101948038446005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17889020513087445743424053 1677095673101948038446005)
                ·
                  refine ⟨157227719353307628604313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1677095673101948038446005 157227719353307628604313)
                  ·
                    rfl

theorem cell23_2755799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 5, 5].length) (baseStart_2755799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2755799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2755799 prefixEnd_2755799 := by exact prefixLift 2755799
  have htrace : WordTrace (prefixWord ++ tailWord_2755799) baseStart_2755799 baseEnd_2755799 := by
    simpa [prefixWord, tailWord_2755799, baseEnd_2755799] using wordTrace_append hprefix tailTrace_2755799
  have hstable : (prefixWord ++ tailWord_2755799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755799).length < 2 ^ (prefixWord ++ tailWord_2755799).sum := by decide
  have hdescent : baseEnd_2755799 < baseStart_2755799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755809 : List Nat := [1, 2, 3, 1, 3, 2, 1, 2, 2, 3, 3]
def baseStart_2755809 : Nat := 118140960795 + 2755809 * 2 ^ 59
def prefixEnd_2755809 : Nat := 4983230072969 + 3 ^ 40 * 2755809 * 2
def baseEnd_2755809 : Nat := 1415054608986313618313771

theorem tailTrace_2755809 : CollatzResearch.WordTrace tailWord_2755809 prefixEnd_2755809 1415054608986313618313771 := by
  unfold tailWord_2755809
  simp only [CollatzResearch.WordTrace]
  refine ⟨100512611673182122551574481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67008407782121415034382987 100512611673182122551574481)
  ·
    refine ⟨75384458754886591913680861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100512611673182122551574481 75384458754886591913680861)
    ·
      refine ⟨28269172033082471967630323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75384458754886591913680861 28269172033082471967630323)
      ·
        refine ⟨42403758049623707951445485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28269172033082471967630323 42403758049623707951445485)
        ·
          refine ⟨15901409268608890481792057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42403758049623707951445485 15901409268608890481792057)
          ·
            refine ⟨11926056951456667861344043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15901409268608890481792057 11926056951456667861344043)
            ·
              refine ⟨17889085427185001792016065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11926056951456667861344043 17889085427185001792016065)
              ·
                refine ⟨13416814070388751344012049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17889085427185001792016065 13416814070388751344012049)
                ·
                  refine ⟨10062610552791563508009037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13416814070388751344012049 10062610552791563508009037)
                  ·
                    refine ⟨3773478957296836315503389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10062610552791563508009037 3773478957296836315503389)
                    ·
                      refine ⟨1415054608986313618313771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3773478957296836315503389 1415054608986313618313771)
                      ·
                        rfl

theorem cell23_2755809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 3, 3].length) (baseStart_2755809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2755809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2755809 prefixEnd_2755809 := by exact prefixLift 2755809
  have htrace : WordTrace (prefixWord ++ tailWord_2755809) baseStart_2755809 baseEnd_2755809 := by
    simpa [prefixWord, tailWord_2755809, baseEnd_2755809] using wordTrace_append hprefix tailTrace_2755809
  have hstable : (prefixWord ++ tailWord_2755809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755809).length < 2 ^ (prefixWord ++ tailWord_2755809).sum := by decide
  have hdescent : baseEnd_2755809 < baseStart_2755809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755849 : List Nat := [1, 2, 1, 1, 3, 3, 2, 3, 2, 1, 4]
def baseStart_2755849 : Nat := 118140960795 + 2755849 * 2 ^ 59
def prefixEnd_2755849 : Nat := 4983230072969 + 3 ^ 40 * 2755849 * 2
def baseEnd_2755849 : Nat := 1415075148212493461813587

theorem tailTrace_2755849 : CollatzResearch.WordTrace tailWord_2755849 prefixEnd_2755849 1415075148212493461813587 := by
  unfold tailWord_2755849
  simp only [CollatzResearch.WordTrace]
  refine ⟨100514070593037209383030601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67009380395358139588687067 100514070593037209383030601)
  ·
    refine ⟨75385552944777907037272951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100514070593037209383030601 75385552944777907037272951)
    ·
      refine ⟨113078329417166860555909427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75385552944777907037272951 113078329417166860555909427)
      ·
        refine ⟨169617494125750290833864141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113078329417166860555909427 169617494125750290833864141)
        ·
          refine ⟨63606560297156359062699053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169617494125750290833864141 63606560297156359062699053)
          ·
            refine ⟨23852460111433634648512145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63606560297156359062699053 23852460111433634648512145)
            ·
              refine ⟨17889345083575225986384109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23852460111433634648512145 17889345083575225986384109)
              ·
                refine ⟨6708504406340709744894041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17889345083575225986384109 6708504406340709744894041)
                ·
                  refine ⟨5031378304755532308670531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6708504406340709744894041 5031378304755532308670531)
                  ·
                    refine ⟨7547067457133298463005797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5031378304755532308670531 7547067457133298463005797)
                    ·
                      refine ⟨1415075148212493461813587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7547067457133298463005797 1415075148212493461813587)
                      ·
                        rfl

theorem cell23_2755849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 2, 1, 4].length) (baseStart_2755849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2755849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2755849 prefixEnd_2755849 := by exact prefixLift 2755849
  have htrace : WordTrace (prefixWord ++ tailWord_2755849) baseStart_2755849 baseEnd_2755849 := by
    simpa [prefixWord, tailWord_2755849, baseEnd_2755849] using wordTrace_append hprefix tailTrace_2755849
  have hstable : (prefixWord ++ tailWord_2755849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755849).length < 2 ^ (prefixWord ++ tailWord_2755849).sum := by decide
  have hdescent : baseEnd_2755849 < baseStart_2755849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755866 : List Nat := [3, 1, 1, 3, 3, 2, 1, 2, 2, 1, 4]
def baseStart_2755866 : Nat := 118140960795 + 2755866 * 2 ^ 59
def prefixEnd_2755866 : Nat := 4983230072969 + 3 ^ 40 * 2755866 * 2
def baseEnd_2755866 : Nat := 1415083877383619895301009

theorem tailTrace_2755866 : CollatzResearch.WordTrace tailWord_2755866 prefixEnd_2755866 1415083877383619895301009 := by
  unfold tailWord_2755866
  simp only [CollatzResearch.WordTrace]
  refine ⟨25128672658493905321599863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67009793755983747524266301 25128672658493905321599863)
  ·
    refine ⟨37693008987740857982399795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25128672658493905321599863 37693008987740857982399795)
    ·
      refine ⟨56539513481611286973599693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37693008987740857982399795 56539513481611286973599693)
      ·
        refine ⟨21202317555604232615099885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56539513481611286973599693 21202317555604232615099885)
        ·
          refine ⟨7950869083351587230662457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21202317555604232615099885 7950869083351587230662457)
          ·
            refine ⟨5963151812513690422996843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7950869083351587230662457 5963151812513690422996843)
            ·
              refine ⟨8944727718770535634495265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5963151812513690422996843 8944727718770535634495265)
              ·
                refine ⟨6708545789077901725871449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8944727718770535634495265 6708545789077901725871449)
                ·
                  refine ⟨5031409341808426294403587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6708545789077901725871449 5031409341808426294403587)
                  ·
                    refine ⟨7547114012712639441605381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5031409341808426294403587 7547114012712639441605381)
                    ·
                      refine ⟨1415083877383619895301009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7547114012712639441605381 1415083877383619895301009)
                      ·
                        rfl

theorem cell23_2755866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_2755866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2755866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2755866 prefixEnd_2755866 := by exact prefixLift 2755866
  have htrace : WordTrace (prefixWord ++ tailWord_2755866) baseStart_2755866 baseEnd_2755866 := by
    simpa [prefixWord, tailWord_2755866, baseEnd_2755866] using wordTrace_append hprefix tailTrace_2755866
  have hstable : (prefixWord ++ tailWord_2755866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755866).length < 2 ^ (prefixWord ++ tailWord_2755866).sum := by decide
  have hdescent : baseEnd_2755866 < baseStart_2755866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755970 : List Nat := [3, 4, 2, 1, 1, 2, 1, 3, 1, 5]
def baseStart_2755970 : Nat := 118140960795 + 2755970 * 2 ^ 59
def prefixEnd_2755970 : Nat := 4983230072969 + 3 ^ 40 * 2755970 * 2
def baseEnd_2755970 : Nat := 471712426457229162800177

theorem tailTrace_2755970 : CollatzResearch.WordTrace tailWord_2755970 prefixEnd_2755970 471712426457229162800177 := by
  unfold tailWord_2755970
  simp only [CollatzResearch.WordTrace]
  refine ⟨25129620956399711762046341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67012322550399231365456909 25129620956399711762046341)
  ·
    refine ⟨4711803929324945955383689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25129620956399711762046341 4711803929324945955383689)
    ·
      refine ⟨3533852946993709466537767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4711803929324945955383689 3533852946993709466537767)
      ·
        refine ⟨5300779420490564199806651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3533852946993709466537767 5300779420490564199806651)
        ·
          refine ⟨7951169130735846299709977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5300779420490564199806651 7951169130735846299709977)
          ·
            refine ⟨5963376848051884724782483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7951169130735846299709977 5963376848051884724782483)
            ·
              refine ⟨8945065272077827087173725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5963376848051884724782483 8945065272077827087173725)
              ·
                refine ⟨3354399477029185157690147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8945065272077827087173725 3354399477029185157690147)
                ·
                  refine ⟨5031599215543777736535221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3354399477029185157690147 5031599215543777736535221)
                  ·
                    refine ⟨471712426457229162800177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5031599215543777736535221 471712426457229162800177)
                    ·
                      rfl

theorem cell23_2755970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_2755970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2755970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2755970 prefixEnd_2755970 := by exact prefixLift 2755970
  have htrace : WordTrace (prefixWord ++ tailWord_2755970) baseStart_2755970 baseEnd_2755970 := by
    simpa [prefixWord, tailWord_2755970, baseEnd_2755970] using wordTrace_append hprefix tailTrace_2755970
  have hstable : (prefixWord ++ tailWord_2755970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755970).length < 2 ^ (prefixWord ++ tailWord_2755970).sum := by decide
  have hdescent : baseEnd_2755970 < baseStart_2755970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755973 : List Nat := [1, 3, 1, 1, 3, 1, 6, 1, 1, 1, 4]
def baseStart_2755973 : Nat := 118140960795 + 2755973 * 2 ^ 59
def prefixEnd_2755973 : Nat := 4983230072969 + 3 ^ 40 * 2755973 * 2
def baseEnd_2755973 : Nat := 1415138819813650976663017

theorem tailTrace_2755973 : CollatzResearch.WordTrace tailWord_2755973 prefixEnd_2755973 1415138819813650976663017 := by
  unfold tailWord_2755973
  simp only [CollatzResearch.WordTrace]
  refine ⟨100518593244587978560544573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67012395496391985707029715 100518593244587978560544573)
  ·
    refine ⟨37694472466720491960204215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100518593244587978560544573 37694472466720491960204215)
    ·
      refine ⟨56541708700080737940306323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37694472466720491960204215 56541708700080737940306323)
      ·
        refine ⟨84812563050121106910459485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56541708700080737940306323 84812563050121106910459485)
        ·
          refine ⟨31804711143795415091422307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84812563050121106910459485 31804711143795415091422307)
          ·
            refine ⟨47707066715693122637133461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31804711143795415091422307 47707066715693122637133461)
            ·
              refine ⟨2236268752298115123615631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 47707066715693122637133461 2236268752298115123615631)
              ·
                refine ⟨3354403128447172685423447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2236268752298115123615631 3354403128447172685423447)
                ·
                  refine ⟨5031604692670759028135171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3354403128447172685423447 5031604692670759028135171)
                  ·
                    refine ⟨7547407039006138542202757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5031604692670759028135171 7547407039006138542202757)
                    ·
                      refine ⟨1415138819813650976663017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7547407039006138542202757 1415138819813650976663017)
                      ·
                        rfl

theorem cell23_2755973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 1, 1, 1, 4].length) (baseStart_2755973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2755973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2755973 prefixEnd_2755973 := by exact prefixLift 2755973
  have htrace : WordTrace (prefixWord ++ tailWord_2755973) baseStart_2755973 baseEnd_2755973 := by
    simpa [prefixWord, tailWord_2755973, baseEnd_2755973] using wordTrace_append hprefix tailTrace_2755973
  have hstable : (prefixWord ++ tailWord_2755973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755973).length < 2 ^ (prefixWord ++ tailWord_2755973).sum := by decide
  have hdescent : baseEnd_2755973 < baseStart_2755973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756013 : List Nat := [1, 5, 2, 2, 1, 1, 4, 7]
def baseStart_2756013 : Nat := 118140960795 + 2756013 * 2 ^ 59
def prefixEnd_2756013 : Nat := 4983230072969 + 3 ^ 40 * 2756013 * 2
def baseEnd_2756013 : Nat := 52413309594067808154179

theorem tailTrace_2756013 : CollatzResearch.WordTrace tailWord_2756013 prefixEnd_2756013 52413309594067808154179 := by
  unfold tailWord_2756013
  simp only [CollatzResearch.WordTrace]
  refine ⟨100520052164443065392000693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67013368109628710261333795 100520052164443065392000693)
  ·
    refine ⟨9423754890416537380500065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 100520052164443065392000693 9423754890416537380500065)
    ·
      refine ⟨7067816167812403035375049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9423754890416537380500065 7067816167812403035375049)
      ·
        refine ⟨5300862125859302276531287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7067816167812403035375049 5300862125859302276531287)
        ·
          refine ⟨7951293188788953414796931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5300862125859302276531287 7951293188788953414796931)
          ·
            refine ⟨11926939783183430122195397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7951293188788953414796931 11926939783183430122195397)
            ·
              refine ⟨2236301209346893147911637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11926939783183430122195397 2236301209346893147911637)
              ·
                refine ⟨52413309594067808154179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2236301209346893147911637 52413309594067808154179)
                ·
                  rfl

theorem cell23_2756013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 7].length) (baseStart_2756013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2756013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2756013 prefixEnd_2756013 := by exact prefixLift 2756013
  have htrace : WordTrace (prefixWord ++ tailWord_2756013) baseStart_2756013 baseEnd_2756013 := by
    simpa [prefixWord, tailWord_2756013, baseEnd_2756013] using wordTrace_append hprefix tailTrace_2756013
  have hstable : (prefixWord ++ tailWord_2756013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756013).length < 2 ^ (prefixWord ++ tailWord_2756013).sum := by decide
  have hdescent : baseEnd_2756013 < baseStart_2756013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756057 : List Nat := [1, 2, 1, 2, 4, 4, 2, 1, 2, 1, 3]
def baseStart_2756057 : Nat := 118140960795 + 2756057 * 2 ^ 59
def prefixEnd_2756057 : Nat := 4983230072969 + 3 ^ 40 * 2756057 * 2
def baseEnd_2756057 : Nat := 1415181952188628648012631

theorem tailTrace_2756057 : CollatzResearch.WordTrace tailWord_2756057 prefixEnd_2756057 1415181952188628648012631 := by
  unfold tailWord_2756057
  simp only [CollatzResearch.WordTrace]
  refine ⟨100521656976283660906602425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67014437984189107271068283 100521656976283660906602425)
  ·
    refine ⟨75391242732212745679951819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100521656976283660906602425 75391242732212745679951819)
    ·
      refine ⟨113086864098319118519927729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75391242732212745679951819 113086864098319118519927729)
      ·
        refine ⟨84815148073739338889945797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113086864098319118519927729 84815148073739338889945797)
        ·
          refine ⟨15902840263826126041864837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84815148073739338889945797 15902840263826126041864837)
          ·
            refine ⟨2981782549467398632849657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15902840263826126041864837 2981782549467398632849657)
            ·
              refine ⟨2236336912100548974637243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2981782549467398632849657 2236336912100548974637243)
              ·
                refine ⟨3354505368150823461955865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2236336912100548974637243 3354505368150823461955865)
                ·
                  refine ⟨2515879026113117596466899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3354505368150823461955865 2515879026113117596466899)
                  ·
                    refine ⟨3773818539169676394700349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2515879026113117596466899 3773818539169676394700349)
                    ·
                      refine ⟨1415181952188628648012631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3773818539169676394700349 1415181952188628648012631)
                      ·
                        rfl

theorem cell23_2756057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 1, 2, 1, 3].length) (baseStart_2756057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2756057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2756057 prefixEnd_2756057 := by exact prefixLift 2756057
  have htrace : WordTrace (prefixWord ++ tailWord_2756057) baseStart_2756057 baseEnd_2756057 := by
    simpa [prefixWord, tailWord_2756057, baseEnd_2756057] using wordTrace_append hprefix tailTrace_2756057
  have hstable : (prefixWord ++ tailWord_2756057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756057).length < 2 ^ (prefixWord ++ tailWord_2756057).sum := by decide
  have hdescent : baseEnd_2756057 < baseStart_2756057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756063 : List Nat := [1, 1, 2, 3, 3, 1, 2, 3, 1, 4, 2]
def baseStart_2756063 : Nat := 118140960795 + 2756063 * 2 ^ 59
def prefixEnd_2756063 : Nat := 4983230072969 + 3 ^ 40 * 2756063 * 2
def baseEnd_2756063 : Nat := 1415185033072555624537603

theorem tailTrace_2756063 : CollatzResearch.WordTrace tailWord_2756063 prefixEnd_2756063 1415185033072555624537603 := by
  unfold tailWord_2756063
  simp only [CollatzResearch.WordTrace]
  refine ⟨100521875814261923931320843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67014583876174615954213895 100521875814261923931320843)
  ·
    refine ⟨150782813721392885896981265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100521875814261923931320843 150782813721392885896981265)
    ·
      refine ⟨113087110291044664422735949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150782813721392885896981265 113087110291044664422735949)
      ·
        refine ⟨42407666359141749158525981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113087110291044664422735949 42407666359141749158525981)
        ·
          refine ⟨15902874884678155934447243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42407666359141749158525981 15902874884678155934447243)
          ·
            refine ⟨23854312327017233901670865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15902874884678155934447243 23854312327017233901670865)
            ·
              refine ⟨17890734245262925426253149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23854312327017233901670865 17890734245262925426253149)
              ·
                refine ⟨6709025341973597034844931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17890734245262925426253149 6709025341973597034844931)
                ·
                  refine ⟨10063538012960395552267397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6709025341973597034844931 10063538012960395552267397)
                  ·
                    refine ⟨1886913377430074166050137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10063538012960395552267397 1886913377430074166050137)
                    ·
                      refine ⟨1415185033072555624537603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1886913377430074166050137 1415185033072555624537603)
                      ·
                        rfl

theorem cell23_2756063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 4, 2].length) (baseStart_2756063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2756063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2756063 prefixEnd_2756063 := by exact prefixLift 2756063
  have htrace : WordTrace (prefixWord ++ tailWord_2756063) baseStart_2756063 baseEnd_2756063 := by
    simpa [prefixWord, tailWord_2756063, baseEnd_2756063] using wordTrace_append hprefix tailTrace_2756063
  have hstable : (prefixWord ++ tailWord_2756063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756063).length < 2 ^ (prefixWord ++ tailWord_2756063).sum := by decide
  have hdescent : baseEnd_2756063 < baseStart_2756063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756067 : List Nat := [1, 1, 1, 6, 2, 3, 1, 2, 1, 3, 2]
def baseStart_2756067 : Nat := 118140960795 + 2756067 * 2 ^ 59
def prefixEnd_2756067 : Nat := 4983230072969 + 3 ^ 40 * 2756067 * 2
def baseEnd_2756067 : Nat := 1415187086995173608887585

theorem tailTrace_2756067 : CollatzResearch.WordTrace tailWord_2756067 prefixEnd_2756067 1415187086995173608887585 := by
  unfold tailWord_2756067
  simp only [CollatzResearch.WordTrace]
  refine ⟨100522021706247432614466455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67014681137498288409644303 100522021706247432614466455)
  ·
    refine ⟨150783032559371148921699683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100522021706247432614466455 150783032559371148921699683)
    ·
      refine ⟨226174548839056723382549525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150783032559371148921699683 226174548839056723382549525)
      ·
        refine ⟨10601931976830783908557009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 226174548839056723382549525 10601931976830783908557009)
        ·
          refine ⟨7951448982623087931417757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10601931976830783908557009 7951448982623087931417757)
          ·
            refine ⟨2981793368483657974281659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7951448982623087931417757 2981793368483657974281659)
            ·
              refine ⟨4472690052725486961422489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2981793368483657974281659 4472690052725486961422489)
              ·
                refine ⟨3354517539544115221066867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4472690052725486961422489 3354517539544115221066867)
                ·
                  refine ⟨5031776309316172831600301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3354517539544115221066867 5031776309316172831600301)
                  ·
                    refine ⟨1886916115993564811850113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5031776309316172831600301 1886916115993564811850113)
                    ·
                      refine ⟨1415187086995173608887585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1886916115993564811850113 1415187086995173608887585)
                      ·
                        rfl

theorem cell23_2756067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_2756067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2756067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2756067 prefixEnd_2756067 := by exact prefixLift 2756067
  have htrace : WordTrace (prefixWord ++ tailWord_2756067) baseStart_2756067 baseEnd_2756067 := by
    simpa [prefixWord, tailWord_2756067, baseEnd_2756067] using wordTrace_append hprefix tailTrace_2756067
  have hstable : (prefixWord ++ tailWord_2756067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756067).length < 2 ^ (prefixWord ++ tailWord_2756067).sum := by decide
  have hdescent : baseEnd_2756067 < baseStart_2756067 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756197 : List Nat := [1, 3, 1, 3, 3, 1, 3, 3, 1, 4]
def baseStart_2756197 : Nat := 118140960795 + 2756197 * 2 ^ 59
def prefixEnd_2756197 : Nat := 4983230072969 + 3 ^ 40 * 2756197 * 2
def baseEnd_2756197 : Nat := 471751279826752700087329

theorem tailTrace_2756197 : CollatzResearch.WordTrace tailWord_2756197 prefixEnd_2756197 471751279826752700087329 := by
  unfold tailWord_2756197
  simp only [CollatzResearch.WordTrace]
  refine ⟨100526763195776464816698845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67017842130517643211132563 100526763195776464816698845)
  ·
    refine ⟨37697536198416174306262067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100526763195776464816698845 37697536198416174306262067)
    ·
      refine ⟨56546304297624261459393101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37697536198416174306262067 56546304297624261459393101)
      ·
        refine ⟨21204864111609098047272413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56546304297624261459393101 21204864111609098047272413)
        ·
          refine ⟨7951824041853411767727155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21204864111609098047272413 7951824041853411767727155)
          ·
            refine ⟨11927736062780117651590733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7951824041853411767727155 11927736062780117651590733)
            ·
              refine ⟨4472901023542544119346525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11927736062780117651590733 4472901023542544119346525)
              ·
                refine ⟨1677337883828454044754947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4472901023542544119346525 1677337883828454044754947)
                ·
                  refine ⟨2516006825742681067132421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1677337883828454044754947 2516006825742681067132421)
                  ·
                    refine ⟨471751279826752700087329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2516006825742681067132421 471751279826752700087329)
                    ·
                      rfl

theorem cell23_2756197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 3, 1, 4].length) (baseStart_2756197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2756197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2756197 prefixEnd_2756197 := by exact prefixLift 2756197
  have htrace : WordTrace (prefixWord ++ tailWord_2756197) baseStart_2756197 baseEnd_2756197 := by
    simpa [prefixWord, tailWord_2756197, baseEnd_2756197] using wordTrace_append hprefix tailTrace_2756197
  have hstable : (prefixWord ++ tailWord_2756197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756197).length < 2 ^ (prefixWord ++ tailWord_2756197).sum := by decide
  have hdescent : baseEnd_2756197 < baseStart_2756197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756247 : List Nat := [1, 1, 3, 3, 2, 3, 2, 1, 2, 3, 2]
def baseStart_2756247 : Nat := 118140960795 + 2756247 * 2 ^ 59
def prefixEnd_2756247 : Nat := 4983230072969 + 3 ^ 40 * 2756247 * 2
def baseEnd_2756247 : Nat := 1415279513512982904636757

theorem tailTrace_2756247 : CollatzResearch.WordTrace tailWord_2756247 prefixEnd_2756247 1415279513512982904636757 := by
  unfold tailWord_2756247
  simp only [CollatzResearch.WordTrace]
  refine ⟨100528586845595323356018995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67019057897063548904012663 100528586845595323356018995)
  ·
    refine ⟨150792880268392985034028493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100528586845595323356018995 150792880268392985034028493)
    ·
      refine ⟨56547330100647369387760685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150792880268392985034028493 56547330100647369387760685)
      ·
        refine ⟨21205248787742763520410257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56547330100647369387760685 21205248787742763520410257)
        ·
          refine ⟨15903936590807072640307693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21205248787742763520410257 15903936590807072640307693)
          ·
            refine ⟨5963976221552652240115385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15903936590807072640307693 5963976221552652240115385)
            ·
              refine ⟨4472982166164489180086539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5963976221552652240115385 4472982166164489180086539)
              ·
                refine ⟨6709473249246733770129809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4472982166164489180086539 6709473249246733770129809)
                ·
                  refine ⟨5032104936935050327597357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6709473249246733770129809 5032104936935050327597357)
                  ·
                    refine ⟨1887039351350643872849009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5032104936935050327597357 1887039351350643872849009)
                    ·
                      refine ⟨1415279513512982904636757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1887039351350643872849009 1415279513512982904636757)
                      ·
                        rfl

theorem cell23_2756247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 2, 3, 2].length) (baseStart_2756247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2756247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2756247 prefixEnd_2756247 := by exact prefixLift 2756247
  have htrace : WordTrace (prefixWord ++ tailWord_2756247) baseStart_2756247 baseEnd_2756247 := by
    simpa [prefixWord, tailWord_2756247, baseEnd_2756247] using wordTrace_append hprefix tailTrace_2756247
  have hstable : (prefixWord ++ tailWord_2756247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756247).length < 2 ^ (prefixWord ++ tailWord_2756247).sum := by decide
  have hdescent : baseEnd_2756247 < baseStart_2756247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756257 : List Nat := [1, 2, 3, 3, 2, 2, 3, 1, 1, 5]
def baseStart_2756257 : Nat := 118140960795 + 2756257 * 2 ^ 59
def prefixEnd_2756257 : Nat := 4983230072969 + 3 ^ 40 * 2756257 * 2
def baseEnd_2756257 : Nat := 471761549439842621837237

theorem tailTrace_2756257 : CollatzResearch.WordTrace tailWord_2756257 prefixEnd_2756257 471761549439842621837237 := by
  unfold tailWord_2756257
  simp only [CollatzResearch.WordTrace]
  refine ⟨100528951575559095063883025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67019301050372730042588683 100528951575559095063883025)
  ·
    refine ⟨75396713681669321297912269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100528951575559095063883025 75396713681669321297912269)
    ·
      refine ⟨28273767630625995486717101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75396713681669321297912269 28273767630625995486717101)
      ·
        refine ⟨10602662861484748307518913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28273767630625995486717101 10602662861484748307518913)
        ·
          refine ⟨7951997146113561230639185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10602662861484748307518913 7951997146113561230639185)
          ·
            refine ⟨5963997859585170922979389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7951997146113561230639185 5963997859585170922979389)
            ·
              refine ⟨2236499197344439096117271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5963997859585170922979389 2236499197344439096117271)
              ·
                refine ⟨3354748796016658644175907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2236499197344439096117271 3354748796016658644175907)
                ·
                  refine ⟨5032123194024987966263861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3354748796016658644175907 5032123194024987966263861)
                  ·
                    refine ⟨471761549439842621837237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5032123194024987966263861 471761549439842621837237)
                    ·
                      rfl

theorem cell23_2756257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 1, 1, 5].length) (baseStart_2756257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2756257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2756257 prefixEnd_2756257 := by exact prefixLift 2756257
  have htrace : WordTrace (prefixWord ++ tailWord_2756257) baseStart_2756257 baseEnd_2756257 := by
    simpa [prefixWord, tailWord_2756257, baseEnd_2756257] using wordTrace_append hprefix tailTrace_2756257
  have hstable : (prefixWord ++ tailWord_2756257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756257).length < 2 ^ (prefixWord ++ tailWord_2756257).sum := by decide
  have hdescent : baseEnd_2756257 < baseStart_2756257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756293 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 5, 3, 3]
def baseStart_2756293 : Nat := 118140960795 + 2756293 * 2 ^ 59
def prefixEnd_2756293 : Nat := 4983230072969 + 3 ^ 40 * 2756293 * 2
def baseEnd_2756293 : Nat := 1415303133623089724661545

theorem tailTrace_2756293 : CollatzResearch.WordTrace tailWord_2756293 prefixEnd_2756293 1415303133623089724661545 := by
  unfold tailWord_2756293
  simp only [CollatzResearch.WordTrace]
  refine ⟨100530264603428673212193533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67020176402285782141462355 100530264603428673212193533)
  ·
    refine ⟨37698849226285752454572575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100530264603428673212193533 37698849226285752454572575)
    ·
      refine ⟨56548273839428628681858863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37698849226285752454572575 56548273839428628681858863)
      ·
        refine ⟨84822410759142943022788295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56548273839428628681858863 84822410759142943022788295)
        ·
          refine ⟨127233616138714414534182443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84822410759142943022788295 127233616138714414534182443)
          ·
            refine ⟨190850424208071621801273665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127233616138714414534182443 190850424208071621801273665)
            ·
              refine ⟨143137818156053716350955249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190850424208071621801273665 143137818156053716350955249)
              ·
                refine ⟨107353363617040287263216437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143137818156053716350955249 107353363617040287263216437)
                ·
                  refine ⟨10064377839097526930926541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 107353363617040287263216437 10064377839097526930926541)
                  ·
                    refine ⟨3774141689661572599097453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10064377839097526930926541 3774141689661572599097453)
                    ·
                      refine ⟨1415303133623089724661545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3774141689661572599097453 1415303133623089724661545)
                      ·
                        rfl

theorem cell23_2756293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 3, 3].length) (baseStart_2756293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2756293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2756293 prefixEnd_2756293 := by exact prefixLift 2756293
  have htrace : WordTrace (prefixWord ++ tailWord_2756293) baseStart_2756293 baseEnd_2756293 := by
    simpa [prefixWord, tailWord_2756293, baseEnd_2756293] using wordTrace_append hprefix tailTrace_2756293
  have hstable : (prefixWord ++ tailWord_2756293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756293).length < 2 ^ (prefixWord ++ tailWord_2756293).sum := by decide
  have hdescent : baseEnd_2756293 < baseStart_2756293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756294 : List Nat := [6, 1, 2, 1, 1, 1, 2, 1, 3, 1, 4]
def baseStart_2756294 : Nat := 118140960795 + 2756294 * 2 ^ 59
def prefixEnd_2756294 : Nat := 4983230072969 + 3 ^ 40 * 2756294 * 2
def baseEnd_2756294 : Nat := 1415303647103744220749041

theorem tailTrace_2756294 : CollatzResearch.WordTrace tailWord_2756294 prefixEnd_2756294 1415303647103744220749041 := by
  unfold tailWord_2756294
  simp only [CollatzResearch.WordTrace]
  refine ⟨3141571908638282824468123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 67020200717616700255319957 3141571908638282824468123)
  ·
    refine ⟨4712357862957424236702185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3141571908638282824468123 4712357862957424236702185)
    ·
      refine ⟨3534268397218068177526639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4712357862957424236702185 3534268397218068177526639)
      ·
        refine ⟨5301402595827102266289959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3534268397218068177526639 5301402595827102266289959)
        ·
          refine ⟨7952103893740653399434939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5301402595827102266289959 7952103893740653399434939)
          ·
            refine ⟨11928155840610980099152409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7952103893740653399434939 11928155840610980099152409)
            ·
              refine ⟨8946116880458235074364307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11928155840610980099152409 8946116880458235074364307)
              ·
                refine ⟨13419175320687352611546461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8946116880458235074364307 13419175320687352611546461)
                ·
                  refine ⟨5032190745257757229329923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13419175320687352611546461 5032190745257757229329923)
                  ·
                    refine ⟨7548286117886635843994885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5032190745257757229329923 7548286117886635843994885)
                    ·
                      refine ⟨1415303647103744220749041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7548286117886635843994885 1415303647103744220749041)
                      ·
                        rfl

theorem cell23_2756294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_2756294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2756294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2756294 prefixEnd_2756294 := by exact prefixLift 2756294
  have htrace : WordTrace (prefixWord ++ tailWord_2756294) baseStart_2756294 baseEnd_2756294 := by
    simpa [prefixWord, tailWord_2756294, baseEnd_2756294] using wordTrace_append hprefix tailTrace_2756294
  have hstable : (prefixWord ++ tailWord_2756294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756294).length < 2 ^ (prefixWord ++ tailWord_2756294).sum := by decide
  have hdescent : baseEnd_2756294 < baseStart_2756294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756314 : List Nat := [3, 1, 1, 2, 2, 5, 2, 1, 1, 2, 3]
def baseStart_2756314 : Nat := 118140960795 + 2756314 * 2 ^ 59
def prefixEnd_2756314 : Nat := 4983230072969 + 3 ^ 40 * 2756314 * 2
def baseEnd_2756314 : Nat := 1415313916716834142498949

theorem tailTrace_2756314 : CollatzResearch.WordTrace tailWord_2756314 prefixEnd_2756314 1415313916716834142498949 := by
  unfold tailWord_2756314
  simp only [CollatzResearch.WordTrace]
  refine ⟨25132757634088148449676999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67020687024235062532471997 25132757634088148449676999)
  ·
    refine ⟨37699136451132222674515499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25132757634088148449676999 37699136451132222674515499)
    ·
      refine ⟨56548704676698334011773249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37699136451132222674515499 56548704676698334011773249)
      ·
        refine ⟨42411528507523750508829937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56548704676698334011773249 42411528507523750508829937)
        ·
          refine ⟨31808646380642812881622453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42411528507523750508829937 31808646380642812881622453)
          ·
            refine ⟨2982060598185263707652105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31808646380642812881622453 2982060598185263707652105)
            ·
              refine ⟨2236545448638947780739079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2982060598185263707652105 2236545448638947780739079)
              ·
                refine ⟨3354818172958421671108619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2236545448638947780739079 3354818172958421671108619)
                ·
                  refine ⟨5032227259437632506662929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3354818172958421671108619 5032227259437632506662929)
                  ·
                    refine ⟨3774170444578224379997197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5032227259437632506662929 3774170444578224379997197)
                    ·
                      refine ⟨1415313916716834142498949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3774170444578224379997197 1415313916716834142498949)
                      ·
                        rfl

theorem cell23_2756314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 1, 1, 2, 3].length) (baseStart_2756314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2756314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2756314 prefixEnd_2756314 := by exact prefixLift 2756314
  have htrace : WordTrace (prefixWord ++ tailWord_2756314) baseStart_2756314 baseEnd_2756314 := by
    simpa [prefixWord, tailWord_2756314, baseEnd_2756314] using wordTrace_append hprefix tailTrace_2756314
  have hstable : (prefixWord ++ tailWord_2756314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756314).length < 2 ^ (prefixWord ++ tailWord_2756314).sum := by decide
  have hdescent : baseEnd_2756314 < baseStart_2756314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756343 : List Nat := [1, 1, 3, 1, 1, 1, 6, 1, 2, 6]
def baseStart_2756343 : Nat := 118140960795 + 2756343 * 2 ^ 59
def prefixEnd_2756343 : Nat := 4983230072969 + 3 ^ 40 * 2756343 * 2
def baseEnd_2756343 : Nat := 471776269218604843012105

theorem tailTrace_2756343 : CollatzResearch.WordTrace tailWord_2756343 prefixEnd_2756343 471776269218604843012105 := by
  unfold tailWord_2756343
  simp only [CollatzResearch.WordTrace]
  refine ⟨100532088253247531751513683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67021392168831687834342455 100532088253247531751513683)
  ·
    refine ⟨150798132379871297627270525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100532088253247531751513683 150798132379871297627270525)
    ·
      refine ⟨56549299642451736610226447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150798132379871297627270525 56549299642451736610226447)
      ·
        refine ⟨84823949463677604915339671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56549299642451736610226447 84823949463677604915339671)
        ·
          refine ⟨127235924195516407373009507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84823949463677604915339671 127235924195516407373009507)
          ·
            refine ⟨190853886293274611059514261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127235924195516407373009507 190853886293274611059514261)
            ·
              refine ⟨8946275919997247393414731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 190853886293274611059514261 8946275919997247393414731)
              ·
                refine ⟨13419413879995871090122097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8946275919997247393414731 13419413879995871090122097)
                ·
                  refine ⟨10064560409996903317591573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13419413879995871090122097 10064560409996903317591573)
                  ·
                    refine ⟨471776269218604843012105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10064560409996903317591573 471776269218604843012105)
                    ·
                      rfl

theorem cell23_2756343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 6].length) (baseStart_2756343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2756343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2756343 prefixEnd_2756343 := by exact prefixLift 2756343
  have htrace : WordTrace (prefixWord ++ tailWord_2756343) baseStart_2756343 baseEnd_2756343 := by
    simpa [prefixWord, tailWord_2756343, baseEnd_2756343] using wordTrace_append hprefix tailTrace_2756343
  have hstable : (prefixWord ++ tailWord_2756343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756343).length < 2 ^ (prefixWord ++ tailWord_2756343).sum := by decide
  have hdescent : baseEnd_2756343 < baseStart_2756343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756363 : List Nat := [1, 1, 1, 1, 5, 1, 2, 2, 1, 4, 4]
def baseStart_2756363 : Nat := 118140960795 + 2756363 * 2 ^ 59
def prefixEnd_2756363 : Nat := 4983230072969 + 3 ^ 40 * 2756363 * 2
def baseEnd_2756363 : Nat := 1415339077268904450786223

theorem tailTrace_2756363 : CollatzResearch.WordTrace tailWord_2756363 prefixEnd_2756363 1415339077268904450786223 := by
  unfold tailWord_2756363
  simp only [CollatzResearch.WordTrace]
  refine ⟨100532817713175075167241743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67021878475450050111494495 100532817713175075167241743)
  ·
    refine ⟨150799226569762612750862615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100532817713175075167241743 150799226569762612750862615)
    ·
      refine ⟨226198839854643919126293923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150799226569762612750862615 226198839854643919126293923)
      ·
        refine ⟨339298259781965878689440885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226198839854643919126293923 339298259781965878689440885)
        ·
          refine ⟨31809211854559301127135083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 339298259781965878689440885 31809211854559301127135083)
          ·
            refine ⟨47713817781838951690702625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31809211854559301127135083 47713817781838951690702625)
            ·
              refine ⟨35785363336379213768026969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47713817781838951690702625 35785363336379213768026969)
              ·
                refine ⟨26839022502284410326020227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35785363336379213768026969 26839022502284410326020227)
                ·
                  refine ⟨40258533753426615489030341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26839022502284410326020227 40258533753426615489030341)
                  ·
                    refine ⟨7548475078767490404193189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40258533753426615489030341 7548475078767490404193189)
                    ·
                      refine ⟨1415339077268904450786223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7548475078767490404193189 1415339077268904450786223)
                      ·
                        rfl

theorem cell23_2756363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 4, 4].length) (baseStart_2756363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2756363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2756363 prefixEnd_2756363 := by exact prefixLift 2756363
  have htrace : WordTrace (prefixWord ++ tailWord_2756363) baseStart_2756363 baseEnd_2756363 := by
    simpa [prefixWord, tailWord_2756363, baseEnd_2756363] using wordTrace_append hprefix tailTrace_2756363
  have hstable : (prefixWord ++ tailWord_2756363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756363).length < 2 ^ (prefixWord ++ tailWord_2756363).sum := by decide
  have hdescent : baseEnd_2756363 < baseStart_2756363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756383 : List Nat := [1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 7]
def baseStart_2756383 : Nat := 118140960795 + 2756383 * 2 ^ 59
def prefixEnd_2756383 : Nat := 4983230072969 + 3 ^ 40 * 2756383 * 2
def baseEnd_2756383 : Nat := 1415349346881994372536131

theorem tailTrace_2756383 : CollatzResearch.WordTrace tailWord_2756383 prefixEnd_2756383 1415349346881994372536131 := by
  unfold tailWord_2756383
  simp only [CollatzResearch.WordTrace]
  refine ⟨100533547173102618582969803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67022364782068412388646535 100533547173102618582969803)
  ·
    refine ⟨150800320759653927874454705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100533547173102618582969803 150800320759653927874454705)
    ·
      refine ⟨113100240569740445905841029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150800320759653927874454705 113100240569740445905841029)
      ·
        refine ⟨21206295106826333607345193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113100240569740445905841029 21206295106826333607345193)
        ·
          refine ⟨15904721330119750205508895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21206295106826333607345193 15904721330119750205508895)
          ·
            refine ⟨23857081995179625308263343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15904721330119750205508895 23857081995179625308263343)
            ·
              refine ⟨35785622992769437962395015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23857081995179625308263343 35785622992769437962395015)
              ·
                refine ⟨53678434489154156943592523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35785622992769437962395015 53678434489154156943592523)
                ·
                  refine ⟨80517651733731235415388785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53678434489154156943592523 80517651733731235415388785)
                  ·
                    refine ⟨60388238800298426561541589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 80517651733731235415388785 60388238800298426561541589)
                    ·
                      refine ⟨1415349346881994372536131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 60388238800298426561541589 1415349346881994372536131)
                      ·
                        rfl

theorem cell23_2756383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_2756383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2756383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2756383 prefixEnd_2756383 := by exact prefixLift 2756383
  have htrace : WordTrace (prefixWord ++ tailWord_2756383) baseStart_2756383 baseEnd_2756383 := by
    simpa [prefixWord, tailWord_2756383, baseEnd_2756383] using wordTrace_append hprefix tailTrace_2756383
  have hstable : (prefixWord ++ tailWord_2756383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756383).length < 2 ^ (prefixWord ++ tailWord_2756383).sum := by decide
  have hdescent : baseEnd_2756383 < baseStart_2756383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756384 : List Nat := [2, 1, 1, 5, 1, 1, 2, 4, 2, 2, 2]
def baseStart_2756384 : Nat := 118140960795 + 2756384 * 2 ^ 59
def prefixEnd_2756384 : Nat := 4983230072969 + 3 ^ 40 * 2756384 * 2
def baseEnd_2756384 : Nat := 1415349860362648868623627

theorem tailTrace_2756384 : CollatzResearch.WordTrace tailWord_2756384 prefixEnd_2756384 1415349860362648868623627 := by
  unfold tailWord_2756384
  simp only [CollatzResearch.WordTrace]
  refine ⟨50266791823049497876878103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67022389097399330502504137 50266791823049497876878103)
  ·
    refine ⟨75400187734574246815317155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50266791823049497876878103 75400187734574246815317155)
    ·
      refine ⟨113100281601861370222975733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75400187734574246815317155 113100281601861370222975733)
      ·
        refine ⟨10603151400174503458403975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 113100281601861370222975733 10603151400174503458403975)
        ·
          refine ⟨15904727100261755187605963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10603151400174503458403975 15904727100261755187605963)
          ·
            refine ⟨23857090650392632781408945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15904727100261755187605963 23857090650392632781408945)
            ·
              refine ⟨17892817987794474586056709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23857090650392632781408945 17892817987794474586056709)
              ·
                refine ⟨3354903372711463984885633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17892817987794474586056709 3354903372711463984885633)
                ·
                  refine ⟨2516177529533597988664225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3354903372711463984885633 2516177529533597988664225)
                  ·
                    refine ⟨1887133147150198491498169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2516177529533597988664225 1887133147150198491498169)
                    ·
                      refine ⟨1415349860362648868623627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1887133147150198491498169 1415349860362648868623627)
                      ·
                        rfl

theorem cell23_2756384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_2756384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2756384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2756384 prefixEnd_2756384 := by exact prefixLift 2756384
  have htrace : WordTrace (prefixWord ++ tailWord_2756384) baseStart_2756384 baseEnd_2756384 := by
    simpa [prefixWord, tailWord_2756384, baseEnd_2756384] using wordTrace_append hprefix tailTrace_2756384
  have hstable : (prefixWord ++ tailWord_2756384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756384).length < 2 ^ (prefixWord ++ tailWord_2756384).sum := by decide
  have hdescent : baseEnd_2756384 < baseStart_2756384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756401 : List Nat := [1, 2, 2, 3, 2, 2, 4, 1, 2, 2, 2]
def baseStart_2756401 : Nat := 118140960795 + 2756401 * 2 ^ 59
def prefixEnd_2756401 : Nat := 4983230072969 + 3 ^ 40 * 2756401 * 2
def baseEnd_2756401 : Nat := 1415358589533775302111049

theorem tailTrace_2756401 : CollatzResearch.WordTrace tailWord_2756401 prefixEnd_2756401 1415358589533775302111049 := by
  unfold tailWord_2756401
  simp only [CollatzResearch.WordTrace]
  refine ⟨100534203687037407657125057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67022802458024938438083371 100534203687037407657125057)
  ·
    refine ⟨75400652765278055742843793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100534203687037407657125057 75400652765278055742843793)
    ·
      refine ⟨56550489573958541807132845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75400652765278055742843793 56550489573958541807132845)
      ·
        refine ⟨21206433590234453177674817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56550489573958541807132845 21206433590234453177674817)
        ·
          refine ⟨15904825192675839883256113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21206433590234453177674817 15904825192675839883256113)
          ·
            refine ⟨11928618894506879912442085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15904825192675839883256113 11928618894506879912442085)
            ·
              refine ⟨2236616042720039983582891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11928618894506879912442085 2236616042720039983582891)
              ·
                refine ⟨3354924064080059975374337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2236616042720039983582891 3354924064080059975374337)
                ·
                  refine ⟨2516193048060044981530753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3354924064080059975374337 2516193048060044981530753)
                  ·
                    refine ⟨1887144786045033736148065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2516193048060044981530753 1887144786045033736148065)
                    ·
                      refine ⟨1415358589533775302111049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1887144786045033736148065 1415358589533775302111049)
                      ·
                        rfl

theorem cell23_2756401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 1, 2, 2, 2].length) (baseStart_2756401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2756401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2756401 prefixEnd_2756401 := by exact prefixLift 2756401
  have htrace : WordTrace (prefixWord ++ tailWord_2756401) baseStart_2756401 baseEnd_2756401 := by
    simpa [prefixWord, tailWord_2756401, baseEnd_2756401] using wordTrace_append hprefix tailTrace_2756401
  have hstable : (prefixWord ++ tailWord_2756401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756401).length < 2 ^ (prefixWord ++ tailWord_2756401).sum := by decide
  have hdescent : baseEnd_2756401 < baseStart_2756401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756463 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 12]
def baseStart_2756463 : Nat := 118140960795 + 2756463 * 2 ^ 59
def prefixEnd_2756463 : Nat := 4983230072969 + 3 ^ 40 * 2756463 * 2
def baseEnd_2756463 : Nat := 157265602814928228837307

theorem tailTrace_2756463 : CollatzResearch.WordTrace tailWord_2756463 prefixEnd_2756463 157265602814928228837307 := by
  unfold tailWord_2756463
  simp only [CollatzResearch.WordTrace]
  refine ⟨100536465012812792245882043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67024310008541861497254695 100536465012812792245882043)
  ·
    refine ⟨150804697519219188368823065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100536465012812792245882043 150804697519219188368823065)
    ·
      refine ⟨113103523139414391276617299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150804697519219188368823065 113103523139414391276617299)
      ·
        refine ⟨169655284709121586914925949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113103523139414391276617299 169655284709121586914925949)
        ·
          refine ⟨63620731765920595093097231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169655284709121586914925949 63620731765920595093097231)
          ·
            refine ⟨95431097648880892639645847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63620731765920595093097231 95431097648880892639645847)
            ·
              refine ⟨143146646473321338959468771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95431097648880892639645847 143146646473321338959468771)
              ·
                refine ⟨214719969709982008439203157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143146646473321338959468771 214719969709982008439203157)
                ·
                  refine ⟨157265602814928228837307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 214719969709982008439203157 157265602814928228837307)
                  ·
                    rfl

theorem cell23_2756463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 12].length) (baseStart_2756463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2756463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2756463 prefixEnd_2756463 := by exact prefixLift 2756463
  have htrace : WordTrace (prefixWord ++ tailWord_2756463) baseStart_2756463 baseEnd_2756463 := by
    simpa [prefixWord, tailWord_2756463, baseEnd_2756463] using wordTrace_append hprefix tailTrace_2756463
  have hstable : (prefixWord ++ tailWord_2756463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756463).length < 2 ^ (prefixWord ++ tailWord_2756463).sum := by decide
  have hdescent : baseEnd_2756463 < baseStart_2756463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756484 : List Nat := [2, 3, 2, 1, 1, 1, 3, 5, 1, 4]
def baseStart_2756484 : Nat := 118140960795 + 2756484 * 2 ^ 59
def prefixEnd_2756484 : Nat := 4983230072969 + 3 ^ 40 * 2756484 * 2
def baseEnd_2756484 : Nat := 471800402809366159124389

theorem tailTrace_2756484 : CollatzResearch.WordTrace tailWord_2756484 prefixEnd_2756484 471800402809366159124389 := by
  unfold tailWord_2756484
  simp only [CollatzResearch.WordTrace]
  refine ⟨50268615472868356416198253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67024820630491141888264337 50268615472868356416198253)
  ·
    refine ⟨18850730802325633656074345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50268615472868356416198253 18850730802325633656074345)
    ·
      refine ⟨14138048101744225242055759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18850730802325633656074345 14138048101744225242055759)
      ·
        refine ⟨21207072152616337863083639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14138048101744225242055759 21207072152616337863083639)
        ·
          refine ⟨31810608228924506794625459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21207072152616337863083639 31810608228924506794625459)
          ·
            refine ⟨47715912343386760191938189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31810608228924506794625459 47715912343386760191938189)
            ·
              refine ⟨17893467128770035071976821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47715912343386760191938189 17893467128770035071976821)
              ·
                refine ⟨1677512543322190787997827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17893467128770035071976821 1677512543322190787997827)
                ·
                  refine ⟨2516268814983286181996741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1677512543322190787997827 2516268814983286181996741)
                  ·
                    refine ⟨471800402809366159124389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2516268814983286181996741 471800402809366159124389)
                    ·
                      rfl

theorem cell23_2756484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_2756484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2756484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2756484 prefixEnd_2756484 := by exact prefixLift 2756484
  have htrace : WordTrace (prefixWord ++ tailWord_2756484) baseStart_2756484 baseEnd_2756484 := by
    simpa [prefixWord, tailWord_2756484, baseEnd_2756484] using wordTrace_append hprefix tailTrace_2756484
  have hstable : (prefixWord ++ tailWord_2756484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756484).length < 2 ^ (prefixWord ++ tailWord_2756484).sum := by decide
  have hdescent : baseEnd_2756484 < baseStart_2756484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756527 : List Nat := [1, 1, 2, 1, 2, 2, 6, 2, 1, 5]
def baseStart_2756527 : Nat := 118140960795 + 2756527 * 2 ^ 59
def prefixEnd_2756527 : Nat := 4983230072969 + 3 ^ 40 * 2756527 * 2
def baseEnd_2756527 : Nat := 471807762698747269711823

theorem tailTrace_2756527 : CollatzResearch.WordTrace tailWord_2756527 prefixEnd_2756527 471807762698747269711823 := by
  unfold tailWord_2756527
  simp only [CollatzResearch.WordTrace]
  refine ⟨100538799284580931176211835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67025866189720620784141223 100538799284580931176211835)
  ·
    refine ⟨150808198926871396764317753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100538799284580931176211835 150808198926871396764317753)
    ·
      refine ⟨113106149195153547573238315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150808198926871396764317753 113106149195153547573238315)
      ·
        refine ⟨169659223792730321359857473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113106149195153547573238315 169659223792730321359857473)
        ·
          refine ⟨127244417844547741019893105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169659223792730321359857473 127244417844547741019893105)
          ·
            refine ⟨95433313383410805764919829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127244417844547741019893105 95433313383410805764919829)
            ·
              refine ⟨4473436564847381520230617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 95433313383410805764919829 4473436564847381520230617)
              ·
                refine ⟨3355077423635536140172963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4473436564847381520230617 3355077423635536140172963)
                ·
                  refine ⟨5032616135453304210259445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3355077423635536140172963 5032616135453304210259445)
                  ·
                    refine ⟨471807762698747269711823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5032616135453304210259445 471807762698747269711823)
                    ·
                      rfl

theorem cell23_2756527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 2, 1, 5].length) (baseStart_2756527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2756527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2756527 prefixEnd_2756527 := by exact prefixLift 2756527
  have htrace : WordTrace (prefixWord ++ tailWord_2756527) baseStart_2756527 baseEnd_2756527 := by
    simpa [prefixWord, tailWord_2756527, baseEnd_2756527] using wordTrace_append hprefix tailTrace_2756527
  have hstable : (prefixWord ++ tailWord_2756527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756527).length < 2 ^ (prefixWord ++ tailWord_2756527).sum := by decide
  have hdescent : baseEnd_2756527 < baseStart_2756527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756530 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4]
def baseStart_2756530 : Nat := 118140960795 + 2756530 * 2 ^ 59
def prefixEnd_2756530 : Nat := 4983230072969 + 3 ^ 40 * 2756530 * 2
def baseEnd_2756530 : Nat := 1415424828538205297397955

theorem tailTrace_2756530 : CollatzResearch.WordTrace tailWord_2756530 prefixEnd_2756530 1415424828538205297397955 := by
  unfold tailWord_2756530
  simp only [CollatzResearch.WordTrace]
  refine ⟨25134727175892515672142761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67025939135713375125714029 25134727175892515672142761)
  ·
    refine ⟨18851045381919386754107071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25134727175892515672142761 18851045381919386754107071)
    ·
      refine ⟨28276568072879080131160607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18851045381919386754107071 28276568072879080131160607)
      ·
        refine ⟨42414852109318620196740911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28276568072879080131160607 42414852109318620196740911)
        ·
          refine ⟨63622278163977930295111367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42414852109318620196740911 63622278163977930295111367)
          ·
            refine ⟨95433417245966895442667051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63622278163977930295111367 95433417245966895442667051)
            ·
              refine ⟨143150125868950343164000577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95433417245966895442667051 143150125868950343164000577)
              ·
                refine ⟨107362594401712757373000433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143150125868950343164000577 107362594401712757373000433)
                ·
                  refine ⟨80521945801284568029750325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107362594401712757373000433 80521945801284568029750325)
                  ·
                    refine ⟨7548932418870428252789093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 80521945801284568029750325 7548932418870428252789093)
                    ·
                      refine ⟨1415424828538205297397955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7548932418870428252789093 1415424828538205297397955)
                      ·
                        rfl

theorem cell23_2756530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_2756530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2756530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2756530 prefixEnd_2756530 := by exact prefixLift 2756530
  have htrace : WordTrace (prefixWord ++ tailWord_2756530) baseStart_2756530 baseEnd_2756530 := by
    simpa [prefixWord, tailWord_2756530, baseEnd_2756530] using wordTrace_append hprefix tailTrace_2756530
  have hstable : (prefixWord ++ tailWord_2756530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756530).length < 2 ^ (prefixWord ++ tailWord_2756530).sum := by decide
  have hdescent : baseEnd_2756530 < baseStart_2756530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756558 : List Nat := [4, 1, 1, 1, 2, 2, 5, 2, 1, 1, 3]
def baseStart_2756558 : Nat := 118140960795 + 2756558 * 2 ^ 59
def prefixEnd_2756558 : Nat := 4983230072969 + 3 ^ 40 * 2756558 * 2
def baseEnd_2756558 : Nat := 1415439205996531187847827

theorem tailTrace_2756558 : CollatzResearch.WordTrace tailWord_2756558 prefixEnd_2756558 1415439205996531187847827 := by
  unfold tailWord_2756558
  simp only [CollatzResearch.WordTrace]
  refine ⟨12567491243433577933823791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67026619964979082313726885 12567491243433577933823791)
  ·
    refine ⟨18851236865150366900735687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12567491243433577933823791 18851236865150366900735687)
    ·
      refine ⟨28276855297725550351103531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18851236865150366900735687 28276855297725550351103531)
      ·
        refine ⟨42415282946588325526655297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28276855297725550351103531 42415282946588325526655297)
        ·
          refine ⟨31811462209941244144991473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42415282946588325526655297 31811462209941244144991473)
          ·
            refine ⟨23858596657455933108743605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31811462209941244144991473 23858596657455933108743605)
            ·
              refine ⟨2236743436636493728944713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23858596657455933108743605 2236743436636493728944713)
              ·
                refine ⟨1677557577477370296708535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2236743436636493728944713 1677557577477370296708535)
                ·
                  refine ⟨2516336366216055445062803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1677557577477370296708535 2516336366216055445062803)
                  ·
                    refine ⟨3774504549324083167594205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2516336366216055445062803 3774504549324083167594205)
                    ·
                      refine ⟨1415439205996531187847827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3774504549324083167594205 1415439205996531187847827)
                      ·
                        rfl

theorem cell23_2756558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 2, 1, 1, 3].length) (baseStart_2756558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2756558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2756558 prefixEnd_2756558 := by exact prefixLift 2756558
  have htrace : WordTrace (prefixWord ++ tailWord_2756558) baseStart_2756558 baseEnd_2756558 := by
    simpa [prefixWord, tailWord_2756558, baseEnd_2756558] using wordTrace_append hprefix tailTrace_2756558
  have hstable : (prefixWord ++ tailWord_2756558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756558).length < 2 ^ (prefixWord ++ tailWord_2756558).sum := by decide
  have hdescent : baseEnd_2756558 < baseStart_2756558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756560 : List Nat := [2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 6]
def baseStart_2756560 : Nat := 118140960795 + 2756560 * 2 ^ 59
def prefixEnd_2756560 : Nat := 4983230072969 + 3 ^ 40 * 2756560 * 2
def baseEnd_2756560 : Nat := 1415440232957840180022817

theorem tailTrace_2756560 : CollatzResearch.WordTrace tailWord_2756560 prefixEnd_2756560 1415440232957840180022817 := by
  unfold tailWord_2756560
  simp only [CollatzResearch.WordTrace]
  refine ⟨50270001446730688906081567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67026668595640918541442089 50270001446730688906081567)
  ·
    refine ⟨75405002170096033359122351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50270001446730688906081567 75405002170096033359122351)
    ·
      refine ⟨113107503255144050038683527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75405002170096033359122351 113107503255144050038683527)
      ·
        refine ⟨169661254882716075058025291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113107503255144050038683527 169661254882716075058025291)
        ·
          refine ⟨254491882324074112587037937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169661254882716075058025291 254491882324074112587037937)
          ·
            refine ⟨190868911743055584440278453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 254491882324074112587037937 190868911743055584440278453)
            ·
              refine ⟨17893960475911461041276105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 190868911743055584440278453 17893960475911461041276105)
              ·
                refine ⟨13420470356933595780957079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17893960475911461041276105 13420470356933595780957079)
                ·
                  refine ⟨20130705535400393671435619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13420470356933595780957079 20130705535400393671435619)
                  ·
                    refine ⟨30196058303100590507153429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20130705535400393671435619 30196058303100590507153429)
                    ·
                      refine ⟨1415440232957840180022817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30196058303100590507153429 1415440232957840180022817)
                      ·
                        rfl

theorem cell23_2756560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 6].length) (baseStart_2756560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2756560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2756560 prefixEnd_2756560 := by exact prefixLift 2756560
  have htrace : WordTrace (prefixWord ++ tailWord_2756560) baseStart_2756560 baseEnd_2756560 := by
    simpa [prefixWord, tailWord_2756560, baseEnd_2756560] using wordTrace_append hprefix tailTrace_2756560
  have hstable : (prefixWord ++ tailWord_2756560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756560).length < 2 ^ (prefixWord ++ tailWord_2756560).sum := by decide
  have hdescent : baseEnd_2756560 < baseStart_2756560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756567 : List Nat := [1, 1, 3, 2, 1, 1, 4, 2, 3, 2, 3]
def baseStart_2756567 : Nat := 118140960795 + 2756567 * 2 ^ 59
def prefixEnd_2756567 : Nat := 4983230072969 + 3 ^ 40 * 2756567 * 2
def baseEnd_2756567 : Nat := 1415443827322421652635285

theorem tailTrace_2756567 : CollatzResearch.WordTrace tailWord_2756567 prefixEnd_2756567 1415443827322421652635285 := by
  unfold tailWord_2756567
  simp only [CollatzResearch.WordTrace]
  refine ⟨100540258204436018007667955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67026838802957345338445303 100540258204436018007667955)
  ·
    refine ⟨150810387306654027011501933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100540258204436018007667955 150810387306654027011501933)
    ·
      refine ⟨56553895239995260129313225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150810387306654027011501933 56553895239995260129313225)
      ·
        refine ⟨42415421429996445096984919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56553895239995260129313225 42415421429996445096984919)
        ·
          refine ⟨63623132144994667645477379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42415421429996445096984919 63623132144994667645477379)
          ·
            refine ⟨95434698217492001468216069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63623132144994667645477379 95434698217492001468216069)
            ·
              refine ⟨17894005915779750275290513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95434698217492001468216069 17894005915779750275290513)
              ·
                refine ⟨13420504436834812706467885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17894005915779750275290513 13420504436834812706467885)
                ·
                  refine ⟨5032689163813054764925457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13420504436834812706467885 5032689163813054764925457)
                  ·
                    refine ⟨3774516872859791073694093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5032689163813054764925457 3774516872859791073694093)
                    ·
                      refine ⟨1415443827322421652635285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3774516872859791073694093 1415443827322421652635285)
                      ·
                        rfl

theorem cell23_2756567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 3, 2, 3].length) (baseStart_2756567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2756567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2756567 prefixEnd_2756567 := by exact prefixLift 2756567
  have htrace : WordTrace (prefixWord ++ tailWord_2756567) baseStart_2756567 baseEnd_2756567 := by
    simpa [prefixWord, tailWord_2756567, baseEnd_2756567] using wordTrace_append hprefix tailTrace_2756567
  have hstable : (prefixWord ++ tailWord_2756567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756567).length < 2 ^ (prefixWord ++ tailWord_2756567).sum := by decide
  have hdescent : baseEnd_2756567 < baseStart_2756567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756578 : List Nat := [3, 3, 3, 1, 2, 2, 1, 2, 1, 5]
def baseStart_2756578 : Nat := 118140960795 + 2756578 * 2 ^ 59
def prefixEnd_2756578 : Nat := 4983230072969 + 3 ^ 40 * 2756578 * 2
def baseEnd_2756578 : Nat := 471816491869873703199245

theorem tailTrace_2756578 : CollatzResearch.WordTrace tailWord_2756578 prefixEnd_2756578 471816491869873703199245 := by
  unfold tailWord_2756578
  simp only [CollatzResearch.WordTrace]
  refine ⟨25135164851849041721579597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67027106271597444590878925 25135164851849041721579597)
  ·
    refine ⟨9425686819443390645592349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25135164851849041721579597 9425686819443390645592349)
    ·
      refine ⟨3534632557291271492097131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9425686819443390645592349 3534632557291271492097131)
      ·
        refine ⟨5301948835936907238145697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3534632557291271492097131 5301948835936907238145697)
        ·
          refine ⟨3976461626952680428609273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5301948835936907238145697 3976461626952680428609273)
          ·
            refine ⟨2982346220214510321456955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3976461626952680428609273 2982346220214510321456955)
            ·
              refine ⟨4473519330321765482185433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2982346220214510321456955 4473519330321765482185433)
              ·
                refine ⟨3355139497741324111639075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4473519330321765482185433 3355139497741324111639075)
                ·
                  refine ⟨5032709246611986167458613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3355139497741324111639075 5032709246611986167458613)
                  ·
                    refine ⟨471816491869873703199245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5032709246611986167458613 471816491869873703199245)
                    ·
                      rfl

theorem cell23_2756578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_2756578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2756578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2756578 prefixEnd_2756578 := by exact prefixLift 2756578
  have htrace : WordTrace (prefixWord ++ tailWord_2756578) baseStart_2756578 baseEnd_2756578 := by
    simpa [prefixWord, tailWord_2756578, baseEnd_2756578] using wordTrace_append hprefix tailTrace_2756578
  have hstable : (prefixWord ++ tailWord_2756578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756578).length < 2 ^ (prefixWord ++ tailWord_2756578).sum := by decide
  have hdescent : baseEnd_2756578 < baseStart_2756578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756598 : List Nat := [5, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4]
def baseStart_2756598 : Nat := 118140960795 + 2756598 * 2 ^ 59
def prefixEnd_2756598 : Nat := 4983230072969 + 3 ^ 40 * 2756598 * 2
def baseEnd_2756598 : Nat := 1415459745222711031347643

theorem tailTrace_2756598 : CollatzResearch.WordTrace tailWord_2756598 prefixEnd_2756598 1415459745222711031347643 := by
  unfold tailWord_2756598
  simp only [CollatzResearch.WordTrace]
  refine ⟨6283836804207731893877903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67027592578215806868030965 6283836804207731893877903)
  ·
    refine ⟨9425755206311597840816855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6283836804207731893877903 9425755206311597840816855)
    ·
      refine ⟨14138632809467396761225283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9425755206311597840816855 14138632809467396761225283)
      ·
        refine ⟨21207949214201095141837925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14138632809467396761225283 21207949214201095141837925)
        ·
          refine ⟨3976490477662705339094611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21207949214201095141837925 3976490477662705339094611)
          ·
            refine ⟨5964735716494058008641917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3976490477662705339094611 5964735716494058008641917)
            ·
              refine ⟨2236775893685271753240719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5964735716494058008641917 2236775893685271753240719)
              ·
                refine ⟨3355163840527907629861079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2236775893685271753240719 3355163840527907629861079)
                ·
                  refine ⟨5032745760791861444791619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3355163840527907629861079 5032745760791861444791619)
                  ·
                    refine ⟨7549118641187792167187429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5032745760791861444791619 7549118641187792167187429)
                    ·
                      refine ⟨1415459745222711031347643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7549118641187792167187429 1415459745222711031347643)
                      ·
                        rfl

theorem cell23_2756598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4].length) (baseStart_2756598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2756598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2756598 prefixEnd_2756598 := by exact prefixLift 2756598
  have htrace : WordTrace (prefixWord ++ tailWord_2756598) baseStart_2756598 baseEnd_2756598 := by
    simpa [prefixWord, tailWord_2756598, baseEnd_2756598] using wordTrace_append hprefix tailTrace_2756598
  have hstable : (prefixWord ++ tailWord_2756598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756598).length < 2 ^ (prefixWord ++ tailWord_2756598).sum := by decide
  have hdescent : baseEnd_2756598 < baseStart_2756598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756601 : List Nat := [1, 2, 1, 3, 1, 5, 3, 1, 1, 2, 3]
def baseStart_2756601 : Nat := 118140960795 + 2756601 * 2 ^ 59
def prefixEnd_2756601 : Nat := 4983230072969 + 3 ^ 40 * 2756601 * 2
def baseEnd_2756601 : Nat := 1415461285664674519610129

theorem tailTrace_2756601 : CollatzResearch.WordTrace tailWord_2756601 prefixEnd_2756601 1415461285664674519610129 := by
  unfold tailWord_2756601
  simp only [CollatzResearch.WordTrace]
  refine ⟨100541498286312841814405657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67027665524208561209603771 100541498286312841814405657)
  ·
    refine ⟨75406123714734631360804243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100541498286312841814405657 75406123714734631360804243)
    ·
      refine ⟨113109185572101947041206365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75406123714734631360804243 113109185572101947041206365)
      ·
        refine ⟨42415944589538230140452387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113109185572101947041206365 42415944589538230140452387)
        ·
          refine ⟨63623916884307345210678581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42415944589538230140452387 63623916884307345210678581)
          ·
            refine ⟨5964742207903813613501117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63623916884307345210678581 5964742207903813613501117)
            ·
              refine ⟨2236778327963930105062919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5964742207903813613501117 2236778327963930105062919)
              ·
                refine ⟨3355167491945895157594379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2236778327963930105062919 3355167491945895157594379)
                ·
                  refine ⟨5032751237918842736391569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3355167491945895157594379 5032751237918842736391569)
                  ·
                    refine ⟨3774563428439132052293677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5032751237918842736391569 3774563428439132052293677)
                    ·
                      refine ⟨1415461285664674519610129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3774563428439132052293677 1415461285664674519610129)
                      ·
                        rfl

theorem cell23_2756601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 1, 1, 2, 3].length) (baseStart_2756601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2756601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2756601 prefixEnd_2756601 := by exact prefixLift 2756601
  have htrace : WordTrace (prefixWord ++ tailWord_2756601) baseStart_2756601 baseEnd_2756601 := by
    simpa [prefixWord, tailWord_2756601, baseEnd_2756601] using wordTrace_append hprefix tailTrace_2756601
  have hstable : (prefixWord ++ tailWord_2756601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756601).length < 2 ^ (prefixWord ++ tailWord_2756601).sum := by decide
  have hdescent : baseEnd_2756601 < baseStart_2756601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
