import V185TrunkScan23Chunk0657

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3890071 : List Nat := [1, 1, 3, 3, 1, 2, 3, 1, 2, 3, 3]
def baseStart_3890071 : Nat := 118140960795 + 3890071 * 2 ^ 59
def prefixEnd_3890071 : Nat := 4983230072969 + 3 ^ 40 * 3890071 * 2
def baseEnd_3890071 : Nat := 1997476203116354813022395

theorem tailTrace_3890071 : CollatzResearch.WordTrace tailWord_3890071 prefixEnd_3890071 1997476203116354813022395 := by
  unfold tailWord_3890071
  simp only [CollatzResearch.WordTrace]
  refine ⟨141882545489944613078614067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94588363659963075385742711 141882545489944613078614067)
  ·
    refine ⟨212823818234916919617921101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141882545489944613078614067 212823818234916919617921101)
    ·
      refine ⟨79808931838093844856720413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212823818234916919617921101 79808931838093844856720413)
      ·
        refine ⟨29928349439285191821270155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79808931838093844856720413 29928349439285191821270155)
        ·
          refine ⟨44892524158927787731905233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29928349439285191821270155 44892524158927787731905233)
          ·
            refine ⟨33669393119195840798928925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44892524158927787731905233 33669393119195840798928925)
            ·
              refine ⟨12626022419698440299598347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33669393119195840798928925 12626022419698440299598347)
              ·
                refine ⟨18939033629547660449397521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12626022419698440299598347 18939033629547660449397521)
                ·
                  refine ⟨14204275222160745337048141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18939033629547660449397521 14204275222160745337048141)
                  ·
                    refine ⟨5326603208310279501393053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14204275222160745337048141 5326603208310279501393053)
                    ·
                      refine ⟨1997476203116354813022395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5326603208310279501393053 1997476203116354813022395)
                      ·
                        rfl

theorem cell23_3890071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_3890071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3890071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3890071 prefixEnd_3890071 := by exact prefixLift 3890071
  have htrace : WordTrace (prefixWord ++ tailWord_3890071) baseStart_3890071 baseEnd_3890071 := by
    simpa [prefixWord, tailWord_3890071, baseEnd_3890071] using wordTrace_append hprefix tailTrace_3890071
  have hstable : (prefixWord ++ tailWord_3890071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890071).length < 2 ^ (prefixWord ++ tailWord_3890071).sum := by decide
  have hdescent : baseEnd_3890071 < baseStart_3890071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890138 : List Nat := [3, 1, 1, 2, 4, 1, 2, 2, 3, 4]
def baseStart_3890138 : Nat := 118140960795 + 3890138 * 2 ^ 59
def prefixEnd_3890138 : Nat := 4983230072969 + 3 ^ 40 * 3890138 * 2
def baseEnd_3890138 : Nat := 665836868773402016961529

theorem tailTrace_3890138 : CollatzResearch.WordTrace tailWord_3890138 prefixEnd_3890138 665836868773402016961529 := by
  unfold tailWord_3890138
  simp only [CollatzResearch.WordTrace]
  refine ⟨35471247295175470880325767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94589992787134589014202045 35471247295175470880325767)
  ·
    refine ⟨53206870942763206320488651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35471247295175470880325767 53206870942763206320488651)
    ·
      refine ⟨79810306414144809480732977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53206870942763206320488651 79810306414144809480732977)
      ·
        refine ⟨59857729810608607110549733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79810306414144809480732977 59857729810608607110549733)
        ·
          refine ⟨11223324339489113833228075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59857729810608607110549733 11223324339489113833228075)
          ·
            refine ⟨16834986509233670749842113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11223324339489113833228075 16834986509233670749842113)
            ·
              refine ⟨12626239881925253062381585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16834986509233670749842113 12626239881925253062381585)
              ·
                refine ⟨9469679911443939796786189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12626239881925253062381585 9469679911443939796786189)
                ·
                  refine ⟨3551129966791477423794821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9469679911443939796786189 3551129966791477423794821)
                  ·
                    refine ⟨665836868773402016961529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3551129966791477423794821 665836868773402016961529)
                    ·
                      rfl

theorem cell23_3890138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 3, 4].length) (baseStart_3890138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3890138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3890138 prefixEnd_3890138 := by exact prefixLift 3890138
  have htrace : WordTrace (prefixWord ++ tailWord_3890138) baseStart_3890138 baseEnd_3890138 := by
    simpa [prefixWord, tailWord_3890138, baseEnd_3890138] using wordTrace_append hprefix tailTrace_3890138
  have hstable : (prefixWord ++ tailWord_3890138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890138).length < 2 ^ (prefixWord ++ tailWord_3890138).sum := by decide
  have hdescent : baseEnd_3890138 < baseStart_3890138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890144 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 9]
def baseStart_3890144 : Nat := 118140960795 + 3890144 * 2 ^ 59
def prefixEnd_3890144 : Nat := 4983230072969 + 3 ^ 40 * 3890144 * 2
def baseEnd_3890144 : Nat := 1997513687204133027409559

theorem tailTrace_3890144 : CollatzResearch.WordTrace tailWord_3890144 prefixEnd_3890144 1997513687204133027409559 := by
  unfold tailWord_3890144
  simp only [CollatzResearch.WordTrace]
  refine ⟨70942604009340073273010743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94590138679120097697347657 70942604009340073273010743)
  ·
    refine ⟨106413906014010109909516115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70942604009340073273010743 106413906014010109909516115)
    ·
      refine ⟨159620859021015164864274173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106413906014010109909516115 159620859021015164864274173)
      ·
        refine ⟨59857822132880686824102815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159620859021015164864274173 59857822132880686824102815)
        ·
          refine ⟨89786733199321030236154223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59857822132880686824102815 89786733199321030236154223)
          ·
            refine ⟨134680099798981545354231335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89786733199321030236154223 134680099798981545354231335)
            ·
              refine ⟨202020149698472318031347003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134680099798981545354231335 202020149698472318031347003)
              ·
                refine ⟨303030224547708477047020505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202020149698472318031347003 303030224547708477047020505)
                ·
                  refine ⟨227272668410781357785265379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 303030224547708477047020505 227272668410781357785265379)
                  ·
                    refine ⟨340909002616172036677898069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 227272668410781357785265379 340909002616172036677898069)
                    ·
                      refine ⟨1997513687204133027409559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 340909002616172036677898069 1997513687204133027409559)
                      ·
                        rfl

theorem cell23_3890144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_3890144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3890144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3890144 prefixEnd_3890144 := by exact prefixLift 3890144
  have htrace : WordTrace (prefixWord ++ tailWord_3890144) baseStart_3890144 baseEnd_3890144 := by
    simpa [prefixWord, tailWord_3890144, baseEnd_3890144] using wordTrace_append hprefix tailTrace_3890144
  have hstable : (prefixWord ++ tailWord_3890144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890144).length < 2 ^ (prefixWord ++ tailWord_3890144).sum := by decide
  have hdescent : baseEnd_3890144 < baseStart_3890144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890151 : List Nat := [1, 1, 5, 2, 2, 1, 1, 2, 8]
def baseStart_3890151 : Nat := 118140960795 + 3890151 * 2 ^ 59
def prefixEnd_3890151 : Nat := 4983230072969 + 3 ^ 40 * 3890151 * 2
def baseEnd_3890151 : Nat := 221946364618746055558003

theorem tailTrace_3890151 : CollatzResearch.WordTrace tailWord_3890151 prefixEnd_3890151 221946364618746055558003 := by
  unfold tailWord_3890151
  simp only [CollatzResearch.WordTrace]
  refine ⟨141885463329654786741526307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94590308886436524494350871 141885463329654786741526307)
  ·
    refine ⟨212828194994482180112289461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141885463329654786741526307 212828194994482180112289461)
    ·
      refine ⟨19952643280732704385527137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 212828194994482180112289461 19952643280732704385527137)
      ·
        refine ⟨14964482460549528289145353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19952643280732704385527137 14964482460549528289145353)
        ·
          refine ⟨11223361845412146216859015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14964482460549528289145353 11223361845412146216859015)
          ·
            refine ⟨16835042768118219325288523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11223361845412146216859015 16835042768118219325288523)
            ·
              refine ⟨25252564152177328987932785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16835042768118219325288523 25252564152177328987932785)
              ·
                refine ⟨18939423114132996740949589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25252564152177328987932785 18939423114132996740949589)
                ·
                  refine ⟨221946364618746055558003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18939423114132996740949589 221946364618746055558003)
                  ·
                    rfl

theorem cell23_3890151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 8].length) (baseStart_3890151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3890151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3890151 prefixEnd_3890151 := by exact prefixLift 3890151
  have htrace : WordTrace (prefixWord ++ tailWord_3890151) baseStart_3890151 baseEnd_3890151 := by
    simpa [prefixWord, tailWord_3890151, baseEnd_3890151] using wordTrace_append hprefix tailTrace_3890151
  have hstable : (prefixWord ++ tailWord_3890151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890151).length < 2 ^ (prefixWord ++ tailWord_3890151).sum := by decide
  have hdescent : baseEnd_3890151 < baseStart_3890151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890172 : List Nat := [2, 2, 2, 1, 2, 4, 3, 2, 1, 4]
def baseStart_3890172 : Nat := 118140960795 + 3890172 * 2 ^ 59
def prefixEnd_3890172 : Nat := 4983230072969 + 3 ^ 40 * 3890172 * 2
def baseEnd_3890172 : Nat := 665842688220819639286477

theorem tailTrace_3890172 : CollatzResearch.WordTrace tailWord_3890172 prefixEnd_3890172 665842688220819639286477 := by
  unfold tailWord_3890172
  simp only [CollatzResearch.WordTrace]
  refine ⟨70943114631289353664020385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94590819508385804885360513 70943114631289353664020385)
  ·
    refine ⟨53207335973467015248015289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70943114631289353664020385 53207335973467015248015289)
    ·
      refine ⟨39905501980100261436011467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53207335973467015248015289 39905501980100261436011467)
      ·
        refine ⟨59858252970150392154017201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39905501980100261436011467 59858252970150392154017201)
        ·
          refine ⟨44893689727612794115512901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59858252970150392154017201 44893689727612794115512901)
          ·
            refine ⟨8417566823927398896658669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44893689727612794115512901 8417566823927398896658669)
            ·
              refine ⟨3156587558972774586247001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8417566823927398896658669 3156587558972774586247001)
              ·
                refine ⟨2367440669229580939685251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3156587558972774586247001 2367440669229580939685251)
                ·
                  refine ⟨3551161003844371409527877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2367440669229580939685251 3551161003844371409527877)
                  ·
                    refine ⟨665842688220819639286477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3551161003844371409527877 665842688220819639286477)
                    ·
                      rfl

theorem cell23_3890172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 2, 1, 4].length) (baseStart_3890172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3890172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3890172 prefixEnd_3890172 := by exact prefixLift 3890172
  have htrace : WordTrace (prefixWord ++ tailWord_3890172) baseStart_3890172 baseEnd_3890172 := by
    simpa [prefixWord, tailWord_3890172, baseEnd_3890172] using wordTrace_append hprefix tailTrace_3890172
  have hstable : (prefixWord ++ tailWord_3890172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890172).length < 2 ^ (prefixWord ++ tailWord_3890172).sum := by decide
  have hdescent : baseEnd_3890172 < baseStart_3890172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890181 : List Nat := [1, 3, 1, 1, 2, 3, 2, 2, 3, 5]
def baseStart_3890181 : Nat := 118140960795 + 3890181 * 2 ^ 59
def prefixEnd_3890181 : Nat := 4983230072969 + 3 ^ 40 * 3890181 * 2
def baseEnd_3890181 : Nat := 665844228662783127548963

theorem tailTrace_3890181 : CollatzResearch.WordTrace tailWord_3890181 prefixEnd_3890181 665844228662783127548963 := by
  unfold tailWord_3890181
  simp only [CollatzResearch.WordTrace]
  refine ⟨141886557519546101865118397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94591038346364067910078931 141886557519546101865118397)
  ·
    refine ⟨53207459069829788199419399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141886557519546101865118397 53207459069829788199419399)
    ·
      refine ⟨79811188604744682299129099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53207459069829788199419399 79811188604744682299129099)
      ·
        refine ⟨119716782907117023448693649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79811188604744682299129099 119716782907117023448693649)
        ·
          refine ⟨89787587180337767586520237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119716782907117023448693649 89787587180337767586520237)
          ·
            refine ⟨33670345192626662844945089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89787587180337767586520237 33670345192626662844945089)
            ·
              refine ⟨25252758894469997133708817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33670345192626662844945089 25252758894469997133708817)
              ·
                refine ⟨18939569170852497850281613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25252758894469997133708817 18939569170852497850281613)
                ·
                  refine ⟨7102338439069686693855605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18939569170852497850281613 7102338439069686693855605)
                  ·
                    refine ⟨665844228662783127548963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7102338439069686693855605 665844228662783127548963)
                    ·
                      rfl

theorem cell23_3890181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 3, 5].length) (baseStart_3890181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3890181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3890181 prefixEnd_3890181 := by exact prefixLift 3890181
  have htrace : WordTrace (prefixWord ++ tailWord_3890181) baseStart_3890181 baseEnd_3890181 := by
    simpa [prefixWord, tailWord_3890181, baseEnd_3890181] using wordTrace_append hprefix tailTrace_3890181
  have hstable : (prefixWord ++ tailWord_3890181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890181).length < 2 ^ (prefixWord ++ tailWord_3890181).sum := by decide
  have hdescent : baseEnd_3890181 < baseStart_3890181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890211 : List Nat := [1, 1, 1, 4, 3, 2, 1, 1, 3, 6]
def baseStart_3890211 : Nat := 118140960795 + 3890211 * 2 ^ 59
def prefixEnd_3890211 : Nat := 4983230072969 + 3 ^ 40 * 3890211 * 2
def baseEnd_3890211 : Nat := 665849363469328088423917

theorem tailTrace_3890211 : CollatzResearch.WordTrace tailWord_3890211 prefixEnd_3890211 665849363469328088423917 := by
  unfold tailWord_3890211
  simp only [CollatzResearch.WordTrace]
  refine ⟨141887651709437416988710487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94591767806291611325806991 141887651709437416988710487)
  ·
    refine ⟨212831477564156125483065731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141887651709437416988710487 212831477564156125483065731)
    ·
      refine ⟨319247216346234188224598597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212831477564156125483065731 319247216346234188224598597)
      ·
        refine ⟨59858853064918910292112237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 319247216346234188224598597 59858853064918910292112237)
        ·
          refine ⟨22447069899344591359542089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59858853064918910292112237 22447069899344591359542089)
          ·
            refine ⟨16835302424508443519656567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22447069899344591359542089 16835302424508443519656567)
            ·
              refine ⟨25252953636762665279484851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16835302424508443519656567 25252953636762665279484851)
              ·
                refine ⟨37879430455143997919227277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25252953636762665279484851 37879430455143997919227277)
                ·
                  refine ⟨14204786420678999219710229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37879430455143997919227277 14204786420678999219710229)
                  ·
                    refine ⟨665849363469328088423917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14204786420678999219710229 665849363469328088423917)
                    ·
                      rfl

theorem cell23_3890211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 6].length) (baseStart_3890211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3890211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3890211 prefixEnd_3890211 := by exact prefixLift 3890211
  have htrace : WordTrace (prefixWord ++ tailWord_3890211) baseStart_3890211 baseEnd_3890211 := by
    simpa [prefixWord, tailWord_3890211, baseEnd_3890211] using wordTrace_append hprefix tailTrace_3890211
  have hstable : (prefixWord ++ tailWord_3890211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890211).length < 2 ^ (prefixWord ++ tailWord_3890211).sum := by decide
  have hdescent : baseEnd_3890211 < baseStart_3890211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890231 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 5, 2, 4]
def baseStart_3890231 : Nat := 118140960795 + 3890231 * 2 ^ 59
def prefixEnd_3890231 : Nat := 4983230072969 + 3 ^ 40 * 3890231 * 2
def baseEnd_3890231 : Nat := 1997558360021074187021659

theorem tailTrace_3890231 : CollatzResearch.WordTrace tailWord_3890231 prefixEnd_3890231 1997558360021074187021659 := by
  unfold tailWord_3890231
  simp only [CollatzResearch.WordTrace]
  refine ⟨141888381169364960404438547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94592254112909973602959031 141888381169364960404438547)
  ·
    refine ⟨212832571754047440606657821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141888381169364960404438547 212832571754047440606657821)
    ·
      refine ⟨79812214407767790227496683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212832571754047440606657821 79812214407767790227496683)
      ·
        refine ⟨119718321611651685341245025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79812214407767790227496683 119718321611651685341245025)
        ·
          refine ⟨89788741208738764005933769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119718321611651685341245025 89788741208738764005933769)
          ·
            refine ⟨67341555906554073004450327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89788741208738764005933769 67341555906554073004450327)
            ·
              refine ⟨101012333859831109506675491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67341555906554073004450327 101012333859831109506675491)
              ·
                refine ⟨151518500789746664260013237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101012333859831109506675491 151518500789746664260013237)
                ·
                  refine ⟨14204859449038749774376241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 151518500789746664260013237 14204859449038749774376241)
                  ·
                    refine ⟨10653644586779062330782181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14204859449038749774376241 10653644586779062330782181)
                    ·
                      refine ⟨1997558360021074187021659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10653644586779062330782181 1997558360021074187021659)
                      ·
                        rfl

theorem cell23_3890231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 2, 4].length) (baseStart_3890231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3890231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3890231 prefixEnd_3890231 := by exact prefixLift 3890231
  have htrace : WordTrace (prefixWord ++ tailWord_3890231) baseStart_3890231 baseEnd_3890231 := by
    simpa [prefixWord, tailWord_3890231, baseEnd_3890231] using wordTrace_append hprefix tailTrace_3890231
  have hstable : (prefixWord ++ tailWord_3890231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890231).length < 2 ^ (prefixWord ++ tailWord_3890231).sum := by decide
  have hdescent : baseEnd_3890231 < baseStart_3890231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890248 : List Nat := [2, 1, 3, 1, 1, 1, 6, 1, 1, 2, 4]
def baseStart_3890248 : Nat := 118140960795 + 3890248 * 2 ^ 59
def prefixEnd_3890248 : Nat := 4983230072969 + 3 ^ 40 * 3890248 * 2
def baseEnd_3890248 : Nat := 1997567089192200620509081

theorem tailTrace_3890248 : CollatzResearch.WordTrace tailWord_3890248 prefixEnd_3890248 1997567089192200620509081 := by
  unfold tailWord_3890248
  simp only [CollatzResearch.WordTrace]
  refine ⟨70944500605151686153903699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94592667473535581538538265 70944500605151686153903699)
  ·
    refine ⟨106416750907727529230855549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70944500605151686153903699 106416750907727529230855549)
    ·
      refine ⟨39906281590397823461570831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106416750907727529230855549 39906281590397823461570831)
      ·
        refine ⟨59859422385596735192356247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39906281590397823461570831 59859422385596735192356247)
        ·
          refine ⟨89789133578395102788534371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59859422385596735192356247 89789133578395102788534371)
          ·
            refine ⟨134683700367592654182801557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89789133578395102788534371 134683700367592654182801557)
            ·
              refine ⟨6313298454730905664818823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 134683700367592654182801557 6313298454730905664818823)
              ·
                refine ⟨9469947682096358497228235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6313298454730905664818823 9469947682096358497228235)
                ·
                  refine ⟨14204921523144537745842353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9469947682096358497228235 14204921523144537745842353)
                  ·
                    refine ⟨10653691142358403309381765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14204921523144537745842353 10653691142358403309381765)
                    ·
                      refine ⟨1997567089192200620509081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10653691142358403309381765 1997567089192200620509081)
                      ·
                        rfl

theorem cell23_3890248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 1, 2, 4].length) (baseStart_3890248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3890248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3890248 prefixEnd_3890248 := by exact prefixLift 3890248
  have htrace : WordTrace (prefixWord ++ tailWord_3890248) baseStart_3890248 baseEnd_3890248 := by
    simpa [prefixWord, tailWord_3890248, baseEnd_3890248] using wordTrace_append hprefix tailTrace_3890248
  have hstable : (prefixWord ++ tailWord_3890248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890248).length < 2 ^ (prefixWord ++ tailWord_3890248).sum := by decide
  have hdescent : baseEnd_3890248 < baseStart_3890248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890328 : List Nat := [2, 1, 2, 4, 2, 1, 1, 1, 1, 3, 5]
def baseStart_3890328 : Nat := 118140960795 + 3890328 * 2 ^ 59
def prefixEnd_3890328 : Nat := 4983230072969 + 3 ^ 40 * 3890328 * 2
def baseEnd_3890328 : Nat := 1997608167644560307508713

theorem tailTrace_3890328 : CollatzResearch.WordTrace tailWord_3890328 prefixEnd_3890328 1997608167644560307508713 := by
  unfold tailWord_3890328
  simp only [CollatzResearch.WordTrace]
  refine ⟨70945959525006772985359819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94594612700009030647146425 70945959525006772985359819)
  ·
    refine ⟨106418939287510159478039729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70945959525006772985359819 106418939287510159478039729)
    ·
      refine ⟨79814204465632619608529797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106418939287510159478039729 79814204465632619608529797)
      ·
        refine ⟨14965163337306116176599337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79814204465632619608529797 14965163337306116176599337)
        ·
          refine ⟨11223872502979587132449503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14965163337306116176599337 11223872502979587132449503)
          ·
            refine ⟨16835808754469380698674255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11223872502979587132449503 16835808754469380698674255)
            ·
              refine ⟨25253713131704071048011383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16835808754469380698674255 25253713131704071048011383)
              ·
                refine ⟨37880569697556106572017075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25253713131704071048011383 37880569697556106572017075)
                ·
                  refine ⟨56820854546334159858025613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37880569697556106572017075 56820854546334159858025613)
                  ·
                    refine ⟨21307820454875309946759605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56820854546334159858025613 21307820454875309946759605)
                    ·
                      refine ⟨1997608167644560307508713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21307820454875309946759605 1997608167644560307508713)
                      ·
                        rfl

theorem cell23_3890328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_3890328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3890328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3890328 prefixEnd_3890328 := by exact prefixLift 3890328
  have htrace : WordTrace (prefixWord ++ tailWord_3890328) baseStart_3890328 baseEnd_3890328 := by
    simpa [prefixWord, tailWord_3890328, baseEnd_3890328] using wordTrace_append hprefix tailTrace_3890328
  have hstable : (prefixWord ++ tailWord_3890328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890328).length < 2 ^ (prefixWord ++ tailWord_3890328).sum := by decide
  have hdescent : baseEnd_3890328 < baseStart_3890328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890425 : List Nat := [1, 2, 1, 3, 1, 1, 5, 2, 3, 4]
def baseStart_3890425 : Nat := 118140960795 + 3890425 * 2 ^ 59
def prefixEnd_3890425 : Nat := 4983230072969 + 3 ^ 40 * 3890425 * 2
def baseEnd_3890425 : Nat := 665885991756015475998589

theorem tailTrace_3890425 : CollatzResearch.WordTrace tailWord_3890425 prefixEnd_3890425 665885991756015475998589 := by
  unfold tailWord_3890425
  simp only [CollatzResearch.WordTrace]
  refine ⟨141895456930662131537000729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94596971287108087691333819 141895456930662131537000729)
  ·
    refine ⟨106421592697996598652750547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141895456930662131537000729 106421592697996598652750547)
    ·
      refine ⟨159632389046994897979125821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106421592697996598652750547 159632389046994897979125821)
      ·
        refine ⟨59862145892623086742172183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159632389046994897979125821 59862145892623086742172183)
        ·
          refine ⟨89793218838934630113258275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59862145892623086742172183 89793218838934630113258275)
          ·
            refine ⟨134689828258401945169887413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89793218838934630113258275 134689828258401945169887413)
            ·
              refine ⟨12627171399225182359676945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 134689828258401945169887413 12627171399225182359676945)
              ·
                refine ⟨9470378549418886769757709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12627171399225182359676945 9470378549418886769757709)
                ·
                  refine ⟨3551391956032082538659141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9470378549418886769757709 3551391956032082538659141)
                  ·
                    refine ⟨665885991756015475998589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3551391956032082538659141 665885991756015475998589)
                    ·
                      rfl

theorem cell23_3890425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 3, 4].length) (baseStart_3890425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3890425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3890425 prefixEnd_3890425 := by exact prefixLift 3890425
  have htrace : WordTrace (prefixWord ++ tailWord_3890425) baseStart_3890425 baseEnd_3890425 := by
    simpa [prefixWord, tailWord_3890425, baseEnd_3890425] using wordTrace_append hprefix tailTrace_3890425
  have hstable : (prefixWord ++ tailWord_3890425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890425).length < 2 ^ (prefixWord ++ tailWord_3890425).sum := by decide
  have hdescent : baseEnd_3890425 < baseStart_3890425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890435 : List Nat := [1, 1, 1, 3, 2, 5, 1, 1, 1, 4, 3]
def baseStart_3890435 : Nat := 118140960795 + 3890435 * 2 ^ 59
def prefixEnd_3890435 : Nat := 4983230072969 + 3 ^ 40 * 3890435 * 2
def baseEnd_3890435 : Nat := 1997663110074591388870721

theorem tailTrace_3890435 : CollatzResearch.WordTrace tailWord_3890435 prefixEnd_3890435 1997663110074591388870721 := by
  unfold tailWord_3890435
  simp only [CollatzResearch.WordTrace]
  refine ⟨141895821660625903244864759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94597214440417268829909839 141895821660625903244864759)
  ·
    refine ⟨212843732490938854867297139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141895821660625903244864759 212843732490938854867297139)
    ·
      refine ⟨319265598736408282300945709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212843732490938854867297139 319265598736408282300945709)
      ·
        refine ⟨119724599526153105862854641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 319265598736408282300945709 119724599526153105862854641)
        ·
          refine ⟨89793449644614829397140981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119724599526153105862854641 89793449644614829397140981)
          ·
            refine ⟨8418135904182640255981967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89793449644614829397140981 8418135904182640255981967)
            ·
              refine ⟨12627203856273960383972951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8418135904182640255981967 12627203856273960383972951)
              ·
                refine ⟨18940805784410940575959427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12627203856273960383972951 18940805784410940575959427)
                ·
                  refine ⟨28411208676616410863939141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18940805784410940575959427 28411208676616410863939141)
                  ·
                    refine ⟨5327101626865577036988589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28411208676616410863939141 5327101626865577036988589)
                    ·
                      refine ⟨1997663110074591388870721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5327101626865577036988589 1997663110074591388870721)
                      ·
                        rfl

theorem cell23_3890435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 4, 3].length) (baseStart_3890435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3890435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3890435 prefixEnd_3890435 := by exact prefixLift 3890435
  have htrace : WordTrace (prefixWord ++ tailWord_3890435) baseStart_3890435 baseEnd_3890435 := by
    simpa [prefixWord, tailWord_3890435, baseEnd_3890435] using wordTrace_append hprefix tailTrace_3890435
  have hstable : (prefixWord ++ tailWord_3890435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890435).length < 2 ^ (prefixWord ++ tailWord_3890435).sum := by decide
  have hdescent : baseEnd_3890435 < baseStart_3890435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890492 : List Nat := [2, 2, 2, 2, 1, 3, 2, 1, 1, 5, 2]
def baseStart_3890492 : Nat := 118140960795 + 3890492 * 2 ^ 59
def prefixEnd_3890492 : Nat := 4983230072969 + 3 ^ 40 * 3890492 * 2
def baseEnd_3890492 : Nat := 1997692378471897665857959

theorem tailTrace_3890492 : CollatzResearch.WordTrace tailWord_3890492 prefixEnd_3890492 1997692378471897665857959 := by
  unfold tailWord_3890492
  simp only [CollatzResearch.WordTrace]
  refine ⟨70948950310709700989844865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94598600414279601319793153 70948950310709700989844865)
  ·
    refine ⟨53211712733032275742383649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70948950310709700989844865 53211712733032275742383649)
    ·
      refine ⟨39908784549774206806787737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53211712733032275742383649 39908784549774206806787737)
      ·
        refine ⟨29931588412330655105090803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39908784549774206806787737 29931588412330655105090803)
        ·
          refine ⟨44897382618495982657636205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29931588412330655105090803 44897382618495982657636205)
          ·
            refine ⟨16836518481935993496613577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44897382618495982657636205 16836518481935993496613577)
            ·
              refine ⟨12627388861451995122460183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16836518481935993496613577 12627388861451995122460183)
              ·
                refine ⟨18941083292177992683690275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12627388861451995122460183 18941083292177992683690275)
                ·
                  refine ⟨28411624938266989025535413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18941083292177992683690275 28411624938266989025535413)
                  ·
                    refine ⟨2663589837962530221143945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28411624938266989025535413 2663589837962530221143945)
                    ·
                      refine ⟨1997692378471897665857959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2663589837962530221143945 1997692378471897665857959)
                      ·
                        rfl

theorem cell23_3890492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 1, 5, 2].length) (baseStart_3890492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3890492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3890492 prefixEnd_3890492 := by exact prefixLift 3890492
  have htrace : WordTrace (prefixWord ++ tailWord_3890492) baseStart_3890492 baseEnd_3890492 := by
    simpa [prefixWord, tailWord_3890492, baseEnd_3890492] using wordTrace_append hprefix tailTrace_3890492
  have hstable : (prefixWord ++ tailWord_3890492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890492).length < 2 ^ (prefixWord ++ tailWord_3890492).sum := by decide
  have hdescent : baseEnd_3890492 < baseStart_3890492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890493 : List Nat := [1, 4, 1, 5, 1, 2, 1, 3, 1, 4]
def baseStart_3890493 : Nat := 118140960795 + 3890493 * 2 ^ 59
def prefixEnd_3890493 : Nat := 4983230072969 + 3 ^ 40 * 3890493 * 2
def baseEnd_3890493 : Nat := 665897630650850720648485

theorem tailTrace_3890493 : CollatzResearch.WordTrace tailWord_3890493 prefixEnd_3890493 665897630650850720648485 := by
  unfold tailWord_3890493
  simp only [CollatzResearch.WordTrace]
  refine ⟨141897937094415779150476133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94598624729610519433650755 141897937094415779150476133)
  ·
    refine ⟨26605863205202958590714275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141897937094415779150476133 26605863205202958590714275)
    ·
      refine ⟨39908794807804437886071413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26605863205202958590714275 39908794807804437886071413)
      ·
        refine ⟨3741449513231666051819195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39908794807804437886071413 3741449513231666051819195)
        ·
          refine ⟨5612174269847499077728793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3741449513231666051819195 5612174269847499077728793)
          ·
            refine ⟨4209130702385624308296595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5612174269847499077728793 4209130702385624308296595)
            ·
              refine ⟨6313696053578436462444893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4209130702385624308296595 6313696053578436462444893)
              ·
                refine ⟨2367636020091913673416835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6313696053578436462444893 2367636020091913673416835)
                ·
                  refine ⟨3551454030137870510125253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2367636020091913673416835 3551454030137870510125253)
                  ·
                    refine ⟨665897630650850720648485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3551454030137870510125253 665897630650850720648485)
                    ·
                      rfl

theorem cell23_3890493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 3, 1, 4].length) (baseStart_3890493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3890493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3890493 prefixEnd_3890493 := by exact prefixLift 3890493
  have htrace : WordTrace (prefixWord ++ tailWord_3890493) baseStart_3890493 baseEnd_3890493 := by
    simpa [prefixWord, tailWord_3890493, baseEnd_3890493] using wordTrace_append hprefix tailTrace_3890493
  have hstable : (prefixWord ++ tailWord_3890493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890493).length < 2 ^ (prefixWord ++ tailWord_3890493).sum := by decide
  have hdescent : baseEnd_3890493 < baseStart_3890493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890515 : List Nat := [1, 1, 1, 2, 1, 1, 5, 3, 4, 4]
def baseStart_3890515 : Nat := 118140960795 + 3890515 * 2 ^ 59
def prefixEnd_3890515 : Nat := 4983230072969 + 3 ^ 40 * 3890515 * 2
def baseEnd_3890515 : Nat := 665901396175650358623451

theorem tailTrace_3890515 : CollatzResearch.WordTrace tailWord_3890515 prefixEnd_3890515 665901396175650358623451 := by
  unfold tailWord_3890515
  simp only [CollatzResearch.WordTrace]
  refine ⟨141898739500336076907776999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94599159666890717938517999 141898739500336076907776999)
  ·
    refine ⟨212848109250504115361665499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141898739500336076907776999 212848109250504115361665499)
    ·
      refine ⟨319272163875756173042498249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212848109250504115361665499 319272163875756173042498249)
      ·
        refine ⟨239454122906817129781873687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319272163875756173042498249 239454122906817129781873687)
        ·
          refine ⟨359181184360225694672810531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239454122906817129781873687 359181184360225694672810531)
          ·
            refine ⟨538771776540338542009215797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359181184360225694672810531 538771776540338542009215797)
            ·
              refine ⟨50509854050656738313363981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 538771776540338542009215797 50509854050656738313363981)
              ·
                refine ⟨18941195268996276867511493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50509854050656738313363981 18941195268996276867511493)
                ·
                  refine ⟨3551474112936801912658405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18941195268996276867511493 3551474112936801912658405)
                  ·
                    refine ⟨665901396175650358623451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3551474112936801912658405 665901396175650358623451)
                    ·
                      rfl

theorem cell23_3890515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 4, 4].length) (baseStart_3890515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3890515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3890515 prefixEnd_3890515 := by exact prefixLift 3890515
  have htrace : WordTrace (prefixWord ++ tailWord_3890515) baseStart_3890515 baseEnd_3890515 := by
    simpa [prefixWord, tailWord_3890515, baseEnd_3890515] using wordTrace_append hprefix tailTrace_3890515
  have hstable : (prefixWord ++ tailWord_3890515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890515).length < 2 ^ (prefixWord ++ tailWord_3890515).sum := by decide
  have hdescent : baseEnd_3890515 < baseStart_3890515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890536 : List Nat := [2, 1, 4, 2, 4, 1, 1, 2, 1, 5]
def baseStart_3890536 : Nat := 118140960795 + 3890536 * 2 ^ 59
def prefixEnd_3890536 : Nat := 4983230072969 + 3 ^ 40 * 3890536 * 2
def baseEnd_3890536 : Nat := 665904990540231831235919

theorem tailTrace_3890536 : CollatzResearch.WordTrace tailWord_3890536 prefixEnd_3890536 665904990540231831235919 := by
  unfold tailWord_3890536
  simp only [CollatzResearch.WordTrace]
  refine ⟨70949752716629998747145731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94599670288839998329527641 70949752716629998747145731)
  ·
    refine ⟨106424629074944998120718597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70949752716629998747145731 106424629074944998120718597)
    ·
      refine ⟨19954617951552187147634737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106424629074944998120718597 19954617951552187147634737)
      ·
        refine ⟨14965963463664140360726053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19954617951552187147634737 14965963463664140360726053)
        ·
          refine ⟨2806118149437026317636135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14965963463664140360726053 2806118149437026317636135)
          ·
            refine ⟨4209177224155539476454203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2806118149437026317636135 4209177224155539476454203)
            ·
              refine ⟨6313765836233309214681305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4209177224155539476454203 6313765836233309214681305)
              ·
                refine ⟨4735324377174981911010979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6313765836233309214681305 4735324377174981911010979)
                ·
                  refine ⟨7102986565762472866516469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4735324377174981911010979 7102986565762472866516469)
                  ·
                    refine ⟨665904990540231831235919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7102986565762472866516469 665904990540231831235919)
                    ·
                      rfl

theorem cell23_3890536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_3890536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3890536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3890536 prefixEnd_3890536 := by exact prefixLift 3890536
  have htrace : WordTrace (prefixWord ++ tailWord_3890536) baseStart_3890536 baseEnd_3890536 := by
    simpa [prefixWord, tailWord_3890536, baseEnd_3890536] using wordTrace_append hprefix tailTrace_3890536
  have hstable : (prefixWord ++ tailWord_3890536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890536).length < 2 ^ (prefixWord ++ tailWord_3890536).sum := by decide
  have hdescent : baseEnd_3890536 < baseStart_3890536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890556 : List Nat := [2, 2, 2, 1, 1, 1, 4, 5, 1, 2, 2]
def baseStart_3890556 : Nat := 118140960795 + 3890556 * 2 ^ 59
def prefixEnd_3890556 : Nat := 4983230072969 + 3 ^ 40 * 3890556 * 2
def baseEnd_3890556 : Nat := 1997725241233785415457665

theorem tailTrace_3890556 : CollatzResearch.WordTrace tailWord_3890556 prefixEnd_3890556 1997725241233785415457665 := by
  unfold tailWord_3890556
  simp only [CollatzResearch.WordTrace]
  refine ⟨70950117446593770455009761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94600156595458360606679681 70950117446593770455009761)
  ·
    refine ⟨53212588084945327841257321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70950117446593770455009761 53212588084945327841257321)
    ·
      refine ⟨39909441063708995880942991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53212588084945327841257321 39909441063708995880942991)
      ·
        refine ⟨59864161595563493821414487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39909441063708995880942991 59864161595563493821414487)
        ·
          refine ⟨89796242393345240732121731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59864161595563493821414487 89796242393345240732121731)
          ·
            refine ⟨134694363590017861098182597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89796242393345240732121731 134694363590017861098182597)
            ·
              refine ⟨25255193173128348955909237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134694363590017861098182597 25255193173128348955909237)
              ·
                refine ⟨2367674359980782714616491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25255193173128348955909237 2367674359980782714616491)
                ·
                  refine ⟨3551511539971174071924737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2367674359980782714616491 3551511539971174071924737)
                  ·
                    refine ⟨2663633654978380553943553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3551511539971174071924737 2663633654978380553943553)
                    ·
                      refine ⟨1997725241233785415457665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2663633654978380553943553 1997725241233785415457665)
                      ·
                        rfl

theorem cell23_3890556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 5, 1, 2, 2].length) (baseStart_3890556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3890556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3890556 prefixEnd_3890556 := by exact prefixLift 3890556
  have htrace : WordTrace (prefixWord ++ tailWord_3890556) baseStart_3890556 baseEnd_3890556 := by
    simpa [prefixWord, tailWord_3890556, baseEnd_3890556] using wordTrace_append hprefix tailTrace_3890556
  have hstable : (prefixWord ++ tailWord_3890556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890556).length < 2 ^ (prefixWord ++ tailWord_3890556).sum := by decide
  have hdescent : baseEnd_3890556 < baseStart_3890556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890562 : List Nat := [3, 4, 2, 1, 1, 12]
def baseStart_3890562 : Nat := 118140960795 + 3890562 * 2 ^ 59
def prefixEnd_3890562 : Nat := 4983230072969 + 3 ^ 40 * 3890562 * 2
def baseEnd_3890562 : Nat := 8221104206245730008159

theorem tailTrace_3890562 : CollatzResearch.WordTrace tailWord_3890562 prefixEnd_3890562 8221104206245730008159 := by
  unfold tailWord_3890562
  simp only [CollatzResearch.WordTrace]
  refine ⟨35475113432791450983684485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94600302487443869289825293 35475113432791450983684485)
  ·
    refine ⟨6651583768648397059440841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35475113432791450983684485 6651583768648397059440841)
    ·
      refine ⟨4988687826486297794580631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6651583768648397059440841 4988687826486297794580631)
      ·
        refine ⟨7483031739729446691870947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4988687826486297794580631 7483031739729446691870947)
        ·
          refine ⟨11224547609594170037806421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7483031739729446691870947 11224547609594170037806421)
          ·
            refine ⟨8221104206245730008159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 11224547609594170037806421 8221104206245730008159)
            ·
              rfl

theorem cell23_3890562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 12].length) (baseStart_3890562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3890562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3890562 prefixEnd_3890562 := by exact prefixLift 3890562
  have htrace : WordTrace (prefixWord ++ tailWord_3890562) baseStart_3890562 baseEnd_3890562 := by
    simpa [prefixWord, tailWord_3890562, baseEnd_3890562] using wordTrace_append hprefix tailTrace_3890562
  have hstable : (prefixWord ++ tailWord_3890562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890562).length < 2 ^ (prefixWord ++ tailWord_3890562).sum := by decide
  have hdescent : baseEnd_3890562 < baseStart_3890562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890589 : List Nat := [1, 4, 2, 1, 3, 2, 2, 1, 1, 3, 3]
def baseStart_3890589 : Nat := 118140960795 + 3890589 * 2 ^ 59
def prefixEnd_3890589 : Nat := 4983230072969 + 3 ^ 40 * 3890589 * 2
def baseEnd_3890589 : Nat := 1997742186095383786345013

theorem tailTrace_3890589 : CollatzResearch.WordTrace tailWord_3890589 prefixEnd_3890589 1997742186095383786345013 := by
  unfold tailWord_3890589
  simp only [CollatzResearch.WordTrace]
  refine ⟨141901438502067987545970821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94600959001378658363980547 141901438502067987545970821)
  ·
    refine ⟨26606519719137747664869529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141901438502067987545970821 26606519719137747664869529)
    ·
      refine ⟨19954889789353310748652147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26606519719137747664869529 19954889789353310748652147)
      ·
        refine ⟨29932334684029966122978221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19954889789353310748652147 29932334684029966122978221)
        ·
          refine ⟨11224625506511237296116833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29932334684029966122978221 11224625506511237296116833)
          ·
            refine ⟨8418469129883427972087625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11224625506511237296116833 8418469129883427972087625)
            ·
              refine ⟨6313851847412570979065719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8418469129883427972087625 6313851847412570979065719)
              ·
                refine ⟨9470777771118856468598579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6313851847412570979065719 9470777771118856468598579)
                ·
                  refine ⟨14206166656678284702897869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9470777771118856468598579 14206166656678284702897869)
                  ·
                    refine ⟨5327312496254356763586701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14206166656678284702897869 5327312496254356763586701)
                    ·
                      refine ⟨1997742186095383786345013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5327312496254356763586701 1997742186095383786345013)
                      ·
                        rfl

theorem cell23_3890589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_3890589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3890589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3890589 prefixEnd_3890589 := by exact prefixLift 3890589
  have htrace : WordTrace (prefixWord ++ tailWord_3890589) baseStart_3890589 baseEnd_3890589 := by
    simpa [prefixWord, tailWord_3890589, baseEnd_3890589] using wordTrace_append hprefix tailTrace_3890589
  have hstable : (prefixWord ++ tailWord_3890589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890589).length < 2 ^ (prefixWord ++ tailWord_3890589).sum := by decide
  have hdescent : baseEnd_3890589 < baseStart_3890589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890595 : List Nat := [1, 1, 1, 4, 1, 3, 1, 2, 2, 3, 4]
def baseStart_3890595 : Nat := 118140960795 + 3890595 * 2 ^ 59
def prefixEnd_3890595 : Nat := 4983230072969 + 3 ^ 40 * 3890595 * 2
def baseEnd_3890595 : Nat := 1997745266979310762869985

theorem tailTrace_3890595 : CollatzResearch.WordTrace tailWord_3890595 prefixEnd_3890595 1997745266979310762869985 := by
  unfold tailWord_3890595
  simp only [CollatzResearch.WordTrace]
  refine ⟨141901657340046250570689239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94601104893364167047126159 141901657340046250570689239)
  ·
    refine ⟨212852486010069375856033859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141901657340046250570689239 212852486010069375856033859)
    ·
      refine ⟨319278729015104063784050789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212852486010069375856033859 319278729015104063784050789)
      ·
        refine ⟨59864761690332011959509523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 319278729015104063784050789 59864761690332011959509523)
        ·
          refine ⟨89797142535498017939264285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59864761690332011959509523 89797142535498017939264285)
          ·
            refine ⟨33673928450811756727224107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89797142535498017939264285 33673928450811756727224107)
            ·
              refine ⟨50510892676217635090836161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33673928450811756727224107 50510892676217635090836161)
              ·
                refine ⟨37883169507163226318127121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50510892676217635090836161 37883169507163226318127121)
                ·
                  refine ⟨28412377130372419738595341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37883169507163226318127121 28412377130372419738595341)
                  ·
                    refine ⟨10654641423889657401973253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28412377130372419738595341 10654641423889657401973253)
                    ·
                      refine ⟨1997745266979310762869985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10654641423889657401973253 1997745266979310762869985)
                      ·
                        rfl

theorem cell23_3890595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_3890595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3890595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3890595 prefixEnd_3890595 := by exact prefixLift 3890595
  have htrace : WordTrace (prefixWord ++ tailWord_3890595) baseStart_3890595 baseEnd_3890595 := by
    simpa [prefixWord, tailWord_3890595, baseEnd_3890595] using wordTrace_append hprefix tailTrace_3890595
  have hstable : (prefixWord ++ tailWord_3890595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890595).length < 2 ^ (prefixWord ++ tailWord_3890595).sum := by decide
  have hdescent : baseEnd_3890595 < baseStart_3890595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890599 : List Nat := [1, 1, 6, 1, 1, 1, 1, 3, 3, 3, 2]
def baseStart_3890599 : Nat := 118140960795 + 3890599 * 2 ^ 59
def prefixEnd_3890599 : Nat := 4983230072969 + 3 ^ 40 * 3890599 * 2
def baseEnd_3890599 : Nat := 1997747320901928747219967

theorem tailTrace_3890599 : CollatzResearch.WordTrace tailWord_3890599 prefixEnd_3890599 1997747320901928747219967 := by
  unfold tailWord_3890599
  simp only [CollatzResearch.WordTrace]
  refine ⟨141901803232031759253834851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94601202154687839502556567 141901803232031759253834851)
  ·
    refine ⟨212852704848047638880752277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141901803232031759253834851 212852704848047638880752277)
    ·
      refine ⟨9977470539752233072535263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 212852704848047638880752277 9977470539752233072535263)
      ·
        refine ⟨14966205809628349608802895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9977470539752233072535263 14966205809628349608802895)
        ·
          refine ⟨22449308714442524413204343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14966205809628349608802895 22449308714442524413204343)
          ·
            refine ⟨33673963071663786619806515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22449308714442524413204343 33673963071663786619806515)
            ·
              refine ⟨50510944607495679929709773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33673963071663786619806515 50510944607495679929709773)
              ·
                refine ⟨18941604227810879973641165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50510944607495679929709773 18941604227810879973641165)
                ·
                  refine ⟨7103101585429079990115437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18941604227810879973641165 7103101585429079990115437)
                  ·
                    refine ⟨2663663094535904996293289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7103101585429079990115437 2663663094535904996293289)
                    ·
                      refine ⟨1997747320901928747219967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2663663094535904996293289 1997747320901928747219967)
                      ·
                        rfl

theorem cell23_3890599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_3890599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3890599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3890599 prefixEnd_3890599 := by exact prefixLift 3890599
  have htrace : WordTrace (prefixWord ++ tailWord_3890599) baseStart_3890599 baseEnd_3890599 := by
    simpa [prefixWord, tailWord_3890599, baseEnd_3890599] using wordTrace_append hprefix tailTrace_3890599
  have hstable : (prefixWord ++ tailWord_3890599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890599).length < 2 ^ (prefixWord ++ tailWord_3890599).sum := by decide
  have hdescent : baseEnd_3890599 < baseStart_3890599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890615 : List Nat := [1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 5]
def baseStart_3890615 : Nat := 118140960795 + 3890615 * 2 ^ 59
def prefixEnd_3890615 : Nat := 4983230072969 + 3 ^ 40 * 3890615 * 2
def baseEnd_3890615 : Nat := 1997755536592400684619893

theorem tailTrace_3890615 : CollatzResearch.WordTrace tailWord_3890615 prefixEnd_3890615 1997755536592400684619893 := by
  unfold tailWord_3890615
  simp only [CollatzResearch.WordTrace]
  refine ⟨141902386799973793986417299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94601591199982529324278199 141902386799973793986417299)
  ·
    refine ⟨212853580199960690979625949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141902386799973793986417299 212853580199960690979625949)
    ·
      refine ⟨79820092574985259117359731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212853580199960690979625949 79820092574985259117359731)
      ·
        refine ⟨119730138862477888676039597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79820092574985259117359731 119730138862477888676039597)
        ·
          refine ⟨44898802073429208253514849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119730138862477888676039597 44898802073429208253514849)
          ·
            refine ⟨33674101555071906190136137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44898802073429208253514849 33674101555071906190136137)
            ·
              refine ⟨25255576166303929642602103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33674101555071906190136137 25255576166303929642602103)
              ·
                refine ⟨37883364249455894463903155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25255576166303929642602103 37883364249455894463903155)
                ·
                  refine ⟨56825046374183841695854733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37883364249455894463903155 56825046374183841695854733)
                  ·
                    refine ⟨21309392390318940635945525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56825046374183841695854733 21309392390318940635945525)
                    ·
                      refine ⟨1997755536592400684619893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21309392390318940635945525 1997755536592400684619893)
                      ·
                        rfl

theorem cell23_3890615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 5].length) (baseStart_3890615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3890615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3890615 prefixEnd_3890615 := by exact prefixLift 3890615
  have htrace : WordTrace (prefixWord ++ tailWord_3890615) baseStart_3890615 baseEnd_3890615 := by
    simpa [prefixWord, tailWord_3890615, baseEnd_3890615] using wordTrace_append hprefix tailTrace_3890615
  have hstable : (prefixWord ++ tailWord_3890615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890615).length < 2 ^ (prefixWord ++ tailWord_3890615).sum := by decide
  have hdescent : baseEnd_3890615 < baseStart_3890615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890616 : List Nat := [2, 1, 2, 1, 2, 2, 6, 1, 1, 3, 2]
def baseStart_3890616 : Nat := 118140960795 + 3890616 * 2 ^ 59
def prefixEnd_3890616 : Nat := 4983230072969 + 3 ^ 40 * 3890616 * 2
def baseEnd_3890616 : Nat := 1997756050073055180707389

theorem tailTrace_3890616 : CollatzResearch.WordTrace tailWord_3890616 prefixEnd_3890616 1997756050073055180707389 := by
  unfold tailWord_3890616
  simp only [CollatzResearch.WordTrace]
  refine ⟨70951211636485085578601851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94601615515313447438135801 70951211636485085578601851)
  ·
    refine ⟨106426817454727628367902777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70951211636485085578601851 106426817454727628367902777)
    ·
      refine ⟨79820113091045721275927083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106426817454727628367902777 79820113091045721275927083)
      ·
        refine ⟨119730169636568581913890625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79820113091045721275927083 119730169636568581913890625)
        ·
          refine ⟨89797627227426436435417969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119730169636568581913890625 89797627227426436435417969)
          ·
            refine ⟨67348220420569827326563477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89797627227426436435417969 67348220420569827326563477)
            ·
              refine ⟨3156947832214210655932663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 67348220420569827326563477 3156947832214210655932663)
              ·
                refine ⟨4735421748321315983898995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3156947832214210655932663 4735421748321315983898995)
                ·
                  refine ⟨7103132622481973975848493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4735421748321315983898995 7103132622481973975848493)
                  ·
                    refine ⟨2663674733430740240943185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7103132622481973975848493 2663674733430740240943185)
                    ·
                      refine ⟨1997756050073055180707389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2663674733430740240943185 1997756050073055180707389)
                      ·
                        rfl

theorem cell23_3890616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 1, 1, 3, 2].length) (baseStart_3890616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3890616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3890616 prefixEnd_3890616 := by exact prefixLift 3890616
  have htrace : WordTrace (prefixWord ++ tailWord_3890616) baseStart_3890616 baseEnd_3890616 := by
    simpa [prefixWord, tailWord_3890616, baseEnd_3890616] using wordTrace_append hprefix tailTrace_3890616
  have hstable : (prefixWord ++ tailWord_3890616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890616).length < 2 ^ (prefixWord ++ tailWord_3890616).sum := by decide
  have hdescent : baseEnd_3890616 < baseStart_3890616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890635 : List Nat := [1, 1, 1, 1, 3, 3, 3, 3, 7]
def baseStart_3890635 : Nat := 118140960795 + 3890635 * 2 ^ 59
def prefixEnd_3890635 : Nat := 4983230072969 + 3 ^ 40 * 3890635 * 2
def baseEnd_3890635 : Nat := 221973978467276734041089

theorem tailTrace_3890635 : CollatzResearch.WordTrace tailWord_3890635 prefixEnd_3890635 221973978467276734041089 := by
  unfold tailWord_3890635
  simp only [CollatzResearch.WordTrace]
  refine ⟨141903116259901337402145359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94602077506600891601430239 141903116259901337402145359)
  ·
    refine ⟨212854674389852006103218039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141903116259901337402145359 212854674389852006103218039)
    ·
      refine ⟨319282011584778009154827059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212854674389852006103218039 319282011584778009154827059)
      ·
        refine ⟨478923017377167013732240589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319282011584778009154827059 478923017377167013732240589)
        ·
          refine ⟨179596131516437630149590221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 478923017377167013732240589 179596131516437630149590221)
          ·
            refine ⟨67348549318664111306096333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179596131516437630149590221 67348549318664111306096333)
            ·
              refine ⟨25255705994499041739786125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67348549318664111306096333 25255705994499041739786125)
              ·
                refine ⟨9470889747937140652419797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25255705994499041739786125 9470889747937140652419797)
                ·
                  refine ⟨221973978467276734041089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9470889747937140652419797 221973978467276734041089)
                  ·
                    rfl

theorem cell23_3890635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 7].length) (baseStart_3890635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3890635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3890635 prefixEnd_3890635 := by exact prefixLift 3890635
  have htrace : WordTrace (prefixWord ++ tailWord_3890635) baseStart_3890635 baseEnd_3890635 := by
    simpa [prefixWord, tailWord_3890635, baseEnd_3890635] using wordTrace_append hprefix tailTrace_3890635
  have hstable : (prefixWord ++ tailWord_3890635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890635).length < 2 ^ (prefixWord ++ tailWord_3890635).sum := by decide
  have hdescent : baseEnd_3890635 < baseStart_3890635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890682 : List Nat := [3, 1, 1, 1, 1, 2, 5, 2, 2, 5]
def baseStart_3890682 : Nat := 118140960795 + 3890682 * 2 ^ 59
def prefixEnd_3890682 : Nat := 4983230072969 + 3 ^ 40 * 3890682 * 2
def baseEnd_3890682 : Nat := 665929979932083974160695

theorem tailTrace_3890682 : CollatzResearch.WordTrace tailWord_3890682 prefixEnd_3890682 665929979932083974160695 := by
  unfold tailWord_3890682
  simp only [CollatzResearch.WordTrace]
  refine ⟨35476207622682766107276575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94603220327154042952737533 35476207622682766107276575)
  ·
    refine ⟨53214311434024149160914863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35476207622682766107276575 53214311434024149160914863)
    ·
      refine ⟨79821467151036223741372295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53214311434024149160914863 79821467151036223741372295)
      ·
        refine ⟨119732200726554335612058443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79821467151036223741372295 119732200726554335612058443)
        ·
          refine ⟨179598301089831503418087665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119732200726554335612058443 179598301089831503418087665)
          ·
            refine ⟨134698725817373627563565749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179598301089831503418087665 134698725817373627563565749)
            ·
              refine ⟨12628005545378777584084289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 134698725817373627563565749 12628005545378777584084289)
              ·
                refine ⟨9471004159034083188063217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12628005545378777584084289 9471004159034083188063217)
                ·
                  refine ⟨7103253119275562391047413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9471004159034083188063217 7103253119275562391047413)
                  ·
                    refine ⟨665929979932083974160695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7103253119275562391047413 665929979932083974160695)
                    ·
                      rfl

theorem cell23_3890682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 2, 5].length) (baseStart_3890682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3890682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3890682 prefixEnd_3890682 := by exact prefixLift 3890682
  have htrace : WordTrace (prefixWord ++ tailWord_3890682) baseStart_3890682 baseEnd_3890682 := by
    simpa [prefixWord, tailWord_3890682, baseEnd_3890682] using wordTrace_append hprefix tailTrace_3890682
  have hstable : (prefixWord ++ tailWord_3890682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890682).length < 2 ^ (prefixWord ++ tailWord_3890682).sum := by decide
  have hdescent : baseEnd_3890682 < baseStart_3890682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890739 : List Nat := [1, 1, 1, 2, 4, 3, 2, 2, 2, 2, 3]
def baseStart_3890739 : Nat := 118140960795 + 3890739 * 2 ^ 59
def prefixEnd_3890739 : Nat := 4983230072969 + 3 ^ 40 * 3890739 * 2
def baseEnd_3890739 : Nat := 1997819208193558199469323

theorem tailTrace_3890739 : CollatzResearch.WordTrace tailWord_3890739 prefixEnd_3890739 1997819208193558199469323 := by
  unfold tailWord_3890739
  simp only [CollatzResearch.WordTrace]
  refine ⟨141906909451524563163931271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94604606301016375442620847 141906909451524563163931271)
  ·
    refine ⟨212860364177286844745896907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141906909451524563163931271 212860364177286844745896907)
    ·
      refine ⟨319290546265930267118845361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212860364177286844745896907 319290546265930267118845361)
      ·
        refine ⟨239467909699447700339134021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319290546265930267118845361 239467909699447700339134021)
        ·
          refine ⟨44900233068646443813587629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 239467909699447700339134021 44900233068646443813587629)
          ·
            refine ⟨16837587400742416430095361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44900233068646443813587629 16837587400742416430095361)
            ·
              refine ⟨12628190550556812322571521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16837587400742416430095361 12628190550556812322571521)
              ·
                refine ⟨9471142912917609241928641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12628190550556812322571521 9471142912917609241928641)
                ·
                  refine ⟨7103357184688206931446481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9471142912917609241928641 7103357184688206931446481)
                  ·
                    refine ⟨5327517888516155198584861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7103357184688206931446481 5327517888516155198584861)
                    ·
                      refine ⟨1997819208193558199469323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5327517888516155198584861 1997819208193558199469323)
                      ·
                        rfl

theorem cell23_3890739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 2, 2, 3].length) (baseStart_3890739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3890739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3890739 prefixEnd_3890739 := by exact prefixLift 3890739
  have htrace : WordTrace (prefixWord ++ tailWord_3890739) baseStart_3890739 baseEnd_3890739 := by
    simpa [prefixWord, tailWord_3890739, baseEnd_3890739] using wordTrace_append hprefix tailTrace_3890739
  have hstable : (prefixWord ++ tailWord_3890739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890739).length < 2 ^ (prefixWord ++ tailWord_3890739).sum := by decide
  have hdescent : baseEnd_3890739 < baseStart_3890739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890746 : List Nat := [3, 1, 1, 1, 3, 2, 3, 4, 1, 4]
def baseStart_3890746 : Nat := 118140960795 + 3890746 * 2 ^ 59
def prefixEnd_3890746 : Nat := 4983230072969 + 3 ^ 40 * 3890746 * 2
def baseEnd_3890746 : Nat := 665940934186046557360597

theorem tailTrace_3890746 : CollatzResearch.WordTrace tailWord_3890746 prefixEnd_3890746 665940934186046557360597 := by
  unfold tailWord_3890746
  simp only [CollatzResearch.WordTrace]
  refine ⟨35476791190624800839859023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94604776508332802239624061 35476791190624800839859023)
  ·
    refine ⟨53215186785937201259788535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35476791190624800839859023 53215186785937201259788535)
    ·
      refine ⟨79822780178905801889682803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53215186785937201259788535 79822780178905801889682803)
      ·
        refine ⟨119734170268358702834524205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79822780178905801889682803 119734170268358702834524205)
        ·
          refine ⟨44900313850634513562946577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119734170268358702834524205 44900313850634513562946577)
          ·
            refine ⟨33675235387975885172209933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44900313850634513562946577 33675235387975885172209933)
            ·
              refine ⟨12628213270490956939578725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33675235387975885172209933 12628213270490956939578725)
              ·
                refine ⟨2367789988217054426171011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12628213270490956939578725 2367789988217054426171011)
                ·
                  refine ⟨3551684982325581639256517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2367789988217054426171011 3551684982325581639256517)
                  ·
                    refine ⟨665940934186046557360597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3551684982325581639256517 665940934186046557360597)
                    ·
                      rfl

theorem cell23_3890746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 4, 1, 4].length) (baseStart_3890746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3890746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3890746 prefixEnd_3890746 := by exact prefixLift 3890746
  have htrace : WordTrace (prefixWord ++ tailWord_3890746) baseStart_3890746 baseEnd_3890746 := by
    simpa [prefixWord, tailWord_3890746, baseEnd_3890746] using wordTrace_append hprefix tailTrace_3890746
  have hstable : (prefixWord ++ tailWord_3890746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890746).length < 2 ^ (prefixWord ++ tailWord_3890746).sum := by decide
  have hdescent : baseEnd_3890746 < baseStart_3890746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890752 : List Nat := [2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 3]
def baseStart_3890752 : Nat := 118140960795 + 3890752 * 2 ^ 59
def prefixEnd_3890752 : Nat := 4983230072969 + 3 ^ 40 * 3890752 * 2
def baseEnd_3890752 : Nat := 1997825883442066648606763

theorem tailTrace_3890752 : CollatzResearch.WordTrace tailWord_3890752 prefixEnd_3890752 1997825883442066648606763 := by
  unfold tailWord_3890752
  simp only [CollatzResearch.WordTrace]
  refine ⟨70953691800238733192077255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94604922400318310922769673 70953691800238733192077255)
  ·
    refine ⟨106430537700358099788115883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70953691800238733192077255 106430537700358099788115883)
    ·
      refine ⟨159645806550537149682173825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106430537700358099788115883 159645806550537149682173825)
      ·
        refine ⟨119734354912902862261630369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159645806550537149682173825 119734354912902862261630369)
        ·
          refine ⟨89800766184677146696222777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119734354912902862261630369 89800766184677146696222777)
          ·
            refine ⟨67350574638507860022167083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89800766184677146696222777 67350574638507860022167083)
            ·
              refine ⟨101025861957761790033250625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67350574638507860022167083 101025861957761790033250625)
              ·
                refine ⟨75769396468321342524937969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101025861957761790033250625 75769396468321342524937969)
                ·
                  refine ⟨56827047351241006893703477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75769396468321342524937969 56827047351241006893703477)
                  ·
                    refine ⟨5327535689178844396284701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56827047351241006893703477 5327535689178844396284701)
                    ·
                      refine ⟨1997825883442066648606763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5327535689178844396284701 1997825883442066648606763)
                      ·
                        rfl

theorem cell23_3890752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 3].length) (baseStart_3890752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3890752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3890752 prefixEnd_3890752 := by exact prefixLift 3890752
  have htrace : WordTrace (prefixWord ++ tailWord_3890752) baseStart_3890752 baseEnd_3890752 := by
    simpa [prefixWord, tailWord_3890752, baseEnd_3890752] using wordTrace_append hprefix tailTrace_3890752
  have hstable : (prefixWord ++ tailWord_3890752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890752).length < 2 ^ (prefixWord ++ tailWord_3890752).sum := by decide
  have hdescent : baseEnd_3890752 < baseStart_3890752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890826 : List Nat := [3, 1, 2, 3, 2, 1, 1, 4, 1, 1, 4]
def baseStart_3890826 : Nat := 118140960795 + 3890826 * 2 ^ 59
def prefixEnd_3890826 : Nat := 4983230072969 + 3 ^ 40 * 3890826 * 2
def baseEnd_3890826 : Nat := 1997863881010499359081423

theorem tailTrace_3890826 : CollatzResearch.WordTrace tailWord_3890826 prefixEnd_3890826 1997863881010499359081423 := by
  unfold tailWord_3890826
  simp only [CollatzResearch.WordTrace]
  refine ⟨35477520650552344255587083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94606721734806251348232221 35477520650552344255587083)
  ·
    refine ⟨53216280975828516383380625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35477520650552344255587083 53216280975828516383380625)
    ·
      refine ⟨39912210731871387287535469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53216280975828516383380625 39912210731871387287535469)
      ·
        refine ⟨14967079024451770232825801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39912210731871387287535469 14967079024451770232825801)
        ·
          refine ⟨11225309268338827674619351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14967079024451770232825801 11225309268338827674619351)
          ·
            refine ⟨16837963902508241511929027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11225309268338827674619351 16837963902508241511929027)
            ·
              refine ⟨25256945853762362267893541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16837963902508241511929027 25256945853762362267893541)
              ·
                refine ⟨4735677347580442925230039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25256945853762362267893541 4735677347580442925230039)
                ·
                  refine ⟨7103516021370664387845059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4735677347580442925230039 7103516021370664387845059)
                  ·
                    refine ⟨10655274032055996581767589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7103516021370664387845059 10655274032055996581767589)
                    ·
                      refine ⟨1997863881010499359081423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10655274032055996581767589 1997863881010499359081423)
                      ·
                        rfl

theorem cell23_3890826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_3890826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3890826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3890826 prefixEnd_3890826 := by exact prefixLift 3890826
  have htrace : WordTrace (prefixWord ++ tailWord_3890826) baseStart_3890826 baseEnd_3890826 := by
    simpa [prefixWord, tailWord_3890826, baseEnd_3890826] using wordTrace_append hprefix tailTrace_3890826
  have hstable : (prefixWord ++ tailWord_3890826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890826).length < 2 ^ (prefixWord ++ tailWord_3890826).sum := by decide
  have hdescent : baseEnd_3890826 < baseStart_3890826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890846 : List Nat := [4, 3, 1, 1, 1, 2, 1, 3, 1, 1, 5]
def baseStart_3890846 : Nat := 118140960795 + 3890846 * 2 ^ 59
def prefixEnd_3890846 : Nat := 4983230072969 + 3 ^ 40 * 3890846 * 2
def baseEnd_3890846 : Nat := 1997874150623589280831331

theorem tailTrace_3890846 : CollatzResearch.WordTrace tailWord_3890846 prefixEnd_3890846 1997874150623589280831331 := by
  unfold tailWord_3890846
  simp only [CollatzResearch.WordTrace]
  refine ⟨17738851507767115054759549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94607208041424613625384261 17738851507767115054759549)
  ·
    refine ⟨6652069315412668145534831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17738851507767115054759549 6652069315412668145534831)
    ·
      refine ⟨9978103973119002218302247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6652069315412668145534831 9978103973119002218302247)
      ·
        refine ⟨14967155959678503327453371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9978103973119002218302247 14967155959678503327453371)
        ·
          refine ⟨22450733939517754991180057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14967155959678503327453371 22450733939517754991180057)
          ·
            refine ⟨16838050454638316243385043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22450733939517754991180057 16838050454638316243385043)
            ·
              refine ⟨25257075681957474365077565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16838050454638316243385043 25257075681957474365077565)
              ·
                refine ⟨9471403380734052886904087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25257075681957474365077565 9471403380734052886904087)
                ·
                  refine ⟨14207105071101079330356131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9471403380734052886904087 14207105071101079330356131)
                  ·
                    refine ⟨21310657606651618995534197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14207105071101079330356131 21310657606651618995534197)
                    ·
                      refine ⟨1997874150623589280831331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21310657606651618995534197 1997874150623589280831331)
                      ·
                        rfl

theorem cell23_3890846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_3890846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3890846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3890846 prefixEnd_3890846 := by exact prefixLift 3890846
  have htrace : WordTrace (prefixWord ++ tailWord_3890846) baseStart_3890846 baseEnd_3890846 := by
    simpa [prefixWord, tailWord_3890846, baseEnd_3890846] using wordTrace_append hprefix tailTrace_3890846
  have hstable : (prefixWord ++ tailWord_3890846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890846).length < 2 ^ (prefixWord ++ tailWord_3890846).sum := by decide
  have hdescent : baseEnd_3890846 < baseStart_3890846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890849 : List Nat := [1, 2, 3, 3, 2, 3, 9]
def baseStart_3890849 : Nat := 118140960795 + 3890849 * 2 ^ 59
def prefixEnd_3890849 : Nat := 4983230072969 + 3 ^ 40 * 3890849 * 2
def baseEnd_3890849 : Nat := 24665131988463614433257

theorem tailTrace_3890849 : CollatzResearch.WordTrace tailWord_3890849 prefixEnd_3890849 24665131988463614433257 := by
  unfold tailWord_3890849
  simp only [CollatzResearch.WordTrace]
  refine ⟨141910921481126051950435601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94607280987417367966957067 141910921481126051950435601)
  ·
    refine ⟨106433191110844538962826701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141910921481126051950435601 106433191110844538962826701)
    ·
      refine ⟨39912446666566702111060013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106433191110844538962826701 39912446666566702111060013)
      ·
        refine ⟨14967167499962513291647505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39912446666566702111060013 14967167499962513291647505)
        ·
          refine ⟨11225375624971884968735629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14967167499962513291647505 11225375624971884968735629)
          ·
            refine ⟨4209515859364456863275861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11225375624971884968735629 4209515859364456863275861)
            ·
              refine ⟨24665131988463614433257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4209515859364456863275861 24665131988463614433257)
              ·
                rfl

theorem cell23_3890849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 9].length) (baseStart_3890849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3890849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3890849 prefixEnd_3890849 := by exact prefixLift 3890849
  have htrace : WordTrace (prefixWord ++ tailWord_3890849) baseStart_3890849 baseEnd_3890849 := by
    simpa [prefixWord, tailWord_3890849, baseEnd_3890849] using wordTrace_append hprefix tailTrace_3890849
  have hstable : (prefixWord ++ tailWord_3890849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890849).length < 2 ^ (prefixWord ++ tailWord_3890849).sum := by decide
  have hdescent : baseEnd_3890849 < baseStart_3890849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890870 : List Nat := [5, 1, 3, 1, 1, 2, 1, 3, 2, 4]
def baseStart_3890870 : Nat := 118140960795 + 3890870 * 2 ^ 59
def prefixEnd_3890870 : Nat := 4983230072969 + 3 ^ 40 * 3890870 * 2
def baseEnd_3890870 : Nat := 665962158053099062310407

theorem tailTrace_3890870 : CollatzResearch.WordTrace tailWord_3890870 prefixEnd_3890870 665962158053099062310407 := by
  unfold tailWord_3890870
  simp only [CollatzResearch.WordTrace]
  refine ⟨8869480463378123283559379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94607791609366648357966709 8869480463378123283559379)
  ·
    refine ⟨13304220695067184925339069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8869480463378123283559379 13304220695067184925339069)
    ·
      refine ⟨4989082760650194347002151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13304220695067184925339069 4989082760650194347002151)
      ·
        refine ⟨7483624140975291520503227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4989082760650194347002151 7483624140975291520503227)
        ·
          refine ⟨11225436211462937280754841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7483624140975291520503227 11225436211462937280754841)
          ·
            refine ⟨8419077158597202960566131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11225436211462937280754841 8419077158597202960566131)
            ·
              refine ⟨12628615737895804440849197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8419077158597202960566131 12628615737895804440849197)
              ·
                refine ⟨4735730901710926665318449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12628615737895804440849197 4735730901710926665318449)
                ·
                  refine ⟨3551798176283194998988837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4735730901710926665318449 3551798176283194998988837)
                  ·
                    refine ⟨665962158053099062310407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3551798176283194998988837 665962158053099062310407)
                    ·
                      rfl

theorem cell23_3890870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_3890870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3890870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3890870 prefixEnd_3890870 := by exact prefixLift 3890870
  have htrace : WordTrace (prefixWord ++ tailWord_3890870) baseStart_3890870 baseEnd_3890870 := by
    simpa [prefixWord, tailWord_3890870, baseEnd_3890870] using wordTrace_append hprefix tailTrace_3890870
  have hstable : (prefixWord ++ tailWord_3890870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890870).length < 2 ^ (prefixWord ++ tailWord_3890870).sum := by decide
  have hdescent : baseEnd_3890870 < baseStart_3890870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890893 : List Nat := [1, 6, 2, 1, 1, 1, 1, 1, 3, 3, 3]
def baseStart_3890893 : Nat := 118140960795 + 3890893 * 2 ^ 59
def prefixEnd_3890893 : Nat := 4983230072969 + 3 ^ 40 * 3890893 * 2
def baseEnd_3890893 : Nat := 1997898284214350596943615

theorem tailTrace_3890893 : CollatzResearch.WordTrace tailWord_3890893 prefixEnd_3890893 1997898284214350596943615 := by
  unfold tailWord_3890893
  simp only [CollatzResearch.WordTrace]
  refine ⟨141912526292966647465037333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94608350861977764976691555 141912526292966647465037333)
  ·
    refine ⟨6652149669982811599923625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 141912526292966647465037333 6652149669982811599923625)
    ·
      refine ⟨4989112252487108699942719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6652149669982811599923625 4989112252487108699942719)
      ·
        refine ⟨7483668378730663049914079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4989112252487108699942719 7483668378730663049914079)
        ·
          refine ⟨11225502568095994574871119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7483668378730663049914079 11225502568095994574871119)
          ·
            refine ⟨16838253852143991862306679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11225502568095994574871119 16838253852143991862306679)
            ·
              refine ⟨25257380778215987793460019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16838253852143991862306679 25257380778215987793460019)
              ·
                refine ⟨37886071167323981690190029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25257380778215987793460019 37886071167323981690190029)
                ·
                  refine ⟨14207276687746493133821261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37886071167323981690190029 14207276687746493133821261)
                  ·
                    refine ⟨5327728757904934925182973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14207276687746493133821261 5327728757904934925182973)
                    ·
                      refine ⟨1997898284214350596943615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5327728757904934925182973 1997898284214350596943615)
                      ·
                        rfl

theorem cell23_3890893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_3890893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3890893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3890893 prefixEnd_3890893 := by exact prefixLift 3890893
  have htrace : WordTrace (prefixWord ++ tailWord_3890893) baseStart_3890893 baseEnd_3890893 := by
    simpa [prefixWord, tailWord_3890893, baseEnd_3890893] using wordTrace_append hprefix tailTrace_3890893
  have hstable : (prefixWord ++ tailWord_3890893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890893).length < 2 ^ (prefixWord ++ tailWord_3890893).sum := by decide
  have hdescent : baseEnd_3890893 < baseStart_3890893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890916 : List Nat := [2, 3, 1, 1, 1, 3, 1, 2, 3, 4, 2]
def baseStart_3890916 : Nat := 118140960795 + 3890916 * 2 ^ 59
def prefixEnd_3890916 : Nat := 4983230072969 + 3 ^ 40 * 3890916 * 2
def baseEnd_3890916 : Nat := 1997910094269404006956009

theorem tailTrace_3890916 : CollatzResearch.WordTrace tailWord_3890916 prefixEnd_3890916 1997910094269404006956009 := by
  unfold tailWord_3890916
  simp only [CollatzResearch.WordTrace]
  refine ⟨70956682585941661196562301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94608910114588881595416401 70956682585941661196562301)
  ·
    refine ⟨26608755969728122948710863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70956682585941661196562301 26608755969728122948710863)
    ·
      refine ⟨39913133954592184423066295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26608755969728122948710863 39913133954592184423066295)
      ·
        refine ⟨59869700931888276634599443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39913133954592184423066295 59869700931888276634599443)
        ·
          refine ⟨89804551397832414951899165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59869700931888276634599443 89804551397832414951899165)
          ·
            refine ⟨33676706774187155606962187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89804551397832414951899165 33676706774187155606962187)
            ·
              refine ⟨50515060161280733410443281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33676706774187155606962187 50515060161280733410443281)
              ·
                refine ⟨37886295120960550057832461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50515060161280733410443281 37886295120960550057832461)
                ·
                  refine ⟨14207360670360206271687173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37886295120960550057832461 14207360670360206271687173)
                  ·
                    refine ⟨2663880125692538675941345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14207360670360206271687173 2663880125692538675941345)
                    ·
                      refine ⟨1997910094269404006956009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2663880125692538675941345 1997910094269404006956009)
                      ·
                        rfl

theorem cell23_3890916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 3, 4, 2].length) (baseStart_3890916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3890916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3890916 prefixEnd_3890916 := by exact prefixLift 3890916
  have htrace : WordTrace (prefixWord ++ tailWord_3890916) baseStart_3890916 baseEnd_3890916 := by
    simpa [prefixWord, tailWord_3890916, baseEnd_3890916] using wordTrace_append hprefix tailTrace_3890916
  have hstable : (prefixWord ++ tailWord_3890916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890916).length < 2 ^ (prefixWord ++ tailWord_3890916).sum := by decide
  have hdescent : baseEnd_3890916 < baseStart_3890916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890929 : List Nat := [1, 2, 2, 2, 2, 3, 1, 1, 1, 4, 4]
def baseStart_3890929 : Nat := 118140960795 + 3890929 * 2 ^ 59
def prefixEnd_3890929 : Nat := 4983230072969 + 3 ^ 40 * 3890929 * 2
def baseEnd_3890929 : Nat := 1997916769517912456093449

theorem tailTrace_3890929 : CollatzResearch.WordTrace tailWord_3890929 prefixEnd_3890929 1997916769517912456093449 := by
  unfold tailWord_3890929
  simp only [CollatzResearch.WordTrace]
  refine ⟨141913839320836225613347841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94609226213890817075565227 141913839320836225613347841)
  ·
    refine ⟨106435379490627169210010881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141913839320836225613347841 106435379490627169210010881)
    ·
      refine ⟨79826534617970376907508161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106435379490627169210010881 79826534617970376907508161)
      ·
        refine ⟨59869900963477782680631121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79826534617970376907508161 59869900963477782680631121)
        ·
          refine ⟨44902425722608337010473341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59869900963477782680631121 44902425722608337010473341)
          ·
            refine ⟨16838409645978126378927503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44902425722608337010473341 16838409645978126378927503)
            ·
              refine ⟨25257614468967189568391255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16838409645978126378927503 25257614468967189568391255)
              ·
                refine ⟨37886421703450784352586883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25257614468967189568391255 37886421703450784352586883)
                ·
                  refine ⟨56829632555176176528880325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37886421703450784352586883 56829632555176176528880325)
                  ·
                    refine ⟨10655556104095533099165061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56829632555176176528880325 10655556104095533099165061)
                    ·
                      refine ⟨1997916769517912456093449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10655556104095533099165061 1997916769517912456093449)
                      ·
                        rfl

theorem cell23_3890929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_3890929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3890929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3890929 prefixEnd_3890929 := by exact prefixLift 3890929
  have htrace : WordTrace (prefixWord ++ tailWord_3890929) baseStart_3890929 baseEnd_3890929 := by
    simpa [prefixWord, tailWord_3890929, baseEnd_3890929] using wordTrace_append hprefix tailTrace_3890929
  have hstable : (prefixWord ++ tailWord_3890929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890929).length < 2 ^ (prefixWord ++ tailWord_3890929).sum := by decide
  have hdescent : baseEnd_3890929 < baseStart_3890929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890946 : List Nat := [3, 4, 1, 1, 1, 1, 1, 2, 1, 4, 4]
def baseStart_3890946 : Nat := 118140960795 + 3890946 * 2 ^ 59
def prefixEnd_3890946 : Nat := 4983230072969 + 3 ^ 40 * 3890946 * 2
def baseEnd_3890946 : Nat := 1997925498689038889580871

theorem tailTrace_3890946 : CollatzResearch.WordTrace tailWord_3890946 prefixEnd_3890946 1997925498689038889580871 := by
  unfold tailWord_3890946
  simp only [CollatzResearch.WordTrace]
  refine ⟨35478614840443659379179173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94609639574516425011144461 35478614840443659379179173)
  ·
    refine ⟨6652240282583186133596095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35478614840443659379179173 6652240282583186133596095)
    ·
      refine ⟨9978360423874779200394143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6652240282583186133596095 9978360423874779200394143)
      ·
        refine ⟨14967540635812168800591215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9978360423874779200394143 14967540635812168800591215)
        ·
          refine ⟨22451310953718253200886823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14967540635812168800591215 22451310953718253200886823)
          ·
            refine ⟨33676966430577379801330235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22451310953718253200886823 33676966430577379801330235)
            ·
              refine ⟨50515449645866069701995353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33676966430577379801330235 50515449645866069701995353)
              ·
                refine ⟨37886587234399552276496515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50515449645866069701995353 37886587234399552276496515)
                ·
                  refine ⟨56829880851599328414744773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37886587234399552276496515 56829880851599328414744773)
                  ·
                    refine ⟨10655602659674874077764645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56829880851599328414744773 10655602659674874077764645)
                    ·
                      refine ⟨1997925498689038889580871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10655602659674874077764645 1997925498689038889580871)
                      ·
                        rfl

theorem cell23_3890946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_3890946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3890946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3890946 prefixEnd_3890946 := by exact prefixLift 3890946
  have htrace : WordTrace (prefixWord ++ tailWord_3890946) baseStart_3890946 baseEnd_3890946 := by
    simpa [prefixWord, tailWord_3890946, baseEnd_3890946] using wordTrace_append hprefix tailTrace_3890946
  have hstable : (prefixWord ++ tailWord_3890946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890946).length < 2 ^ (prefixWord ++ tailWord_3890946).sum := by decide
  have hdescent : baseEnd_3890946 < baseStart_3890946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890956 : List Nat := [2, 2, 1, 2, 2, 1, 3, 5, 5]
def baseStart_3890956 : Nat := 118140960795 + 3890956 * 2 ^ 59
def prefixEnd_3890956 : Nat := 4983230072969 + 3 ^ 40 * 3890956 * 2
def baseEnd_3890956 : Nat := 221992292610620427828425

theorem tailTrace_3890956 : CollatzResearch.WordTrace tailWord_3890956 prefixEnd_3890956 221992292610620427828425 := by
  unfold tailWord_3890956
  simp only [CollatzResearch.WordTrace]
  refine ⟨70957412045869204612290361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94609882727825606149720481 70957412045869204612290361)
  ·
    refine ⟨53218059034401903459217771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70957412045869204612290361 53218059034401903459217771)
    ·
      refine ⟨79827088551602855188826657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53218059034401903459217771 79827088551602855188826657)
      ·
        refine ⟨59870316413702141391619993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79827088551602855188826657 59870316413702141391619993)
        ·
          refine ⟨44902737310276606043714995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59870316413702141391619993 44902737310276606043714995)
          ·
            refine ⟨67354105965414909065572493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44902737310276606043714995 67354105965414909065572493)
            ·
              refine ⟨25257789737030590899589685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67354105965414909065572493 25257789737030590899589685)
              ·
                refine ⟨2367917787846617896836533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25257789737030590899589685 2367917787846617896836533)
                ·
                  refine ⟨221992292610620427828425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2367917787846617896836533 221992292610620427828425)
                  ·
                    rfl

theorem cell23_3890956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 5, 5].length) (baseStart_3890956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3890956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3890956 prefixEnd_3890956 := by exact prefixLift 3890956
  have htrace : WordTrace (prefixWord ++ tailWord_3890956) baseStart_3890956 baseEnd_3890956 := by
    simpa [prefixWord, tailWord_3890956, baseEnd_3890956] using wordTrace_append hprefix tailTrace_3890956
  have hstable : (prefixWord ++ tailWord_3890956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890956).length < 2 ^ (prefixWord ++ tailWord_3890956).sum := by decide
  have hdescent : baseEnd_3890956 < baseStart_3890956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890967 : List Nat := [1, 1, 3, 4, 2, 3, 1, 2, 2, 2, 2]
def baseStart_3890967 : Nat := 118140960795 + 3890967 * 2 ^ 59
def prefixEnd_3890967 : Nat := 4983230072969 + 3 ^ 40 * 3890967 * 2
def baseEnd_3890967 : Nat := 1997936281782783307418275

theorem tailTrace_3890967 : CollatzResearch.WordTrace tailWord_3890967 prefixEnd_3890967 1997936281782783307418275 := by
  unfold tailWord_3890967
  simp only [CollatzResearch.WordTrace]
  refine ⟨141915225294698558103231155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94610150196465705402154103 141915225294698558103231155)
  ·
    refine ⟨212872837942047837154846733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141915225294698558103231155 212872837942047837154846733)
    ·
      refine ⟨79827314228267938933067525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212872837942047837154846733 79827314228267938933067525)
      ·
        refine ⟨14967621417800238549950161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79827314228267938933067525 14967621417800238549950161)
        ·
          refine ⟨11225716063350178912462621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14967621417800238549950161 11225716063350178912462621)
          ·
            refine ⟨4209643523756317092173483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11225716063350178912462621 4209643523756317092173483)
            ·
              refine ⟨6314465285634475638260225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4209643523756317092173483 6314465285634475638260225)
              ·
                refine ⟨4735848964225856728695169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6314465285634475638260225 4735848964225856728695169)
                ·
                  refine ⟨3551886723169392546521377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4735848964225856728695169 3551886723169392546521377)
                  ·
                    refine ⟨2663915042377044409891033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3551886723169392546521377 2663915042377044409891033)
                    ·
                      refine ⟨1997936281782783307418275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2663915042377044409891033 1997936281782783307418275)
                      ·
                        rfl

theorem cell23_3890967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_3890967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3890967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3890967 prefixEnd_3890967 := by exact prefixLift 3890967
  have htrace : WordTrace (prefixWord ++ tailWord_3890967) baseStart_3890967 baseEnd_3890967 := by
    simpa [prefixWord, tailWord_3890967, baseEnd_3890967] using wordTrace_append hprefix tailTrace_3890967
  have hstable : (prefixWord ++ tailWord_3890967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890967).length < 2 ^ (prefixWord ++ tailWord_3890967).sum := by decide
  have hdescent : baseEnd_3890967 < baseStart_3890967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890979 : List Nat := [1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 5]
def baseStart_3890979 : Nat := 118140960795 + 3890979 * 2 ^ 59
def prefixEnd_3890979 : Nat := 4983230072969 + 3 ^ 40 * 3890979 * 2
def baseEnd_3890979 : Nat := 1997942443550637260468219

theorem tailTrace_3890979 : CollatzResearch.WordTrace tailWord_3890979 prefixEnd_3890979 1997942443550637260468219 := by
  unfold tailWord_3890979
  simp only [CollatzResearch.WordTrace]
  refine ⟨141915662970655084152667991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94610441980436722768445327 141915662970655084152667991)
  ·
    refine ⟨212873494455982626229001987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141915662970655084152667991 212873494455982626229001987)
    ·
      refine ⟨319310241683973939343502981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212873494455982626229001987 319310241683973939343502981)
      ·
        refine ⟨59870670315745113626906809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 319310241683973939343502981 59870670315745113626906809)
        ·
          refine ⟨44903002736808835220180107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59870670315745113626906809 44903002736808835220180107)
          ·
            refine ⟨67354504105213252830270161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44903002736808835220180107 67354504105213252830270161)
            ·
              refine ⟨50515878078909939622702621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67354504105213252830270161 50515878078909939622702621)
              ·
                refine ⟨18943454279591227358513483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50515878078909939622702621 18943454279591227358513483)
                ·
                  refine ⟨28415181419386841037770225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18943454279591227358513483 28415181419386841037770225)
                  ·
                    refine ⟨21311386064540130778327669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28415181419386841037770225 21311386064540130778327669)
                    ·
                      refine ⟨1997942443550637260468219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21311386064540130778327669 1997942443550637260468219)
                      ·
                        rfl

theorem cell23_3890979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_3890979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3890979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3890979 prefixEnd_3890979 := by exact prefixLift 3890979
  have htrace : WordTrace (prefixWord ++ tailWord_3890979) baseStart_3890979 baseEnd_3890979 := by
    simpa [prefixWord, tailWord_3890979, baseEnd_3890979] using wordTrace_append hprefix tailTrace_3890979
  have hstable : (prefixWord ++ tailWord_3890979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890979).length < 2 ^ (prefixWord ++ tailWord_3890979).sum := by decide
  have hdescent : baseEnd_3890979 < baseStart_3890979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891049 : List Nat := [1, 2, 1, 1, 1, 3, 1, 4, 1, 2, 6]
def baseStart_3891049 : Nat := 118140960795 + 3891049 * 2 ^ 59
def prefixEnd_3891049 : Nat := 4983230072969 + 3 ^ 40 * 3891049 * 2
def baseEnd_3891049 : Nat := 1997978387196451986592897

theorem tailTrace_3891049 : CollatzResearch.WordTrace tailWord_3891049 prefixEnd_3891049 1997978387196451986592897 := by
  unfold tailWord_3891049
  simp only [CollatzResearch.WordTrace]
  refine ⟨141918216080401486107716201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94612144053600990738477467 141918216080401486107716201)
  ·
    refine ⟨106438662060301114580787151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141918216080401486107716201 106438662060301114580787151)
    ·
      refine ⟨159657993090451671871180727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106438662060301114580787151 159657993090451671871180727)
      ·
        refine ⟨239486989635677507806771091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159657993090451671871180727 239486989635677507806771091)
        ·
          refine ⟨359230484453516261710156637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239486989635677507806771091 359230484453516261710156637)
          ·
            refine ⟨134711431670068598141308739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 359230484453516261710156637 134711431670068598141308739)
            ·
              refine ⟨202067147505102897211963109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134711431670068598141308739 202067147505102897211963109)
              ·
                refine ⟨37887590157206793227243083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 202067147505102897211963109 37887590157206793227243083)
                ·
                  refine ⟨56831385235810189840864625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37887590157206793227243083 56831385235810189840864625)
                  ·
                    refine ⟨42623538926857642380648469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56831385235810189840864625 42623538926857642380648469)
                    ·
                      refine ⟨1997978387196451986592897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42623538926857642380648469 1997978387196451986592897)
                      ·
                        rfl

theorem cell23_3891049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 2, 6].length) (baseStart_3891049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3891049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3891049 prefixEnd_3891049 := by exact prefixLift 3891049
  have htrace : WordTrace (prefixWord ++ tailWord_3891049) baseStart_3891049 baseEnd_3891049 := by
    simpa [prefixWord, tailWord_3891049, baseEnd_3891049] using wordTrace_append hprefix tailTrace_3891049
  have hstable : (prefixWord ++ tailWord_3891049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891049).length < 2 ^ (prefixWord ++ tailWord_3891049).sum := by decide
  have hdescent : baseEnd_3891049 < baseStart_3891049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891147 : List Nat := [1, 1, 1, 1, 3, 4, 1, 6, 1, 2, 2]
def baseStart_3891147 : Nat := 118140960795 + 3891147 * 2 ^ 59
def prefixEnd_3891147 : Nat := 4983230072969 + 3 ^ 40 * 3891147 * 2
def baseEnd_3891147 : Nat := 1998028708300592603167447

theorem tailTrace_3891147 : CollatzResearch.WordTrace tailWord_3891147 prefixEnd_3891147 1998028708300592603167447 := by
  unfold tailWord_3891147
  simp only [CollatzResearch.WordTrace]
  refine ⟨141921790434046448844783695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94614526956030965896522463 141921790434046448844783695)
  ·
    refine ⟨212882685651069673267175543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141921790434046448844783695 212882685651069673267175543)
    ·
      refine ⟨319324028476604509900763315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212882685651069673267175543 319324028476604509900763315)
      ·
        refine ⟨478986042714906764851144973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319324028476604509900763315 478986042714906764851144973)
        ·
          refine ⟨179619766018090036819179365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 478986042714906764851144973 179619766018090036819179365)
          ·
            refine ⟨33678706128391881903596131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179619766018090036819179365 33678706128391881903596131)
            ·
              refine ⟨50518059192587822855394197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33678706128391881903596131 50518059192587822855394197)
              ·
                refine ⟨2368034024652554196346603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50518059192587822855394197 2368034024652554196346603)
                ·
                  refine ⟨3552051036978831294519905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2368034024652554196346603 3552051036978831294519905)
                  ·
                    refine ⟨2664038277734123470889929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3552051036978831294519905 2664038277734123470889929)
                    ·
                      refine ⟨1998028708300592603167447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2664038277734123470889929 1998028708300592603167447)
                      ·
                        rfl

theorem cell23_3891147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 6, 1, 2, 2].length) (baseStart_3891147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3891147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3891147 prefixEnd_3891147 := by exact prefixLift 3891147
  have htrace : WordTrace (prefixWord ++ tailWord_3891147) baseStart_3891147 baseEnd_3891147 := by
    simpa [prefixWord, tailWord_3891147, baseEnd_3891147] using wordTrace_append hprefix tailTrace_3891147
  have hstable : (prefixWord ++ tailWord_3891147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891147).length < 2 ^ (prefixWord ++ tailWord_3891147).sum := by decide
  have hdescent : baseEnd_3891147 < baseStart_3891147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891157 : List Nat := [1, 3, 2, 3, 2, 2, 3, 1, 2, 4]
def baseStart_3891157 : Nat := 118140960795 + 3891157 * 2 ^ 59
def prefixEnd_3891157 : Nat := 4983230072969 + 3 ^ 40 * 3891157 * 2
def baseEnd_3891157 : Nat := 666011281035712521347467

theorem tailTrace_3891157 : CollatzResearch.WordTrace tailWord_3891157 prefixEnd_3891157 666011281035712521347467 := by
  unfold tailWord_3891157
  simp only [CollatzResearch.WordTrace]
  refine ⟨141922155164010220552647725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94614770109340147035098483 141922155164010220552647725)
  ·
    refine ⟨53220808186503832707242897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141922155164010220552647725 53220808186503832707242897)
    ·
      refine ⟨39915606139877874530432173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53220808186503832707242897 39915606139877874530432173)
      ·
        refine ⟨14968352302454202948912065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39915606139877874530432173 14968352302454202948912065)
        ·
          refine ⟨11226264226840652211684049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14968352302454202948912065 11226264226840652211684049)
          ·
            refine ⟨8419698170130489158763037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11226264226840652211684049 8419698170130489158763037)
            ·
              refine ⟨3157386813798933434536139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8419698170130489158763037 3157386813798933434536139)
              ·
                refine ⟨4736080220698400151804209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3157386813798933434536139 4736080220698400151804209)
                ·
                  refine ⟨3552060165523800113853157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4736080220698400151804209 3552060165523800113853157)
                  ·
                    refine ⟨666011281035712521347467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3552060165523800113853157 666011281035712521347467)
                    ·
                      rfl

theorem cell23_3891157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 1, 2, 4].length) (baseStart_3891157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3891157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3891157 prefixEnd_3891157 := by exact prefixLift 3891157
  have htrace : WordTrace (prefixWord ++ tailWord_3891157) baseStart_3891157 baseEnd_3891157 := by
    simpa [prefixWord, tailWord_3891157, baseEnd_3891157] using wordTrace_append hprefix tailTrace_3891157
  have hstable : (prefixWord ++ tailWord_3891157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891157).length < 2 ^ (prefixWord ++ tailWord_3891157).sum := by decide
  have hdescent : baseEnd_3891157 < baseStart_3891157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891170 : List Nat := [3, 3, 3, 1, 2, 1, 1, 9]
def baseStart_3891170 : Nat := 118140960795 + 3891170 * 2 ^ 59
def prefixEnd_3891170 : Nat := 4983230072969 + 3 ^ 40 * 3891170 * 2
def baseEnd_3891170 : Nat := 74001500679838741228883

theorem tailTrace_3891170 : CollatzResearch.WordTrace tailWord_3891170 prefixEnd_3891170 74001500679838741228883 := by
  unfold tailWord_3891170
  simp only [CollatzResearch.WordTrace]
  refine ⟨35480657328240780943217741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94615086208642082515247309 35480657328240780943217741)
  ·
    refine ⟨13305246498090292853706653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35480657328240780943217741 13305246498090292853706653)
    ·
      refine ⟨4989467436783859820139995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13305246498090292853706653 4989467436783859820139995)
      ·
        refine ⟨7484201155175789730209993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4989467436783859820139995 7484201155175789730209993)
        ·
          refine ⟨5613150866381842297657495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7484201155175789730209993 5613150866381842297657495)
          ·
            refine ⟨8419726299572763446486243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5613150866381842297657495 8419726299572763446486243)
            ·
              refine ⟨12629589449359145169729365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8419726299572763446486243 12629589449359145169729365)
              ·
                refine ⟨74001500679838741228883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12629589449359145169729365 74001500679838741228883)
                ·
                  rfl

theorem cell23_3891170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 9].length) (baseStart_3891170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3891170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3891170 prefixEnd_3891170 := by exact prefixLift 3891170
  have htrace : WordTrace (prefixWord ++ tailWord_3891170) baseStart_3891170 baseEnd_3891170 := by
    simpa [prefixWord, tailWord_3891170, baseEnd_3891170] using wordTrace_append hprefix tailTrace_3891170
  have hstable : (prefixWord ++ tailWord_3891170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891170).length < 2 ^ (prefixWord ++ tailWord_3891170).sum := by decide
  have hdescent : baseEnd_3891170 < baseStart_3891170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891198 : List Nat := [4, 2, 2, 2, 1, 2, 3, 2, 1, 2, 2]
def baseStart_3891198 : Nat := 118140960795 + 3891198 * 2 ^ 59
def prefixEnd_3891198 : Nat := 4983230072969 + 3 ^ 40 * 3891198 * 2
def baseEnd_3891198 : Nat := 1998054895813971903629713

theorem tailTrace_3891198 : CollatzResearch.WordTrace tailWord_3891198 prefixEnd_3891198 1998054895813971903629713 := by
  unfold tailWord_3891198
  simp only [CollatzResearch.WordTrace]
  refine ⟨17740456319607710569361281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94615767037907789703260165 17740456319607710569361281)
  ·
    refine ⟨13305342239705782927020961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17740456319607710569361281 13305342239705782927020961)
    ·
      refine ⟨9979006679779337195265721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13305342239705782927020961 9979006679779337195265721)
      ·
        refine ⟨7484255009834502896449291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9979006679779337195265721 7484255009834502896449291)
        ·
          refine ⟨11226382514751754344673937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7484255009834502896449291 11226382514751754344673937)
          ·
            refine ⟨8419786886063815758505453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11226382514751754344673937 8419786886063815758505453)
            ·
              refine ⟨3157420082273930909439545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8419786886063815758505453 3157420082273930909439545)
              ·
                refine ⟨2368065061705448182079659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3157420082273930909439545 2368065061705448182079659)
                ·
                  refine ⟨3552097592558172273119489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2368065061705448182079659 3552097592558172273119489)
                  ·
                    refine ⟨2664073194418629204839617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3552097592558172273119489 2664073194418629204839617)
                    ·
                      refine ⟨1998054895813971903629713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2664073194418629204839617 1998054895813971903629713)
                      ·
                        rfl

theorem cell23_3891198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_3891198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3891198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3891198 prefixEnd_3891198 := by exact prefixLift 3891198
  have htrace : WordTrace (prefixWord ++ tailWord_3891198) baseStart_3891198 baseEnd_3891198 := by
    simpa [prefixWord, tailWord_3891198, baseEnd_3891198] using wordTrace_append hprefix tailTrace_3891198
  have hstable : (prefixWord ++ tailWord_3891198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891198).length < 2 ^ (prefixWord ++ tailWord_3891198).sum := by decide
  have hdescent : baseEnd_3891198 < baseStart_3891198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891260 : List Nat := [2, 2, 2, 2, 2, 1, 3, 4, 5]
def baseStart_3891260 : Nat := 118140960795 + 3891260 * 2 ^ 59
def prefixEnd_3891260 : Nat := 4983230072969 + 3 ^ 40 * 3891260 * 2
def baseEnd_3891260 : Nat := 222009636846061184561603

theorem tailTrace_3891260 : CollatzResearch.WordTrace tailWord_3891260 prefixEnd_3891260 222009636846061184561603 := by
  unfold tailWord_3891260
  simp only [CollatzResearch.WordTrace]
  refine ⟨70962955941318534571823617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94617274588424712762431489 70962955941318534571823617)
  ·
    refine ⟨53222216955988900928867713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70962955941318534571823617 53222216955988900928867713)
    ·
      refine ⟨39916662716991675696650785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53222216955988900928867713 39916662716991675696650785)
      ·
        refine ⟨29937497037743756772488089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39916662716991675696650785 29937497037743756772488089)
        ·
          refine ⟨22453122778307817579366067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29937497037743756772488089 22453122778307817579366067)
          ·
            refine ⟨33679684167461726369049101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22453122778307817579366067 33679684167461726369049101)
            ·
              refine ⟨12629881562798147388393413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33679684167461726369049101 12629881562798147388393413)
              ·
                refine ⟨2368102793024652635323765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12629881562798147388393413 2368102793024652635323765)
                ·
                  refine ⟨222009636846061184561603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2368102793024652635323765 222009636846061184561603)
                  ·
                    rfl

theorem cell23_3891260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 4, 5].length) (baseStart_3891260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3891260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3891260 prefixEnd_3891260 := by exact prefixLift 3891260
  have htrace : WordTrace (prefixWord ++ tailWord_3891260) baseStart_3891260 baseEnd_3891260 := by
    simpa [prefixWord, tailWord_3891260, baseEnd_3891260] using wordTrace_append hprefix tailTrace_3891260
  have hstable : (prefixWord ++ tailWord_3891260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891260).length < 2 ^ (prefixWord ++ tailWord_3891260).sum := by decide
  have hdescent : baseEnd_3891260 < baseStart_3891260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891310 : List Nat := [4, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4]
def baseStart_3891310 : Nat := 118140960795 + 3891310 * 2 ^ 59
def prefixEnd_3891310 : Nat := 4983230072969 + 3 ^ 40 * 3891310 * 2
def baseEnd_3891310 : Nat := 1998112405647275465429197

theorem tailTrace_3891310 : CollatzResearch.WordTrace tailWord_3891310 prefixEnd_3891310 1998112405647275465429197 := by
  unfold tailWord_3891310
  simp only [CollatzResearch.WordTrace]
  refine ⟨17740966941556990960370923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94618490354970618455311589 17740966941556990960370923)
  ·
    refine ⟨26611450412335486440556385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17740966941556990960370923 26611450412335486440556385)
    ·
      refine ⟨19958587809251614830417289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26611450412335486440556385 19958587809251614830417289)
      ·
        refine ⟨14968940856938711122812967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19958587809251614830417289 14968940856938711122812967)
        ·
          refine ⟨22453411285408066684219451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14968940856938711122812967 22453411285408066684219451)
          ·
            refine ⟨33680116928112100026329177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22453411285408066684219451 33680116928112100026329177)
            ·
              refine ⟨25260087696084075019746883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33680116928112100026329177 25260087696084075019746883)
              ·
                refine ⟨37890131544126112529620325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25260087696084075019746883 37890131544126112529620325)
                ·
                  refine ⟨7104399664523646099303811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37890131544126112529620325 7104399664523646099303811)
                  ·
                    refine ⟨10656599496785469148955717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7104399664523646099303811 10656599496785469148955717)
                    ·
                      refine ⟨1998112405647275465429197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10656599496785469148955717 1998112405647275465429197)
                      ·
                        rfl

theorem cell23_3891310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_3891310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3891310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3891310 prefixEnd_3891310 := by exact prefixLift 3891310
  have htrace : WordTrace (prefixWord ++ tailWord_3891310) baseStart_3891310 baseEnd_3891310 := by
    simpa [prefixWord, tailWord_3891310, baseEnd_3891310] using wordTrace_append hprefix tailTrace_3891310
  have hstable : (prefixWord ++ tailWord_3891310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891310).length < 2 ^ (prefixWord ++ tailWord_3891310).sum := by decide
  have hdescent : baseEnd_3891310 < baseStart_3891310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891363 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 7, 5]
def baseStart_3891363 : Nat := 118140960795 + 3891363 * 2 ^ 59
def prefixEnd_3891363 : Nat := 4983230072969 + 3 ^ 40 * 3891363 * 2
def baseEnd_3891363 : Nat := 666046540040654586022151

theorem tailTrace_3891363 : CollatzResearch.WordTrace tailWord_3891363 prefixEnd_3891363 666046540040654586022151 := by
  unfold tailWord_3891363
  simp only [CollatzResearch.WordTrace]
  refine ⟨141929668601263917734646743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94619779067509278489764495 141929668601263917734646743)
  ·
    refine ⟨212894502901895876601970115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141929668601263917734646743 212894502901895876601970115)
    ·
      refine ⟨319341754352843814902955173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212894502901895876601970115 319341754352843814902955173)
      ·
        refine ⟨59876578941158215294304095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 319341754352843814902955173 59876578941158215294304095)
        ·
          refine ⟨89814868411737322941456143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59876578941158215294304095 89814868411737322941456143)
          ·
            refine ⟨134722302617605984412184215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89814868411737322941456143 134722302617605984412184215)
            ·
              refine ⟨202083453926408976618276323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134722302617605984412184215 202083453926408976618276323)
              ·
                refine ⟨303125180889613464927414485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202083453926408976618276323 303125180889613464927414485)
                ·
                  refine ⟨7104496427100315584236277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 303125180889613464927414485 7104496427100315584236277)
                  ·
                    refine ⟨666046540040654586022151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7104496427100315584236277 666046540040654586022151)
                    ·
                      rfl

theorem cell23_3891363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 7, 5].length) (baseStart_3891363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3891363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3891363 prefixEnd_3891363 := by exact prefixLift 3891363
  have htrace : WordTrace (prefixWord ++ tailWord_3891363) baseStart_3891363 baseEnd_3891363 := by
    simpa [prefixWord, tailWord_3891363, baseEnd_3891363] using wordTrace_append hprefix tailTrace_3891363
  have hstable : (prefixWord ++ tailWord_3891363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891363).length < 2 ^ (prefixWord ++ tailWord_3891363).sum := by decide
  have hdescent : baseEnd_3891363 < baseStart_3891363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891410 : List Nat := [3, 2, 2, 2, 1, 2, 1, 1, 3, 6]
def baseStart_3891410 : Nat := 118140960795 + 3891410 * 2 ^ 59
def prefixEnd_3891410 : Nat := 4983230072969 + 3 ^ 40 * 3891410 * 2
def baseEnd_3891410 : Nat := 666054584570908358059579

theorem tailTrace_3891410 : CollatzResearch.WordTrace tailWord_3891410 prefixEnd_3891410 666054584570908358059579 := by
  unfold tailWord_3891410
  simp only [CollatzResearch.WordTrace]
  refine ⟨35482845708023411190401921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94620921888062429841071789 35482845708023411190401921)
  ·
    refine ⟨26612134281017558392801441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35482845708023411190401921 26612134281017558392801441)
    ·
      refine ⟨19959100710763168794601081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26612134281017558392801441 19959100710763168794601081)
      ·
        refine ⟨14969325533072376595950811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19959100710763168794601081 14969325533072376595950811)
        ·
          refine ⟨22453988299608564893926217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14969325533072376595950811 22453988299608564893926217)
          ·
            refine ⟨16840491224706423670444663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22453988299608564893926217 16840491224706423670444663)
            ·
              refine ⟨25260736837059635505666995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16840491224706423670444663 25260736837059635505666995)
              ·
                refine ⟨37891105255589453258500493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25260736837059635505666995 37891105255589453258500493)
                ·
                  refine ⟨14209164470846044971937685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37891105255589453258500493 14209164470846044971937685)
                  ·
                    refine ⟨666054584570908358059579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14209164470846044971937685 666054584570908358059579)
                    ·
                      rfl

theorem cell23_3891410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_3891410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3891410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3891410 prefixEnd_3891410 := by exact prefixLift 3891410
  have htrace : WordTrace (prefixWord ++ tailWord_3891410) baseStart_3891410 baseEnd_3891410 := by
    simpa [prefixWord, tailWord_3891410, baseEnd_3891410] using wordTrace_append hprefix tailTrace_3891410
  have hstable : (prefixWord ++ tailWord_3891410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891410).length < 2 ^ (prefixWord ++ tailWord_3891410).sum := by decide
  have hdescent : baseEnd_3891410 < baseStart_3891410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891434 : List Nat := [3, 1, 3, 1, 1, 2, 2, 3, 3, 2, 2]
def baseStart_3891434 : Nat := 118140960795 + 3891434 * 2 ^ 59
def prefixEnd_3891434 : Nat := 4983230072969 + 3 ^ 40 * 3891434 * 2
def baseEnd_3891434 : Nat := 1998176077248432980278627

theorem tailTrace_3891434 : CollatzResearch.WordTrace tailWord_3891434 prefixEnd_3891434 1998176077248432980278627 := by
  unfold tailWord_3891434
  simp only [CollatzResearch.WordTrace]
  refine ⟨35483064546001674215120339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94621505456004464573654237 35483064546001674215120339)
  ·
    refine ⟨53224596819002511322680509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35483064546001674215120339 53224596819002511322680509)
    ·
      refine ⟨19959223807125941746005191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53224596819002511322680509 19959223807125941746005191)
      ·
        refine ⟨29938835710688912619007787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19959223807125941746005191 29938835710688912619007787)
        ·
          refine ⟨44908253566033368928511681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29938835710688912619007787 44908253566033368928511681)
          ·
            refine ⟨33681190174525026696383761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44908253566033368928511681 33681190174525026696383761)
            ·
              refine ⟨25260892630893770022287821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33681190174525026696383761 25260892630893770022287821)
              ·
                refine ⟨9472834736585163758357933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25260892630893770022287821 9472834736585163758357933)
                ·
                  refine ⟨3552313026219436409384225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9472834736585163758357933 3552313026219436409384225)
                  ·
                    refine ⟨2664234769664577307038169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3552313026219436409384225 2664234769664577307038169)
                    ·
                      refine ⟨1998176077248432980278627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2664234769664577307038169 1998176077248432980278627)
                      ·
                        rfl

theorem cell23_3891434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 3, 2, 2].length) (baseStart_3891434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3891434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3891434 prefixEnd_3891434 := by exact prefixLift 3891434
  have htrace : WordTrace (prefixWord ++ tailWord_3891434) baseStart_3891434 baseEnd_3891434 := by
    simpa [prefixWord, tailWord_3891434, baseEnd_3891434] using wordTrace_append hprefix tailTrace_3891434
  have hstable : (prefixWord ++ tailWord_3891434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891434).length < 2 ^ (prefixWord ++ tailWord_3891434).sum := by decide
  have hdescent : baseEnd_3891434 < baseStart_3891434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891454 : List Nat := [4, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3]
def baseStart_3891454 : Nat := 118140960795 + 3891454 * 2 ^ 59
def prefixEnd_3891454 : Nat := 4983230072969 + 3 ^ 40 * 3891454 * 2
def baseEnd_3891454 : Nat := 1998186346861522902028535

theorem tailTrace_3891454 : CollatzResearch.WordTrace tailWord_3891454 prefixEnd_3891454 1998186346861522902028535 := by
  unfold tailWord_3891454
  simp only [CollatzResearch.WordTrace]
  refine ⟨17741623455491780034526177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94621991762622826850806277 17741623455491780034526177)
  ·
    refine ⟨13306217591618835025894633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17741623455491780034526177 13306217591618835025894633)
    ·
      refine ⟨9979663193714126269420975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13306217591618835025894633 9979663193714126269420975)
      ·
        refine ⟨14969494790571189404131463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9979663193714126269420975 14969494790571189404131463)
        ·
          refine ⟨22454242185856784106197195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14969494790571189404131463 22454242185856784106197195)
          ·
            refine ⟨33681363278785176159295793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22454242185856784106197195 33681363278785176159295793)
            ·
              refine ⟨25261022459088882119471845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33681363278785176159295793 25261022459088882119471845)
              ·
                refine ⟨4736441711079165397400971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25261022459088882119471845 4736441711079165397400971)
                ·
                  refine ⟨7104662566618748096101457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4736441711079165397400971 7104662566618748096101457)
                  ·
                    refine ⟨5328496924964061072076093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7104662566618748096101457 5328496924964061072076093)
                    ·
                      refine ⟨1998186346861522902028535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5328496924964061072076093 1998186346861522902028535)
                      ·
                        rfl

theorem cell23_3891454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_3891454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3891454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3891454 prefixEnd_3891454 := by exact prefixLift 3891454
  have htrace : WordTrace (prefixWord ++ tailWord_3891454) baseStart_3891454 baseEnd_3891454 := by
    simpa [prefixWord, tailWord_3891454, baseEnd_3891454] using wordTrace_append hprefix tailTrace_3891454
  have hstable : (prefixWord ++ tailWord_3891454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891454).length < 2 ^ (prefixWord ++ tailWord_3891454).sum := by decide
  have hdescent : baseEnd_3891454 < baseStart_3891454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891467 : List Nat := [1, 1, 1, 1, 5, 2, 2, 2, 4, 1, 3]
def baseStart_3891467 : Nat := 118140960795 + 3891467 * 2 ^ 59
def prefixEnd_3891467 : Nat := 4983230072969 + 3 ^ 40 * 3891467 * 2
def baseEnd_3891467 : Nat := 1998193022110031351165975

theorem tailTrace_3891467 : CollatzResearch.WordTrace tailWord_3891467 prefixEnd_3891467 1998193022110031351165975 := by
  unfold tailWord_3891467
  simp only [CollatzResearch.WordTrace]
  refine ⟨141933461792887143496432655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94622307861924762330955103 141933461792887143496432655)
  ·
    refine ⟨212900192689330715244648983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141933461792887143496432655 212900192689330715244648983)
    ·
      refine ⟨319350289033996072866973475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212900192689330715244648983 319350289033996072866973475)
      ·
        refine ⟨479025433550994109300460213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319350289033996072866973475 479025433550994109300460213)
        ·
          refine ⟨44908634395405697746918145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 479025433550994109300460213 44908634395405697746918145)
          ·
            refine ⟨33681475796554273310188609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44908634395405697746918145 33681475796554273310188609)
            ·
              refine ⟨25261106847415704982641457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33681475796554273310188609 25261106847415704982641457)
              ·
                refine ⟨18945830135561778736981093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25261106847415704982641457 18945830135561778736981093)
                ·
                  refine ⟨3552343150417833513183955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18945830135561778736981093 3552343150417833513183955)
                  ·
                    refine ⟨5328514725626750269775933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3552343150417833513183955 5328514725626750269775933)
                    ·
                      refine ⟨1998193022110031351165975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5328514725626750269775933 1998193022110031351165975)
                      ·
                        rfl

theorem cell23_3891467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 4, 1, 3].length) (baseStart_3891467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3891467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3891467 prefixEnd_3891467 := by exact prefixLift 3891467
  have htrace : WordTrace (prefixWord ++ tailWord_3891467) baseStart_3891467 baseEnd_3891467 := by
    simpa [prefixWord, tailWord_3891467, baseEnd_3891467] using wordTrace_append hprefix tailTrace_3891467
  have hstable : (prefixWord ++ tailWord_3891467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891467).length < 2 ^ (prefixWord ++ tailWord_3891467).sum := by decide
  have hdescent : baseEnd_3891467 < baseStart_3891467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891495 : List Nat := [1, 1, 8, 1, 1, 1, 3, 1, 2, 4]
def baseStart_3891495 : Nat := 118140960795 + 3891495 * 2 ^ 59
def prefixEnd_3891495 : Nat := 4983230072969 + 3 ^ 40 * 3891495 * 2
def baseEnd_3891495 : Nat := 666069133189452413871949

theorem tailTrace_3891495 : CollatzResearch.WordTrace tailWord_3891495 prefixEnd_3891495 666069133189452413871949 := by
  unfold tailWord_3891495
  simp only [CollatzResearch.WordTrace]
  refine ⟨141934483036785704278451939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94622988691190469518967959 141934483036785704278451939)
  ·
    refine ⟨212901724555178556417677909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141934483036785704278451939 212901724555178556417677909)
    ·
      refine ⟨2494942084630998708019663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 212901724555178556417677909 2494942084630998708019663)
      ·
        refine ⟨3742413126946498062029495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2494942084630998708019663 3742413126946498062029495)
        ·
          refine ⟨5613619690419747093044243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3742413126946498062029495 5613619690419747093044243)
          ·
            refine ⟨8420429535629620639566365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5613619690419747093044243 8420429535629620639566365)
            ·
              refine ⟨3157661075861107739837387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8420429535629620639566365 3157661075861107739837387)
              ·
                refine ⟨4736491613791661609756081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3157661075861107739837387 4736491613791661609756081)
                ·
                  refine ⟨3552368710343746207317061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4736491613791661609756081 3552368710343746207317061)
                  ·
                    refine ⟨666069133189452413871949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3552368710343746207317061 666069133189452413871949)
                    ·
                      rfl

theorem cell23_3891495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_3891495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3891495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3891495 prefixEnd_3891495 := by exact prefixLift 3891495
  have htrace : WordTrace (prefixWord ++ tailWord_3891495) baseStart_3891495 baseEnd_3891495 := by
    simpa [prefixWord, tailWord_3891495, baseEnd_3891495] using wordTrace_append hprefix tailTrace_3891495
  have hstable : (prefixWord ++ tailWord_3891495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891495).length < 2 ^ (prefixWord ++ tailWord_3891495).sum := by decide
  have hdescent : baseEnd_3891495 < baseStart_3891495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891500 : List Nat := [2, 2, 1, 1, 1, 3, 4, 1, 2, 6]
def baseStart_3891500 : Nat := 118140960795 + 3891500 * 2 ^ 59
def prefixEnd_3891500 : Nat := 4983230072969 + 3 ^ 40 * 3891500 * 2
def baseEnd_3891500 : Nat := 666069988990543240684441

theorem tailTrace_3891500 : CollatzResearch.WordTrace tailWord_3891500 prefixEnd_3891500 666069988990543240684441 := by
  unfold tailWord_3891500
  simp only [CollatzResearch.WordTrace]
  refine ⟨70967332700883795066191977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94623110267845060088255969 70967332700883795066191977)
  ·
    refine ⟨53225499525662846299643983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70967332700883795066191977 53225499525662846299643983)
    ·
      refine ⟨79838249288494269449465975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53225499525662846299643983 79838249288494269449465975)
      ·
        refine ⟨119757373932741404174198963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79838249288494269449465975 119757373932741404174198963)
        ·
          refine ⟨179636060899112106261298445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119757373932741404174198963 179636060899112106261298445)
          ·
            refine ⟨67363522837167039847986917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179636060899112106261298445 67363522837167039847986917)
            ·
              refine ⟨12630660531968819971497547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67363522837167039847986917 12630660531968819971497547)
              ·
                refine ⟨18945990797953229957246321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12630660531968819971497547 18945990797953229957246321)
                ·
                  refine ⟨14209493098464922467934741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18945990797953229957246321 14209493098464922467934741)
                  ·
                    refine ⟨666069988990543240684441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14209493098464922467934741 666069988990543240684441)
                    ·
                      rfl

theorem cell23_3891500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 6].length) (baseStart_3891500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3891500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3891500 prefixEnd_3891500 := by exact prefixLift 3891500
  have htrace : WordTrace (prefixWord ++ tailWord_3891500) baseStart_3891500 baseEnd_3891500 := by
    simpa [prefixWord, tailWord_3891500, baseEnd_3891500] using wordTrace_append hprefix tailTrace_3891500
  have hstable : (prefixWord ++ tailWord_3891500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891500).length < 2 ^ (prefixWord ++ tailWord_3891500).sum := by decide
  have hdescent : baseEnd_3891500 < baseStart_3891500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891520 : List Nat := [2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 4]
def baseStart_3891520 : Nat := 118140960795 + 3891520 * 2 ^ 59
def prefixEnd_3891520 : Nat := 4983230072969 + 3 ^ 40 * 3891520 * 2
def baseEnd_3891520 : Nat := 1998220236584719643803231

theorem tailTrace_3891520 : CollatzResearch.WordTrace tailWord_3891520 prefixEnd_3891520 1998220236584719643803231 := by
  unfold tailWord_3891520
  simp only [CollatzResearch.WordTrace]
  refine ⟨70967697430847566774056007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94623596574463422365408009 70967697430847566774056007)
  ·
    refine ⟨106451546146271350161084011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70967697430847566774056007 106451546146271350161084011)
    ·
      refine ⟨159677319219407025241626017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106451546146271350161084011 159677319219407025241626017)
      ·
        refine ⟨119757989414555268931219513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159677319219407025241626017 119757989414555268931219513)
        ·
          refine ⟨89818492060916451698414635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119757989414555268931219513 89818492060916451698414635)
          ·
            refine ⟨134727738091374677547621953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89818492060916451698414635 134727738091374677547621953)
            ·
              refine ⟨101045803568531008160716465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134727738091374677547621953 101045803568531008160716465)
              ·
                refine ⟨75784352676398256120537349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101045803568531008160716465 75784352676398256120537349)
                ·
                  refine ⟨14209566126824673022600753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75784352676398256120537349 14209566126824673022600753)
                  ·
                    refine ⟨10657174595118504766950565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14209566126824673022600753 10657174595118504766950565)
                    ·
                      refine ⟨1998220236584719643803231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10657174595118504766950565 1998220236584719643803231)
                      ·
                        rfl

theorem cell23_3891520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 4].length) (baseStart_3891520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3891520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3891520 prefixEnd_3891520 := by exact prefixLift 3891520
  have htrace : WordTrace (prefixWord ++ tailWord_3891520) baseStart_3891520 baseEnd_3891520 := by
    simpa [prefixWord, tailWord_3891520, baseEnd_3891520] using wordTrace_append hprefix tailTrace_3891520
  have hstable : (prefixWord ++ tailWord_3891520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891520).length < 2 ^ (prefixWord ++ tailWord_3891520).sum := by decide
  have hdescent : baseEnd_3891520 < baseStart_3891520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891567 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 4, 5, 2]
def baseStart_3891567 : Nat := 118140960795 + 3891567 * 2 ^ 59
def prefixEnd_3891567 : Nat := 4983230072969 + 3 ^ 40 * 3891567 * 2
def baseEnd_3891567 : Nat := 1998244370175480959915515

theorem tailTrace_3891567 : CollatzResearch.WordTrace tailWord_3891567 prefixEnd_3891567 1998244370175480959915515 := by
  unfold tailWord_3891567
  simp only [CollatzResearch.WordTrace]
  refine ⟨141937109092524860575072955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94624739395016573716715303 141937109092524860575072955)
  ·
    refine ⟨212905663638787290862609433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141937109092524860575072955 212905663638787290862609433)
    ·
      refine ⟨159679247729090468146957075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212905663638787290862609433 159679247729090468146957075)
      ·
        refine ⟨239518871593635702220435613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159679247729090468146957075 239518871593635702220435613)
        ·
          refine ⟨89819576847613388332663355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239518871593635702220435613 89819576847613388332663355)
          ·
            refine ⟨134729365271420082498995033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89819576847613388332663355 134729365271420082498995033)
            ·
              refine ⟨101047023953565061874246275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134729365271420082498995033 101047023953565061874246275)
              ·
                refine ⟨151570535930347592811369413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101047023953565061874246275 151570535930347592811369413)
                ·
                  refine ⟨28419475486940173652131765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 151570535930347592811369413 28419475486940173652131765)
                  ·
                    refine ⟨2664325826900641279887353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28419475486940173652131765 2664325826900641279887353)
                    ·
                      refine ⟨1998244370175480959915515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2664325826900641279887353 1998244370175480959915515)
                      ·
                        rfl

theorem cell23_3891567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 5, 2].length) (baseStart_3891567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3891567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3891567 prefixEnd_3891567 := by exact prefixLift 3891567
  have htrace : WordTrace (prefixWord ++ tailWord_3891567) baseStart_3891567 baseEnd_3891567 := by
    simpa [prefixWord, tailWord_3891567, baseEnd_3891567] using wordTrace_append hprefix tailTrace_3891567
  have hstable : (prefixWord ++ tailWord_3891567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891567).length < 2 ^ (prefixWord ++ tailWord_3891567).sum := by decide
  have hdescent : baseEnd_3891567 < baseStart_3891567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891598 : List Nat := [4, 1, 1, 4, 1, 3, 2, 2, 5]
def baseStart_3891598 : Nat := 118140960795 + 3891598 * 2 ^ 59
def prefixEnd_3891598 : Nat := 4983230072969 + 3 ^ 40 * 3891598 * 2
def baseEnd_3891598 : Nat := 222028920897307815403097

theorem tailTrace_3891598 : CollatzResearch.WordTrace tailWord_3891598 prefixEnd_3891598 222028920897307815403097 := by
  unfold tailWord_3891598
  simp only [CollatzResearch.WordTrace]
  refine ⟨17742279969426569108681431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94625493170275035246300965 17742279969426569108681431)
  ·
    refine ⟨26613419954139853663022147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17742279969426569108681431 26613419954139853663022147)
    ·
      refine ⟨39920129931209780494533221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26613419954139853663022147 39920129931209780494533221)
      ·
        refine ⟨7485024362101833842724979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39920129931209780494533221 7485024362101833842724979)
        ·
          refine ⟨11227536543152750764087469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7485024362101833842724979 11227536543152750764087469)
          ·
            refine ⟨4210326203682281536532801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11227536543152750764087469 4210326203682281536532801)
            ·
              refine ⟨3157744652761711152399601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4210326203682281536532801 3157744652761711152399601)
              ·
                refine ⟨2368308489571283364299701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3157744652761711152399601 2368308489571283364299701)
                ·
                  refine ⟨222028920897307815403097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2368308489571283364299701 222028920897307815403097)
                  ·
                    rfl

theorem cell23_3891598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 2, 5].length) (baseStart_3891598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3891598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3891598 prefixEnd_3891598 := by exact prefixLift 3891598
  have htrace : WordTrace (prefixWord ++ tailWord_3891598) baseStart_3891598 baseEnd_3891598 := by
    simpa [prefixWord, tailWord_3891598, baseEnd_3891598] using wordTrace_append hprefix tailTrace_3891598
  have hstable : (prefixWord ++ tailWord_3891598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891598).length < 2 ^ (prefixWord ++ tailWord_3891598).sum := by decide
  have hdescent : baseEnd_3891598 < baseStart_3891598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891641 : List Nat := [1, 2, 1, 4, 3, 1, 1, 5, 1, 4]
def baseStart_3891641 : Nat := 118140960795 + 3891641 * 2 ^ 59
def prefixEnd_3891641 : Nat := 4983230072969 + 3 ^ 40 * 3891641 * 2
def baseEnd_3891641 : Nat := 666094122581304556796725

theorem tailTrace_3891641 : CollatzResearch.WordTrace tailWord_3891641 prefixEnd_3891641 666094122581304556796725 := by
  unfold tailWord_3891641
  simp only [CollatzResearch.WordTrace]
  refine ⟨141939808094256771213266777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94626538729504514142177851 141939808094256771213266777)
  ·
    refine ⟨106454856070692578409950083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141939808094256771213266777 106454856070692578409950083)
    ·
      refine ⟨159682284106038867614925125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106454856070692578409950083 159682284106038867614925125)
      ·
        refine ⟨29940428269882287677798461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159682284106038867614925125 29940428269882287677798461)
        ·
          refine ⟨11227660601205857879174423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29940428269882287677798461 11227660601205857879174423)
          ·
            refine ⟨16841490901808786818761635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11227660601205857879174423 16841490901808786818761635)
            ·
              refine ⟨25262236352713180228142453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16841490901808786818761635 25262236352713180228142453)
              ·
                refine ⟨2368334658066860646388355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25262236352713180228142453 2368334658066860646388355)
                ·
                  refine ⟨3552501987100290969582533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2368334658066860646388355 3552501987100290969582533)
                  ·
                    refine ⟨666094122581304556796725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3552501987100290969582533 666094122581304556796725)
                    ·
                      rfl

theorem cell23_3891641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 5, 1, 4].length) (baseStart_3891641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3891641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3891641 prefixEnd_3891641 := by exact prefixLift 3891641
  have htrace : WordTrace (prefixWord ++ tailWord_3891641) baseStart_3891641 baseEnd_3891641 := by
    simpa [prefixWord, tailWord_3891641, baseEnd_3891641] using wordTrace_append hprefix tailTrace_3891641
  have hstable : (prefixWord ++ tailWord_3891641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891641).length < 2 ^ (prefixWord ++ tailWord_3891641).sum := by decide
  have hdescent : baseEnd_3891641 < baseStart_3891641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891674 : List Nat := [3, 1, 1, 2, 3, 1, 1, 1, 3, 5, 2]
def baseStart_3891674 : Nat := 118140960795 + 3891674 * 2 ^ 59
def prefixEnd_3891674 : Nat := 4983230072969 + 3 ^ 40 * 3891674 * 2
def baseEnd_3891674 : Nat := 1998299312605512041277523

theorem tailTrace_3891674 : CollatzResearch.WordTrace tailWord_3891674 prefixEnd_3891674 1998299312605512041277523 := by
  unfold tailWord_3891674
  simp only [CollatzResearch.WordTrace]
  refine ⟨35485252925784304462304519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94627341135424811899478717 35485252925784304462304519)
  ·
    refine ⟨53227879388676456693456779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35485252925784304462304519 53227879388676456693456779)
    ·
      refine ⟨79841819083014685040185169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53227879388676456693456779 79841819083014685040185169)
      ·
        refine ⟨59881364312261013780138877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79841819083014685040185169 59881364312261013780138877)
        ·
          refine ⟨22455511617097880167552079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59881364312261013780138877 22455511617097880167552079)
          ·
            refine ⟨33683267425646820251328119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22455511617097880167552079 33683267425646820251328119)
            ·
              refine ⟨50524901138470230376992179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33683267425646820251328119 50524901138470230376992179)
              ·
                refine ⟨75787351707705345565488269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50524901138470230376992179 75787351707705345565488269)
                ·
                  refine ⟨28420256890389504587058101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75787351707705345565488269 28420256890389504587058101)
                  ·
                    refine ⟨2664399083474016055036697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28420256890389504587058101 2664399083474016055036697)
                    ·
                      refine ⟨1998299312605512041277523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2664399083474016055036697 1998299312605512041277523)
                      ·
                        rfl

theorem cell23_3891674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 3, 5, 2].length) (baseStart_3891674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3891674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3891674 prefixEnd_3891674 := by exact prefixLift 3891674
  have htrace : WordTrace (prefixWord ++ tailWord_3891674) baseStart_3891674 baseEnd_3891674 := by
    simpa [prefixWord, tailWord_3891674, baseEnd_3891674] using wordTrace_append hprefix tailTrace_3891674
  have hstable : (prefixWord ++ tailWord_3891674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891674).length < 2 ^ (prefixWord ++ tailWord_3891674).sum := by decide
  have hdescent : baseEnd_3891674 < baseStart_3891674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891697 : List Nat := [1, 2, 2, 2, 3, 1, 2, 1, 3, 6]
def baseStart_3891697 : Nat := 118140960795 + 3891697 * 2 ^ 59
def prefixEnd_3891697 : Nat := 4983230072969 + 3 ^ 40 * 3891697 * 2
def baseEnd_3891697 : Nat := 666103707553521817096639

theorem tailTrace_3891697 : CollatzResearch.WordTrace tailWord_3891697 prefixEnd_3891697 666103707553521817096639 := by
  unfold tailWord_3891697
  simp only [CollatzResearch.WordTrace]
  refine ⟨141941850582053892777305345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94627900388035928518203563 141941850582053892777305345)
  ·
    refine ⟨106456387936540419582979009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141941850582053892777305345 106456387936540419582979009)
    ·
      refine ⟨79842290952405314687234257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106456387936540419582979009 79842290952405314687234257)
      ·
        refine ⟨59881718214303986015425693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79842290952405314687234257 59881718214303986015425693)
        ·
          refine ⟨22455644330363994755784635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59881718214303986015425693 22455644330363994755784635)
          ·
            refine ⟨33683466495545992133676953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22455644330363994755784635 33683466495545992133676953)
            ·
              refine ⟨25262599871659494100257715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33683466495545992133676953 25262599871659494100257715)
              ·
                refine ⟨37893899807489241150386573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25262599871659494100257715 37893899807489241150386573)
                ·
                  refine ⟨14210212427808465431394965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37893899807489241150386573 14210212427808465431394965)
                  ·
                    refine ⟨666103707553521817096639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14210212427808465431394965 666103707553521817096639)
                    ·
                      rfl

theorem cell23_3891697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 6].length) (baseStart_3891697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3891697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3891697 prefixEnd_3891697 := by exact prefixLift 3891697
  have htrace : WordTrace (prefixWord ++ tailWord_3891697) baseStart_3891697 baseEnd_3891697 := by
    simpa [prefixWord, tailWord_3891697, baseEnd_3891697] using wordTrace_append hprefix tailTrace_3891697
  have hstable : (prefixWord ++ tailWord_3891697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891697).length < 2 ^ (prefixWord ++ tailWord_3891697).sum := by decide
  have hdescent : baseEnd_3891697 < baseStart_3891697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891704 : List Nat := [2, 1, 2, 1, 1, 4, 1, 5, 1, 1, 4]
def baseStart_3891704 : Nat := 118140960795 + 3891704 * 2 ^ 59
def prefixEnd_3891704 : Nat := 4983230072969 + 3 ^ 40 * 3891704 * 2
def baseEnd_3891704 : Nat := 1998314717025146923902385

theorem tailTrace_3891704 : CollatzResearch.WordTrace tailWord_3891704 prefixEnd_3891704 1998314717025146923902385 := by
  unfold tailWord_3891704
  simp only [CollatzResearch.WordTrace]
  refine ⟨70971052946514266486405083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94628070595352355315206777 70971052946514266486405083)
  ·
    refine ⟨106456579419771399729607625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70971052946514266486405083 106456579419771399729607625)
    ·
      refine ⟨79842434564828549797205719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106456579419771399729607625 79842434564828549797205719)
      ·
        refine ⟨119763651847242824695808579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79842434564828549797205719 119763651847242824695808579)
        ·
          refine ⟨179645477770864237043712869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119763651847242824695808579 179645477770864237043712869)
          ·
            refine ⟨33683527082037044445696163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179645477770864237043712869 33683527082037044445696163)
            ·
              refine ⟨50525290623055566668544245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33683527082037044445696163 50525290623055566668544245)
              ·
                refine ⟨4736745995911459375176023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50525290623055566668544245 4736745995911459375176023)
                ·
                  refine ⟨7105118993867189062764035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4736745995911459375176023 7105118993867189062764035)
                  ·
                    refine ⟨10657678490800783594146053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7105118993867189062764035 10657678490800783594146053)
                    ·
                      refine ⟨1998314717025146923902385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10657678490800783594146053 1998314717025146923902385)
                      ·
                        rfl

theorem cell23_3891704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 5, 1, 1, 4].length) (baseStart_3891704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3891704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3891704 prefixEnd_3891704 := by exact prefixLift 3891704
  have htrace : WordTrace (prefixWord ++ tailWord_3891704) baseStart_3891704 baseEnd_3891704 := by
    simpa [prefixWord, tailWord_3891704, baseEnd_3891704] using wordTrace_append hprefix tailTrace_3891704
  have hstable : (prefixWord ++ tailWord_3891704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891704).length < 2 ^ (prefixWord ++ tailWord_3891704).sum := by decide
  have hdescent : baseEnd_3891704 < baseStart_3891704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891717 : List Nat := [1, 3, 1, 1, 2, 2, 3, 2, 1, 1, 6]
def baseStart_3891717 : Nat := 118140960795 + 3891717 * 2 ^ 59
def prefixEnd_3891717 : Nat := 4983230072969 + 3 ^ 40 * 3891717 * 2
def baseEnd_3891717 : Nat := 1998321392273655373039825

theorem tailTrace_3891717 : CollatzResearch.WordTrace tailWord_3891717 prefixEnd_3891717 1998321392273655373039825 := by
  unfold tailWord_3891717
  simp only [CollatzResearch.WordTrace]
  refine ⟨141942580041981436193033405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94628386694654290795355603 141942580041981436193033405)
  ·
    refine ⟨53228467515743038572387527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141942580041981436193033405 53228467515743038572387527)
    ·
      refine ⟨79842701273614557858581291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53228467515743038572387527 79842701273614557858581291)
      ·
        refine ⟨119764051910421836787871937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79842701273614557858581291 119764051910421836787871937)
        ·
          refine ⟨89823038932816377590903953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119764051910421836787871937 89823038932816377590903953)
          ·
            refine ⟨67367279199612283193177965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89823038932816377590903953 67367279199612283193177965)
            ·
              refine ⟨25262729699854606197441737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67367279199612283193177965 25262729699854606197441737)
              ·
                refine ⟨18947047274890954648081303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25262729699854606197441737 18947047274890954648081303)
                ·
                  refine ⟨28420570912336431972121955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18947047274890954648081303 28420570912336431972121955)
                  ·
                    refine ⟨42630856368504647958182933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28420570912336431972121955 42630856368504647958182933)
                    ·
                      refine ⟨1998321392273655373039825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42630856368504647958182933 1998321392273655373039825)
                      ·
                        rfl

theorem cell23_3891717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 1, 6].length) (baseStart_3891717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3891717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3891717 prefixEnd_3891717 := by exact prefixLift 3891717
  have htrace : WordTrace (prefixWord ++ tailWord_3891717) baseStart_3891717 baseEnd_3891717 := by
    simpa [prefixWord, tailWord_3891717, baseEnd_3891717] using wordTrace_append hprefix tailTrace_3891717
  have hstable : (prefixWord ++ tailWord_3891717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891717).length < 2 ^ (prefixWord ++ tailWord_3891717).sum := by decide
  have hdescent : baseEnd_3891717 < baseStart_3891717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891721 : List Nat := [1, 2, 1, 1, 3, 1, 2, 5, 3, 2, 2]
def baseStart_3891721 : Nat := 118140960795 + 3891721 * 2 ^ 59
def prefixEnd_3891721 : Nat := 4983230072969 + 3 ^ 40 * 3891721 * 2
def baseEnd_3891721 : Nat := 1998323446196273357389807

theorem tailTrace_3891721 : CollatzResearch.WordTrace tailWord_3891721 prefixEnd_3891721 1998323446196273357389807 := by
  unfold tailWord_3891721
  simp only [CollatzResearch.WordTrace]
  refine ⟨141942725933966944876179017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94628483955977963250786011 141942725933966944876179017)
  ·
    refine ⟨106457044450475208657134263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141942725933966944876179017 106457044450475208657134263)
    ·
      refine ⟨159685566675712812985701395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106457044450475208657134263 159685566675712812985701395)
      ·
        refine ⟨239528350013569219478552093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159685566675712812985701395 239528350013569219478552093)
        ·
          refine ⟨89823131255088457304457035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239528350013569219478552093 89823131255088457304457035)
          ·
            refine ⟨134734696882632685956685553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89823131255088457304457035 134734696882632685956685553)
            ·
              refine ⟨101051022661974514467514165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134734696882632685956685553 101051022661974514467514165)
              ·
                refine ⟨9473533374560110731329453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101051022661974514467514165 9473533374560110731329453)
                ·
                  refine ⟨3552575015460041524248545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9473533374560110731329453 3552575015460041524248545)
                  ·
                    refine ⟨2664431261595031143186409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3552575015460041524248545 2664431261595031143186409)
                    ·
                      refine ⟨1998323446196273357389807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2664431261595031143186409 1998323446196273357389807)
                      ·
                        rfl

theorem cell23_3891721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 3, 2, 2].length) (baseStart_3891721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3891721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3891721 prefixEnd_3891721 := by exact prefixLift 3891721
  have htrace : WordTrace (prefixWord ++ tailWord_3891721) baseStart_3891721 baseEnd_3891721 := by
    simpa [prefixWord, tailWord_3891721, baseEnd_3891721] using wordTrace_append hprefix tailTrace_3891721
  have hstable : (prefixWord ++ tailWord_3891721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891721).length < 2 ^ (prefixWord ++ tailWord_3891721).sum := by decide
  have hdescent : baseEnd_3891721 < baseStart_3891721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891724 : List Nat := [2, 2, 1, 2, 4, 1, 2, 2, 1, 1, 5]
def baseStart_3891724 : Nat := 118140960795 + 3891724 * 2 ^ 59
def prefixEnd_3891724 : Nat := 4983230072969 + 3 ^ 40 * 3891724 * 2
def baseEnd_3891724 : Nat := 1998324986638236845652293

theorem tailTrace_3891724 : CollatzResearch.WordTrace tailWord_3891724 prefixEnd_3891724 1998324986638236845652293 := by
  unfold tailWord_3891724
  simp only [CollatzResearch.WordTrace]
  refine ⟨70971417676478038194269113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94628556901970717592358817 70971417676478038194269113)
  ·
    refine ⟨53228563257358528645701835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70971417676478038194269113 53228563257358528645701835)
    ·
      refine ⟨79842844886037792968552753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53228563257358528645701835 79842844886037792968552753)
      ·
        refine ⟨59882133664528344726414565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79842844886037792968552753 59882133664528344726414565)
        ·
          refine ⟨11227900062099064636202731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59882133664528344726414565 11227900062099064636202731)
          ·
            refine ⟨16841850093148596954304097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11227900062099064636202731 16841850093148596954304097)
            ·
              refine ⟨12631387569861447715728073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16841850093148596954304097 12631387569861447715728073)
              ·
                refine ⟨9473540677396085786796055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12631387569861447715728073 9473540677396085786796055)
                ·
                  refine ⟨14210311016094128680194083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9473540677396085786796055 14210311016094128680194083)
                  ·
                    refine ⟨21315466524141193020291125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14210311016094128680194083 21315466524141193020291125)
                    ·
                      refine ⟨1998324986638236845652293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21315466524141193020291125 1998324986638236845652293)
                      ·
                        rfl

theorem cell23_3891724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_3891724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3891724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3891724 prefixEnd_3891724 := by exact prefixLift 3891724
  have htrace : WordTrace (prefixWord ++ tailWord_3891724) baseStart_3891724 baseEnd_3891724 := by
    simpa [prefixWord, tailWord_3891724, baseEnd_3891724] using wordTrace_append hprefix tailTrace_3891724
  have hstable : (prefixWord ++ tailWord_3891724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891724).length < 2 ^ (prefixWord ++ tailWord_3891724).sum := by decide
  have hdescent : baseEnd_3891724 < baseStart_3891724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891735 : List Nat := [1, 1, 3, 6, 2, 1, 1, 2, 1, 5]
def baseStart_3891735 : Nat := 118140960795 + 3891735 * 2 ^ 59
def prefixEnd_3891735 : Nat := 4983230072969 + 3 ^ 40 * 3891735 * 2
def baseEnd_3891735 : Nat := 666110211641812100871581

theorem tailTrace_3891735 : CollatzResearch.WordTrace tailWord_3891735 prefixEnd_3891735 666110211641812100871581 := by
  unfold tailWord_3891735
  simp only [CollatzResearch.WordTrace]
  refine ⟨141943236555916225267188659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94628824370610816844792439 141943236555916225267188659)
  ·
    refine ⟨212914854833874337900782989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141943236555916225267188659 212914854833874337900782989)
    ·
      refine ⟨79843070562702876712793621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212914854833874337900782989 79843070562702876712793621)
      ·
        refine ⟨3742643932626697345912201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 79843070562702876712793621 3742643932626697345912201)
        ·
          refine ⟨2806982949470023009434151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3742643932626697345912201 2806982949470023009434151)
          ·
            refine ⟨4210474424205034514151227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2806982949470023009434151 4210474424205034514151227)
            ·
              refine ⟨6315711636307551771226841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4210474424205034514151227 6315711636307551771226841)
              ·
                refine ⟨4736783727230663828420131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6315711636307551771226841 4736783727230663828420131)
                ·
                  refine ⟨7105175590845995742630197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4736783727230663828420131 7105175590845995742630197)
                  ·
                    refine ⟨666110211641812100871581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7105175590845995742630197 666110211641812100871581)
                    ·
                      rfl

theorem cell23_3891735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 2, 1, 5].length) (baseStart_3891735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3891735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3891735 prefixEnd_3891735 := by exact prefixLift 3891735
  have htrace : WordTrace (prefixWord ++ tailWord_3891735) baseStart_3891735 baseEnd_3891735 := by
    simpa [prefixWord, tailWord_3891735, baseEnd_3891735] using wordTrace_append hprefix tailTrace_3891735
  have hstable : (prefixWord ++ tailWord_3891735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891735).length < 2 ^ (prefixWord ++ tailWord_3891735).sum := by decide
  have hdescent : baseEnd_3891735 < baseStart_3891735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891741 : List Nat := [1, 4, 2, 2, 1, 3, 1, 1, 3, 2, 3]
def baseStart_3891741 : Nat := 118140960795 + 3891741 * 2 ^ 59
def prefixEnd_3891741 : Nat := 4983230072969 + 3 ^ 40 * 3891741 * 2
def baseEnd_3891741 : Nat := 1998333715809363279139715

theorem tailTrace_3891741 : CollatzResearch.WordTrace tailWord_3891741 prefixEnd_3891741 1998333715809363279139715 := by
  unfold tailWord_3891741
  simp only [CollatzResearch.WordTrace]
  refine ⟨141943455393894488291907077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94628970262596325527938051 141943455393894488291907077)
  ·
    refine ⟨26614397886355216554732577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141943455393894488291907077 26614397886355216554732577)
    ·
      refine ⟨19960798414766412416049433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26614397886355216554732577 19960798414766412416049433)
      ·
        refine ⟨14970598811074809312037075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19960798414766412416049433 14970598811074809312037075)
        ·
          refine ⟨22455898216612213968055613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14970598811074809312037075 22455898216612213968055613)
          ·
            refine ⟨8420961831229580238020855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22455898216612213968055613 8420961831229580238020855)
            ·
              refine ⟨12631442746844370357031283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8420961831229580238020855 12631442746844370357031283)
              ·
                refine ⟨18947164120266555535546925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12631442746844370357031283 18947164120266555535546925)
                ·
                  refine ⟨7105186545099958325830097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18947164120266555535546925 7105186545099958325830097)
                  ·
                    refine ⟨5328889908824968744372573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7105186545099958325830097 5328889908824968744372573)
                    ·
                      refine ⟨1998333715809363279139715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5328889908824968744372573 1998333715809363279139715)
                      ·
                        rfl

theorem cell23_3891741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_3891741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3891741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3891741 prefixEnd_3891741 := by exact prefixLift 3891741
  have htrace : WordTrace (prefixWord ++ tailWord_3891741) baseStart_3891741 baseEnd_3891741 := by
    simpa [prefixWord, tailWord_3891741, baseEnd_3891741] using wordTrace_append hprefix tailTrace_3891741
  have hstable : (prefixWord ++ tailWord_3891741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891741).length < 2 ^ (prefixWord ++ tailWord_3891741).sum := by decide
  have hdescent : baseEnd_3891741 < baseStart_3891741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891758 : List Nat := [4, 1, 3, 1, 3, 2, 1, 1, 1, 1, 5]
def baseStart_3891758 : Nat := 118140960795 + 3891758 * 2 ^ 59
def prefixEnd_3891758 : Nat := 4983230072969 + 3 ^ 40 * 3891758 * 2
def baseEnd_3891758 : Nat := 1998342444980489712627137

theorem tailTrace_3891758 : CollatzResearch.WordTrace tailWord_3891758 prefixEnd_3891758 1998342444980489712627137 := by
  unfold tailWord_3891758
  simp only [CollatzResearch.WordTrace]
  refine ⟨17743009429354112524409491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94629383623221933463517285 17743009429354112524409491)
  ·
    refine ⟨26614514144031168786614237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17743009429354112524409491 26614514144031168786614237)
    ·
      refine ⟨9980442804011688294980339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26614514144031168786614237 9980442804011688294980339)
      ·
        refine ⟨14970664206017532442470509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9980442804011688294980339 14970664206017532442470509)
        ·
          refine ⟨5613999077256574665926441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14970664206017532442470509 5613999077256574665926441)
          ·
            refine ⟨4210499307942430999444831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5613999077256574665926441 4210499307942430999444831)
            ·
              refine ⟨6315748961913646499167247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4210499307942430999444831 6315748961913646499167247)
              ·
                refine ⟨9473623442870469748750871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6315748961913646499167247 9473623442870469748750871)
                ·
                  refine ⟨14210435164305704623126307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9473623442870469748750871 14210435164305704623126307)
                  ·
                    refine ⟨21315652746458556934689461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14210435164305704623126307 21315652746458556934689461)
                    ·
                      refine ⟨1998342444980489712627137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21315652746458556934689461 1998342444980489712627137)
                      ·
                        rfl

theorem cell23_3891758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_3891758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3891758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3891758 prefixEnd_3891758 := by exact prefixLift 3891758
  have htrace : WordTrace (prefixWord ++ tailWord_3891758) baseStart_3891758 baseEnd_3891758 := by
    simpa [prefixWord, tailWord_3891758, baseEnd_3891758] using wordTrace_append hprefix tailTrace_3891758
  have hstable : (prefixWord ++ tailWord_3891758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891758).length < 2 ^ (prefixWord ++ tailWord_3891758).sum := by decide
  have hdescent : baseEnd_3891758 < baseStart_3891758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891772 : List Nat := [2, 2, 2, 2, 3, 1, 4, 2, 1, 2, 2]
def baseStart_3891772 : Nat := 118140960795 + 3891772 * 2 ^ 59
def prefixEnd_3891772 : Nat := 4983230072969 + 3 ^ 40 * 3891772 * 2
def baseEnd_3891772 : Nat := 1998349633709652657852073

theorem tailTrace_3891772 : CollatzResearch.WordTrace tailWord_3891772 prefixEnd_3891772 1998349633709652657852073 := by
  unfold tailWord_3891772
  simp only [CollatzResearch.WordTrace]
  refine ⟨70972293028391090293142785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94629724037854787057523713 70972293028391090293142785)
  ·
    refine ⟨53229219771293317719857089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70972293028391090293142785 53229219771293317719857089)
    ·
      refine ⟨39921914828469988289892817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53229219771293317719857089 39921914828469988289892817)
      ·
        refine ⟨29941436121352491217419613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39921914828469988289892817 29941436121352491217419613)
        ·
          refine ⟨11228038545507184206532355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29941436121352491217419613 11228038545507184206532355)
          ·
            refine ⟨16842057818260776309798533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11228038545507184206532355 16842057818260776309798533)
            ·
              refine ⟨3157885840923895558087225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16842057818260776309798533 3157885840923895558087225)
              ·
                refine ⟨2368414380692921668565419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3157885840923895558087225 2368414380692921668565419)
                ·
                  refine ⟨3552621571039382502848129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2368414380692921668565419 3552621571039382502848129)
                  ·
                    refine ⟨2664466178279536877136097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3552621571039382502848129 2664466178279536877136097)
                    ·
                      refine ⟨1998349633709652657852073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2664466178279536877136097 1998349633709652657852073)
                      ·
                        rfl

theorem cell23_3891772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 2, 1, 2, 2].length) (baseStart_3891772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3891772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3891772 prefixEnd_3891772 := by exact prefixLift 3891772
  have htrace : WordTrace (prefixWord ++ tailWord_3891772) baseStart_3891772 baseEnd_3891772 := by
    simpa [prefixWord, tailWord_3891772, baseEnd_3891772] using wordTrace_append hprefix tailTrace_3891772
  have hstable : (prefixWord ++ tailWord_3891772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891772).length < 2 ^ (prefixWord ++ tailWord_3891772).sum := by decide
  have hdescent : baseEnd_3891772 < baseStart_3891772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891781 : List Nat := [1, 3, 1, 1, 1, 5, 1, 2, 3, 3, 2]
def baseStart_3891781 : Nat := 118140960795 + 3891781 * 2 ^ 59
def prefixEnd_3891781 : Nat := 4983230072969 + 3 ^ 40 * 3891781 * 2
def baseEnd_3891781 : Nat := 1998354255035543122639531

theorem tailTrace_3891781 : CollatzResearch.WordTrace tailWord_3891781 prefixEnd_3891781 1998354255035543122639531 := by
  unfold tailWord_3891781
  simp only [CollatzResearch.WordTrace]
  refine ⟨141944914313749575123363197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94629942875833050082242131 141944914313749575123363197)
  ·
    refine ⟨53229342867656090671261199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141944914313749575123363197 53229342867656090671261199)
    ·
      refine ⟨79844014301484136006891799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53229342867656090671261199 79844014301484136006891799)
      ·
        refine ⟨119766021452226204010337699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79844014301484136006891799 119766021452226204010337699)
        ·
          refine ⟨179649032178339306015506549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119766021452226204010337699 179649032178339306015506549)
          ·
            refine ⟨16842096766719309938953739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 179649032178339306015506549 16842096766719309938953739)
            ·
              refine ⟨25263145150078964908430609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16842096766719309938953739 25263145150078964908430609)
              ·
                refine ⟨18947358862559223681322957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25263145150078964908430609 18947358862559223681322957)
                ·
                  refine ⟨7105259573459708880496109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18947358862559223681322957 7105259573459708880496109)
                  ·
                    refine ⟨2664472340047390830186041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7105259573459708880496109 2664472340047390830186041)
                    ·
                      refine ⟨1998354255035543122639531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2664472340047390830186041 1998354255035543122639531)
                      ·
                        rfl

theorem cell23_3891781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 3, 3, 2].length) (baseStart_3891781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3891781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3891781 prefixEnd_3891781 := by exact prefixLift 3891781
  have htrace : WordTrace (prefixWord ++ tailWord_3891781) baseStart_3891781 baseEnd_3891781 := by
    simpa [prefixWord, tailWord_3891781, baseEnd_3891781] using wordTrace_append hprefix tailTrace_3891781
  have hstable : (prefixWord ++ tailWord_3891781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891781).length < 2 ^ (prefixWord ++ tailWord_3891781).sum := by decide
  have hdescent : baseEnd_3891781 < baseStart_3891781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891787 : List Nat := [1, 1, 1, 1, 3, 1, 5, 1, 1, 8]
def baseStart_3891787 : Nat := 118140960795 + 3891787 * 2 ^ 59
def prefixEnd_3891787 : Nat := 4983230072969 + 3 ^ 40 * 3891787 * 2
def baseEnd_3891787 : Nat := 666119111973156699721501

theorem tailTrace_3891787 : CollatzResearch.WordTrace tailWord_3891787 prefixEnd_3891787 666119111973156699721501 := by
  unfold tailWord_3891787
  simp only [CollatzResearch.WordTrace]
  refine ⟨141945133151727838148081615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94630088767818558765387743 141945133151727838148081615)
  ·
    refine ⟨212917699727591757222122423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141945133151727838148081615 212917699727591757222122423)
    ·
      refine ⟨319376549591387635833183635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212917699727591757222122423 319376549591387635833183635)
      ·
        refine ⟨479064824387081453749775453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319376549591387635833183635 479064824387081453749775453)
        ·
          refine ⟨179649309145155545156165795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 479064824387081453749775453 179649309145155545156165795)
          ·
            refine ⟨269473963717733317734248693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179649309145155545156165795 269473963717733317734248693)
            ·
              refine ⟨25263184098537498537585815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 269473963717733317734248693 25263184098537498537585815)
              ·
                refine ⟨37894776147806247806378723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25263184098537498537585815 37894776147806247806378723)
                ·
                  refine ⟨56842164221709371709568085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37894776147806247806378723 56842164221709371709568085)
                  ·
                    refine ⟨666119111973156699721501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 56842164221709371709568085 666119111973156699721501)
                    ·
                      rfl

theorem cell23_3891787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 8].length) (baseStart_3891787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3891787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3891787 prefixEnd_3891787 := by exact prefixLift 3891787
  have htrace : WordTrace (prefixWord ++ tailWord_3891787) baseStart_3891787 baseEnd_3891787 := by
    simpa [prefixWord, tailWord_3891787, baseEnd_3891787] using wordTrace_append hprefix tailTrace_3891787
  have hstable : (prefixWord ++ tailWord_3891787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891787).length < 2 ^ (prefixWord ++ tailWord_3891787).sum := by decide
  have hdescent : baseEnd_3891787 < baseStart_3891787 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891794 : List Nat := [3, 2, 2, 1, 2, 1, 1, 2, 2, 3, 4]
def baseStart_3891794 : Nat := 118140960795 + 3891794 * 2 ^ 59
def prefixEnd_3891794 : Nat := 4983230072969 + 3 ^ 40 * 3891794 * 2
def baseEnd_3891794 : Nat := 1998360930284051571776971

theorem tailTrace_3891794 : CollatzResearch.WordTrace tailWord_3891794 prefixEnd_3891794 1998360930284051571776971 := by
  unfold tailWord_3891794
  simp only [CollatzResearch.WordTrace]
  refine ⟨35486347115675619585896609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94630258975134985562390957 35486347115675619585896609)
  ·
    refine ⟨26614760336756714689422457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35486347115675619585896609 26614760336756714689422457)
    ·
      refine ⟨19961070252567536017066843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26614760336756714689422457 19961070252567536017066843)
      ·
        refine ⟨29941605378851304025600265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19961070252567536017066843 29941605378851304025600265)
        ·
          refine ⟨22456204034138478019200199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29941605378851304025600265 22456204034138478019200199)
          ·
            refine ⟨33684306051207717028800299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22456204034138478019200199 33684306051207717028800299)
            ·
              refine ⟨50526459076811575543200449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33684306051207717028800299 50526459076811575543200449)
              ·
                refine ⟨37894844307608681657400337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50526459076811575543200449 37894844307608681657400337)
                ·
                  refine ⟨28421133230706511243050253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37894844307608681657400337 28421133230706511243050253)
                  ·
                    refine ⟨10657924961514941716143845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28421133230706511243050253 10657924961514941716143845)
                    ·
                      refine ⟨1998360930284051571776971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10657924961514941716143845 1998360930284051571776971)
                      ·
                        rfl

theorem cell23_3891794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_3891794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3891794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3891794 prefixEnd_3891794 := by exact prefixLift 3891794
  have htrace : WordTrace (prefixWord ++ tailWord_3891794) baseStart_3891794 baseEnd_3891794 := by
    simpa [prefixWord, tailWord_3891794, baseEnd_3891794] using wordTrace_append hprefix tailTrace_3891794
  have hstable : (prefixWord ++ tailWord_3891794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891794).length < 2 ^ (prefixWord ++ tailWord_3891794).sum := by decide
  have hdescent : baseEnd_3891794 < baseStart_3891794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891806 : List Nat := [4, 4, 1, 2, 2, 1, 2, 1, 1, 1, 4]
def baseStart_3891806 : Nat := 118140960795 + 3891806 * 2 ^ 59
def prefixEnd_3891806 : Nat := 4983230072969 + 3 ^ 40 * 3891806 * 2
def baseEnd_3891806 : Nat := 1998367092051905524826917

theorem tailTrace_3891806 : CollatzResearch.WordTrace tailWord_3891806 prefixEnd_3891806 1998367092051905524826917 := by
  unfold tailWord_3891806
  simp only [CollatzResearch.WordTrace]
  refine ⟨17743228267332375549127909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94630550759106002928682181 17743228267332375549127909)
  ·
    refine ⟨3326855300124820415461483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17743228267332375549127909 3326855300124820415461483)
    ·
      refine ⟨4990282950187230623192225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3326855300124820415461483 4990282950187230623192225)
      ·
        refine ⟨3742712212640422967394169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4990282950187230623192225 3742712212640422967394169)
        ·
          refine ⟨2807034159480317225545627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3742712212640422967394169 2807034159480317225545627)
          ·
            refine ⟨4210551239220475838318441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2807034159480317225545627 4210551239220475838318441)
            ·
              refine ⟨3157913429415356878738831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4210551239220475838318441 3157913429415356878738831)
              ·
                refine ⟨4736870144123035318108247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3157913429415356878738831 4736870144123035318108247)
                ·
                  refine ⟨7105305216184552977162371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4736870144123035318108247 7105305216184552977162371)
                  ·
                    refine ⟨10657957824276829465743557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7105305216184552977162371 10657957824276829465743557)
                    ·
                      refine ⟨1998367092051905524826917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10657957824276829465743557 1998367092051905524826917)
                      ·
                        rfl

theorem cell23_3891806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_3891806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3891806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3891806 prefixEnd_3891806 := by exact prefixLift 3891806
  have htrace : WordTrace (prefixWord ++ tailWord_3891806) baseStart_3891806 baseEnd_3891806 := by
    simpa [prefixWord, tailWord_3891806, baseEnd_3891806] using wordTrace_append hprefix tailTrace_3891806
  have hstable : (prefixWord ++ tailWord_3891806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891806).length < 2 ^ (prefixWord ++ tailWord_3891806).sum := by decide
  have hdescent : baseEnd_3891806 < baseStart_3891806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891811 : List Nat := [1, 1, 1, 5, 1, 2, 1, 4, 1, 4, 2]
def baseStart_3891811 : Nat := 118140960795 + 3891811 * 2 ^ 59
def prefixEnd_3891811 : Nat := 4983230072969 + 3 ^ 40 * 3891811 * 2
def baseEnd_3891811 : Nat := 1998369659455178005264393

theorem tailTrace_3891811 : CollatzResearch.WordTrace tailWord_3891811 prefixEnd_3891811 1998369659455178005264393 := by
  unfold tailWord_3891811
  simp only [CollatzResearch.WordTrace]
  refine ⟨141946008503640890246955287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94630672335760593497970191 141946008503640890246955287)
  ·
    refine ⟨212919012755461335370432931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141946008503640890246955287 212919012755461335370432931)
    ·
      refine ⟨319378519133192003055649397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212919012755461335370432931 319378519133192003055649397)
      ·
        refine ⟨29941736168736750286467131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 319378519133192003055649397 29941736168736750286467131)
        ·
          refine ⟨44912604253105125429700697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29941736168736750286467131 44912604253105125429700697)
          ·
            refine ⟨33684453189828844072275523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44912604253105125429700697 33684453189828844072275523)
            ·
              refine ⟨50526679784743266108413285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33684453189828844072275523 50526679784743266108413285)
              ·
                refine ⟨9473752459639362395327491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50526679784743266108413285 9473752459639362395327491)
                ·
                  refine ⟨14210628689459043592991237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9473752459639362395327491 14210628689459043592991237)
                  ·
                    refine ⟨2664492879273570673685857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14210628689459043592991237 2664492879273570673685857)
                    ·
                      refine ⟨1998369659455178005264393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2664492879273570673685857 1998369659455178005264393)
                      ·
                        rfl

theorem cell23_3891811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 4, 2].length) (baseStart_3891811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3891811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3891811 prefixEnd_3891811 := by exact prefixLift 3891811
  have htrace : WordTrace (prefixWord ++ tailWord_3891811) baseStart_3891811 baseEnd_3891811 := by
    simpa [prefixWord, tailWord_3891811, baseEnd_3891811] using wordTrace_append hprefix tailTrace_3891811
  have hstable : (prefixWord ++ tailWord_3891811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891811).length < 2 ^ (prefixWord ++ tailWord_3891811).sum := by decide
  have hdescent : baseEnd_3891811 < baseStart_3891811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891817 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 11]
def baseStart_3891817 : Nat := 118140960795 + 3891817 * 2 ^ 59
def prefixEnd_3891817 : Nat := 4983230072969 + 3 ^ 40 * 3891817 * 2
def baseEnd_3891817 : Nat := 222041415593233886865485

theorem tailTrace_3891817 : CollatzResearch.WordTrace tailWord_3891817 prefixEnd_3891817 222041415593233886865485 := by
  unfold tailWord_3891817
  simp only [CollatzResearch.WordTrace]
  refine ⟨141946227341619153271673705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94630818227746102181115803 141946227341619153271673705)
  ·
    refine ⟨106459670506214364953755279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141946227341619153271673705 106459670506214364953755279)
    ·
      refine ⟨159689505759321547430632919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106459670506214364953755279 159689505759321547430632919)
      ·
        refine ⟨239534258638982321145949379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159689505759321547430632919 239534258638982321145949379)
        ·
          refine ⟨359301387958473481718924069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239534258638982321145949379 359301387958473481718924069)
          ·
            refine ⟨67369010242213777822298263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 359301387958473481718924069 67369010242213777822298263)
            ·
              refine ⟨101053515363320666733447395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67369010242213777822298263 101053515363320666733447395)
              ·
                refine ⟨151580273044981000100171093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101053515363320666733447395 151580273044981000100171093)
                ·
                  refine ⟨222041415593233886865485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 151580273044981000100171093 222041415593233886865485)
                  ·
                    rfl

theorem cell23_3891817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 11].length) (baseStart_3891817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3891817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3891817 prefixEnd_3891817 := by exact prefixLift 3891817
  have htrace : WordTrace (prefixWord ++ tailWord_3891817) baseStart_3891817 baseEnd_3891817 := by
    simpa [prefixWord, tailWord_3891817, baseEnd_3891817] using wordTrace_append hprefix tailTrace_3891817
  have hstable : (prefixWord ++ tailWord_3891817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891817).length < 2 ^ (prefixWord ++ tailWord_3891817).sum := by decide
  have hdescent : baseEnd_3891817 < baseStart_3891817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891827 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 9]
def baseStart_3891827 : Nat := 118140960795 + 3891827 * 2 ^ 59
def prefixEnd_3891827 : Nat := 4983230072969 + 3 ^ 40 * 3891827 * 2
def baseEnd_3891827 : Nat := 1998377875145649942664319

theorem tailTrace_3891827 : CollatzResearch.WordTrace tailWord_3891827 prefixEnd_3891827 1998377875145649942664319 := by
  unfold tailWord_3891827
  simp only [CollatzResearch.WordTrace]
  refine ⟨141946592071582924979537735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94631061381055283319691823 141946592071582924979537735)
  ·
    refine ⟨212919888107374387469306603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141946592071582924979537735 212919888107374387469306603)
    ·
      refine ⟨319379832161061581203959905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212919888107374387469306603 319379832161061581203959905)
      ·
        refine ⟨239534874120796185902969929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319379832161061581203959905 239534874120796185902969929)
        ·
          refine ⟨179651155590597139427227447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239534874120796185902969929 179651155590597139427227447)
          ·
            refine ⟨269476733385895709140841171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179651155590597139427227447 269476733385895709140841171)
            ·
              refine ⟨404215100078843563711261757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269476733385895709140841171 404215100078843563711261757)
              ·
                refine ⟨151580662529566336391723159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 404215100078843563711261757 151580662529566336391723159)
                ·
                  refine ⟨227370993794349504587584739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151580662529566336391723159 227370993794349504587584739)
                  ·
                    refine ⟨341056490691524256881377109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 227370993794349504587584739 341056490691524256881377109)
                    ·
                      refine ⟨1998377875145649942664319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 341056490691524256881377109 1998377875145649942664319)
                      ·
                        rfl

theorem cell23_3891827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 9].length) (baseStart_3891827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3891827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3891827 prefixEnd_3891827 := by exact prefixLift 3891827
  have htrace : WordTrace (prefixWord ++ tailWord_3891827) baseStart_3891827 baseEnd_3891827 := by
    simpa [prefixWord, tailWord_3891827, baseEnd_3891827] using wordTrace_append hprefix tailTrace_3891827
  have hstable : (prefixWord ++ tailWord_3891827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891827).length < 2 ^ (prefixWord ++ tailWord_3891827).sum := by decide
  have hdescent : baseEnd_3891827 < baseStart_3891827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891864 : List Nat := [2, 1, 2, 4, 1, 1, 1, 3, 1, 7]
def baseStart_3891864 : Nat := 118140960795 + 3891864 * 2 ^ 59
def prefixEnd_3891864 : Nat := 4983230072969 + 3 ^ 40 * 3891864 * 2
def baseEnd_3891864 : Nat := 666132291309955432633883

theorem tailTrace_3891864 : CollatzResearch.WordTrace tailWord_3891864 prefixEnd_3891864 666132291309955432633883 := by
  unfold tailWord_3891864
  simp only [CollatzResearch.WordTrace]
  refine ⟨70973970786224440149317323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94631961048299253532423097 70973970786224440149317323)
  ·
    refine ⟨106460956179336660223975985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70973970786224440149317323 106460956179336660223975985)
    ·
      refine ⟨79845717134502495167981989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106460956179336660223975985 79845717134502495167981989)
      ·
        refine ⟨14971071962719217843996623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79845717134502495167981989 14971071962719217843996623)
        ·
          refine ⟨22456607944078826765994935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14971071962719217843996623 22456607944078826765994935)
          ·
            refine ⟨33684911916118240148992403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22456607944078826765994935 33684911916118240148992403)
            ·
              refine ⟨50527367874177360223488605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33684911916118240148992403 50527367874177360223488605)
              ·
                refine ⟨18947762952816510083808227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50527367874177360223488605 18947762952816510083808227)
                ·
                  refine ⟨28421644429224765125712341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18947762952816510083808227 28421644429224765125712341)
                  ·
                    refine ⟨666132291309955432633883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28421644429224765125712341 666132291309955432633883)
                    ·
                      rfl

theorem cell23_3891864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 1, 7].length) (baseStart_3891864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3891864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3891864 prefixEnd_3891864 := by exact prefixLift 3891864
  have htrace : WordTrace (prefixWord ++ tailWord_3891864) baseStart_3891864 baseEnd_3891864 := by
    simpa [prefixWord, tailWord_3891864, baseEnd_3891864] using wordTrace_append hprefix tailTrace_3891864
  have hstable : (prefixWord ++ tailWord_3891864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891864).length < 2 ^ (prefixWord ++ tailWord_3891864).sum := by decide
  have hdescent : baseEnd_3891864 < baseStart_3891864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891868 : List Nat := [2, 2, 3, 2, 2, 1, 3, 3, 5]
def baseStart_3891868 : Nat := 118140960795 + 3891868 * 2 ^ 59
def prefixEnd_3891868 : Nat := 4983230072969 + 3 ^ 40 * 3891868 * 2
def baseEnd_3891868 : Nat := 222044325316942698027959

theorem tailTrace_3891868 : CollatzResearch.WordTrace tailWord_3891868 prefixEnd_3891868 222044325316942698027959 := by
  unfold tailWord_3891868
  simp only [CollatzResearch.WordTrace]
  refine ⟨70974043732217194490890129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94632058309622925987853505 70974043732217194490890129)
  ·
    refine ⟨53230532799162895868167597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70974043732217194490890129 53230532799162895868167597)
    ·
      refine ⟨19961449799686085950562849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53230532799162895868167597 19961449799686085950562849)
      ·
        refine ⟨14971087349764564462922137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19961449799686085950562849 14971087349764564462922137)
        ·
          refine ⟨11228315512323423347191603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14971087349764564462922137 11228315512323423347191603)
          ·
            refine ⟨16842473268485135020787405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11228315512323423347191603 16842473268485135020787405)
            ·
              refine ⟨6315927475681925632795277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16842473268485135020787405 6315927475681925632795277)
              ·
                refine ⟨2368472803380722112298229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6315927475681925632795277 2368472803380722112298229)
                ·
                  refine ⟨222044325316942698027959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2368472803380722112298229 222044325316942698027959)
                  ·
                    rfl

theorem cell23_3891868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 3, 5].length) (baseStart_3891868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3891868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3891868 prefixEnd_3891868 := by exact prefixLift 3891868
  have htrace : WordTrace (prefixWord ++ tailWord_3891868) baseStart_3891868 baseEnd_3891868 := by
    simpa [prefixWord, tailWord_3891868, baseEnd_3891868] using wordTrace_append hprefix tailTrace_3891868
  have hstable : (prefixWord ++ tailWord_3891868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891868).length < 2 ^ (prefixWord ++ tailWord_3891868).sum := by decide
  have hdescent : baseEnd_3891868 < baseStart_3891868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891885 : List Nat := [1, 5, 2, 1, 1, 3, 3, 2, 5]
def baseStart_3891885 : Nat := 118140960795 + 3891885 * 2 ^ 59
def prefixEnd_3891885 : Nat := 4983230072969 + 3 ^ 40 * 3891885 * 2
def baseEnd_3891885 : Nat := 222045295224845635082117

theorem tailTrace_3891885 : CollatzResearch.WordTrace tailWord_3891885 prefixEnd_3891885 222045295224845635082117 := by
  unfold tailWord_3891885
  simp only [CollatzResearch.WordTrace]
  refine ⟨141948707505372800885149109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94632471670248533923432739 141948707505372800885149109)
  ·
    refine ⟨13307691328628700082982729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141948707505372800885149109 13307691328628700082982729)
    ·
      refine ⟨9980768496471525062237047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13307691328628700082982729 9980768496471525062237047)
      ·
        refine ⟨14971152744707287593355571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9980768496471525062237047 14971152744707287593355571)
        ·
          refine ⟨22456729117060931390033357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14971152744707287593355571 22456729117060931390033357)
          ·
            refine ⟨8421273418897849271262509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22456729117060931390033357 8421273418897849271262509)
            ·
              refine ⟨3157977532086693476723441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8421273418897849271262509 3157977532086693476723441)
              ·
                refine ⟨2368483149065020107542581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3157977532086693476723441 2368483149065020107542581)
                ·
                  refine ⟨222045295224845635082117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2368483149065020107542581 222045295224845635082117)
                  ·
                    rfl

theorem cell23_3891885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 2, 5].length) (baseStart_3891885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3891885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3891885 prefixEnd_3891885 := by exact prefixLift 3891885
  have htrace : WordTrace (prefixWord ++ tailWord_3891885) baseStart_3891885 baseEnd_3891885 := by
    simpa [prefixWord, tailWord_3891885, baseEnd_3891885] using wordTrace_append hprefix tailTrace_3891885
  have hstable : (prefixWord ++ tailWord_3891885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891885).length < 2 ^ (prefixWord ++ tailWord_3891885).sum := by decide
  have hdescent : baseEnd_3891885 < baseStart_3891885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891918 : List Nat := [4, 1, 1, 1, 3, 3, 2, 1, 2, 1, 4]
def baseStart_3891918 : Nat := 118140960795 + 3891918 * 2 ^ 59
def prefixEnd_3891918 : Nat := 4983230072969 + 3 ^ 40 * 3891918 * 2
def baseEnd_3891918 : Nat := 1998424601885209086626401

theorem tailTrace_3891918 : CollatzResearch.WordTrace tailWord_3891918 prefixEnd_3891918 1998424601885209086626401 := by
  unfold tailWord_3891918
  simp only [CollatzResearch.WordTrace]
  refine ⟨17743738889281655940137551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94633274076168831680733605 17743738889281655940137551)
  ·
    refine ⟨26615608333922483910206327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17743738889281655940137551 26615608333922483910206327)
    ·
      refine ⟨39923412500883725865309491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26615608333922483910206327 39923412500883725865309491)
      ·
        refine ⟨59885118751325588797964237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39923412500883725865309491 59885118751325588797964237)
        ·
          refine ⟨22456919531747095799236589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59885118751325588797964237 22456919531747095799236589)
          ·
            refine ⟨8421344824405160924713721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22456919531747095799236589 8421344824405160924713721)
            ·
              refine ⟨6316008618303870693535291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8421344824405160924713721 6316008618303870693535291)
              ·
                refine ⟨9474012927455806040302937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6316008618303870693535291 9474012927455806040302937)
                ·
                  refine ⟨7105509695591854530227203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9474012927455806040302937 7105509695591854530227203)
                  ·
                    refine ⟨10658264543387781795340805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7105509695591854530227203 10658264543387781795340805)
                    ·
                      refine ⟨1998424601885209086626401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10658264543387781795340805 1998424601885209086626401)
                      ·
                        rfl

theorem cell23_3891918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 2, 1, 4].length) (baseStart_3891918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3891918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3891918 prefixEnd_3891918 := by exact prefixLift 3891918
  have htrace : WordTrace (prefixWord ++ tailWord_3891918) baseStart_3891918 baseEnd_3891918 := by
    simpa [prefixWord, tailWord_3891918, baseEnd_3891918] using wordTrace_append hprefix tailTrace_3891918
  have hstable : (prefixWord ++ tailWord_3891918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891918).length < 2 ^ (prefixWord ++ tailWord_3891918).sum := by decide
  have hdescent : baseEnd_3891918 < baseStart_3891918 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891941 : List Nat := [1, 3, 1, 4, 1, 2, 1, 4, 6]
def baseStart_3891941 : Nat := 118140960795 + 3891941 * 2 ^ 59
def prefixEnd_3891941 : Nat := 4983230072969 + 3 ^ 40 * 3891941 * 2
def baseEnd_3891941 : Nat := 222048490215584721848755

theorem tailTrace_3891941 : CollatzResearch.WordTrace tailWord_3891941 prefixEnd_3891941 222048490215584721848755 := by
  unfold tailWord_3891941
  simp only [CollatzResearch.WordTrace]
  refine ⟨141950749993169922449187677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94633833328779948299458451 141950749993169922449187677)
  ·
    refine ⟨53231531247438720918445379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141950749993169922449187677 53231531247438720918445379)
    ·
      refine ⟨79847296871158081377668069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53231531247438720918445379 79847296871158081377668069)
      ·
        refine ⟨14971368163342140258312763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79847296871158081377668069 14971368163342140258312763)
        ·
          refine ⟨22457052245013210387469145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14971368163342140258312763 22457052245013210387469145)
          ·
            refine ⟨16842789183759907790601859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22457052245013210387469145 16842789183759907790601859)
            ·
              refine ⟨25264183775639861685902789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16842789183759907790601859 25264183775639861685902789)
              ·
                refine ⟨4737034457932474066106773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25264183775639861685902789 4737034457932474066106773)
                ·
                  refine ⟨222048490215584721848755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4737034457932474066106773 222048490215584721848755)
                  ·
                    rfl

theorem cell23_3891941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 4, 6].length) (baseStart_3891941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3891941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3891941 prefixEnd_3891941 := by exact prefixLift 3891941
  have htrace : WordTrace (prefixWord ++ tailWord_3891941) baseStart_3891941 baseEnd_3891941 := by
    simpa [prefixWord, tailWord_3891941, baseEnd_3891941] using wordTrace_append hprefix tailTrace_3891941
  have hstable : (prefixWord ++ tailWord_3891941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891941).length < 2 ^ (prefixWord ++ tailWord_3891941).sum := by decide
  have hdescent : baseEnd_3891941 < baseStart_3891941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891945 : List Nat := [1, 2, 1, 1, 1, 2, 8, 2, 1, 4]
def baseStart_3891945 : Nat := 118140960795 + 3891945 * 2 ^ 59
def prefixEnd_3891945 : Nat := 4983230072969 + 3 ^ 40 * 3891945 * 2
def baseEnd_3891945 : Nat := 666146155287626826996259

theorem tailTrace_3891945 : CollatzResearch.WordTrace tailWord_3891945 prefixEnd_3891945 666146155287626826996259 := by
  unfold tailWord_3891945
  simp only [CollatzResearch.WordTrace]
  refine ⟨141950895885155431132333289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94633930590103620754888859 141950895885155431132333289)
  ·
    refine ⟨106463171913866573349249967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141950895885155431132333289 106463171913866573349249967)
    ·
      refine ⟨159694757870799860023874951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106463171913866573349249967 159694757870799860023874951)
      ·
        refine ⟨239542136806199790035812427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159694757870799860023874951 239542136806199790035812427)
        ·
          refine ⟨359313205209299685053718641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239542136806199790035812427 359313205209299685053718641)
          ·
            refine ⟨269484903906974763790288981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 359313205209299685053718641 269484903906974763790288981)
            ·
              refine ⟨3158026217659860513167449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 269484903906974763790288981 3158026217659860513167449)
              ·
                refine ⟨2368519663244895384875587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3158026217659860513167449 2368519663244895384875587)
                ·
                  refine ⟨3552779494867343077313381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2368519663244895384875587 3552779494867343077313381)
                  ·
                    refine ⟨666146155287626826996259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3552779494867343077313381 666146155287626826996259)
                    ·
                      rfl

theorem cell23_3891945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 2, 1, 4].length) (baseStart_3891945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3891945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3891945 prefixEnd_3891945 := by exact prefixLift 3891945
  have htrace : WordTrace (prefixWord ++ tailWord_3891945) baseStart_3891945 baseEnd_3891945 := by
    simpa [prefixWord, tailWord_3891945, baseEnd_3891945] using wordTrace_append hprefix tailTrace_3891945
  have hstable : (prefixWord ++ tailWord_3891945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891945).length < 2 ^ (prefixWord ++ tailWord_3891945).sum := by decide
  have hdescent : baseEnd_3891945 < baseStart_3891945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891971 : List Nat := [1, 1, 1, 3, 2, 2, 1, 6, 1, 5]
def baseStart_3891971 : Nat := 118140960795 + 3891971 * 2 ^ 59
def prefixEnd_3891971 : Nat := 4983230072969 + 3 ^ 40 * 3891971 * 2
def baseEnd_3891971 : Nat := 666150605453299126421219

theorem tailTrace_3891971 : CollatzResearch.WordTrace tailWord_3891971 prefixEnd_3891971 666150605453299126421219 := by
  unfold tailWord_3891971
  simp only [CollatzResearch.WordTrace]
  refine ⟨141951844183061237572779767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94634562788707491715186511 141951844183061237572779767)
  ·
    refine ⟨212927766274591856359169651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141951844183061237572779767 212927766274591856359169651)
    ·
      refine ⟨319391649411887784538754477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212927766274591856359169651 319391649411887784538754477)
      ·
        refine ⟨119771868529457919202032929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 319391649411887784538754477 119771868529457919202032929)
        ·
          refine ⟨89828901397093439401524697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119771868529457919202032929 89828901397093439401524697)
          ·
            refine ⟨67371676047820079551143523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89828901397093439401524697 67371676047820079551143523)
            ·
              refine ⟨101057514071730119326715285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67371676047820079551143523 101057514071730119326715285)
              ·
                refine ⟨4737070972112349343439779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 101057514071730119326715285 4737070972112349343439779)
                ·
                  refine ⟨7105606458168524015159669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4737070972112349343439779 7105606458168524015159669)
                  ·
                    refine ⟨666150605453299126421219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7105606458168524015159669 666150605453299126421219)
                    ·
                      rfl

theorem cell23_3891971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 6, 1, 5].length) (baseStart_3891971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3891971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3891971 prefixEnd_3891971 := by exact prefixLift 3891971
  have htrace : WordTrace (prefixWord ++ tailWord_3891971) baseStart_3891971 baseEnd_3891971 := by
    simpa [prefixWord, tailWord_3891971, baseEnd_3891971] using wordTrace_append hprefix tailTrace_3891971
  have hstable : (prefixWord ++ tailWord_3891971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891971).length < 2 ^ (prefixWord ++ tailWord_3891971).sum := by decide
  have hdescent : baseEnd_3891971 < baseStart_3891971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891978 : List Nat := [3, 1, 2, 2, 1, 2, 3, 1, 1, 5, 2]
def baseStart_3891978 : Nat := 118140960795 + 3891978 * 2 ^ 59
def prefixEnd_3891978 : Nat := 4983230072969 + 3 ^ 40 * 3891978 * 2
def baseEnd_3891978 : Nat := 1998455410724478851876125

theorem tailTrace_3891978 : CollatzResearch.WordTrace tailWord_3891978 prefixEnd_3891978 1998455410724478851876125 := by
  unfold tailWord_3891978
  simp only [CollatzResearch.WordTrace]
  refine ⟨35488024873508969442071147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94634732996023918512189725 35488024873508969442071147)
  ·
    refine ⟨53232037310263454163106721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35488024873508969442071147 53232037310263454163106721)
    ·
      refine ⟨39924027982697590622330041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53232037310263454163106721 39924027982697590622330041)
      ·
        refine ⟨29943020987023192966747531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39924027982697590622330041 29943020987023192966747531)
        ·
          refine ⟨44914531480534789450121297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29943020987023192966747531 44914531480534789450121297)
          ·
            refine ⟨33685898610401092087590973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44914531480534789450121297 33685898610401092087590973)
            ·
              refine ⟨12632211978900409532846615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33685898610401092087590973 12632211978900409532846615)
              ·
                refine ⟨18948317968350614299269923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12632211978900409532846615 18948317968350614299269923)
                ·
                  refine ⟨28422476952525921448904885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18948317968350614299269923 28422476952525921448904885)
                  ·
                    refine ⟨2664607214299305135834833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28422476952525921448904885 2664607214299305135834833)
                    ·
                      refine ⟨1998455410724478851876125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2664607214299305135834833 1998455410724478851876125)
                      ·
                        rfl

theorem cell23_3891978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 1, 5, 2].length) (baseStart_3891978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3891978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3891978 prefixEnd_3891978 := by exact prefixLift 3891978
  have htrace : WordTrace (prefixWord ++ tailWord_3891978) baseStart_3891978 baseEnd_3891978 := by
    simpa [prefixWord, tailWord_3891978, baseEnd_3891978] using wordTrace_append hprefix tailTrace_3891978
  have hstable : (prefixWord ++ tailWord_3891978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891978).length < 2 ^ (prefixWord ++ tailWord_3891978).sum := by decide
  have hdescent : baseEnd_3891978 < baseStart_3891978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891985 : List Nat := [1, 2, 2, 1, 1, 3, 3, 5, 1, 1, 3]
def baseStart_3891985 : Nat := 118140960795 + 3891985 * 2 ^ 59
def prefixEnd_3891985 : Nat := 4983230072969 + 3 ^ 40 * 3891985 * 2
def baseEnd_3891985 : Nat := 1998459005089060324488593

theorem tailTrace_3891985 : CollatzResearch.WordTrace tailWord_3891985 prefixEnd_3891985 1998459005089060324488593 := by
  unfold tailWord_3891985
  simp only [CollatzResearch.WordTrace]
  refine ⟨141952354805010517963789409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94634903203340345309192939 141952354805010517963789409)
  ·
    refine ⟨106464266103757888472842057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141952354805010517963789409 106464266103757888472842057)
    ·
      refine ⟨79848199577818416354631543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106464266103757888472842057 79848199577818416354631543)
      ·
        refine ⟨119772299366727624531947315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79848199577818416354631543 119772299366727624531947315)
        ·
          refine ⟨179658449050091436797920973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119772299366727624531947315 179658449050091436797920973)
          ·
            refine ⟨67371918393784288799220365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179658449050091436797920973 67371918393784288799220365)
            ·
              refine ⟨25264469397669108299707637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67371918393784288799220365 25264469397669108299707637)
              ·
                refine ⟨2368544006031478903097591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25264469397669108299707637 2368544006031478903097591)
                ·
                  refine ⟨3552816009047218354646387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2368544006031478903097591 3552816009047218354646387)
                  ·
                    refine ⟨5329224013570827531969581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3552816009047218354646387 5329224013570827531969581)
                    ·
                      refine ⟨1998459005089060324488593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5329224013570827531969581 1998459005089060324488593)
                      ·
                        rfl

theorem cell23_3891985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 5, 1, 1, 3].length) (baseStart_3891985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3891985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3891985 prefixEnd_3891985 := by exact prefixLift 3891985
  have htrace : WordTrace (prefixWord ++ tailWord_3891985) baseStart_3891985 baseEnd_3891985 := by
    simpa [prefixWord, tailWord_3891985, baseEnd_3891985] using wordTrace_append hprefix tailTrace_3891985
  have hstable : (prefixWord ++ tailWord_3891985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891985).length < 2 ^ (prefixWord ++ tailWord_3891985).sum := by decide
  have hdescent : baseEnd_3891985 < baseStart_3891985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892002 : List Nat := [3, 3, 1, 1, 2, 2, 2, 4, 1, 1, 3]
def baseStart_3892002 : Nat := 118140960795 + 3892002 * 2 ^ 59
def prefixEnd_3892002 : Nat := 4983230072969 + 3 ^ 40 * 3892002 * 2
def baseEnd_3892002 : Nat := 1998467734260186757976015

theorem tailTrace_3892002 : CollatzResearch.WordTrace tailWord_3892002 prefixEnd_3892002 1998467734260186757976015 := by
  unfold tailWord_3892002
  simp only [CollatzResearch.WordTrace]
  refine ⟨35488243711487232466789565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94635316563965953244772173 35488243711487232466789565)
  ·
    refine ⟨13308091391807712175046087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35488243711487232466789565 13308091391807712175046087)
    ·
      refine ⟨19962137087711568262569131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13308091391807712175046087 19962137087711568262569131)
      ·
        refine ⟨29943205631567352393853697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19962137087711568262569131 29943205631567352393853697)
        ·
          refine ⟨22457404223675514295390273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29943205631567352393853697 22457404223675514295390273)
          ·
            refine ⟨16843053167756635721542705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22457404223675514295390273 16843053167756635721542705)
            ·
              refine ⟨12632289875817476791157029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16843053167756635721542705 12632289875817476791157029)
              ·
                refine ⟨2368554351715776898341943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12632289875817476791157029 2368554351715776898341943)
                ·
                  refine ⟨3552831527573665347512915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2368554351715776898341943 3552831527573665347512915)
                  ·
                    refine ⟨5329247291360498021269373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3552831527573665347512915 5329247291360498021269373)
                    ·
                      refine ⟨1998467734260186757976015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5329247291360498021269373 1998467734260186757976015)
                      ·
                        rfl

theorem cell23_3892002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 4, 1, 1, 3].length) (baseStart_3892002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892002 prefixEnd_3892002 := by exact prefixLift 3892002
  have htrace : WordTrace (prefixWord ++ tailWord_3892002) baseStart_3892002 baseEnd_3892002 := by
    simpa [prefixWord, tailWord_3892002, baseEnd_3892002] using wordTrace_append hprefix tailTrace_3892002
  have hstable : (prefixWord ++ tailWord_3892002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892002).length < 2 ^ (prefixWord ++ tailWord_3892002).sum := by decide
  have hdescent : baseEnd_3892002 < baseStart_3892002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892022 : List Nat := [5, 1, 2, 2, 2, 1, 2, 2, 1, 5]
def baseStart_3892022 : Nat := 118140960795 + 3892022 * 2 ^ 59
def prefixEnd_3892022 : Nat := 4983230072969 + 3 ^ 40 * 3892022 * 2
def baseEnd_3892022 : Nat := 666159334624425559908641

theorem tailTrace_3892022 : CollatzResearch.WordTrace tailWord_3892022 prefixEnd_3892022 666159334624425559908641 := by
  unfold tailWord_3892022
  simp only [CollatzResearch.WordTrace]
  refine ⟨8872106519117279580180395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94635802870584315521924213 8872106519117279580180395)
  ·
    refine ⟨13308159778675919370270593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8872106519117279580180395 13308159778675919370270593)
    ·
      refine ⟨9981119834006939527702945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13308159778675919370270593 9981119834006939527702945)
      ·
        refine ⟨7485839875505204645777209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9981119834006939527702945 7485839875505204645777209)
        ·
          refine ⟨5614379906628903484332907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7485839875505204645777209 5614379906628903484332907)
          ·
            refine ⟨8421569859943355226499361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5614379906628903484332907 8421569859943355226499361)
            ·
              refine ⟨6316177394957516419874521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8421569859943355226499361 6316177394957516419874521)
              ·
                refine ⟨4737133046218137314905891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6316177394957516419874521 4737133046218137314905891)
                ·
                  refine ⟨7105699569327205972358837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4737133046218137314905891 7105699569327205972358837)
                  ·
                    refine ⟨666159334624425559908641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7105699569327205972358837 666159334624425559908641)
                    ·
                      rfl

theorem cell23_3892022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_3892022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892022 prefixEnd_3892022 := by exact prefixLift 3892022
  have htrace : WordTrace (prefixWord ++ tailWord_3892022) baseStart_3892022 baseEnd_3892022 := by
    simpa [prefixWord, tailWord_3892022, baseEnd_3892022] using wordTrace_append hprefix tailTrace_3892022
  have hstable : (prefixWord ++ tailWord_3892022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892022).length < 2 ^ (prefixWord ++ tailWord_3892022).sum := by decide
  have hdescent : baseEnd_3892022 < baseStart_3892022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892031 : List Nat := [1, 1, 2, 2, 5, 2, 1, 9]
def baseStart_3892031 : Nat := 118140960795 + 3892031 * 2 ^ 59
def prefixEnd_3892031 : Nat := 4983230072969 + 3 ^ 40 * 3892031 * 2
def baseEnd_3892031 : Nat := 74017875007376560907903

theorem tailTrace_3892031 : CollatzResearch.WordTrace tailWord_3892031 prefixEnd_3892031 74017875007376560907903 := by
  unfold tailWord_3892031
  simp only [CollatzResearch.WordTrace]
  refine ⟨141954032562843867819963947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94636021708562578546642631 141954032562843867819963947)
  ·
    refine ⟨212931048844265801729945921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141954032562843867819963947 212931048844265801729945921)
    ·
      refine ⟨159698286633199351297459441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212931048844265801729945921 159698286633199351297459441)
      ·
        refine ⟨119773714974899513473094581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159698286633199351297459441 119773714974899513473094581)
        ·
          refine ⟨11228785778896829388102617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119773714974899513473094581 11228785778896829388102617)
          ·
            refine ⟨8421589334172622041076963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11228785778896829388102617 8421589334172622041076963)
            ·
              refine ⟨12632384001258933061615445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8421589334172622041076963 12632384001258933061615445)
              ·
                refine ⟨74017875007376560907903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12632384001258933061615445 74017875007376560907903)
                ·
                  rfl

theorem cell23_3892031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 9].length) (baseStart_3892031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892031 prefixEnd_3892031 := by exact prefixLift 3892031
  have htrace : WordTrace (prefixWord ++ tailWord_3892031) baseStart_3892031 baseEnd_3892031 := by
    simpa [prefixWord, tailWord_3892031, baseEnd_3892031] using wordTrace_append hprefix tailTrace_3892031
  have hstable : (prefixWord ++ tailWord_3892031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892031).length < 2 ^ (prefixWord ++ tailWord_3892031).sum := by decide
  have hdescent : baseEnd_3892031 < baseStart_3892031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892042 : List Nat := [3, 1, 2, 1, 1, 1, 2, 7, 1, 2, 2]
def baseStart_3892042 : Nat := 118140960795 + 3892042 * 2 ^ 59
def prefixEnd_3892042 : Nat := 4983230072969 + 3 ^ 40 * 3892042 * 2
def baseEnd_3892042 : Nat := 1998488273486366601475831

theorem tailTrace_3892042 : CollatzResearch.WordTrace tailWord_3892042 prefixEnd_3892042 1998488273486366601475831 := by
  unfold tailWord_3892042
  simp only [CollatzResearch.WordTrace]
  refine ⟨35488608441451004174653595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94636289177202677799076253 35488608441451004174653595)
  ·
    refine ⟨53232912662176506261980393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35488608441451004174653595 53232912662176506261980393)
    ·
      refine ⟨39924684496632379696485295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53232912662176506261980393 39924684496632379696485295)
      ·
        refine ⟨59887026744948569544727943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39924684496632379696485295 59887026744948569544727943)
        ·
          refine ⟨89830540117422854317091915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59887026744948569544727943 89830540117422854317091915)
          ·
            refine ⟨134745810176134281475637873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89830540117422854317091915 134745810176134281475637873)
            ·
              refine ⟨101059357632100711106728405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134745810176134281475637873 101059357632100711106728405)
              ·
                refine ⟨2368578694502360416563947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 101059357632100711106728405 2368578694502360416563947)
                ·
                  refine ⟨3552868041753540624845921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2368578694502360416563947 3552868041753540624845921)
                  ·
                    refine ⟨2664651031315155468634441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3552868041753540624845921 2664651031315155468634441)
                    ·
                      refine ⟨1998488273486366601475831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2664651031315155468634441 1998488273486366601475831)
                      ·
                        rfl

theorem cell23_3892042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 7, 1, 2, 2].length) (baseStart_3892042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892042 prefixEnd_3892042 := by exact prefixLift 3892042
  have htrace : WordTrace (prefixWord ++ tailWord_3892042) baseStart_3892042 baseEnd_3892042 := by
    simpa [prefixWord, tailWord_3892042, baseEnd_3892042] using wordTrace_append hprefix tailTrace_3892042
  have hstable : (prefixWord ++ tailWord_3892042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892042).length < 2 ^ (prefixWord ++ tailWord_3892042).sum := by decide
  have hdescent : baseEnd_3892042 < baseStart_3892042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892121 : List Nat := [1, 2, 1, 2, 1, 3, 1, 5, 7]
def baseStart_3892121 : Nat := 118140960795 + 3892121 * 2 ^ 59
def prefixEnd_3892121 : Nat := 4983230072969 + 3 ^ 40 * 3892121 * 2
def baseEnd_3892121 : Nat := 222058759828674643598663

theorem tailTrace_3892121 : CollatzResearch.WordTrace tailWord_3892121 prefixEnd_3892121 222058759828674643598663 := by
  unfold tailWord_3892121
  simp only [CollatzResearch.WordTrace]
  refine ⟨141957315132517813190740217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94638210088345208793826811 141957315132517813190740217)
  ·
    refine ⟨106467986349388359893055163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141957315132517813190740217 106467986349388359893055163)
    ·
      refine ⟨159701979524082539839582745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106467986349388359893055163 159701979524082539839582745)
      ·
        refine ⟨119776484643061904879687059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159701979524082539839582745 119776484643061904879687059)
        ·
          refine ⟨179664726964592857319530589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119776484643061904879687059 179664726964592857319530589)
          ·
            refine ⟨67374272611722321494823971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179664726964592857319530589 67374272611722321494823971)
            ·
              refine ⟨101061408917583482242235957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67374272611722321494823971 101061408917583482242235957)
              ·
                refine ⟨9474507086023451460209621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101061408917583482242235957 9474507086023451460209621)
                ·
                  refine ⟨222058759828674643598663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9474507086023451460209621 222058759828674643598663)
                  ·
                    rfl

theorem cell23_3892121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 7].length) (baseStart_3892121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892121 prefixEnd_3892121 := by exact prefixLift 3892121
  have htrace : WordTrace (prefixWord ++ tailWord_3892121) baseStart_3892121 baseEnd_3892121 := by
    simpa [prefixWord, tailWord_3892121, baseEnd_3892121] using wordTrace_append hprefix tailTrace_3892121
  have hstable : (prefixWord ++ tailWord_3892121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892121).length < 2 ^ (prefixWord ++ tailWord_3892121).sum := by decide
  have hdescent : baseEnd_3892121 < baseStart_3892121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892132 : List Nat := [2, 3, 1, 2, 1, 2, 1, 5, 2, 2, 2]
def baseStart_3892132 : Nat := 118140960795 + 3892132 * 2 ^ 59
def prefixEnd_3892132 : Nat := 4983230072969 + 3 ^ 40 * 3892132 * 2
def baseEnd_3892132 : Nat := 1998534486745271249350417

theorem tailTrace_3892132 : CollatzResearch.WordTrace tailWord_3892132 prefixEnd_3892132 1998534486745271249350417 := by
  unfold tailWord_3892132
  simp only [CollatzResearch.WordTrace]
  refine ⟨70978858167738981034695325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94638477556985308046260433 70978858167738981034695325)
  ·
    refine ⟨26617071812902117888010747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70978858167738981034695325 26617071812902117888010747)
    ·
      refine ⟨39925607719353176832016121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26617071812902117888010747 39925607719353176832016121)
      ·
        refine ⟨29944205789514882624012091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39925607719353176832016121 29944205789514882624012091)
        ·
          refine ⟨44916308684272323936018137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29944205789514882624012091 44916308684272323936018137)
          ·
            refine ⟨33687231513204242952013603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44916308684272323936018137 33687231513204242952013603)
            ·
              refine ⟨50530847269806364428020405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33687231513204242952013603 50530847269806364428020405)
              ·
                refine ⟨4737266931544346665126913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50530847269806364428020405 4737266931544346665126913)
                ·
                  refine ⟨3552950198658259998845185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4737266931544346665126913 3552950198658259998845185)
                  ·
                    refine ⟨2664712648993694999133889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3552950198658259998845185 2664712648993694999133889)
                    ·
                      refine ⟨1998534486745271249350417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2664712648993694999133889 1998534486745271249350417)
                      ·
                        rfl

theorem cell23_3892132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 5, 2, 2, 2].length) (baseStart_3892132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892132 prefixEnd_3892132 := by exact prefixLift 3892132
  have htrace : WordTrace (prefixWord ++ tailWord_3892132) baseStart_3892132 baseEnd_3892132 := by
    simpa [prefixWord, tailWord_3892132, baseEnd_3892132] using wordTrace_append hprefix tailTrace_3892132
  have hstable : (prefixWord ++ tailWord_3892132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892132).length < 2 ^ (prefixWord ++ tailWord_3892132).sum := by decide
  have hdescent : baseEnd_3892132 < baseStart_3892132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892182 : List Nat := [5, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3]
def baseStart_3892182 : Nat := 118140960795 + 3892182 * 2 ^ 59
def prefixEnd_3892182 : Nat := 4983230072969 + 3 ^ 40 * 3892182 * 2
def baseEnd_3892182 : Nat := 1998560160777996053725187

theorem tailTrace_3892182 : CollatzResearch.WordTrace tailWord_3892182 prefixEnd_3892182 1998560160777996053725187 := by
  unfold tailWord_3892182
  simp only [CollatzResearch.WordTrace]
  refine ⟨8872471249081051288044425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94639693323531213739140533 8872471249081051288044425)
  ·
    refine ⟨6654353436810788466033319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8872471249081051288044425 6654353436810788466033319)
    ·
      refine ⟨9981530155216182699049979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6654353436810788466033319 9981530155216182699049979)
      ·
        refine ⟨14972295232824274048574969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9981530155216182699049979 14972295232824274048574969)
        ·
          refine ⟨11229221424618205536431227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14972295232824274048574969 11229221424618205536431227)
          ·
            refine ⟨16843832136927308304646841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11229221424618205536431227 16843832136927308304646841)
            ·
              refine ⟨12632874102695481228485131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16843832136927308304646841 12632874102695481228485131)
              ·
                refine ⟨18949311154043221842727697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12632874102695481228485131 18949311154043221842727697)
                ·
                  refine ⟨14211983365532416382045773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18949311154043221842727697 14211983365532416382045773)
                  ·
                    refine ⟨5329493762074656143267165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14211983365532416382045773 5329493762074656143267165)
                    ·
                      refine ⟨1998560160777996053725187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5329493762074656143267165 1998560160777996053725187)
                      ·
                        rfl

theorem cell23_3892182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_3892182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892182 prefixEnd_3892182 := by exact prefixLift 3892182
  have htrace : WordTrace (prefixWord ++ tailWord_3892182) baseStart_3892182 baseEnd_3892182 := by
    simpa [prefixWord, tailWord_3892182, baseEnd_3892182] using wordTrace_append hprefix tailTrace_3892182
  have hstable : (prefixWord ++ tailWord_3892182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892182).length < 2 ^ (prefixWord ++ tailWord_3892182).sum := by decide
  have hdescent : baseEnd_3892182 < baseStart_3892182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892225 : List Nat := [1, 2, 4, 1, 2, 2, 1, 1, 4, 2, 3]
def baseStart_3892225 : Nat := 118140960795 + 3892225 * 2 ^ 59
def prefixEnd_3892225 : Nat := 4983230072969 + 3 ^ 40 * 3892225 * 2
def baseEnd_3892225 : Nat := 1998582240446139385487489

theorem tailTrace_3892225 : CollatzResearch.WordTrace tailWord_3892225 prefixEnd_3892225 1998582240446139385487489 := by
  unfold tailWord_3892225
  simp only [CollatzResearch.WordTrace]
  refine ⟨141961108324141038952526129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94640738882760692635017419 141961108324141038952526129)
  ·
    refine ⟨106470831243105779214394597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141961108324141038952526129 106470831243105779214394597)
    ·
      refine ⟨19963280858082333602698987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106470831243105779214394597 19963280858082333602698987)
      ·
        refine ⟨29944921287123500404048481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19963280858082333602698987 29944921287123500404048481)
        ·
          refine ⟨22458690965342625303036361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29944921287123500404048481 22458690965342625303036361)
          ·
            refine ⟨16844018224006968977277271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22458690965342625303036361 16844018224006968977277271)
            ·
              refine ⟨25266027336010453465915907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16844018224006968977277271 25266027336010453465915907)
              ·
                refine ⟨37899041004015680198873861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25266027336010453465915907 37899041004015680198873861)
                ·
                  refine ⟨7106070188252940037288849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37899041004015680198873861 7106070188252940037288849)
                  ·
                    refine ⟨5329552641189705027966637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7106070188252940037288849 5329552641189705027966637)
                    ·
                      refine ⟨1998582240446139385487489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5329552641189705027966637 1998582240446139385487489)
                      ·
                        rfl

theorem cell23_3892225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_3892225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892225 prefixEnd_3892225 := by exact prefixLift 3892225
  have htrace : WordTrace (prefixWord ++ tailWord_3892225) baseStart_3892225 baseEnd_3892225 := by
    simpa [prefixWord, tailWord_3892225, baseEnd_3892225] using wordTrace_append hprefix tailTrace_3892225
  have hstable : (prefixWord ++ tailWord_3892225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892225).length < 2 ^ (prefixWord ++ tailWord_3892225).sum := by decide
  have hdescent : baseEnd_3892225 < baseStart_3892225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892232 : List Nat := [2, 1, 3, 2, 1, 5, 1, 1, 3, 4]
def baseStart_3892232 : Nat := 118140960795 + 3892232 * 2 ^ 59
def prefixEnd_3892232 : Nat := 4983230072969 + 3 ^ 40 * 3892232 * 2
def baseEnd_3892232 : Nat := 666195278270240286033319

theorem tailTrace_3892232 : CollatzResearch.WordTrace tailWord_3892232 prefixEnd_3892232 666195278270240286033319 := by
  unfold tailWord_3892232
  simp only [CollatzResearch.WordTrace]
  refine ⟨70980681817557839574015475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94640909090077119432020633 70980681817557839574015475)
  ·
    refine ⟨106471022726336759361023213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70980681817557839574015475 106471022726336759361023213)
    ·
      refine ⟨39926633522376284760383705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106471022726336759361023213 39926633522376284760383705)
      ·
        refine ⟨29944975141782213570287779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39926633522376284760383705 29944975141782213570287779)
        ·
          refine ⟨44917462712673320355431669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29944975141782213570287779 44917462712673320355431669)
          ·
            refine ⟨4211012129313123783321719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44917462712673320355431669 4211012129313123783321719)
            ·
              refine ⟨6316518193969685674982579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4211012129313123783321719 6316518193969685674982579)
              ·
                refine ⟨9474777290954528512473869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6316518193969685674982579 9474777290954528512473869)
                ·
                  refine ⟨3553041484107948192177701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9474777290954528512473869 3553041484107948192177701)
                  ·
                    refine ⟨666195278270240286033319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3553041484107948192177701 666195278270240286033319)
                    ·
                      rfl

theorem cell23_3892232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 3, 4].length) (baseStart_3892232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892232 prefixEnd_3892232 := by exact prefixLift 3892232
  have htrace : WordTrace (prefixWord ++ tailWord_3892232) baseStart_3892232 baseEnd_3892232 := by
    simpa [prefixWord, tailWord_3892232, baseEnd_3892232] using wordTrace_append hprefix tailTrace_3892232
  have hstable : (prefixWord ++ tailWord_3892232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892232).length < 2 ^ (prefixWord ++ tailWord_3892232).sum := by decide
  have hdescent : baseEnd_3892232 < baseStart_3892232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892245 : List Nat := [1, 3, 2, 1, 4, 2, 1, 3, 6]
def baseStart_3892245 : Nat := 118140960795 + 3892245 * 2 ^ 59
def prefixEnd_3892245 : Nat := 4983230072969 + 3 ^ 40 * 3892245 * 2
def baseEnd_3892245 : Nat := 222065834451025478581933

theorem tailTrace_3892245 : CollatzResearch.WordTrace tailWord_3892245 prefixEnd_3892245 222065834451025478581933 := by
  unfold tailWord_3892245
  simp only [CollatzResearch.WordTrace]
  refine ⟨141961837784068582368254189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94641225189379054912169459 141961837784068582368254189)
  ·
    refine ⟨53235689169025718388095321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141961837784068582368254189 53235689169025718388095321)
    ·
      refine ⟨39926766876769288791071491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53235689169025718388095321 39926766876769288791071491)
      ·
        refine ⟨59890150315153933186607237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39926766876769288791071491 59890150315153933186607237)
        ·
          refine ⟨11229403184091362472488857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59890150315153933186607237 11229403184091362472488857)
          ·
            refine ⟨8422052388068521854366643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11229403184091362472488857 8422052388068521854366643)
            ·
              refine ⟨12633078582102782781549965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8422052388068521854366643 12633078582102782781549965)
              ·
                refine ⟨4737404468288543543081237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12633078582102782781549965 4737404468288543543081237)
                ·
                  refine ⟨222065834451025478581933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4737404468288543543081237 222065834451025478581933)
                  ·
                    rfl

theorem cell23_3892245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 3, 6].length) (baseStart_3892245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892245 prefixEnd_3892245 := by exact prefixLift 3892245
  have htrace : WordTrace (prefixWord ++ tailWord_3892245) baseStart_3892245 baseEnd_3892245 := by
    simpa [prefixWord, tailWord_3892245, baseEnd_3892245] using wordTrace_append hprefix tailTrace_3892245
  have hstable : (prefixWord ++ tailWord_3892245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892245).length < 2 ^ (prefixWord ++ tailWord_3892245).sum := by decide
  have hdescent : baseEnd_3892245 < baseStart_3892245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892282 : List Nat := [3, 1, 1, 1, 3, 1, 4, 2, 2, 3, 2]
def baseStart_3892282 : Nat := 118140960795 + 3892282 * 2 ^ 59
def prefixEnd_3892282 : Nat := 4983230072969 + 3 ^ 40 * 3892282 * 2
def baseEnd_3892282 : Nat := 1998611508843445662474727

theorem tailTrace_3892282 : CollatzResearch.WordTrace tailWord_3892282 prefixEnd_3892282 1998611508843445662474727 := by
  unfold tailWord_3892282
  simp only [CollatzResearch.WordTrace]
  refine ⟨35490796821233634421837775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94642124856623025124900733 35490796821233634421837775)
  ·
    refine ⟨53236195231850451632756663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35490796821233634421837775 53236195231850451632756663)
    ·
      refine ⟨79854292847775677449134995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53236195231850451632756663 79854292847775677449134995)
      ·
        refine ⟨119781439271663516173702493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79854292847775677449134995 119781439271663516173702493)
        ·
          refine ⟨44918039726873818565138435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119781439271663516173702493 44918039726873818565138435)
          ·
            refine ⟨67377059590310727847707653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44918039726873818565138435 67377059590310727847707653)
            ·
              refine ⟨12633198673183261471445185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67377059590310727847707653 12633198673183261471445185)
              ·
                refine ⟨9474899004887446103583889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12633198673183261471445185 9474899004887446103583889)
                ·
                  refine ⟨7106174253665584577687917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9474899004887446103583889 7106174253665584577687917)
                  ·
                    refine ⟨2664815345124594216632969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7106174253665584577687917 2664815345124594216632969)
                    ·
                      refine ⟨1998611508843445662474727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2664815345124594216632969 1998611508843445662474727)
                      ·
                        rfl

theorem cell23_3892282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 2, 3, 2].length) (baseStart_3892282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892282 prefixEnd_3892282 := by exact prefixLift 3892282
  have htrace : WordTrace (prefixWord ++ tailWord_3892282) baseStart_3892282 baseEnd_3892282 := by
    simpa [prefixWord, tailWord_3892282, baseEnd_3892282] using wordTrace_append hprefix tailTrace_3892282
  have hstable : (prefixWord ++ tailWord_3892282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892282).length < 2 ^ (prefixWord ++ tailWord_3892282).sum := by decide
  have hdescent : baseEnd_3892282 < baseStart_3892282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892288 : List Nat := [2, 1, 1, 2, 2, 3, 1, 2, 3, 6]
def baseStart_3892288 : Nat := 118140960795 + 3892288 * 2 ^ 59
def prefixEnd_3892288 : Nat := 4983230072969 + 3 ^ 40 * 3892288 * 2
def baseEnd_3892288 : Nat := 666204863242457546333233

theorem tailTrace_3892288 : CollatzResearch.WordTrace tailWord_3892288 prefixEnd_3892288 666204863242457546333233 := by
  unfold tailWord_3892288
  simp only [CollatzResearch.WordTrace]
  refine ⟨70981703061456400356034759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94642270748608533808046345 70981703061456400356034759)
  ·
    refine ⟨106472554592184600534052139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70981703061456400356034759 106472554592184600534052139)
    ·
      refine ⟨159708831888276900801078209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106472554592184600534052139 159708831888276900801078209)
      ·
        refine ⟨119781623916207675600808657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159708831888276900801078209 119781623916207675600808657)
        ·
          refine ⟨89836217937155756700606493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119781623916207675600808657 89836217937155756700606493)
          ·
            refine ⟨33688581726433408762727435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89836217937155756700606493 33688581726433408762727435)
            ·
              refine ⟨50532872589650113144091153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33688581726433408762727435 50532872589650113144091153)
              ·
                refine ⟨37899654442237584858068365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50532872589650113144091153 37899654442237584858068365)
                ·
                  refine ⟨14212370415839094321775637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37899654442237584858068365 14212370415839094321775637)
                  ·
                    refine ⟨666204863242457546333233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14212370415839094321775637 666204863242457546333233)
                    ·
                      rfl

theorem cell23_3892288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 3, 6].length) (baseStart_3892288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892288 prefixEnd_3892288 := by exact prefixLift 3892288
  have htrace : WordTrace (prefixWord ++ tailWord_3892288) baseStart_3892288 baseEnd_3892288 := by
    simpa [prefixWord, tailWord_3892288, baseEnd_3892288] using wordTrace_append hprefix tailTrace_3892288
  have hstable : (prefixWord ++ tailWord_3892288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892288).length < 2 ^ (prefixWord ++ tailWord_3892288).sum := by decide
  have hdescent : baseEnd_3892288 < baseStart_3892288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892295 : List Nat := [1, 1, 4, 1, 3, 2, 1, 2, 3, 1, 4]
def baseStart_3892295 : Nat := 118140960795 + 3892295 * 2 ^ 59
def prefixEnd_3892295 : Nat := 4983230072969 + 3 ^ 40 * 3892295 * 2
def baseEnd_3892295 : Nat := 1998618184091954111612167

theorem tailTrace_3892295 : CollatzResearch.WordTrace tailWord_3892295 prefixEnd_3892295 1998618184091954111612167 := by
  unfold tailWord_3892295
  simp only [CollatzResearch.WordTrace]
  refine ⟨141963661433887440907574339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94642440955924960605049559 141963661433887440907574339)
  ·
    refine ⟨212945492150831161361361509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141963661433887440907574339 212945492150831161361361509)
    ·
      refine ⟨39927279778280842755255283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212945492150831161361361509 39927279778280842755255283)
      ·
        refine ⟨59890919667421264132882925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39927279778280842755255283 59890919667421264132882925)
        ·
          refine ⟨22459094875282974049831097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59890919667421264132882925 22459094875282974049831097)
          ·
            refine ⟨16844321156462230537373323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22459094875282974049831097 16844321156462230537373323)
            ·
              refine ⟨25266481734693345806059985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16844321156462230537373323 25266481734693345806059985)
              ·
                refine ⟨18949861301020009354544989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25266481734693345806059985 18949861301020009354544989)
                ·
                  refine ⟨7106197987882503507954371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18949861301020009354544989 7106197987882503507954371)
                  ·
                    refine ⟨10659296981823755261931557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7106197987882503507954371 10659296981823755261931557)
                    ·
                      refine ⟨1998618184091954111612167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10659296981823755261931557 1998618184091954111612167)
                      ·
                        rfl

theorem cell23_3892295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_3892295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892295 prefixEnd_3892295 := by exact prefixLift 3892295
  have htrace : WordTrace (prefixWord ++ tailWord_3892295) baseStart_3892295 baseEnd_3892295 := by
    simpa [prefixWord, tailWord_3892295, baseEnd_3892295] using wordTrace_append hprefix tailTrace_3892295
  have hstable : (prefixWord ++ tailWord_3892295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892295).length < 2 ^ (prefixWord ++ tailWord_3892295).sum := by decide
  have hdescent : baseEnd_3892295 < baseStart_3892295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892322 : List Nat := [3, 3, 2, 2, 1, 1, 2, 2, 1, 6]
def baseStart_3892322 : Nat := 118140960795 + 3892322 * 2 ^ 59
def prefixEnd_3892322 : Nat := 4983230072969 + 3 ^ 40 * 3892322 * 2
def baseEnd_3892322 : Nat := 666210682689875168658181

theorem tailTrace_3892322 : CollatzResearch.WordTrace tailWord_3892322 prefixEnd_3892322 666210682689875168658181 := by
  unfold tailWord_3892322
  simp only [CollatzResearch.WordTrace]
  refine ⟨35491161551197406129701805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94643097469859749679204813 35491161551197406129701805)
  ·
    refine ⟨13309185581699027298638177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35491161551197406129701805 13309185581699027298638177)
    ·
      refine ⟨9981889186274270473978633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13309185581699027298638177 9981889186274270473978633)
      ·
        refine ⟨7486416889705702855483975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9981889186274270473978633 7486416889705702855483975)
        ·
          refine ⟨11229625334558554283225963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7486416889705702855483975 11229625334558554283225963)
          ·
            refine ⟨16844438001837831424838945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11229625334558554283225963 16844438001837831424838945)
            ·
              refine ⟨12633328501378373568629209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16844438001837831424838945 12633328501378373568629209)
              ·
                refine ⟨9474996376033780176471907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12633328501378373568629209 9474996376033780176471907)
                ·
                  refine ⟨14212494564050670264707861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9474996376033780176471907 14212494564050670264707861)
                  ·
                    refine ⟨666210682689875168658181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14212494564050670264707861 666210682689875168658181)
                    ·
                      rfl

theorem cell23_3892322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_3892322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892322 prefixEnd_3892322 := by exact prefixLift 3892322
  have htrace : WordTrace (prefixWord ++ tailWord_3892322) baseStart_3892322 baseEnd_3892322 := by
    simpa [prefixWord, tailWord_3892322, baseEnd_3892322] using wordTrace_append hprefix tailTrace_3892322
  have hstable : (prefixWord ++ tailWord_3892322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892322).length < 2 ^ (prefixWord ++ tailWord_3892322).sum := by decide
  have hdescent : baseEnd_3892322 < baseStart_3892322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892325 : List Nat := [1, 3, 1, 3, 2, 1, 1, 4, 1, 2, 4]
def baseStart_3892325 : Nat := 118140960795 + 3892325 * 2 ^ 59
def prefixEnd_3892325 : Nat := 4983230072969 + 3 ^ 40 * 3892325 * 2
def baseEnd_3892325 : Nat := 1998633588511588994237029

theorem tailTrace_3892325 : CollatzResearch.WordTrace tailWord_3892325 prefixEnd_3892325 1998633588511588994237029 := by
  unfold tailWord_3892325
  simp only [CollatzResearch.WordTrace]
  refine ⟨141964755623778756031166429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94643170415852504020777619 141964755623778756031166429)
  ·
    refine ⟨53236783358917033511687411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141964755623778756031166429 53236783358917033511687411)
    ·
      refine ⟨79855175038375550267531117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53236783358917033511687411 79855175038375550267531117)
      ·
        refine ⟨29945690639390831350324169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79855175038375550267531117 29945690639390831350324169)
        ·
          refine ⟨22459267979543123512743127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29945690639390831350324169 22459267979543123512743127)
          ·
            refine ⟨33688901969314685269114691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22459267979543123512743127 33688901969314685269114691)
            ·
              refine ⟨50533352953972027903672037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33688901969314685269114691 50533352953972027903672037)
              ·
                refine ⟨9475003678869755231938507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50533352953972027903672037 9475003678869755231938507)
                ·
                  refine ⟨14212505518304632847907761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9475003678869755231938507 14212505518304632847907761)
                  ·
                    refine ⟨10659379138728474635930821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14212505518304632847907761 10659379138728474635930821)
                    ·
                      refine ⟨1998633588511588994237029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10659379138728474635930821 1998633588511588994237029)
                      ·
                        rfl

theorem cell23_3892325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_3892325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892325 prefixEnd_3892325 := by exact prefixLift 3892325
  have htrace : WordTrace (prefixWord ++ tailWord_3892325) baseStart_3892325 baseEnd_3892325 := by
    simpa [prefixWord, tailWord_3892325, baseEnd_3892325] using wordTrace_append hprefix tailTrace_3892325
  have hstable : (prefixWord ++ tailWord_3892325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892325).length < 2 ^ (prefixWord ++ tailWord_3892325).sum := by decide
  have hdescent : baseEnd_3892325 < baseStart_3892325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892329 : List Nat := [1, 2, 1, 1, 1, 8, 2, 1, 1, 1, 4]
def baseStart_3892329 : Nat := 118140960795 + 3892329 * 2 ^ 59
def prefixEnd_3892329 : Nat := 4983230072969 + 3 ^ 40 * 3892329 * 2
def baseEnd_3892329 : Nat := 1998635642434206978587011

theorem tailTrace_3892329 : CollatzResearch.WordTrace tailWord_3892329 prefixEnd_3892329 1998635642434206978587011 := by
  unfold tailWord_3892329
  simp only [CollatzResearch.WordTrace]
  refine ⟨141964901515764264714312041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94643267677176176476208027 141964901515764264714312041)
  ·
    refine ⟨106473676136823198535734031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141964901515764264714312041 106473676136823198535734031)
    ·
      refine ⟨159710514205234797803601047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106473676136823198535734031 159710514205234797803601047)
      ·
        refine ⟨239565771307852196705401571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159710514205234797803601047 239565771307852196705401571)
        ·
          refine ⟨359348656961778295058102357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239565771307852196705401571 359348656961778295058102357)
          ·
            refine ⟨4211117073770839395212137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 359348656961778295058102357 4211117073770839395212137)
            ·
              refine ⟨3158337805328129546409103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4211117073770839395212137 3158337805328129546409103)
              ·
                refine ⟨4737506707992194319613655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3158337805328129546409103 4737506707992194319613655)
                ·
                  refine ⟨7106260061988291479420483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4737506707992194319613655 7106260061988291479420483)
                  ·
                    refine ⟨10659390092982437219130725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7106260061988291479420483 10659390092982437219130725)
                    ·
                      refine ⟨1998635642434206978587011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10659390092982437219130725 1998635642434206978587011)
                      ·
                        rfl

theorem cell23_3892329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 1, 1, 1, 4].length) (baseStart_3892329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892329 prefixEnd_3892329 := by exact prefixLift 3892329
  have htrace : WordTrace (prefixWord ++ tailWord_3892329) baseStart_3892329 baseEnd_3892329 := by
    simpa [prefixWord, tailWord_3892329, baseEnd_3892329] using wordTrace_append hprefix tailTrace_3892329
  have hstable : (prefixWord ++ tailWord_3892329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892329).length < 2 ^ (prefixWord ++ tailWord_3892329).sum := by decide
  have hdescent : baseEnd_3892329 < baseStart_3892329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892332 : List Nat := [2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 3]
def baseStart_3892332 : Nat := 118140960795 + 3892332 * 2 ^ 59
def prefixEnd_3892332 : Nat := 4983230072969 + 3 ^ 40 * 3892332 * 2
def baseEnd_3892332 : Nat := 1998637182876170466849497

theorem tailTrace_3892332 : CollatzResearch.WordTrace tailWord_3892332 prefixEnd_3892332 1998637182876170466849497 := by
  unfold tailWord_3892332
  simp only [CollatzResearch.WordTrace]
  refine ⟨70982505467376698113335625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94643340623168930817780833 70982505467376698113335625)
  ·
    refine ⟨53236879100532523585001719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70982505467376698113335625 53236879100532523585001719)
    ·
      refine ⟨79855318650798785377502579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53236879100532523585001719 79855318650798785377502579)
      ·
        refine ⟨119782977976198178066253869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79855318650798785377502579 119782977976198178066253869)
        ·
          refine ⟨44918616741074316774845201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119782977976198178066253869 44918616741074316774845201)
          ·
            refine ⟨33688962555805737581133901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44918616741074316774845201 33688962555805737581133901)
            ·
              refine ⟨12633360958427151592925213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33688962555805737581133901 12633360958427151592925213)
              ·
                refine ⟨4737510359410181847346955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12633360958427151592925213 4737510359410181847346955)
                ·
                  refine ⟨7106265539115272771020433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4737510359410181847346955 7106265539115272771020433)
                  ·
                    refine ⟨5329699154336454578265325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7106265539115272771020433 5329699154336454578265325)
                    ·
                      refine ⟨1998637182876170466849497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5329699154336454578265325 1998637182876170466849497)
                      ·
                        rfl

theorem cell23_3892332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 3].length) (baseStart_3892332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892332 prefixEnd_3892332 := by exact prefixLift 3892332
  have htrace : WordTrace (prefixWord ++ tailWord_3892332) baseStart_3892332 baseEnd_3892332 := by
    simpa [prefixWord, tailWord_3892332, baseEnd_3892332] using wordTrace_append hprefix tailTrace_3892332
  have hstable : (prefixWord ++ tailWord_3892332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892332).length < 2 ^ (prefixWord ++ tailWord_3892332).sum := by decide
  have hdescent : baseEnd_3892332 < baseStart_3892332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892368 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 8]
def baseStart_3892368 : Nat := 118140960795 + 3892368 * 2 ^ 59
def prefixEnd_3892368 : Nat := 4983230072969 + 3 ^ 40 * 3892368 * 2
def baseEnd_3892368 : Nat := 1998655668179732325999331

theorem tailTrace_3892368 : CollatzResearch.WordTrace tailWord_3892368 prefixEnd_3892368 1998655668179732325999331 := by
  unfold tailWord_3892368
  simp only [CollatzResearch.WordTrace]
  refine ⟨70983161981311487187490879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94644215975081982916654505 70983161981311487187490879)
  ·
    refine ⟨106474742971967230781236319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70983161981311487187490879 106474742971967230781236319)
    ·
      refine ⟨159712114457950846171854479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106474742971967230781236319 159712114457950846171854479)
      ·
        refine ⟨239568171686926269257781719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159712114457950846171854479 239568171686926269257781719)
        ·
          refine ⟨359352257530389403886672579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239568171686926269257781719 359352257530389403886672579)
          ·
            refine ⟨539028386295584105830008869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359352257530389403886672579 539028386295584105830008869)
            ·
              refine ⟨101067822430422019843126663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 539028386295584105830008869 101067822430422019843126663)
              ·
                refine ⟨151601733645633029764689995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101067822430422019843126663 151601733645633029764689995)
                ·
                  refine ⟨227402600468449544647034993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151601733645633029764689995 227402600468449544647034993)
                  ·
                    refine ⟨170551950351337158485276245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 227402600468449544647034993 170551950351337158485276245)
                    ·
                      refine ⟨1998655668179732325999331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 170551950351337158485276245 1998655668179732325999331)
                      ·
                        rfl

theorem cell23_3892368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 8].length) (baseStart_3892368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892368 prefixEnd_3892368 := by exact prefixLift 3892368
  have htrace : WordTrace (prefixWord ++ tailWord_3892368) baseStart_3892368 baseEnd_3892368 := by
    simpa [prefixWord, tailWord_3892368, baseEnd_3892368] using wordTrace_append hprefix tailTrace_3892368
  have hstable : (prefixWord ++ tailWord_3892368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892368).length < 2 ^ (prefixWord ++ tailWord_3892368).sum := by decide
  have hdescent : baseEnd_3892368 < baseStart_3892368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892375 : List Nat := [1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 5]
def baseStart_3892375 : Nat := 118140960795 + 3892375 * 2 ^ 59
def prefixEnd_3892375 : Nat := 4983230072969 + 3 ^ 40 * 3892375 * 2
def baseEnd_3892375 : Nat := 1998659262544313798611799

theorem tailTrace_3892375 : CollatzResearch.WordTrace tailWord_3892375 prefixEnd_3892375 1998659262544313798611799 := by
  unfold tailWord_3892375
  simp only [CollatzResearch.WordTrace]
  refine ⟨141966579273597614570486579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94644386182398409713657719 141966579273597614570486579)
  ·
    refine ⟨212949868910396421855729869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141966579273597614570486579 212949868910396421855729869)
    ·
      refine ⟨79856200841398658195898701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212949868910396421855729869 79856200841398658195898701)
      ·
        refine ⟨29946075315524496823462013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79856200841398658195898701 29946075315524496823462013)
        ·
          refine ⟨11229778243321686308798255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29946075315524496823462013 11229778243321686308798255)
          ·
            refine ⟨16844667364982529463197383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11229778243321686308798255 16844667364982529463197383)
            ·
              refine ⟨25267001047473794194796075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16844667364982529463197383 25267001047473794194796075)
              ·
                refine ⟨37900501571210691292194113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25267001047473794194796075 37900501571210691292194113)
                ·
                  refine ⟨28425376178408018469145585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37900501571210691292194113 28425376178408018469145585)
                  ·
                    refine ⟨21319032133806013851859189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28425376178408018469145585 21319032133806013851859189)
                    ·
                      refine ⟨1998659262544313798611799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21319032133806013851859189 1998659262544313798611799)
                      ·
                        rfl

theorem cell23_3892375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_3892375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892375 prefixEnd_3892375 := by exact prefixLift 3892375
  have htrace : WordTrace (prefixWord ++ tailWord_3892375) baseStart_3892375 baseEnd_3892375 := by
    simpa [prefixWord, tailWord_3892375, baseEnd_3892375] using wordTrace_append hprefix tailTrace_3892375
  have hstable : (prefixWord ++ tailWord_3892375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892375).length < 2 ^ (prefixWord ++ tailWord_3892375).sum := by decide
  have hdescent : baseEnd_3892375 < baseStart_3892375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892389 : List Nat := [1, 3, 1, 2, 1, 4, 2, 3, 1, 3, 2]
def baseStart_3892389 : Nat := 118140960795 + 3892389 * 2 ^ 59
def prefixEnd_3892389 : Nat := 4983230072969 + 3 ^ 40 * 3892389 * 2
def baseEnd_3892389 : Nat := 1998666451273476743836735

theorem tailTrace_3892389 : CollatzResearch.WordTrace tailWord_3892389 prefixEnd_3892389 1998666451273476743836735 := by
  unfold tailWord_3892389
  simp only [CollatzResearch.WordTrace]
  refine ⟨141967089895546894961496221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94644726597031263307664147 141967089895546894961496221)
  ·
    refine ⟨53237658710830085610561083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141967089895546894961496221 53237658710830085610561083)
    ·
      refine ⟨79856488066245128415841625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53237658710830085610561083 79856488066245128415841625)
      ·
        refine ⟨59892366049683846311881219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79856488066245128415841625 59892366049683846311881219)
        ·
          refine ⟨89838549074525769467821829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59892366049683846311881219 89838549074525769467821829)
          ·
            refine ⟨16844727951473581775216593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89838549074525769467821829 16844727951473581775216593)
            ·
              refine ⟨12633545963605186331412445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16844727951473581775216593 12633545963605186331412445)
              ·
                refine ⟨4737579736351944874279667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12633545963605186331412445 4737579736351944874279667)
                ·
                  refine ⟨7106369604527917311419501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4737579736351944874279667 7106369604527917311419501)
                  ·
                    refine ⟨2664888601697968991782313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7106369604527917311419501 2664888601697968991782313)
                    ·
                      refine ⟨1998666451273476743836735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2664888601697968991782313 1998666451273476743836735)
                      ·
                        rfl

theorem cell23_3892389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 3, 1, 3, 2].length) (baseStart_3892389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892389 prefixEnd_3892389 := by exact prefixLift 3892389
  have htrace : WordTrace (prefixWord ++ tailWord_3892389) baseStart_3892389 baseEnd_3892389 := by
    simpa [prefixWord, tailWord_3892389, baseEnd_3892389] using wordTrace_append hprefix tailTrace_3892389
  have hstable : (prefixWord ++ tailWord_3892389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892389).length < 2 ^ (prefixWord ++ tailWord_3892389).sum := by decide
  have hdescent : baseEnd_3892389 < baseStart_3892389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892415 : List Nat := [1, 1, 2, 2, 2, 2, 2, 3, 2, 2, 4]
def baseStart_3892415 : Nat := 118140960795 + 3892415 * 2 ^ 59
def prefixEnd_3892415 : Nat := 4983230072969 + 3 ^ 40 * 3892415 * 2
def baseEnd_3892415 : Nat := 1998679801770493642111615

theorem tailTrace_3892415 : CollatzResearch.WordTrace tailWord_3892415 prefixEnd_3892415 1998679801770493642111615 := by
  unfold tailWord_3892415
  simp only [CollatzResearch.WordTrace]
  refine ⟨141968038193452701401942699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94645358795635134267961799 141968038193452701401942699)
  ·
    refine ⟨212952057290179052102914049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141968038193452701401942699 212952057290179052102914049)
    ·
      refine ⟨159714042967634289077185537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212952057290179052102914049 159714042967634289077185537)
      ·
        refine ⟨119785532225725716807889153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159714042967634289077185537 119785532225725716807889153)
        ·
          refine ⟨89839149169294287605916865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119785532225725716807889153 89839149169294287605916865)
          ·
            refine ⟨67379361876970715704437649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89839149169294287605916865 67379361876970715704437649)
            ·
              refine ⟨50534521407728036778328237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67379361876970715704437649 50534521407728036778328237)
              ·
                refine ⟨18950445527898013791873089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50534521407728036778328237 18950445527898013791873089)
                ·
                  refine ⟨14212834145923510343904817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18950445527898013791873089 14212834145923510343904817)
                  ·
                    refine ⟨10659625609442632757928613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14212834145923510343904817 10659625609442632757928613)
                    ·
                      refine ⟨1998679801770493642111615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10659625609442632757928613 1998679801770493642111615)
                      ·
                        rfl

theorem cell23_3892415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 2, 4].length) (baseStart_3892415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892415 prefixEnd_3892415 := by exact prefixLift 3892415
  have htrace : WordTrace (prefixWord ++ tailWord_3892415) baseStart_3892415 baseEnd_3892415 := by
    simpa [prefixWord, tailWord_3892415, baseEnd_3892415] using wordTrace_append hprefix tailTrace_3892415
  have hstable : (prefixWord ++ tailWord_3892415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892415).length < 2 ^ (prefixWord ++ tailWord_3892415).sum := by decide
  have hdescent : baseEnd_3892415 < baseStart_3892415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892435 : List Nat := [1, 1, 1, 2, 1, 1, 1, 6, 1, 5, 3]
def baseStart_3892435 : Nat := 118140960795 + 3892435 * 2 ^ 59
def prefixEnd_3892435 : Nat := 4983230072969 + 3 ^ 40 * 3892435 * 2
def baseEnd_3892435 : Nat := 1998690071383583563861523

theorem tailTrace_3892435 : CollatzResearch.WordTrace tailWord_3892435 prefixEnd_3892435 1998690071383583563861523 := by
  unfold tailWord_3892435
  simp only [CollatzResearch.WordTrace]
  refine ⟨141968767653380244817670759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94645845102253496545113839 141968767653380244817670759)
  ·
    refine ⟨212953151480070367226506139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141968767653380244817670759 212953151480070367226506139)
    ·
      refine ⟨319429727220105550839759209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212953151480070367226506139 319429727220105550839759209)
      ·
        refine ⟨239572295415079163129819407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319429727220105550839759209 239572295415079163129819407)
        ·
          refine ⟨359358443122618744694729111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239572295415079163129819407 359358443122618744694729111)
          ·
            refine ⟨539037664683928117042093667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359358443122618744694729111 539037664683928117042093667)
            ·
              refine ⟨808556497025892175563140501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 539037664683928117042093667 808556497025892175563140501)
              ·
                refine ⟨37901085798088695729522211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 808556497025892175563140501 37901085798088695729522211)
                ·
                  refine ⟨56851628697133043594283317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37901085798088695729522211 56851628697133043594283317)
                  ·
                    refine ⟨5329840190356222836964061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56851628697133043594283317 5329840190356222836964061)
                    ·
                      refine ⟨1998690071383583563861523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5329840190356222836964061 1998690071383583563861523)
                      ·
                        rfl

theorem cell23_3892435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 5, 3].length) (baseStart_3892435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892435 prefixEnd_3892435 := by exact prefixLift 3892435
  have htrace : WordTrace (prefixWord ++ tailWord_3892435) baseStart_3892435 baseEnd_3892435 := by
    simpa [prefixWord, tailWord_3892435, baseEnd_3892435] using wordTrace_append hprefix tailTrace_3892435
  have hstable : (prefixWord ++ tailWord_3892435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892435).length < 2 ^ (prefixWord ++ tailWord_3892435).sum := by decide
  have hdescent : baseEnd_3892435 < baseStart_3892435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892442 : List Nat := [3, 1, 1, 2, 2, 1, 1, 7, 5]
def baseStart_3892442 : Nat := 118140960795 + 3892442 * 2 ^ 59
def prefixEnd_3892442 : Nat := 4983230072969 + 3 ^ 40 * 3892442 * 2
def baseEnd_3892442 : Nat := 222077073972018337385999

theorem tailTrace_3892442 : CollatzResearch.WordTrace tailWord_3892442 prefixEnd_3892442 222077073972018337385999 := by
  unfold tailWord_3892442
  simp only [CollatzResearch.WordTrace]
  refine ⟨35492255741088721253293895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94646015309569923342117053 35492255741088721253293895)
  ·
    refine ⟨53238383611633081879940843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35492255741088721253293895 53238383611633081879940843)
    ·
      refine ⟨79857575417449622819911265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53238383611633081879940843 79857575417449622819911265)
      ·
        refine ⟨59893181563087217114933449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79857575417449622819911265 59893181563087217114933449)
        ·
          refine ⟨44919886172315412836200087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59893181563087217114933449 44919886172315412836200087)
          ·
            refine ⟨67379829258473119254300131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44919886172315412836200087 67379829258473119254300131)
            ·
              refine ⟨101069743887709678881450197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67379829258473119254300131 101069743887709678881450197)
              ·
                refine ⟨2368822122368195598783989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 101069743887709678881450197 2368822122368195598783989)
                ·
                  refine ⟨222077073972018337385999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2368822122368195598783989 222077073972018337385999)
                  ·
                    rfl

theorem cell23_3892442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 7, 5].length) (baseStart_3892442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892442 prefixEnd_3892442 := by exact prefixLift 3892442
  have htrace : WordTrace (prefixWord ++ tailWord_3892442) baseStart_3892442 baseEnd_3892442 := by
    simpa [prefixWord, tailWord_3892442, baseEnd_3892442] using wordTrace_append hprefix tailTrace_3892442
  have hstable : (prefixWord ++ tailWord_3892442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892442).length < 2 ^ (prefixWord ++ tailWord_3892442).sum := by decide
  have hdescent : baseEnd_3892442 < baseStart_3892442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892453 : List Nat := [1, 3, 1, 4, 3, 1, 2, 2, 2, 2, 2]
def baseStart_3892453 : Nat := 118140960795 + 3892453 * 2 ^ 59
def prefixEnd_3892453 : Nat := 4983230072969 + 3 ^ 40 * 3892453 * 2
def baseEnd_3892453 : Nat := 1998699314035364493436441

theorem tailTrace_3892453 : CollatzResearch.WordTrace tailWord_3892453 prefixEnd_3892453 1998699314035364493436441 := by
  unfold tailWord_3892453
  simp only [CollatzResearch.WordTrace]
  refine ⟨141969424167315033891826013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94646282778210022594550675 141969424167315033891826013)
  ·
    refine ⟨53238534062743137709434755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141969424167315033891826013 53238534062743137709434755)
    ·
      refine ⟨79857801094114706564152133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53238534062743137709434755 79857801094114706564152133)
      ·
        refine ⟨14973337705146507480778525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79857801094114706564152133 14973337705146507480778525)
        ·
          refine ⟨5615001639429940305291947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14973337705146507480778525 5615001639429940305291947)
          ·
            refine ⟨8422502459144910457937921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5615001639429940305291947 8422502459144910457937921)
            ·
              refine ⟨6316876844358682843453441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8422502459144910457937921 6316876844358682843453441)
              ·
                refine ⟨4737657633269012132590081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6316876844358682843453441 4737657633269012132590081)
                ·
                  refine ⟨3553243224951759099442561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4737657633269012132590081 3553243224951759099442561)
                  ·
                    refine ⟨2664932418713819324581921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3553243224951759099442561 2664932418713819324581921)
                    ·
                      refine ⟨1998699314035364493436441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2664932418713819324581921 1998699314035364493436441)
                      ·
                        rfl

theorem cell23_3892453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_3892453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892453 prefixEnd_3892453 := by exact prefixLift 3892453
  have htrace : WordTrace (prefixWord ++ tailWord_3892453) baseStart_3892453 baseEnd_3892453 := by
    simpa [prefixWord, tailWord_3892453, baseEnd_3892453] using wordTrace_append hprefix tailTrace_3892453
  have hstable : (prefixWord ++ tailWord_3892453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892453).length < 2 ^ (prefixWord ++ tailWord_3892453).sum := by decide
  have hdescent : baseEnd_3892453 < baseStart_3892453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892459 : List Nat := [1, 1, 1, 1, 2, 6, 4, 2, 5]
def baseStart_3892459 : Nat := 118140960795 + 3892459 * 2 ^ 59
def prefixEnd_3892459 : Nat := 4983230072969 + 3 ^ 40 * 3892459 * 2
def baseEnd_3892459 : Nat := 222078043879921274440157

theorem tailTrace_3892459 : CollatzResearch.WordTrace tailWord_3892459 prefixEnd_3892459 222078043879921274440157 := by
  unfold tailWord_3892459
  simp only [CollatzResearch.WordTrace]
  refine ⟨141969643005293296916544431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94646428670195531277696287 141969643005293296916544431)
  ·
    refine ⟨212954464507939945374816647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141969643005293296916544431 212954464507939945374816647)
    ·
      refine ⟨319431696761909918062224971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212954464507939945374816647 319431696761909918062224971)
      ·
        refine ⟨479147545142864877093337457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319431696761909918062224971 479147545142864877093337457)
        ·
          refine ⟨359360658857148657820003093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 479147545142864877093337457 359360658857148657820003093)
          ·
            refine ⟨16845030883928843335312645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 359360658857148657820003093 16845030883928843335312645)
            ·
              refine ⟨3158443290736658125371121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16845030883928843335312645 3158443290736658125371121)
              ·
                refine ⟨2368832468052493594028341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3158443290736658125371121 2368832468052493594028341)
                ·
                  refine ⟨222078043879921274440157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2368832468052493594028341 222078043879921274440157)
                  ·
                    rfl

theorem cell23_3892459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 2, 5].length) (baseStart_3892459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892459 prefixEnd_3892459 := by exact prefixLift 3892459
  have htrace : WordTrace (prefixWord ++ tailWord_3892459) baseStart_3892459 baseEnd_3892459 := by
    simpa [prefixWord, tailWord_3892459, baseEnd_3892459] using wordTrace_append hprefix tailTrace_3892459
  have hstable : (prefixWord ++ tailWord_3892459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892459).length < 2 ^ (prefixWord ++ tailWord_3892459).sum := by decide
  have hdescent : baseEnd_3892459 < baseStart_3892459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892492 : List Nat := [2, 2, 1, 2, 2, 4, 1, 1, 1, 3, 4]
def baseStart_3892492 : Nat := 118140960795 + 3892492 * 2 ^ 59
def prefixEnd_3892492 : Nat := 4983230072969 + 3 ^ 40 * 3892492 * 2
def baseEnd_3892492 : Nat := 1998719339780889840848761

theorem tailTrace_3892492 : CollatzResearch.WordTrace tailWord_3892492 prefixEnd_3892492 1998719339780889840848761 := by
  unfold tailWord_3892492
  simp only [CollatzResearch.WordTrace]
  refine ⟨70985423307086871776247865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94647231076115829034997153 70985423307086871776247865)
  ·
    refine ⟨53239067480315153832185899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70985423307086871776247865 53239067480315153832185899)
    ·
      refine ⟨79858601220472730748278849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53239067480315153832185899 79858601220472730748278849)
      ·
        refine ⟨59893950915354548061209137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79858601220472730748278849 59893950915354548061209137)
        ·
          refine ⟨44920463186515911045906853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59893950915354548061209137 44920463186515911045906853)
          ·
            refine ⟨8422586847471733321107535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44920463186515911045906853 8422586847471733321107535)
            ·
              refine ⟨12633880271207599981661303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8422586847471733321107535 12633880271207599981661303)
              ·
                refine ⟨18950820406811399972491955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12633880271207599981661303 18950820406811399972491955)
                ·
                  refine ⟨28426230610217099958737933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18950820406811399972491955 28426230610217099958737933)
                  ·
                    refine ⟨10659836478831412484526725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28426230610217099958737933 10659836478831412484526725)
                    ·
                      refine ⟨1998719339780889840848761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10659836478831412484526725 1998719339780889840848761)
                      ·
                        rfl

theorem cell23_3892492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_3892492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892492 prefixEnd_3892492 := by exact prefixLift 3892492
  have htrace : WordTrace (prefixWord ++ tailWord_3892492) baseStart_3892492 baseEnd_3892492 := by
    simpa [prefixWord, tailWord_3892492, baseEnd_3892492] using wordTrace_append hprefix tailTrace_3892492
  have hstable : (prefixWord ++ tailWord_3892492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892492).length < 2 ^ (prefixWord ++ tailWord_3892492).sum := by decide
  have hdescent : baseEnd_3892492 < baseStart_3892492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892505 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 3, 6, 4]
def baseStart_3892505 : Nat := 118140960795 + 3892505 * 2 ^ 59
def prefixEnd_3892505 : Nat := 4983230072969 + 3 ^ 40 * 3892505 * 2
def baseEnd_3892505 : Nat := 1998726015029398289986201

theorem tailTrace_3892505 : CollatzResearch.WordTrace tailWord_3892505 prefixEnd_3892505 1998726015029398289986201 := by
  unfold tailWord_3892505
  simp only [CollatzResearch.WordTrace]
  refine ⟨141971320763126646772718969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94647547175417764515145979 141971320763126646772718969)
  ·
    refine ⟨106478490572344985079539227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141971320763126646772718969 106478490572344985079539227)
    ·
      refine ⟨159717735858517477619308841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106478490572344985079539227 159717735858517477619308841)
      ·
        refine ⟨119788301893888108214481631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159717735858517477619308841 119788301893888108214481631)
        ·
          refine ⟨179682452840832162321722447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119788301893888108214481631 179682452840832162321722447)
          ·
            refine ⟨269523679261248243482583671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179682452840832162321722447 269523679261248243482583671)
            ·
              refine ⟨404285518891872365223875507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269523679261248243482583671 404285518891872365223875507)
              ·
                refine ⟨606428278337808547835813261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 404285518891872365223875507 606428278337808547835813261)
                ·
                  refine ⟨227410604376678205438429973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 606428278337808547835813261 227410604376678205438429973)
                  ·
                    refine ⟨10659872080156790879926405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 227410604376678205438429973 10659872080156790879926405)
                    ·
                      refine ⟨1998726015029398289986201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10659872080156790879926405 1998726015029398289986201)
                      ·
                        rfl

theorem cell23_3892505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 6, 4].length) (baseStart_3892505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892505 prefixEnd_3892505 := by exact prefixLift 3892505
  have htrace : WordTrace (prefixWord ++ tailWord_3892505) baseStart_3892505 baseEnd_3892505 := by
    simpa [prefixWord, tailWord_3892505, baseEnd_3892505] using wordTrace_append hprefix tailTrace_3892505
  have hstable : (prefixWord ++ tailWord_3892505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892505).length < 2 ^ (prefixWord ++ tailWord_3892505).sum := by decide
  have hdescent : baseEnd_3892505 < baseStart_3892505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892555 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 7]
def baseStart_3892555 : Nat := 118140960795 + 3892555 * 2 ^ 59
def prefixEnd_3892555 : Nat := 4983230072969 + 3 ^ 40 * 3892555 * 2
def baseEnd_3892555 : Nat := 1998751689062123094360971

theorem tailTrace_3892555 : CollatzResearch.WordTrace tailWord_3892555 prefixEnd_3892555 1998751689062123094360971 := by
  unfold tailWord_3892555
  simp only [CollatzResearch.WordTrace]
  refine ⟨141973144412945505312039119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94648762941963670208026079 141973144412945505312039119)
  ·
    refine ⟨212959716619418257968058679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141973144412945505312039119 212959716619418257968058679)
    ·
      refine ⟨319439574929127386952088019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212959716619418257968058679 319439574929127386952088019)
      ·
        refine ⟨479159362393691080428132029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319439574929127386952088019 479159362393691080428132029)
        ·
          refine ⟨179684760897634155160549511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 479159362393691080428132029 179684760897634155160549511)
          ·
            refine ⟨269527141346451232740824267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179684760897634155160549511 269527141346451232740824267)
            ·
              refine ⟨404290712019676849111236401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269527141346451232740824267 404290712019676849111236401)
              ·
                refine ⟨303218034014757636833427301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 404290712019676849111236401 303218034014757636833427301)
                ·
                  refine ⟨56853381377767056906267619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 303218034014757636833427301 56853381377767056906267619)
                  ·
                    refine ⟨85280072066650585359401429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56853381377767056906267619 85280072066650585359401429)
                    ·
                      refine ⟨1998751689062123094360971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 85280072066650585359401429 1998751689062123094360971)
                      ·
                        rfl

theorem cell23_3892555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 7].length) (baseStart_3892555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892555 prefixEnd_3892555 := by exact prefixLift 3892555
  have htrace : WordTrace (prefixWord ++ tailWord_3892555) baseStart_3892555 baseEnd_3892555 := by
    simpa [prefixWord, tailWord_3892555, baseEnd_3892555] using wordTrace_append hprefix tailTrace_3892555
  have hstable : (prefixWord ++ tailWord_3892555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892555).length < 2 ^ (prefixWord ++ tailWord_3892555).sum := by decide
  have hdescent : baseEnd_3892555 < baseStart_3892555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892562 : List Nat := [3, 2, 2, 1, 1, 1, 1, 2, 5, 5]
def baseStart_3892562 : Nat := 118140960795 + 3892562 * 2 ^ 59
def prefixEnd_3892562 : Nat := 4983230072969 + 3 ^ 40 * 3892562 * 2
def baseEnd_3892562 : Nat := 666251761142234855657813

theorem tailTrace_3892562 : CollatzResearch.WordTrace tailWord_3892562 prefixEnd_3892562 666251761142234855657813 := by
  unfold tailWord_3892562
  simp only [CollatzResearch.WordTrace]
  refine ⟨35493349930980036376885985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94648933149280097005029293 35493349930980036376885985)
  ·
    refine ⟨26620012448235027282664489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35493349930980036376885985 26620012448235027282664489)
    ·
      refine ⟨19965009336176270461998367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26620012448235027282664489 19965009336176270461998367)
      ·
        refine ⟨29947514004264405692997551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19965009336176270461998367 29947514004264405692997551)
        ·
          refine ⟨44921271006396608539496327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29947514004264405692997551 44921271006396608539496327)
          ·
            refine ⟨67381906509594912809244491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44921271006396608539496327 67381906509594912809244491)
            ·
              refine ⟨101072859764392369213866737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67381906509594912809244491 101072859764392369213866737)
              ·
                refine ⟨75804644823294276910400053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101072859764392369213866737 75804644823294276910400053)
                ·
                  refine ⟨7106685452183838460350005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75804644823294276910400053 7106685452183838460350005)
                  ·
                    refine ⟨666251761142234855657813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7106685452183838460350005 666251761142234855657813)
                    ·
                      rfl

theorem cell23_3892562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_3892562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892562 prefixEnd_3892562 := by exact prefixLift 3892562
  have htrace : WordTrace (prefixWord ++ tailWord_3892562) baseStart_3892562 baseEnd_3892562 := by
    simpa [prefixWord, tailWord_3892562, baseEnd_3892562] using wordTrace_append hprefix tailTrace_3892562
  have hstable : (prefixWord ++ tailWord_3892562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892562).length < 2 ^ (prefixWord ++ tailWord_3892562).sum := by decide
  have hdescent : baseEnd_3892562 < baseStart_3892562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892569 : List Nat := [1, 2, 1, 2, 2, 2, 3, 1, 4, 3, 2]
def baseStart_3892569 : Nat := 118140960795 + 3892569 * 2 ^ 59
def prefixEnd_3892569 : Nat := 4983230072969 + 3 ^ 40 * 3892569 * 2
def baseEnd_3892569 : Nat := 1998758877791286039585907

theorem tailTrace_3892569 : CollatzResearch.WordTrace tailWord_3892569 prefixEnd_3892569 1998758877791286039585907 := by
  unfold tailWord_3892569
  simp only [CollatzResearch.WordTrace]
  refine ⟨141973655034894785703048761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94649103356596523802032507 141973655034894785703048761)
  ·
    refine ⟨106480241276171089277286571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141973655034894785703048761 106480241276171089277286571)
    ·
      refine ⟨159720361914256633915929857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106480241276171089277286571 159720361914256633915929857)
      ·
        refine ⟨119790271435692475436947393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159720361914256633915929857 119790271435692475436947393)
        ·
          refine ⟨89842703576769356577710545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119790271435692475436947393 89842703576769356577710545)
          ·
            refine ⟨67382027682577017433282909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89842703576769356577710545 67382027682577017433282909)
            ·
              refine ⟨25268260380966381537481091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67382027682577017433282909 25268260380966381537481091)
              ·
                refine ⟨37902390571449572306221637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25268260380966381537481091 37902390571449572306221637)
                ·
                  refine ⟨7106698232146794807416557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37902390571449572306221637 7106698232146794807416557)
                  ·
                    refine ⟨2665011837055048052781209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7106698232146794807416557 2665011837055048052781209)
                    ·
                      refine ⟨1998758877791286039585907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2665011837055048052781209 1998758877791286039585907)
                      ·
                        rfl

theorem cell23_3892569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 4, 3, 2].length) (baseStart_3892569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892569 prefixEnd_3892569 := by exact prefixLift 3892569
  have htrace : WordTrace (prefixWord ++ tailWord_3892569) baseStart_3892569 baseEnd_3892569 := by
    simpa [prefixWord, tailWord_3892569, baseEnd_3892569] using wordTrace_append hprefix tailTrace_3892569
  have hstable : (prefixWord ++ tailWord_3892569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892569).length < 2 ^ (prefixWord ++ tailWord_3892569).sum := by decide
  have hdescent : baseEnd_3892569 < baseStart_3892569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892576 : List Nat := [2, 1, 1, 3, 4, 1, 3, 1, 3, 1, 3]
def baseStart_3892576 : Nat := 118140960795 + 3892576 * 2 ^ 59
def prefixEnd_3892576 : Nat := 4983230072969 + 3 ^ 40 * 3892576 * 2
def baseEnd_3892576 : Nat := 1998762472155867512198375

theorem tailTrace_3892576 : CollatzResearch.WordTrace tailWord_3892576 prefixEnd_3892576 1998762472155867512198375 := by
  unfold tailWord_3892576
  simp only [CollatzResearch.WordTrace]
  refine ⟨70986955172934712949276791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94649273563912950599035721 70986955172934712949276791)
  ·
    refine ⟨106480432759402069423915187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70986955172934712949276791 106480432759402069423915187)
    ·
      refine ⟨159720649139103104135872781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106480432759402069423915187 159720649139103104135872781)
      ·
        refine ⟨59895243427163664050952293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159720649139103104135872781 59895243427163664050952293)
        ·
          refine ⟨11230358142593187009553555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59895243427163664050952293 11230358142593187009553555)
          ·
            refine ⟨16845537213889780514330333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11230358142593187009553555 16845537213889780514330333)
            ·
              refine ⟨6317076455208667692873875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16845537213889780514330333 6317076455208667692873875)
              ·
                refine ⟨9475614682813001539310813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6317076455208667692873875 9475614682813001539310813)
                ·
                  refine ⟨3553355506054875577241555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9475614682813001539310813 3553355506054875577241555)
                  ·
                    refine ⟨5330033259082313365862333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3553355506054875577241555 5330033259082313365862333)
                    ·
                      refine ⟨1998762472155867512198375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5330033259082313365862333 1998762472155867512198375)
                      ·
                        rfl

theorem cell23_3892576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 3, 1, 3].length) (baseStart_3892576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892576 prefixEnd_3892576 := by exact prefixLift 3892576
  have htrace : WordTrace (prefixWord ++ tailWord_3892576) baseStart_3892576 baseEnd_3892576 := by
    simpa [prefixWord, tailWord_3892576, baseEnd_3892576] using wordTrace_append hprefix tailTrace_3892576
  have hstable : (prefixWord ++ tailWord_3892576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892576).length < 2 ^ (prefixWord ++ tailWord_3892576).sum := by decide
  have hdescent : baseEnd_3892576 < baseStart_3892576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892583 : List Nat := [1, 1, 5, 1, 5, 1, 2, 1, 6]
def baseStart_3892583 : Nat := 118140960795 + 3892583 * 2 ^ 59
def prefixEnd_3892583 : Nat := 4983230072969 + 3 ^ 40 * 3892583 * 2
def baseEnd_3892583 : Nat := 222085118502272109423427

theorem tailTrace_3892583 : CollatzResearch.WordTrace tailWord_3892583 prefixEnd_3892583 222085118502272109423427 := by
  unfold tailWord_3892583
  simp only [CollatzResearch.WordTrace]
  refine ⟨141974165656844066094058403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94649443771229377396038935 141974165656844066094058403)
  ·
    refine ⟨212961248485266099141087605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141974165656844066094058403 212961248485266099141087605)
    ·
      refine ⟨19965117045493696794476963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 212961248485266099141087605 19965117045493696794476963)
      ·
        refine ⟨29947675568240545191715445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19965117045493696794476963 29947675568240545191715445)
        ·
          refine ⟨2807594584522551111723323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29947675568240545191715445 2807594584522551111723323)
          ·
            refine ⟨4211391876783826667584985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2807594584522551111723323 4211391876783826667584985)
            ·
              refine ⟨3158543907587870000688739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4211391876783826667584985 3158543907587870000688739)
              ·
                refine ⟨4737815861381805001033109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3158543907587870000688739 4737815861381805001033109)
                ·
                  refine ⟨222085118502272109423427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4737815861381805001033109 222085118502272109423427)
                  ·
                    rfl

theorem cell23_3892583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 1, 6].length) (baseStart_3892583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892583 prefixEnd_3892583 := by exact prefixLift 3892583
  have htrace : WordTrace (prefixWord ++ tailWord_3892583) baseStart_3892583 baseEnd_3892583 := by
    simpa [prefixWord, tailWord_3892583, baseEnd_3892583] using wordTrace_append hprefix tailTrace_3892583
  have hstable : (prefixWord ++ tailWord_3892583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892583).length < 2 ^ (prefixWord ++ tailWord_3892583).sum := by decide
  have hdescent : baseEnd_3892583 < baseStart_3892583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892592 : List Nat := [2, 1, 1, 1, 4, 2, 2, 3, 1, 6]
def baseStart_3892592 : Nat := 118140960795 + 3892592 * 2 ^ 59
def prefixEnd_3892592 : Nat := 4983230072969 + 3 ^ 40 * 3892592 * 2
def baseEnd_3892592 : Nat := 666256895948779816532767

theorem tailTrace_3892592 : CollatzResearch.WordTrace tailWord_3892592 prefixEnd_3892592 666256895948779816532767 := by
  unfold tailWord_3892592
  simp only [CollatzResearch.WordTrace]
  refine ⟨70987246956905730315568015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94649662609207640420757353 70987246956905730315568015)
  ·
    refine ⟨106480870435358595473352023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70987246956905730315568015 106480870435358595473352023)
    ·
      refine ⟨159721305653037893210028035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106480870435358595473352023 159721305653037893210028035)
      ·
        refine ⟨239581958479556839815042053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159721305653037893210028035 239581958479556839815042053)
        ·
          refine ⟨44921617214916907465320385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 239581958479556839815042053 44921617214916907465320385)
          ·
            refine ⟨33691212911187680598990289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44921617214916907465320385 33691212911187680598990289)
            ·
              refine ⟨25268409683390760449242717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33691212911187680598990289 25268409683390760449242717)
              ·
                refine ⟨9475653631271535168466019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25268409683390760449242717 9475653631271535168466019)
                ·
                  refine ⟨14213480446907302752699029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9475653631271535168466019 14213480446907302752699029)
                  ·
                    refine ⟨666256895948779816532767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14213480446907302752699029 666256895948779816532767)
                    ·
                      rfl

theorem cell23_3892592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 1, 6].length) (baseStart_3892592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892592 prefixEnd_3892592 := by exact prefixLift 3892592
  have htrace : WordTrace (prefixWord ++ tailWord_3892592) baseStart_3892592 baseEnd_3892592 := by
    simpa [prefixWord, tailWord_3892592, baseEnd_3892592] using wordTrace_append hprefix tailTrace_3892592
  have hstable : (prefixWord ++ tailWord_3892592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892592).length < 2 ^ (prefixWord ++ tailWord_3892592).sum := by decide
  have hdescent : baseEnd_3892592 < baseStart_3892592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892602 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 2, 6, 3]
def baseStart_3892602 : Nat := 118140960795 + 3892602 * 2 ^ 59
def prefixEnd_3892602 : Nat := 4983230072969 + 3 ^ 40 * 3892602 * 2
def baseEnd_3892602 : Nat := 1998775822652884410473255

theorem tailTrace_3892602 : CollatzResearch.WordTrace tailWord_3892602 prefixEnd_3892602 1998775822652884410473255 := by
  unfold tailWord_3892602
  simp only [CollatzResearch.WordTrace]
  refine ⟨35493714660943808084750015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94649905762516821559333373 35493714660943808084750015)
  ·
    refine ⟨53240571991415712127125023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35493714660943808084750015 53240571991415712127125023)
    ·
      refine ⟨79860857987123568190687535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53240571991415712127125023 79860857987123568190687535)
      ·
        refine ⟨119791286980685352286031303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79860857987123568190687535 119791286980685352286031303)
        ·
          refine ⟨179686930471028028429046955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119791286980685352286031303 179686930471028028429046955)
          ·
            refine ⟨269530395706542042643570433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179686930471028028429046955 269530395706542042643570433)
            ·
              refine ⟨202147796779906531982677825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269530395706542042643570433 202147796779906531982677825)
              ·
                refine ⟨151610847584929898987008369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202147796779906531982677825 151610847584929898987008369)
                ·
                  refine ⟨113708135688697424240256277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151610847584929898987008369 113708135688697424240256277)
                  ·
                    refine ⟨5330068860407691761262013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 113708135688697424240256277 5330068860407691761262013)
                    ·
                      refine ⟨1998775822652884410473255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5330068860407691761262013 1998775822652884410473255)
                      ·
                        rfl

theorem cell23_3892602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 2, 6, 3].length) (baseStart_3892602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892602 prefixEnd_3892602 := by exact prefixLift 3892602
  have htrace : WordTrace (prefixWord ++ tailWord_3892602) baseStart_3892602 baseEnd_3892602 := by
    simpa [prefixWord, tailWord_3892602, baseEnd_3892602] using wordTrace_append hprefix tailTrace_3892602
  have hstable : (prefixWord ++ tailWord_3892602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892602).length < 2 ^ (prefixWord ++ tailWord_3892602).sum := by decide
  have hdescent : baseEnd_3892602 < baseStart_3892602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892622 : List Nat := [4, 1, 1, 4, 13]
def baseStart_3892622 : Nat := 118140960795 + 3892622 * 2 ^ 59
def prefixEnd_3892622 : Nat := 4983230072969 + 3 ^ 40 * 3892622 * 2
def baseEnd_3892622 : Nat := 2741819056606274804147

theorem tailTrace_3892622 : CollatzResearch.WordTrace tailWord_3892622 prefixEnd_3892622 2741819056606274804147 := by
  unfold tailWord_3892622
  simp only [CollatzResearch.WordTrace]
  refine ⟨17746948512962846969341015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94650392069135183836485413 17746948512962846969341015)
  ·
    refine ⟨26620422769444270454011523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17746948512962846969341015 26620422769444270454011523)
    ·
      refine ⟨39930634154166405681017285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26620422769444270454011523 39930634154166405681017285)
      ·
        refine ⟨7486993903906201065190741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39930634154166405681017285 7486993903906201065190741)
        ·
          refine ⟨2741819056606274804147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 7486993903906201065190741 2741819056606274804147)
          ·
            rfl

theorem cell23_3892622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 13].length) (baseStart_3892622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892622 prefixEnd_3892622 := by exact prefixLift 3892622
  have htrace : WordTrace (prefixWord ++ tailWord_3892622) baseStart_3892622 baseEnd_3892622 := by
    simpa [prefixWord, tailWord_3892622, baseEnd_3892622] using wordTrace_append hprefix tailTrace_3892622
  have hstable : (prefixWord ++ tailWord_3892622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892622).length < 2 ^ (prefixWord ++ tailWord_3892622).sum := by decide
  have hdescent : baseEnd_3892622 < baseStart_3892622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892639 : List Nat := [1, 1, 2, 5, 1, 4, 1, 8]
def baseStart_3892639 : Nat := 118140960795 + 3892639 * 2 ^ 59
def prefixEnd_3892639 : Nat := 4983230072969 + 3 ^ 40 * 3892639 * 2
def baseEnd_3892639 : Nat := 74029437831003732063355

theorem tailTrace_3892639 : CollatzResearch.WordTrace tailWord_3892639 prefixEnd_3892639 74029437831003732063355 := by
  unfold tailWord_3892639
  simp only [CollatzResearch.WordTrace]
  refine ⟨141976208144641187658096971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94650805429760791772064647 141976208144641187658096971)
  ·
    refine ⟨212964312216961781487145457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141976208144641187658096971 212964312216961781487145457)
    ·
      refine ⟨159723234162721336115359093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212964312216961781487145457 159723234162721336115359093)
      ·
        refine ⟨14974053202755125260814915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 159723234162721336115359093 14974053202755125260814915)
        ·
          refine ⟨22461079804132687891222373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14974053202755125260814915 22461079804132687891222373)
          ·
            refine ⟨4211452463274878979604195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22461079804132687891222373 4211452463274878979604195)
            ·
              refine ⟨6317178694912318469406293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4211452463274878979604195 6317178694912318469406293)
              ·
                refine ⟨74029437831003732063355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6317178694912318469406293 74029437831003732063355)
                ·
                  rfl

theorem cell23_3892639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 8].length) (baseStart_3892639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892639 prefixEnd_3892639 := by exact prefixLift 3892639
  have htrace : WordTrace (prefixWord ++ tailWord_3892639) baseStart_3892639 baseEnd_3892639 := by
    simpa [prefixWord, tailWord_3892639, baseEnd_3892639] using wordTrace_append hprefix tailTrace_3892639
  have hstable : (prefixWord ++ tailWord_3892639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892639).length < 2 ^ (prefixWord ++ tailWord_3892639).sum := by decide
  have hdescent : baseEnd_3892639 < baseStart_3892639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892649 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 8, 1, 3]
def baseStart_3892649 : Nat := 118140960795 + 3892649 * 2 ^ 59
def prefixEnd_3892649 : Nat := 4983230072969 + 3 ^ 40 * 3892649 * 2
def baseEnd_3892649 : Nat := 1998799956243645726585539

theorem tailTrace_3892649 : CollatzResearch.WordTrace tailWord_3892649 prefixEnd_3892649 1998799956243645726585539 := by
  unfold tailWord_3892649
  simp only [CollatzResearch.WordTrace]
  refine ⟨141976572874604959365961001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94651048583069972910640667 141976572874604959365961001)
  ·
    refine ⟨106482429655953719524470751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141976572874604959365961001 106482429655953719524470751)
    ·
      refine ⟨159723644483930579286706127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106482429655953719524470751 159723644483930579286706127)
      ·
        refine ⟨239585466725895868930059191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159723644483930579286706127 239585466725895868930059191)
        ·
          refine ⟨359378200088843803395088787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239585466725895868930059191 359378200088843803395088787)
          ·
            refine ⟨539067300133265705092633181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359378200088843803395088787 539067300133265705092633181)
            ·
              refine ⟨202150237549974639409737443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 539067300133265705092633181 202150237549974639409737443)
              ·
                refine ⟨303225356324961959114606165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202150237549974639409737443 303225356324961959114606165)
                ·
                  refine ⟨3553422144433147958374291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 303225356324961959114606165 3553422144433147958374291)
                  ·
                    refine ⟨5330133216649721937561437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3553422144433147958374291 5330133216649721937561437)
                    ·
                      refine ⟨1998799956243645726585539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5330133216649721937561437 1998799956243645726585539)
                      ·
                        rfl

theorem cell23_3892649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 8, 1, 3].length) (baseStart_3892649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892649 prefixEnd_3892649 := by exact prefixLift 3892649
  have htrace : WordTrace (prefixWord ++ tailWord_3892649) baseStart_3892649 baseEnd_3892649 := by
    simpa [prefixWord, tailWord_3892649, baseEnd_3892649] using wordTrace_append hprefix tailTrace_3892649
  have hstable : (prefixWord ++ tailWord_3892649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892649).length < 2 ^ (prefixWord ++ tailWord_3892649).sum := by decide
  have hdescent : baseEnd_3892649 < baseStart_3892649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892689 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 2, 8, 2]
def baseStart_3892689 : Nat := 118140960795 + 3892689 * 2 ^ 59
def prefixEnd_3892689 : Nat := 4983230072969 + 3 ^ 40 * 3892689 * 2
def baseEnd_3892689 : Nat := 1998820495469825570085355

theorem tailTrace_3892689 : CollatzResearch.WordTrace tailWord_3892689 prefixEnd_3892689 1998820495469825570085355 := by
  unfold tailWord_3892689
  simp only [CollatzResearch.WordTrace]
  refine ⟨141978031794460046197417121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94652021196306697464944747 141978031794460046197417121)
  ·
    refine ⟨106483523845845034648062841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141978031794460046197417121 106483523845845034648062841)
    ·
      refine ⟨79862642884383775986047131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106483523845845034648062841 79862642884383775986047131)
      ·
        refine ⟨119793964326575663979070697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79862642884383775986047131 119793964326575663979070697)
        ·
          refine ⟨89845473244931747984303023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119793964326575663979070697 89845473244931747984303023)
          ·
            refine ⟨134768209867397621976454535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89845473244931747984303023 134768209867397621976454535)
            ·
              refine ⟨202152314801096432964681803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134768209867397621976454535 202152314801096432964681803)
              ·
                refine ⟨303228472201644649447022705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202152314801096432964681803 303228472201644649447022705)
                ·
                  refine ⟨227421354151233487085267029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 303228472201644649447022705 227421354151233487085267029)
                  ·
                    refine ⟨2665093993959767426780473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 227421354151233487085267029 2665093993959767426780473)
                    ·
                      refine ⟨1998820495469825570085355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2665093993959767426780473 1998820495469825570085355)
                      ·
                        rfl

theorem cell23_3892689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 8, 2].length) (baseStart_3892689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892689 prefixEnd_3892689 := by exact prefixLift 3892689
  have htrace : WordTrace (prefixWord ++ tailWord_3892689) baseStart_3892689 baseEnd_3892689 := by
    simpa [prefixWord, tailWord_3892689, baseEnd_3892689] using wordTrace_append hprefix tailTrace_3892689
  have hstable : (prefixWord ++ tailWord_3892689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892689).length < 2 ^ (prefixWord ++ tailWord_3892689).sum := by decide
  have hdescent : baseEnd_3892689 < baseStart_3892689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892726 : List Nat := [5, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5]
def baseStart_3892726 : Nat := 118140960795 + 3892726 * 2 ^ 59
def prefixEnd_3892726 : Nat := 4983230072969 + 3 ^ 40 * 3892726 * 2
def baseEnd_3892726 : Nat := 1998839494254041925322685

theorem tailTrace_3892726 : CollatzResearch.WordTrace tailWord_3892726 prefixEnd_3892726 1998839494254041925322685 := by
  unfold tailWord_3892726
  simp only [CollatzResearch.WordTrace]
  refine ⟨8873711330957875094782127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94652920863550667677676021 8873711330957875094782127)
  ·
    refine ⟨13310566996436812642173191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8873711330957875094782127 13310566996436812642173191)
    ·
      refine ⟨19965850494655218963259787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13310566996436812642173191 19965850494655218963259787)
      ·
        refine ⟨29948775741982828444889681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19965850494655218963259787 29948775741982828444889681)
        ·
          refine ⟨22461581806487121333667261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29948775741982828444889681 22461581806487121333667261)
          ·
            refine ⟨8423093177432670500125223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22461581806487121333667261 8423093177432670500125223)
            ·
              refine ⟨12634639766149005750187835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8423093177432670500125223 12634639766149005750187835)
              ·
                refine ⟨18951959649223508625281753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12634639766149005750187835 18951959649223508625281753)
                ·
                  refine ⟨14213969736917631468961315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18951959649223508625281753 14213969736917631468961315)
                  ·
                    refine ⟨21320954605376447203441973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14213969736917631468961315 21320954605376447203441973)
                    ·
                      refine ⟨1998839494254041925322685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21320954605376447203441973 1998839494254041925322685)
                      ·
                        rfl

theorem cell23_3892726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_3892726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892726 prefixEnd_3892726 := by exact prefixLift 3892726
  have htrace : WordTrace (prefixWord ++ tailWord_3892726) baseStart_3892726 baseEnd_3892726 := by
    simpa [prefixWord, tailWord_3892726, baseEnd_3892726] using wordTrace_append hprefix tailTrace_3892726
  have hstable : (prefixWord ++ tailWord_3892726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892726).length < 2 ^ (prefixWord ++ tailWord_3892726).sum := by decide
  have hdescent : baseEnd_3892726 < baseStart_3892726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892739 : List Nat := [1, 1, 1, 3, 2, 1, 2, 4, 2, 3, 3]
def baseStart_3892739 : Nat := 118140960795 + 3892739 * 2 ^ 59
def prefixEnd_3892739 : Nat := 4983230072969 + 3 ^ 40 * 3892739 * 2
def baseEnd_3892739 : Nat := 1998846169502550374460125

theorem tailTrace_3892739 : CollatzResearch.WordTrace tailWord_3892739 prefixEnd_3892739 1998846169502550374460125 := by
  unfold tailWord_3892739
  simp only [CollatzResearch.WordTrace]
  refine ⟨141979855444278904736737271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94653236962852603157824847 141979855444278904736737271)
  ·
    refine ⟨212969783166418357105105907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141979855444278904736737271 212969783166418357105105907)
    ·
      refine ⟨319454674749627535657658861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212969783166418357105105907 319454674749627535657658861)
      ·
        refine ⟨119795503031110325871622073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 319454674749627535657658861 119795503031110325871622073)
        ·
          refine ⟨89846627273332744403716555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119795503031110325871622073 89846627273332744403716555)
          ·
            refine ⟨134769940909999116605574833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89846627273332744403716555 134769940909999116605574833)
            ·
              refine ⟨101077455682499337454181125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134769940909999116605574833 101077455682499337454181125)
              ·
                refine ⟨18952022940468625772658961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101077455682499337454181125 18952022940468625772658961)
                ·
                  refine ⟨14214017205351469329494221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18952022940468625772658961 14214017205351469329494221)
                  ·
                    refine ⟨5330256452006800998560333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14214017205351469329494221 5330256452006800998560333)
                    ·
                      refine ⟨1998846169502550374460125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5330256452006800998560333 1998846169502550374460125)
                      ·
                        rfl

theorem cell23_3892739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 3, 3].length) (baseStart_3892739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892739 prefixEnd_3892739 := by exact prefixLift 3892739
  have htrace : WordTrace (prefixWord ++ tailWord_3892739) baseStart_3892739 baseEnd_3892739 := by
    simpa [prefixWord, tailWord_3892739, baseEnd_3892739] using wordTrace_append hprefix tailTrace_3892739
  have hstable : (prefixWord ++ tailWord_3892739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892739).length < 2 ^ (prefixWord ++ tailWord_3892739).sum := by decide
  have hdescent : baseEnd_3892739 < baseStart_3892739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892746 : List Nat := [3, 1, 2, 2, 2, 4, 1, 1, 7]
def baseStart_3892746 : Nat := 118140960795 + 3892746 * 2 ^ 59
def prefixEnd_3892746 : Nat := 4983230072969 + 3 ^ 40 * 3892746 * 2
def baseEnd_3892746 : Nat := 222094418207459094119177

theorem tailTrace_3892746 : CollatzResearch.WordTrace tailWord_3892746 prefixEnd_3892746 222094418207459094119177 := by
  unfold tailWord_3892746
  simp only [CollatzResearch.WordTrace]
  refine ⟨35495027688813386233060523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94653407170169029954828061 35495027688813386233060523)
  ·
    refine ⟨53242541533220079349590785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35495027688813386233060523 53242541533220079349590785)
    ·
      refine ⟨39931906149915059512193089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53242541533220079349590785 39931906149915059512193089)
      ·
        refine ⟨29948929612436294634144817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39931906149915059512193089 29948929612436294634144817)
        ·
          refine ⟨22461697209327220975608613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29948929612436294634144817 22461697209327220975608613)
          ·
            refine ⟨4211568226748853932926615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22461697209327220975608613 4211568226748853932926615)
            ·
              refine ⟨6317352340123280899389923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4211568226748853932926615 6317352340123280899389923)
              ·
                refine ⟨9476028510184921349084885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6317352340123280899389923 9476028510184921349084885)
                ·
                  refine ⟨222094418207459094119177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9476028510184921349084885 222094418207459094119177)
                  ·
                    rfl

theorem cell23_3892746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 7].length) (baseStart_3892746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892746 prefixEnd_3892746 := by exact prefixLift 3892746
  have htrace : WordTrace (prefixWord ++ tailWord_3892746) baseStart_3892746 baseEnd_3892746 := by
    simpa [prefixWord, tailWord_3892746, baseEnd_3892746] using wordTrace_append hprefix tailTrace_3892746
  have hstable : (prefixWord ++ tailWord_3892746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892746).length < 2 ^ (prefixWord ++ tailWord_3892746).sum := by decide
  have hdescent : baseEnd_3892746 < baseStart_3892746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892757 : List Nat := [1, 3, 2, 1, 3, 4, 2, 1, 2, 2, 2]
def baseStart_3892757 : Nat := 118140960795 + 3892757 * 2 ^ 59
def prefixEnd_3892757 : Nat := 4983230072969 + 3 ^ 40 * 3892757 * 2
def baseEnd_3892757 : Nat := 1998855412154331304035043

theorem tailTrace_3892757 : CollatzResearch.WordTrace tailWord_3892757 prefixEnd_3892757 1998855412154331304035043 := by
  unfold tailWord_3892757
  simp only [CollatzResearch.WordTrace]
  refine ⟨141980511958213693810892525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94653674638809129207261683 141980511958213693810892525)
  ·
    refine ⟨53242691984330135179084697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141980511958213693810892525 53242691984330135179084697)
    ·
      refine ⟨39932018988247601384313523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53242691984330135179084697 39932018988247601384313523)
      ·
        refine ⟨59898028482371402076470285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39932018988247601384313523 59898028482371402076470285)
        ·
          refine ⟨22461760680889275778676357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59898028482371402076470285 22461760680889275778676357)
          ·
            refine ⟨4211580127666739208501817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22461760680889275778676357 4211580127666739208501817)
            ·
              refine ⟨3158685095750054406376363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4211580127666739208501817 3158685095750054406376363)
              ·
                refine ⟨4738027643625081609564545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3158685095750054406376363 4738027643625081609564545)
                ·
                  refine ⟨3553520732718811207173409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4738027643625081609564545 3553520732718811207173409)
                  ·
                    refine ⟨2665140549539108405380057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3553520732718811207173409 2665140549539108405380057)
                    ·
                      refine ⟨1998855412154331304035043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2665140549539108405380057 1998855412154331304035043)
                      ·
                        rfl

theorem cell23_3892757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 1, 2, 2, 2].length) (baseStart_3892757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892757 prefixEnd_3892757 := by exact prefixLift 3892757
  have htrace : WordTrace (prefixWord ++ tailWord_3892757) baseStart_3892757 baseEnd_3892757 := by
    simpa [prefixWord, tailWord_3892757, baseEnd_3892757] using wordTrace_append hprefix tailTrace_3892757
  have hstable : (prefixWord ++ tailWord_3892757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892757).length < 2 ^ (prefixWord ++ tailWord_3892757).sum := by decide
  have hdescent : baseEnd_3892757 < baseStart_3892757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892797 : List Nat := [1, 4, 1, 3, 4, 1, 2, 2, 5]
def baseStart_3892797 : Nat := 118140960795 + 3892797 * 2 ^ 59
def prefixEnd_3892797 : Nat := 4983230072969 + 3 ^ 40 * 3892797 * 2
def baseEnd_3892797 : Nat := 222097327931167905281651

theorem tailTrace_3892797 : CollatzResearch.WordTrace tailWord_3892797 prefixEnd_3892797 222097327931167905281651 := by
  unfold tailWord_3892797
  simp only [CollatzResearch.WordTrace]
  refine ⟨141981970878068780642348645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94654647252045853761565763 141981970878068780642348645)
  ·
    refine ⟨26621619539637896370440371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141981970878068780642348645 26621619539637896370440371)
    ·
      refine ⟨39932429309456844555660557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26621619539637896370440371 39932429309456844555660557)
      ·
        refine ⟨14974660991046316708372709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39932429309456844555660557 14974660991046316708372709)
        ·
          refine ⟨2807748935821184382819883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14974660991046316708372709 2807748935821184382819883)
          ·
            refine ⟨4211623403731776574229825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2807748935821184382819883 4211623403731776574229825)
            ·
              refine ⟨3158717552798832430672369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4211623403731776574229825 3158717552798832430672369)
              ·
                refine ⟨2369038164599124323004277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3158717552798832430672369 2369038164599124323004277)
                ·
                  refine ⟨222097327931167905281651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2369038164599124323004277 222097327931167905281651)
                  ·
                    rfl

theorem cell23_3892797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 2, 5].length) (baseStart_3892797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892797 prefixEnd_3892797 := by exact prefixLift 3892797
  have htrace : WordTrace (prefixWord ++ tailWord_3892797) baseStart_3892797 baseEnd_3892797 := by
    simpa [prefixWord, tailWord_3892797, baseEnd_3892797] using wordTrace_append hprefix tailTrace_3892797
  have hstable : (prefixWord ++ tailWord_3892797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892797).length < 2 ^ (prefixWord ++ tailWord_3892797).sum := by decide
  have hdescent : baseEnd_3892797 < baseStart_3892797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892840 : List Nat := [2, 1, 4, 3, 1, 1, 1, 5, 1, 4]
def baseStart_3892840 : Nat := 118140960795 + 3892840 * 2 ^ 59
def prefixEnd_3892840 : Nat := 4983230072969 + 3 ^ 40 * 3892840 * 2
def baseEnd_3892840 : Nat := 666299343682884826432387

theorem tailTrace_3892840 : CollatzResearch.WordTrace tailWord_3892840 prefixEnd_3892840 666299343682884826432387 := by
  unfold tailWord_3892840
  simp only [CollatzResearch.WordTrace]
  refine ⟨70991769608456499493081987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94655692811275332657442649 70991769608456499493081987)
  ·
    refine ⟨106487654412684749239622981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70991769608456499493081987 106487654412684749239622981)
    ·
      refine ⟨19966435202378390482429309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106487654412684749239622981 19966435202378390482429309)
      ·
        refine ⟨7487413200891896430910991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19966435202378390482429309 7487413200891896430910991)
        ·
          refine ⟨11231119801337844646366487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7487413200891896430910991 11231119801337844646366487)
          ·
            refine ⟨16846679702006766969549731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11231119801337844646366487 16846679702006766969549731)
            ·
              refine ⟨25270019553010150454324597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16846679702006766969549731 25270019553010150454324597)
              ·
                refine ⟨2369064333094701605092931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25270019553010150454324597 2369064333094701605092931)
                ·
                  refine ⟨3553596499642052407639397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2369064333094701605092931 3553596499642052407639397)
                  ·
                    refine ⟨666299343682884826432387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3553596499642052407639397 666299343682884826432387)
                    ·
                      rfl

theorem cell23_3892840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_3892840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892840 prefixEnd_3892840 := by exact prefixLift 3892840
  have htrace : WordTrace (prefixWord ++ tailWord_3892840) baseStart_3892840 baseEnd_3892840 := by
    simpa [prefixWord, tailWord_3892840, baseEnd_3892840] using wordTrace_append hprefix tailTrace_3892840
  have hstable : (prefixWord ++ tailWord_3892840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892840).length < 2 ^ (prefixWord ++ tailWord_3892840).sum := by decide
  have hdescent : baseEnd_3892840 < baseStart_3892840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892853 : List Nat := [1, 3, 4, 2, 1, 1, 3, 2, 6]
def baseStart_3892853 : Nat := 118140960795 + 3892853 * 2 ^ 59
def prefixEnd_3892853 : Nat := 4983230072969 + 3 ^ 40 * 3892853 * 2
def baseEnd_3892853 : Nat := 222100522921906992048289

theorem tailTrace_3892853 : CollatzResearch.WordTrace tailWord_3892853 prefixEnd_3892853 222100522921906992048289 := by
  unfold tailWord_3892853
  simp only [CollatzResearch.WordTrace]
  refine ⟨141984013365865902206387213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94656008910577268137591475 141984013365865902206387213)
  ·
    refine ⟨53244005012199713327395205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141984013365865902206387213 53244005012199713327395205)
    ·
      refine ⟨9983250939787446248886601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53244005012199713327395205 9983250939787446248886601)
      ·
        refine ⟨7487438204840584686664951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9983250939787446248886601 7487438204840584686664951)
        ·
          refine ⟨11231157307260877029997427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7487438204840584686664951 11231157307260877029997427)
          ·
            refine ⟨16846735960891315544996141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11231157307260877029997427 16846735960891315544996141)
            ·
              refine ⟨6317525985334243329373553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16846735960891315544996141 6317525985334243329373553)
              ·
                refine ⟨4738144489000682497030165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6317525985334243329373553 4738144489000682497030165)
                ·
                  refine ⟨222100522921906992048289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4738144489000682497030165 222100522921906992048289)
                  ·
                    rfl

theorem cell23_3892853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 2, 6].length) (baseStart_3892853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892853 prefixEnd_3892853 := by exact prefixLift 3892853
  have htrace : WordTrace (prefixWord ++ tailWord_3892853) baseStart_3892853 baseEnd_3892853 := by
    simpa [prefixWord, tailWord_3892853, baseEnd_3892853] using wordTrace_append hprefix tailTrace_3892853
  have hstable : (prefixWord ++ tailWord_3892853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892853).length < 2 ^ (prefixWord ++ tailWord_3892853).sum := by decide
  have hdescent : baseEnd_3892853 < baseStart_3892853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892856 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 5, 5, 2]
def baseStart_3892856 : Nat := 118140960795 + 3892856 * 2 ^ 59
def prefixEnd_3892856 : Nat := 4983230072969 + 3 ^ 40 * 3892856 * 2
def baseEnd_3892856 : Nat := 1998906246739126416697087

theorem tailTrace_3892856 : CollatzResearch.WordTrace tailWord_3892856 prefixEnd_3892856 1998906246739126416697087 := by
  unfold tailWord_3892856
  simp only [CollatzResearch.WordTrace]
  refine ⟨70992061392427516859373211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94656081856570022479164281 70992061392427516859373211)
  ·
    refine ⟨106488092088641275289059817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70992061392427516859373211 106488092088641275289059817)
    ·
      refine ⟨79866069066480956466794863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106488092088641275289059817 79866069066480956466794863)
      ·
        refine ⟨119799103599721434700192295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79866069066480956466794863 119799103599721434700192295)
        ·
          refine ⟨179698655399582152050288443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119799103599721434700192295 179698655399582152050288443)
          ·
            refine ⟨269547983099373228075432665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179698655399582152050288443 269547983099373228075432665)
            ·
              refine ⟨202160987324529921056574499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269547983099373228075432665 202160987324529921056574499)
              ·
                refine ⟨303241480986794881584861749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202160987324529921056574499 303241480986794881584861749)
                ·
                  refine ⟨28428888842512020148580789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 303241480986794881584861749 28428888842512020148580789)
                  ·
                    refine ⟨2665208328985501888929449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28428888842512020148580789 2665208328985501888929449)
                    ·
                      refine ⟨1998906246739126416697087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2665208328985501888929449 1998906246739126416697087)
                      ·
                        rfl

theorem cell23_3892856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 5, 5, 2].length) (baseStart_3892856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892856 prefixEnd_3892856 := by exact prefixLift 3892856
  have htrace : WordTrace (prefixWord ++ tailWord_3892856) baseStart_3892856 baseEnd_3892856 := by
    simpa [prefixWord, tailWord_3892856, baseEnd_3892856] using wordTrace_append hprefix tailTrace_3892856
  have hstable : (prefixWord ++ tailWord_3892856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892856).length < 2 ^ (prefixWord ++ tailWord_3892856).sum := by decide
  have hdescent : baseEnd_3892856 < baseStart_3892856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892897 : List Nat := [1, 2, 3, 3, 2, 1, 3, 3, 1, 1, 3]
def baseStart_3892897 : Nat := 118140960795 + 3892897 * 2 ^ 59
def prefixEnd_3892897 : Nat := 4983230072969 + 3 ^ 40 * 3892897 * 2
def baseEnd_3892897 : Nat := 1998927299445960756284399

theorem tailTrace_3892897 : CollatzResearch.WordTrace tailWord_3892897 prefixEnd_3892897 1998927299445960756284399 := by
  unfold tailWord_3892897
  simp only [CollatzResearch.WordTrace]
  refine ⟨141985618177706497720988945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94657078785137665147325963 141985618177706497720988945)
  ·
    refine ⟨106489213633279873290741709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141985618177706497720988945 106489213633279873290741709)
    ·
      refine ⟨39933455112479952484028141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106489213633279873290741709 39933455112479952484028141)
      ·
        refine ⟨14975045667179982181510553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39933455112479952484028141 14975045667179982181510553)
        ·
          refine ⟨11231284250384986636132915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14975045667179982181510553 11231284250384986636132915)
          ·
            refine ⟨16846926375577479954199373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11231284250384986636132915 16846926375577479954199373)
            ·
              refine ⟨6317597390841554982824765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16846926375577479954199373 6317597390841554982824765)
              ·
                refine ⟨2369099021565583118559287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6317597390841554982824765 2369099021565583118559287)
                ·
                  refine ⟨3553648532348374677838931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2369099021565583118559287 3553648532348374677838931)
                  ·
                    refine ⟨5330472798522562016758397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3553648532348374677838931 5330472798522562016758397)
                    ·
                      refine ⟨1998927299445960756284399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5330472798522562016758397 1998927299445960756284399)
                      ·
                        rfl

theorem cell23_3892897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_3892897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892897 prefixEnd_3892897 := by exact prefixLift 3892897
  have htrace : WordTrace (prefixWord ++ tailWord_3892897) baseStart_3892897 baseEnd_3892897 := by
    simpa [prefixWord, tailWord_3892897, baseEnd_3892897] using wordTrace_append hprefix tailTrace_3892897
  have hstable : (prefixWord ++ tailWord_3892897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892897).length < 2 ^ (prefixWord ++ tailWord_3892897).sum := by decide
  have hdescent : baseEnd_3892897 < baseStart_3892897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892926 : List Nat := [4, 2, 1, 1, 2, 2, 1, 10]
def baseStart_3892926 : Nat := 118140960795 + 3892926 * 2 ^ 59
def prefixEnd_3892926 : Nat := 4983230072969 + 3 ^ 40 * 3892926 * 2
def baseEnd_3892926 : Nat := 74034895940183005289695

theorem tailTrace_3892926 : CollatzResearch.WordTrace tailWord_3892926 prefixEnd_3892926 74034895940183005289695 := by
  unfold tailWord_3892926
  simp only [CollatzResearch.WordTrace]
  refine ⟨17748334486825179459224329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94657783929734290449196421 17748334486825179459224329)
  ·
    refine ⟨13311250865118884594418247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17748334486825179459224329 13311250865118884594418247)
    ·
      refine ⟨19966876297678326891627371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13311250865118884594418247 19966876297678326891627371)
      ·
        refine ⟨29950314446517490337441057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19966876297678326891627371 29950314446517490337441057)
        ·
          refine ⟨22462735834888117753080793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29950314446517490337441057 22462735834888117753080793)
          ·
            refine ⟨16847051876166088314810595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22462735834888117753080793 16847051876166088314810595)
            ·
              refine ⟨25270577814249132472215893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16847051876166088314810595 25270577814249132472215893)
              ·
                refine ⟨74034895940183005289695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 25270577814249132472215893 74034895940183005289695)
                ·
                  rfl

theorem cell23_3892926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 10].length) (baseStart_3892926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892926 prefixEnd_3892926 := by exact prefixLift 3892926
  have htrace : WordTrace (prefixWord ++ tailWord_3892926) baseStart_3892926 baseEnd_3892926 := by
    simpa [prefixWord, tailWord_3892926, baseEnd_3892926] using wordTrace_append hprefix tailTrace_3892926
  have hstable : (prefixWord ++ tailWord_3892926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892926).length < 2 ^ (prefixWord ++ tailWord_3892926).sum := by decide
  have hdescent : baseEnd_3892926 < baseStart_3892926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892934 : List Nat := [6, 1, 2, 1, 1, 3, 1, 2, 1, 5]
def baseStart_3892934 : Nat := 118140960795 + 3892934 * 2 ^ 59
def prefixEnd_3892934 : Nat := 4983230072969 + 3 ^ 40 * 3892934 * 2
def baseEnd_3892934 : Nat := 666315432743392370507243

theorem tailTrace_3892934 : CollatzResearch.WordTrace tailWord_3892934 prefixEnd_3892934 666315432743392370507243 := by
  unfold tailWord_3892934
  simp only [CollatzResearch.WordTrace]
  refine ⟨4437092739955389157502683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 94657978452381635360057237 4437092739955389157502683)
  ·
    refine ⟨6655639109933083736254025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4437092739955389157502683 6655639109933083736254025)
    ·
      refine ⟨4991729332449812802190519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6655639109933083736254025 4991729332449812802190519)
      ·
        refine ⟨7487593998674719203285779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4991729332449812802190519 7487593998674719203285779)
        ·
          refine ⟨11231390998012078804928669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7487593998674719203285779 11231390998012078804928669)
          ·
            refine ⟨4211771624254529551848251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11231390998012078804928669 4211771624254529551848251)
            ·
              refine ⟨6317657436381794327772377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4211771624254529551848251 6317657436381794327772377)
              ·
                refine ⟨4738243077286345745829283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6317657436381794327772377 4738243077286345745829283)
                ·
                  refine ⟨7107364615929518618743925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4738243077286345745829283 7107364615929518618743925)
                  ·
                    refine ⟨666315432743392370507243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7107364615929518618743925 666315432743392370507243)
                    ·
                      rfl

theorem cell23_3892934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_3892934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892934 prefixEnd_3892934 := by exact prefixLift 3892934
  have htrace : WordTrace (prefixWord ++ tailWord_3892934) baseStart_3892934 baseEnd_3892934 := by
    simpa [prefixWord, tailWord_3892934, baseEnd_3892934] using wordTrace_append hprefix tailTrace_3892934
  have hstable : (prefixWord ++ tailWord_3892934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892934).length < 2 ^ (prefixWord ++ tailWord_3892934).sum := by decide
  have hdescent : baseEnd_3892934 < baseStart_3892934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892940 : List Nat := [2, 2, 1, 5, 2, 1, 1, 1, 3, 2, 3]
def baseStart_3892940 : Nat := 118140960795 + 3892940 * 2 ^ 59
def prefixEnd_3892940 : Nat := 4983230072969 + 3 ^ 40 * 3892940 * 2
def baseEnd_3892940 : Nat := 1998949379114104088046701

theorem tailTrace_3892940 : CollatzResearch.WordTrace tailWord_3892940 prefixEnd_3892940 1998949379114104088046701 := by
  unfold tailWord_3892940
  simp only [CollatzResearch.WordTrace]
  refine ⟨70993593258275358032402137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94658124344367144043202849 70993593258275358032402137)
  ·
    refine ⟨53245194943706518524301603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70993593258275358032402137 53245194943706518524301603)
    ·
      refine ⟨79867792415559777786452405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53245194943706518524301603 79867792415559777786452405)
      ·
        refine ⟨7487605538958729167479913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79867792415559777786452405 7487605538958729167479913)
        ·
          refine ⟨5615704154219046875609935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7487605538958729167479913 5615704154219046875609935)
          ·
            refine ⟨8423556231328570313414903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5615704154219046875609935 8423556231328570313414903)
            ·
              refine ⟨12635334346992855470122355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8423556231328570313414903 12635334346992855470122355)
              ·
                refine ⟨18953001520489283205183533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12635334346992855470122355 18953001520489283205183533)
                ·
                  refine ⟨7107375570183481201943825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18953001520489283205183533 7107375570183481201943825)
                  ·
                    refine ⟨5330531677637610901457869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7107375570183481201943825 5330531677637610901457869)
                    ·
                      refine ⟨1998949379114104088046701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5330531677637610901457869 1998949379114104088046701)
                      ·
                        rfl

theorem cell23_3892940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_3892940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892940 prefixEnd_3892940 := by exact prefixLift 3892940
  have htrace : WordTrace (prefixWord ++ tailWord_3892940) baseStart_3892940 baseEnd_3892940 := by
    simpa [prefixWord, tailWord_3892940, baseEnd_3892940] using wordTrace_append hprefix tailTrace_3892940
  have hstable : (prefixWord ++ tailWord_3892940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892940).length < 2 ^ (prefixWord ++ tailWord_3892940).sum := by decide
  have hdescent : baseEnd_3892940 < baseStart_3892940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892953 : List Nat := [1, 2, 1, 2, 3, 4, 1, 2, 1, 3, 3]
def baseStart_3892953 : Nat := 118140960795 + 3892953 * 2 ^ 59
def prefixEnd_3892953 : Nat := 4983230072969 + 3 ^ 40 * 3892953 * 2
def baseEnd_3892953 : Nat := 1998956054362612537184141

theorem tailTrace_3892953 : CollatzResearch.WordTrace tailWord_3892953 prefixEnd_3892953 1998956054362612537184141 := by
  unfold tailWord_3892953
  simp only [CollatzResearch.WordTrace]
  refine ⟨141987660665503619285027513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94658440443669079523351675 141987660665503619285027513)
  ·
    refine ⟨106490745499127714463770635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141987660665503619285027513 106490745499127714463770635)
    ·
      refine ⟨159736118248691571695655953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106490745499127714463770635 159736118248691571695655953)
      ·
        refine ⟨119802088686518678771741965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159736118248691571695655953 119802088686518678771741965)
        ·
          refine ⟨44925783257444504539403237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119802088686518678771741965 44925783257444504539403237)
          ·
            refine ⟨8423584360770844601138107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44925783257444504539403237 8423584360770844601138107)
            ·
              refine ⟨12635376541156266901707161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8423584360770844601138107 12635376541156266901707161)
              ·
                refine ⟨9476532405867200176280371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12635376541156266901707161 9476532405867200176280371)
                ·
                  refine ⟨14214798608800800264420557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9476532405867200176280371 14214798608800800264420557)
                  ·
                    refine ⟨5330549478300300099157709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14214798608800800264420557 5330549478300300099157709)
                    ·
                      refine ⟨1998956054362612537184141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5330549478300300099157709 1998956054362612537184141)
                      ·
                        rfl

theorem cell23_3892953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 3, 3].length) (baseStart_3892953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892953 prefixEnd_3892953 := by exact prefixLift 3892953
  have htrace : WordTrace (prefixWord ++ tailWord_3892953) baseStart_3892953 baseEnd_3892953 := by
    simpa [prefixWord, tailWord_3892953, baseEnd_3892953] using wordTrace_append hprefix tailTrace_3892953
  have hstable : (prefixWord ++ tailWord_3892953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892953).length < 2 ^ (prefixWord ++ tailWord_3892953).sum := by decide
  have hdescent : baseEnd_3892953 < baseStart_3892953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892957 : List Nat := [1, 4, 3, 3, 1, 2, 1, 1, 1, 1, 5]
def baseStart_3892957 : Nat := 118140960795 + 3892957 * 2 ^ 59
def prefixEnd_3892957 : Nat := 4983230072969 + 3 ^ 40 * 3892957 * 2
def baseEnd_3892957 : Nat := 1998958108285230521534123

theorem tailTrace_3892957 : CollatzResearch.WordTrace tailWord_3892957 prefixEnd_3892957 1998958108285230521534123 := by
  unfold tailWord_3892957
  simp only [CollatzResearch.WordTrace]
  refine ⟨141987806557489127968173125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94658537704992751978782083 141987806557489127968173125)
  ·
    refine ⟨26622713729529211494032461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141987806557489127968173125 26622713729529211494032461)
    ·
      refine ⟨9983517648573454310262173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26622713729529211494032461 9983517648573454310262173)
      ·
        refine ⟨3743819118215045366348315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9983517648573454310262173 3743819118215045366348315)
        ·
          refine ⟨5615728677322568049522473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3743819118215045366348315 5615728677322568049522473)
          ·
            refine ⟨4211796507991926037141855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5615728677322568049522473 4211796507991926037141855)
            ·
              refine ⟨6317694761987889055712783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4211796507991926037141855 6317694761987889055712783)
              ·
                refine ⟨9476542142981833583569175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6317694761987889055712783 9476542142981833583569175)
                ·
                  refine ⟨14214813214472750375353763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9476542142981833583569175 14214813214472750375353763)
                  ·
                    refine ⟨21322219821709125563030645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14214813214472750375353763 21322219821709125563030645)
                    ·
                      refine ⟨1998958108285230521534123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21322219821709125563030645 1998958108285230521534123)
                      ·
                        rfl

theorem cell23_3892957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_3892957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892957 prefixEnd_3892957 := by exact prefixLift 3892957
  have htrace : WordTrace (prefixWord ++ tailWord_3892957) baseStart_3892957 baseEnd_3892957 := by
    simpa [prefixWord, tailWord_3892957, baseEnd_3892957] using wordTrace_append hprefix tailTrace_3892957
  have hstable : (prefixWord ++ tailWord_3892957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892957).length < 2 ^ (prefixWord ++ tailWord_3892957).sum := by decide
  have hdescent : baseEnd_3892957 < baseStart_3892957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892970 : List Nat := [3, 1, 3, 1, 1, 1, 3, 4, 2, 1, 3]
def baseStart_3892970 : Nat := 118140960795 + 3892970 * 2 ^ 59
def prefixEnd_3892970 : Nat := 4983230072969 + 3 ^ 40 * 3892970 * 2
def baseEnd_3892970 : Nat := 1998964783533738970671563

theorem tailTrace_3892970 : CollatzResearch.WordTrace tailWord_3892970 prefixEnd_3892970 1998964783533738970671563 := by
  unfold tailWord_3892970
  simp only [CollatzResearch.WordTrace]
  refine ⟨35497070176610507797099091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94658853804294687458930909 35497070176610507797099091)
  ·
    refine ⟨53245605264915761695648637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35497070176610507797099091 53245605264915761695648637)
    ·
      refine ⟨19967101974343410635868239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53245605264915761695648637 19967101974343410635868239)
      ·
        refine ⟨29950652961515115953802359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19967101974343410635868239 29950652961515115953802359)
        ·
          refine ⟨44925979442272673930703539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29950652961515115953802359 44925979442272673930703539)
          ·
            refine ⟨67388969163409010896055309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44925979442272673930703539 67388969163409010896055309)
            ·
              refine ⟨25270863436278379086020741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67388969163409010896055309 25270863436278379086020741)
              ·
                refine ⟨4738286894302196078628889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25270863436278379086020741 4738286894302196078628889)
                ·
                  refine ⟨3553715170726647058971667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4738286894302196078628889 3553715170726647058971667)
                  ·
                    refine ⟨5330572756089970588457501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3553715170726647058971667 5330572756089970588457501)
                    ·
                      refine ⟨1998964783533738970671563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5330572756089970588457501 1998964783533738970671563)
                      ·
                        rfl

theorem cell23_3892970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_3892970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3892970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3892970 prefixEnd_3892970 := by exact prefixLift 3892970
  have htrace : WordTrace (prefixWord ++ tailWord_3892970) baseStart_3892970 baseEnd_3892970 := by
    simpa [prefixWord, tailWord_3892970, baseEnd_3892970] using wordTrace_append hprefix tailTrace_3892970
  have hstable : (prefixWord ++ tailWord_3892970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892970).length < 2 ^ (prefixWord ++ tailWord_3892970).sum := by decide
  have hdescent : baseEnd_3892970 < baseStart_3892970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893005 : List Nat := [1, 7, 2, 1, 2, 1, 2, 1, 1, 1, 4]
def baseStart_3893005 : Nat := 118140960795 + 3893005 * 2 ^ 59
def prefixEnd_3893005 : Nat := 4983230072969 + 3 ^ 40 * 3893005 * 2
def baseEnd_3893005 : Nat := 1998982755356646333733903

theorem tailTrace_3893005 : CollatzResearch.WordTrace tailWord_3893005 prefixEnd_3893005 1998982755356646333733903 := by
  unfold tailWord_3893005
  simp only [CollatzResearch.WordTrace]
  refine ⟨141989557261315232165920469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94659704840876821443946979 141989557261315232165920469)
  ·
    refine ⟨3327880248312075753888761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 141989557261315232165920469 3327880248312075753888761)
    ·
      refine ⟨2495910186234056815416571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3327880248312075753888761 2495910186234056815416571)
      ·
        refine ⟨3743865279351085223124857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2495910186234056815416571 3743865279351085223124857)
        ·
          refine ⟨2807898959513313917343643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3743865279351085223124857 2807898959513313917343643)
          ·
            refine ⟨4211848439269970876015465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2807898959513313917343643 4211848439269970876015465)
            ·
              refine ⟨3158886329452478157011599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4211848439269970876015465 3158886329452478157011599)
              ·
                refine ⟨4738329494178717235517399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3158886329452478157011599 4738329494178717235517399)
                ·
                  refine ⟨7107494241268075853276099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4738329494178717235517399 7107494241268075853276099)
                  ·
                    refine ⟨10661241361902113779914149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7107494241268075853276099 10661241361902113779914149)
                    ·
                      refine ⟨1998982755356646333733903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10661241361902113779914149 1998982755356646333733903)
                      ·
                        rfl

theorem cell23_3893005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_3893005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3893005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3893005 prefixEnd_3893005 := by exact prefixLift 3893005
  have htrace : WordTrace (prefixWord ++ tailWord_3893005) baseStart_3893005 baseEnd_3893005 := by
    simpa [prefixWord, tailWord_3893005, baseEnd_3893005] using wordTrace_append hprefix tailTrace_3893005
  have hstable : (prefixWord ++ tailWord_3893005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893005).length < 2 ^ (prefixWord ++ tailWord_3893005).sum := by decide
  have hdescent : baseEnd_3893005 < baseStart_3893005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893027 : List Nat := [1, 1, 1, 4, 2, 1, 5, 2, 2, 2, 2]
def baseStart_3893027 : Nat := 118140960795 + 3893027 * 2 ^ 59
def prefixEnd_3893027 : Nat := 4983230072969 + 3 ^ 40 * 3893027 * 2
def baseEnd_3893027 : Nat := 1998994051931045247658801

theorem tailTrace_3893027 : CollatzResearch.WordTrace tailWord_3893027 prefixEnd_3893027 1998994051931045247658801 := by
  unfold tailWord_3893027
  simp only [CollatzResearch.WordTrace]
  refine ⟨141990359667235529923221335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94660239778157019948814223 141990359667235529923221335)
  ·
    refine ⟨212985539500853294884832003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141990359667235529923221335 212985539500853294884832003)
    ·
      refine ⟨319478309251279942327248005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212985539500853294884832003 319478309251279942327248005)
      ·
        refine ⟨59902182984614989186359001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 319478309251279942327248005 59902182984614989186359001)
        ·
          refine ⟨44926637238461241889769251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59902182984614989186359001 44926637238461241889769251)
          ·
            refine ⟨67389955857691862834653877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44926637238461241889769251 67389955857691862834653877)
            ·
              refine ⟨6317808361658612140748801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67389955857691862834653877 6317808361658612140748801)
              ·
                refine ⟨4738356271243959105561601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6317808361658612140748801 4738356271243959105561601)
                ·
                  refine ⟨3553767203432969329171201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4738356271243959105561601 3553767203432969329171201)
                  ·
                    refine ⟨2665325402574726996878401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3553767203432969329171201 2665325402574726996878401)
                    ·
                      refine ⟨1998994051931045247658801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2665325402574726996878401 1998994051931045247658801)
                      ·
                        rfl

theorem cell23_3893027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 2, 2, 2, 2].length) (baseStart_3893027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3893027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3893027 prefixEnd_3893027 := by exact prefixLift 3893027
  have htrace : WordTrace (prefixWord ++ tailWord_3893027) baseStart_3893027 baseEnd_3893027 := by
    simpa [prefixWord, tailWord_3893027, baseEnd_3893027] using wordTrace_append hprefix tailTrace_3893027
  have hstable : (prefixWord ++ tailWord_3893027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893027).length < 2 ^ (prefixWord ++ tailWord_3893027).sum := by decide
  have hdescent : baseEnd_3893027 < baseStart_3893027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893044 : List Nat := [2, 5, 1, 1, 2, 3, 1, 1, 1, 4, 2]
def baseStart_3893044 : Nat := 118140960795 + 3893044 * 2 ^ 59
def prefixEnd_3893044 : Nat := 4983230072969 + 3 ^ 40 * 3893044 * 2
def baseEnd_3893044 : Nat := 1999002781102171681146223

theorem tailTrace_3893044 : CollatzResearch.WordTrace tailWord_3893044 prefixEnd_3893044 1999002781102171681146223 := by
  unfold tailWord_3893044
  simp only [CollatzResearch.WordTrace]
  refine ⟨70995489854086970913295093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94660653138782627884393457 70995489854086970913295093)
  ·
    refine ⟨6655827173820653523121415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70995489854086970913295093 6655827173820653523121415)
    ·
      refine ⟨9983740760730980284682123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6655827173820653523121415 9983740760730980284682123)
      ·
        refine ⟨14975611141096470427023185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9983740760730980284682123 14975611141096470427023185)
        ·
          refine ⟨11231708355822352820267389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14975611141096470427023185 11231708355822352820267389)
          ·
            refine ⟨4211890633433382307600271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11231708355822352820267389 4211890633433382307600271)
            ·
              refine ⟨6317835950150073461400407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4211890633433382307600271 6317835950150073461400407)
              ·
                refine ⟨9476753925225110192100611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6317835950150073461400407 9476753925225110192100611)
                ·
                  refine ⟨14215130887837665288150917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9476753925225110192100611 14215130887837665288150917)
                  ·
                    refine ⟨2665337041469562241528297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14215130887837665288150917 2665337041469562241528297)
                    ·
                      refine ⟨1999002781102171681146223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2665337041469562241528297 1999002781102171681146223)
                      ·
                        rfl

theorem cell23_3893044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_3893044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3893044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3893044 prefixEnd_3893044 := by exact prefixLift 3893044
  have htrace : WordTrace (prefixWord ++ tailWord_3893044) baseStart_3893044 baseEnd_3893044 := by
    simpa [prefixWord, tailWord_3893044, baseEnd_3893044] using wordTrace_append hprefix tailTrace_3893044
  have hstable : (prefixWord ++ tailWord_3893044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893044).length < 2 ^ (prefixWord ++ tailWord_3893044).sum := by decide
  have hdescent : baseEnd_3893044 < baseStart_3893044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893056 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 5]
def baseStart_3893056 : Nat := 118140960795 + 3893056 * 2 ^ 59
def prefixEnd_3893056 : Nat := 4983230072969 + 3 ^ 40 * 3893056 * 2
def baseEnd_3893056 : Nat := 1999008942870025634196167

theorem tailTrace_3893056 : CollatzResearch.WordTrace tailWord_3893056 prefixEnd_3893056 1999008942870025634196167 := by
  unfold tailWord_3893056
  simp only [CollatzResearch.WordTrace]
  refine ⟨70995708692065233938013511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94660944922753645250684681 70995708692065233938013511)
  ·
    refine ⟨106493563038097850907020267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70995708692065233938013511 106493563038097850907020267)
    ·
      refine ⟨159740344557146776360530401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106493563038097850907020267 159740344557146776360530401)
      ·
        refine ⟨119805258417860082270397801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159740344557146776360530401 119805258417860082270397801)
        ·
          refine ⟨89853943813395061702798351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119805258417860082270397801 89853943813395061702798351)
          ·
            refine ⟨134780915720092592554197527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89853943813395061702798351 134780915720092592554197527)
            ·
              refine ⟨202171373580138888831296291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134780915720092592554197527 202171373580138888831296291)
              ·
                refine ⟨303257060370208333246944437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202171373580138888831296291 303257060370208333246944437)
                ·
                  refine ⟨28430349409707031241901041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 303257060370208333246944437 28430349409707031241901041)
                  ·
                    refine ⟨21322762057280273431425781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28430349409707031241901041 21322762057280273431425781)
                    ·
                      refine ⟨1999008942870025634196167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21322762057280273431425781 1999008942870025634196167)
                      ·
                        rfl

theorem cell23_3893056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 5].length) (baseStart_3893056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3893056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3893056 prefixEnd_3893056 := by exact prefixLift 3893056
  have htrace : WordTrace (prefixWord ++ tailWord_3893056) baseStart_3893056 baseEnd_3893056 := by
    simpa [prefixWord, tailWord_3893056, baseEnd_3893056] using wordTrace_append hprefix tailTrace_3893056
  have hstable : (prefixWord ++ tailWord_3893056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893056).length < 2 ^ (prefixWord ++ tailWord_3893056).sum := by decide
  have hdescent : baseEnd_3893056 < baseStart_3893056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893084 : List Nat := [2, 2, 4, 2, 2, 1, 3, 2, 5]
def baseStart_3893084 : Nat := 118140960795 + 3893084 * 2 ^ 59
def prefixEnd_3893084 : Nat := 4983230072969 + 3 ^ 40 * 3893084 * 2
def baseEnd_3893084 : Nat := 222113702258705724960671

theorem tailTrace_3893084 : CollatzResearch.WordTrace tailWord_3893084 prefixEnd_3893084 222113702258705724960671 := by
  unfold tailWord_3893084
  simp only [CollatzResearch.WordTrace]
  refine ⟨70996219314014514329023153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94661625752019352438697537 70996219314014514329023153)
  ·
    refine ⟨53247164485510885746767365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70996219314014514329023153 53247164485510885746767365)
    ·
      refine ⟨9983843341033291077518881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53247164485510885746767365 9983843341033291077518881)
      ·
        refine ⟨7487882505774968308139161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9983843341033291077518881 7487882505774968308139161)
        ·
          refine ⟨5615911879331226231104371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7487882505774968308139161 5615911879331226231104371)
          ·
            refine ⟨8423867818996839346656557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5615911879331226231104371 8423867818996839346656557)
            ·
              refine ⟨3158950432123814754996209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8423867818996839346656557 3158950432123814754996209)
              ·
                refine ⟨2369212824092861066247157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3158950432123814754996209 2369212824092861066247157)
                ·
                  refine ⟨222113702258705724960671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2369212824092861066247157 222113702258705724960671)
                  ·
                    rfl

theorem cell23_3893084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 2, 5].length) (baseStart_3893084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3893084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3893084 prefixEnd_3893084 := by exact prefixLift 3893084
  have htrace : WordTrace (prefixWord ++ tailWord_3893084) baseStart_3893084 baseEnd_3893084 := by
    simpa [prefixWord, tailWord_3893084, baseEnd_3893084] using wordTrace_append hprefix tailTrace_3893084
  have hstable : (prefixWord ++ tailWord_3893084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893084).length < 2 ^ (prefixWord ++ tailWord_3893084).sum := by decide
  have hdescent : baseEnd_3893084 < baseStart_3893084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893090 : List Nat := [3, 3, 2, 1, 2, 2, 1, 1, 1, 2, 5]
def baseStart_3893090 : Nat := 118140960795 + 3893090 * 2 ^ 59
def prefixEnd_3893090 : Nat := 4983230072969 + 3 ^ 40 * 3893090 * 2
def baseEnd_3893090 : Nat := 1999026401212278501171011

theorem tailTrace_3893090 : CollatzResearch.WordTrace tailWord_3893090 prefixEnd_3893090 1999026401212278501171011 := by
  unfold tailWord_3893090
  simp only [CollatzResearch.WordTrace]
  refine ⟨35498164366501822920691181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94661771644004861121843149 35498164366501822920691181)
  ·
    refine ⟨13311811637438183595259193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35498164366501822920691181 13311811637438183595259193)
    ·
      refine ⟨9983858728078637696444395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13311811637438183595259193 9983858728078637696444395)
      ·
        refine ⟨14975788092117956544666593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9983858728078637696444395 14975788092117956544666593)
        ·
          refine ⟨11231841069088467408499945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14975788092117956544666593 11231841069088467408499945)
          ·
            refine ⟨8423880801816350556374959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11231841069088467408499945 8423880801816350556374959)
            ·
              refine ⟨12635821202724525834562439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8423880801816350556374959 12635821202724525834562439)
              ·
                refine ⟨18953731804086788751843659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12635821202724525834562439 18953731804086788751843659)
                ·
                  refine ⟨28430597706130183127765489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18953731804086788751843659 28430597706130183127765489)
                  ·
                    refine ⟨21322948279597637345824117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28430597706130183127765489 21322948279597637345824117)
                    ·
                      refine ⟨1999026401212278501171011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21322948279597637345824117 1999026401212278501171011)
                      ·
                        rfl

theorem cell23_3893090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_3893090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3893090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3893090 prefixEnd_3893090 := by exact prefixLift 3893090
  have htrace : WordTrace (prefixWord ++ tailWord_3893090) baseStart_3893090 baseEnd_3893090 := by
    simpa [prefixWord, tailWord_3893090, baseEnd_3893090] using wordTrace_append hprefix tailTrace_3893090
  have hstable : (prefixWord ++ tailWord_3893090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893090).length < 2 ^ (prefixWord ++ tailWord_3893090).sum := by decide
  have hdescent : baseEnd_3893090 < baseStart_3893090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893120 : List Nat := [2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 3]
def baseStart_3893120 : Nat := 118140960795 + 3893120 * 2 ^ 59
def prefixEnd_3893120 : Nat := 4983230072969 + 3 ^ 40 * 3893120 * 2
def baseEnd_3893120 : Nat := 1999041805631913383795873

theorem tailTrace_3893120 : CollatzResearch.WordTrace tailWord_3893120 prefixEnd_3893120 1999041805631913383795873 := by
  unfold tailWord_3893120
  simp only [CollatzResearch.WordTrace]
  refine ⟨70996875827949303403178407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94662501103932404537571209 70996875827949303403178407)
  ·
    refine ⟨106495313741923955104767611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70996875827949303403178407 106495313741923955104767611)
    ·
      refine ⟨159742970612885932657151417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106495313741923955104767611 159742970612885932657151417)
      ·
        refine ⟨119807227959664449492863563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159742970612885932657151417 119807227959664449492863563)
        ·
          refine ⟨179710841939496674239295345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119807227959664449492863563 179710841939496674239295345)
          ·
            refine ⟨134783131454622505679471509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179710841939496674239295345 134783131454622505679471509)
            ·
              refine ⟨6317959286935429953725227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 134783131454622505679471509 6317959286935429953725227)
              ·
                refine ⟨9476938930403144930587841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6317959286935429953725227 9476938930403144930587841)
                ·
                  refine ⟨7107704197802358697940881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9476938930403144930587841 7107704197802358697940881)
                  ·
                    refine ⟨5330778148351769023455661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7107704197802358697940881 5330778148351769023455661)
                    ·
                      refine ⟨1999041805631913383795873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5330778148351769023455661 1999041805631913383795873)
                      ·
                        rfl

theorem cell23_3893120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 3].length) (baseStart_3893120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3893120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3893120 prefixEnd_3893120 := by exact prefixLift 3893120
  have htrace : WordTrace (prefixWord ++ tailWord_3893120) baseStart_3893120 baseEnd_3893120 := by
    simpa [prefixWord, tailWord_3893120, baseEnd_3893120] using wordTrace_append hprefix tailTrace_3893120
  have hstable : (prefixWord ++ tailWord_3893120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893120).length < 2 ^ (prefixWord ++ tailWord_3893120).sum := by decide
  have hdescent : baseEnd_3893120 < baseStart_3893120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893140 : List Nat := [2, 4, 2, 1, 1, 2, 1, 4, 6]
def baseStart_3893140 : Nat := 118140960795 + 3893140 * 2 ^ 59
def prefixEnd_3893140 : Nat := 4983230072969 + 3 ^ 40 * 3893140 * 2
def baseEnd_3893140 : Nat := 222116897249444811727309

theorem tailTrace_3893140 : CollatzResearch.WordTrace tailWord_3893140 prefixEnd_3893140 222116897249444811727309 := by
  unfold tailWord_3893140
  simp only [CollatzResearch.WordTrace]
  refine ⟨70997240557913075111042437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94662987410550766814723249 70997240557913075111042437)
  ·
    refine ⟨13311982604608701583320457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70997240557913075111042437 13311982604608701583320457)
    ·
      refine ⟨9983986953456526187490343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13311982604608701583320457 9983986953456526187490343)
      ·
        refine ⟨14975980430184789281235515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9983986953456526187490343 14975980430184789281235515)
        ·
          refine ⟨22463970645277183921853273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14975980430184789281235515 22463970645277183921853273)
          ·
            refine ⟨16847977983957887941389955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22463970645277183921853273 16847977983957887941389955)
            ·
              refine ⟨25271966975936831912084933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16847977983957887941389955 25271966975936831912084933)
              ·
                refine ⟨4738493807988155983515925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25271966975936831912084933 4738493807988155983515925)
                ·
                  refine ⟨222116897249444811727309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4738493807988155983515925 222116897249444811727309)
                  ·
                    rfl

theorem cell23_3893140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 4, 6].length) (baseStart_3893140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3893140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3893140 prefixEnd_3893140 := by exact prefixLift 3893140
  have htrace : WordTrace (prefixWord ++ tailWord_3893140) baseStart_3893140 baseEnd_3893140 := by
    simpa [prefixWord, tailWord_3893140, baseEnd_3893140] using wordTrace_append hprefix tailTrace_3893140
  have hstable : (prefixWord ++ tailWord_3893140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893140).length < 2 ^ (prefixWord ++ tailWord_3893140).sum := by decide
  have hdescent : baseEnd_3893140 < baseStart_3893140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893183 : List Nat := [1, 1, 2, 2, 2, 1, 3, 4, 1, 6]
def baseStart_3893183 : Nat := 118140960795 + 3893183 * 2 ^ 59
def prefixEnd_3893183 : Nat := 4983230072969 + 3 ^ 40 * 3893183 * 2
def baseEnd_3893183 : Nat := 666358051637715545769361

theorem tailTrace_3893183 : CollatzResearch.WordTrace tailWord_3893183 prefixEnd_3893183 666358051637715545769361 := by
  unfold tailWord_3893183
  simp only [CollatzResearch.WordTrace]
  refine ⟨141996049454670368565900203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94664032969780245710600135 141996049454670368565900203)
  ·
    refine ⟨212994074182005552848850305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141996049454670368565900203 212994074182005552848850305)
    ·
      refine ⟨159745555636504164636637729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212994074182005552848850305 159745555636504164636637729)
      ·
        refine ⟨119809166727378123477478297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159745555636504164636637729 119809166727378123477478297)
        ·
          refine ⟨89856875045533592608108723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119809166727378123477478297 89856875045533592608108723)
          ·
            refine ⟨134785312568300388912163085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89856875045533592608108723 134785312568300388912163085)
            ·
              refine ⟨50544492213112645842061157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134785312568300388912163085 50544492213112645842061157)
              ·
                refine ⟨9477092289958621095386467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50544492213112645842061157 9477092289958621095386467)
                ·
                  refine ⟨14215638434937931643079701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9477092289958621095386467 14215638434937931643079701)
                  ·
                    refine ⟨666358051637715545769361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14215638434937931643079701 666358051637715545769361)
                    ·
                      rfl

theorem cell23_3893183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 6].length) (baseStart_3893183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3893183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3893183 prefixEnd_3893183 := by exact prefixLift 3893183
  have htrace : WordTrace (prefixWord ++ tailWord_3893183) baseStart_3893183 baseEnd_3893183 := by
    simpa [prefixWord, tailWord_3893183, baseEnd_3893183] using wordTrace_append hprefix tailTrace_3893183
  have hstable : (prefixWord ++ tailWord_3893183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893183).length < 2 ^ (prefixWord ++ tailWord_3893183).sum := by decide
  have hdescent : baseEnd_3893183 < baseStart_3893183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893184 : List Nat := [2, 1, 1, 2, 3, 2, 4, 3, 1, 1, 3]
def baseStart_3893184 : Nat := 118140960795 + 3893184 * 2 ^ 59
def prefixEnd_3893184 : Nat := 4983230072969 + 3 ^ 40 * 3893184 * 2
def baseEnd_3893184 : Nat := 1999074668393801133395579

theorem tailTrace_3893184 : CollatzResearch.WordTrace tailWord_3893184 prefixEnd_3893184 1999074668393801133395579 := by
  unfold tailWord_3893184
  simp only [CollatzResearch.WordTrace]
  refine ⟨70998042963833372868343303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94664057285111163824457737 70998042963833372868343303)
  ·
    refine ⟨106497064445750059302514955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70998042963833372868343303 106497064445750059302514955)
    ·
      refine ⟨159745596668625088953772433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106497064445750059302514955 159745596668625088953772433)
      ·
        refine ⟨119809197501468816715329325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159745596668625088953772433 119809197501468816715329325)
        ·
          refine ⟨44928449063050806268248497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119809197501468816715329325 44928449063050806268248497)
          ·
            refine ⟨33696336797288104701186373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44928449063050806268248497 33696336797288104701186373)
            ·
              refine ⟨6318063149491519631472445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33696336797288104701186373 6318063149491519631472445)
              ·
                refine ⟨2369273681059319861802167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6318063149491519631472445 2369273681059319861802167)
                ·
                  refine ⟨3553910521588979792703251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2369273681059319861802167 3553910521588979792703251)
                  ·
                    refine ⟨5330865782383469689054877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3553910521588979792703251 5330865782383469689054877)
                    ·
                      refine ⟨1999074668393801133395579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5330865782383469689054877 1999074668393801133395579)
                      ·
                        rfl

theorem cell23_3893184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 3, 1, 1, 3].length) (baseStart_3893184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3893184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3893184 prefixEnd_3893184 := by exact prefixLift 3893184
  have htrace : WordTrace (prefixWord ++ tailWord_3893184) baseStart_3893184 baseEnd_3893184 := by
    simpa [prefixWord, tailWord_3893184, baseEnd_3893184] using wordTrace_append hprefix tailTrace_3893184
  have hstable : (prefixWord ++ tailWord_3893184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893184).length < 2 ^ (prefixWord ++ tailWord_3893184).sum := by decide
  have hdescent : baseEnd_3893184 < baseStart_3893184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893230 : List Nat := [4, 1, 2, 1, 3, 2, 1, 9]
def baseStart_3893230 : Nat := 118140960795 + 3893230 * 2 ^ 59
def prefixEnd_3893230 : Nat := 4983230072969 + 3 ^ 40 * 3893230 * 2
def baseEnd_3893230 : Nat := 74040677351996590867421

theorem tailTrace_3893230 : CollatzResearch.WordTrace tailWord_3893230 prefixEnd_3893230 74040677351996590867421 := by
  unfold tailWord_3893230
  simp only [CollatzResearch.WordTrace]
  refine ⟨17749720460687511949107643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94665175790333397061907429 17749720460687511949107643)
  ·
    refine ⟨26624580691031267923661465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17749720460687511949107643 26624580691031267923661465)
    ·
      refine ⟨19968435518273450942746099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26624580691031267923661465 19968435518273450942746099)
      ·
        refine ⟨29952653277410176414119149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19968435518273450942746099 29952653277410176414119149)
        ·
          refine ⟨11232244979028816155294681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29952653277410176414119149 11232244979028816155294681)
          ·
            refine ⟨8424183734271612116471011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11232244979028816155294681 8424183734271612116471011)
            ·
              refine ⟨12636275601407418174706517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8424183734271612116471011 12636275601407418174706517)
              ·
                refine ⟨74040677351996590867421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12636275601407418174706517 74040677351996590867421)
                ·
                  rfl

theorem cell23_3893230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 9].length) (baseStart_3893230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3893230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3893230 prefixEnd_3893230 := by exact prefixLift 3893230
  have htrace : WordTrace (prefixWord ++ tailWord_3893230) baseStart_3893230 baseEnd_3893230 := by
    simpa [prefixWord, tailWord_3893230, baseEnd_3893230] using wordTrace_append hprefix tailTrace_3893230
  have hstable : (prefixWord ++ tailWord_3893230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893230).length < 2 ^ (prefixWord ++ tailWord_3893230).sum := by decide
  have hdescent : baseEnd_3893230 < baseStart_3893230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893240 : List Nat := [2, 1, 2, 1, 1, 3, 2, 4, 1, 3, 3]
def baseStart_3893240 : Nat := 118140960795 + 3893240 * 2 ^ 59
def prefixEnd_3893240 : Nat := 4983230072969 + 3 ^ 40 * 3893240 * 2
def baseEnd_3893240 : Nat := 1999103423310452914295321

theorem tailTrace_3893240 : CollatzResearch.WordTrace tailWord_3893240 prefixEnd_3893240 1999103423310452914295321 := by
  unfold tailWord_3893240
  simp only [CollatzResearch.WordTrace]
  refine ⟨70999064207731933650362587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94665418943642578200483449 70999064207731933650362587)
  ·
    refine ⟨106498596311597900475543881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70999064207731933650362587 106498596311597900475543881)
    ·
      refine ⟨79873947233698425356657911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106498596311597900475543881 79873947233698425356657911)
      ·
        refine ⟨119810920850547638034986867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79873947233698425356657911 119810920850547638034986867)
        ·
          refine ⟨179716381275821457052480301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119810920850547638034986867 179716381275821457052480301)
          ·
            refine ⟨67393642978433046394680113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179716381275821457052480301 67393642978433046394680113)
            ·
              refine ⟨50545232233824784796010085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67393642978433046394680113 50545232233824784796010085)
              ·
                refine ⟨9477231043842147149251891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50545232233824784796010085 9477231043842147149251891)
                ·
                  refine ⟨14215846565763220723877837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9477231043842147149251891 14215846565763220723877837)
                  ·
                    refine ⟨5330942462161207771454189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14215846565763220723877837 5330942462161207771454189)
                    ·
                      refine ⟨1999103423310452914295321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5330942462161207771454189 1999103423310452914295321)
                      ·
                        rfl

theorem cell23_3893240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 1, 3, 3].length) (baseStart_3893240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3893240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3893240 prefixEnd_3893240 := by exact prefixLift 3893240
  have htrace : WordTrace (prefixWord ++ tailWord_3893240) baseStart_3893240 baseEnd_3893240 := by
    simpa [prefixWord, tailWord_3893240, baseEnd_3893240] using wordTrace_append hprefix tailTrace_3893240
  have hstable : (prefixWord ++ tailWord_3893240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893240).length < 2 ^ (prefixWord ++ tailWord_3893240).sum := by decide
  have hdescent : baseEnd_3893240 < baseStart_3893240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893241 : List Nat := [1, 2, 1, 3, 1, 4, 3, 3, 1, 2, 2]
def baseStart_3893241 : Nat := 118140960795 + 3893241 * 2 ^ 59
def prefixEnd_3893241 : Nat := 4983230072969 + 3 ^ 40 * 3893241 * 2
def baseEnd_3893241 : Nat := 1999103936791107410382817

theorem tailTrace_3893241 : CollatzResearch.WordTrace tailWord_3893241 prefixEnd_3893241 1999103936791107410382817 := by
  unfold tailWord_3893241
  simp only [CollatzResearch.WordTrace]
  refine ⟨141998164888460244471511577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94665443258973496314341051 141998164888460244471511577)
  ·
    refine ⟨106498623666345183353633683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141998164888460244471511577 106498623666345183353633683)
    ·
      refine ⟨159747935499517775030450525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106498623666345183353633683 159747935499517775030450525)
      ·
        refine ⟨59905475812319165636418947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159747935499517775030450525 59905475812319165636418947)
        ·
          refine ⟨89858213718478748454628421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59905475812319165636418947 89858213718478748454628421)
          ·
            refine ⟨16848415072214765335242829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89858213718478748454628421 16848415072214765335242829)
            ·
              refine ⟨6318155652080537000716061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16848415072214765335242829 6318155652080537000716061)
              ·
                refine ⟨2369308369530201375268523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6318155652080537000716061 2369308369530201375268523)
                ·
                  refine ⟨3553962554295302062902785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2369308369530201375268523 3553962554295302062902785)
                  ·
                    refine ⟨2665471915721476547177089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3553962554295302062902785 2665471915721476547177089)
                    ·
                      refine ⟨1999103936791107410382817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2665471915721476547177089 1999103936791107410382817)
                      ·
                        rfl

theorem cell23_3893241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 3, 1, 2, 2].length) (baseStart_3893241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3893241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3893241 prefixEnd_3893241 := by exact prefixLift 3893241
  have htrace : WordTrace (prefixWord ++ tailWord_3893241) baseStart_3893241 baseEnd_3893241 := by
    simpa [prefixWord, tailWord_3893241, baseEnd_3893241] using wordTrace_append hprefix tailTrace_3893241
  have hstable : (prefixWord ++ tailWord_3893241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893241).length < 2 ^ (prefixWord ++ tailWord_3893241).sum := by decide
  have hdescent : baseEnd_3893241 < baseStart_3893241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893258 : List Nat := [3, 1, 2, 2, 5, 1, 1, 1, 3, 2, 2]
def baseStart_3893258 : Nat := 118140960795 + 3893258 * 2 ^ 59
def prefixEnd_3893258 : Nat := 4983230072969 + 3 ^ 40 * 3893258 * 2
def baseEnd_3893258 : Nat := 1999112665962233843870239

theorem tailTrace_3893258 : CollatzResearch.WordTrace tailWord_3893258 prefixEnd_3893258 1999112665962233843870239 := by
  unfold tailWord_3893258
  simp only [CollatzResearch.WordTrace]
  refine ⟨35499696232349664093720107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94665856619599104249920285 35499696232349664093720107)
  ·
    refine ⟨53249544348524496140580161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35499696232349664093720107 53249544348524496140580161)
    ·
      refine ⟨39937158261393372105435121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53249544348524496140580161 39937158261393372105435121)
      ·
        refine ⟨29952868696045029079076341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39937158261393372105435121 29952868696045029079076341)
        ·
          refine ⟨2808081440254221476163407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29952868696045029079076341 2808081440254221476163407)
          ·
            refine ⟨4212122160381332214245111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2808081440254221476163407 4212122160381332214245111)
            ·
              refine ⟨6318183240571998321367667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4212122160381332214245111 6318183240571998321367667)
              ·
                refine ⟨9477274860857997482051501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6318183240571998321367667 9477274860857997482051501)
                ·
                  refine ⟨3553978072821749055769313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9477274860857997482051501 3553978072821749055769313)
                  ·
                    refine ⟨2665483554616311791826985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3553978072821749055769313 2665483554616311791826985)
                    ·
                      refine ⟨1999112665962233843870239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2665483554616311791826985 1999112665962233843870239)
                      ·
                        rfl

theorem cell23_3893258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 3, 2, 2].length) (baseStart_3893258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3893258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3893258 prefixEnd_3893258 := by exact prefixLift 3893258
  have htrace : WordTrace (prefixWord ++ tailWord_3893258) baseStart_3893258 baseEnd_3893258 := by
    simpa [prefixWord, tailWord_3893258, baseEnd_3893258] using wordTrace_append hprefix tailTrace_3893258
  have hstable : (prefixWord ++ tailWord_3893258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893258).length < 2 ^ (prefixWord ++ tailWord_3893258).sum := by decide
  have hdescent : baseEnd_3893258 < baseStart_3893258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893273 : List Nat := [1, 2, 1, 2, 1, 1, 3, 3, 1, 8]
def baseStart_3893273 : Nat := 118140960795 + 3893273 * 2 ^ 59
def prefixEnd_3893273 : Nat := 4983230072969 + 3 ^ 40 * 3893273 * 2
def baseEnd_3893273 : Nat := 666373456057350428394223

theorem tailTrace_3893273 : CollatzResearch.WordTrace tailWord_3893273 prefixEnd_3893273 666373456057350428394223 := by
  unfold tailWord_3893273
  simp only [CollatzResearch.WordTrace]
  refine ⟨141999332024344313936676473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94666221349562875957784315 141999332024344313936676473)
  ·
    refine ⟨106499499018258235452507355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141999332024344313936676473 106499499018258235452507355)
    ·
      refine ⟨159749248527387353178761033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106499499018258235452507355 159749248527387353178761033)
      ·
        refine ⟨119811936395540514884070775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159749248527387353178761033 119811936395540514884070775)
        ·
          refine ⟨179717904593310772326106163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119811936395540514884070775 179717904593310772326106163)
          ·
            refine ⟨269576856889966158489159245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179717904593310772326106163 269576856889966158489159245)
            ·
              refine ⟨101091321333737309433434717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 269576856889966158489159245 101091321333737309433434717)
              ·
                refine ⟨37909245500151491037538019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101091321333737309433434717 37909245500151491037538019)
                ·
                  refine ⟨56863868250227236556307029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37909245500151491037538019 56863868250227236556307029)
                  ·
                    refine ⟨666373456057350428394223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 56863868250227236556307029 666373456057350428394223)
                    ·
                      rfl

theorem cell23_3893273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 8].length) (baseStart_3893273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3893273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3893273 prefixEnd_3893273 := by exact prefixLift 3893273
  have htrace : WordTrace (prefixWord ++ tailWord_3893273) baseStart_3893273 baseEnd_3893273 := by
    simpa [prefixWord, tailWord_3893273, baseEnd_3893273] using wordTrace_append hprefix tailTrace_3893273
  have hstable : (prefixWord ++ tailWord_3893273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893273).length < 2 ^ (prefixWord ++ tailWord_3893273).sum := by decide
  have hdescent : baseEnd_3893273 < baseStart_3893273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893274 : List Nat := [3, 1, 1, 3, 1, 4, 1, 3, 2, 1, 3]
def baseStart_3893274 : Nat := 118140960795 + 3893274 * 2 ^ 59
def prefixEnd_3893274 : Nat := 4983230072969 + 3 ^ 40 * 3893274 * 2
def baseEnd_3893274 : Nat := 1999120881652705781270165

theorem tailTrace_3893274 : CollatzResearch.WordTrace tailWord_3893274 prefixEnd_3893274 1999120881652705781270165 := by
  unfold tailWord_3893274
  simp only [CollatzResearch.WordTrace]
  refine ⟨35499842124335172776865719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94666245664893794071641917 35499842124335172776865719)
  ·
    refine ⟨53249763186502759165298579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35499842124335172776865719 53249763186502759165298579)
    ·
      refine ⟨79874644779754138747947869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53249763186502759165298579 79874644779754138747947869)
      ·
        refine ⟨29952991792407802030480451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79874644779754138747947869 29952991792407802030480451)
        ·
          refine ⟨44929487688611703045720677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29952991792407802030480451 44929487688611703045720677)
          ·
            refine ⟨8424278941614694321072627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44929487688611703045720677 8424278941614694321072627)
            ·
              refine ⟨12636418412422041481608941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8424278941614694321072627 12636418412422041481608941)
              ·
                refine ⟨4738656904658265555603353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12636418412422041481608941 4738656904658265555603353)
                ·
                  refine ⟨3553992678493699166702515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4738656904658265555603353 3553992678493699166702515)
                  ·
                    refine ⟨5330989017740548750053773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3553992678493699166702515 5330989017740548750053773)
                    ·
                      refine ⟨1999120881652705781270165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5330989017740548750053773 1999120881652705781270165)
                      ·
                        rfl

theorem cell23_3893274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_3893274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3893274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3893274 prefixEnd_3893274 := by exact prefixLift 3893274
  have htrace : WordTrace (prefixWord ++ tailWord_3893274) baseStart_3893274 baseEnd_3893274 := by
    simpa [prefixWord, tailWord_3893274, baseEnd_3893274] using wordTrace_append hprefix tailTrace_3893274
  have hstable : (prefixWord ++ tailWord_3893274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893274).length < 2 ^ (prefixWord ++ tailWord_3893274).sum := by decide
  have hdescent : baseEnd_3893274 < baseStart_3893274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893297 : List Nat := [1, 2, 2, 3, 1, 3, 1, 1, 3, 4, 2]
def baseStart_3893297 : Nat := 118140960795 + 3893297 * 2 ^ 59
def prefixEnd_3893297 : Nat := 4983230072969 + 3 ^ 40 * 3893297 * 2
def baseEnd_3893297 : Nat := 1999132691707759191282559

theorem tailTrace_3893297 : CollatzResearch.WordTrace tailWord_3893297 prefixEnd_3893297 1999132691707759191282559 := by
  unfold tailWord_3893297
  simp only [CollatzResearch.WordTrace]
  refine ⟨142000207376257366035550145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94666804917504910690366763 142000207376257366035550145)
  ·
    refine ⟨106500155532193024526662609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142000207376257366035550145 106500155532193024526662609)
    ·
      refine ⟨79875116649144768394996957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106500155532193024526662609 79875116649144768394996957)
      ·
        refine ⟨29953168743429288148123859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79875116649144768394996957 29953168743429288148123859)
        ·
          refine ⟨44929753115143932222185789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29953168743429288148123859 44929753115143932222185789)
          ·
            refine ⟨16848657418178974583319671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44929753115143932222185789 16848657418178974583319671)
            ·
              refine ⟨25272986127268461874979507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16848657418178974583319671 25272986127268461874979507)
              ·
                refine ⟨37909479190902692812469261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25272986127268461874979507 37909479190902692812469261)
                ·
                  refine ⟨14216054696588509804675973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37909479190902692812469261 14216054696588509804675973)
                  ·
                    refine ⟨2665510255610345588376745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14216054696588509804675973 2665510255610345588376745)
                    ·
                      refine ⟨1999132691707759191282559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2665510255610345588376745 1999132691707759191282559)
                      ·
                        rfl

theorem cell23_3893297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 4, 2].length) (baseStart_3893297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3893297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3893297 prefixEnd_3893297 := by exact prefixLift 3893297
  have htrace : WordTrace (prefixWord ++ tailWord_3893297) baseStart_3893297 baseEnd_3893297 := by
    simpa [prefixWord, tailWord_3893297, baseEnd_3893297] using wordTrace_append hprefix tailTrace_3893297
  have hstable : (prefixWord ++ tailWord_3893297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893297).length < 2 ^ (prefixWord ++ tailWord_3893297).sum := by decide
  have hdescent : baseEnd_3893297 < baseStart_3893297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893397 : List Nat := [1, 3, 2, 1, 1, 1, 3, 4, 3, 4]
def baseStart_3893397 : Nat := 118140960795 + 3893397 * 2 ^ 59
def prefixEnd_3893397 : Nat := 4983230072969 + 3 ^ 40 * 3893397 * 2
def baseEnd_3893397 : Nat := 666394679924402933344033

theorem tailTrace_3893397 : CollatzResearch.WordTrace tailWord_3893397 prefixEnd_3893397 666394679924402933344033 := by
  unfold tailWord_3893397
  simp only [CollatzResearch.WordTrace]
  refine ⟨142003854675895083114190445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94669236450596722076126963 142003854675895083114190445)
  ·
    refine ⟨53251445503460656167821417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142003854675895083114190445 53251445503460656167821417)
    ·
      refine ⟨39938584127595492125866063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53251445503460656167821417 39938584127595492125866063)
      ·
        refine ⟨59907876191393238188799095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39938584127595492125866063 59907876191393238188799095)
        ·
          refine ⟨89861814287089857283198643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59907876191393238188799095 89861814287089857283198643)
          ·
            refine ⟨134792721430634785924797965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89861814287089857283198643 134792721430634785924797965)
            ·
              refine ⟨50547270536488044721799237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134792721430634785924797965 50547270536488044721799237)
              ·
                refine ⟨9477613225591508385337357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50547270536488044721799237 9477613225591508385337357)
                ·
                  refine ⟨3554104959596815644501509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9477613225591508385337357 3554104959596815644501509)
                  ·
                    refine ⟨666394679924402933344033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3554104959596815644501509 666394679924402933344033)
                    ·
                      rfl

theorem cell23_3893397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 3, 4].length) (baseStart_3893397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3893397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3893397 prefixEnd_3893397 := by exact prefixLift 3893397
  have htrace : WordTrace (prefixWord ++ tailWord_3893397) baseStart_3893397 baseEnd_3893397 := by
    simpa [prefixWord, tailWord_3893397, baseEnd_3893397] using wordTrace_append hprefix tailTrace_3893397
  have hstable : (prefixWord ++ tailWord_3893397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893397).length < 2 ^ (prefixWord ++ tailWord_3893397).sum := by decide
  have hdescent : baseEnd_3893397 < baseStart_3893397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893428 : List Nat := [2, 5, 3, 1, 1, 1, 1, 1, 1, 2, 5]
def baseStart_3893428 : Nat := 118140960795 + 3893428 * 2 ^ 59
def prefixEnd_3893428 : Nat := 4983230072969 + 3 ^ 40 * 3893428 * 2
def baseEnd_3893428 : Nat := 1999199957673498178744457

theorem tailTrace_3893428 : CollatzResearch.WordTrace tailWord_3893428 prefixEnd_3893428 1999199957673498178744457 := by
  unfold tailWord_3893428
  simp only [CollatzResearch.WordTrace]
  refine ⟨71002492669391387704284469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94669990225855183605712625 71002492669391387704284469)
  ·
    refine ⟨6656483687755442597276669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71002492669391387704284469 6656483687755442597276669)
    ·
      refine ⟨2496181382908290973978751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6656483687755442597276669 2496181382908290973978751)
      ·
        refine ⟨3744272074362436460968127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2496181382908290973978751 3744272074362436460968127)
        ·
          refine ⟨5616408111543654691452191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3744272074362436460968127 5616408111543654691452191)
          ·
            refine ⟨8424612167315482037178287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5616408111543654691452191 8424612167315482037178287)
            ·
              refine ⟨12636918250973223055767431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8424612167315482037178287 12636918250973223055767431)
              ·
                refine ⟨18955377376459834583651147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12636918250973223055767431 18955377376459834583651147)
                ·
                  refine ⟨28433066064689751875476721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18955377376459834583651147 28433066064689751875476721)
                  ·
                    refine ⟨21324799548517313906607541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28433066064689751875476721 21324799548517313906607541)
                    ·
                      refine ⟨1999199957673498178744457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21324799548517313906607541 1999199957673498178744457)
                      ·
                        rfl

theorem cell23_3893428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_3893428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3893428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3893428 prefixEnd_3893428 := by exact prefixLift 3893428
  have htrace : WordTrace (prefixWord ++ tailWord_3893428) baseStart_3893428 baseEnd_3893428 := by
    simpa [prefixWord, tailWord_3893428, baseEnd_3893428] using wordTrace_append hprefix tailTrace_3893428
  have hstable : (prefixWord ++ tailWord_3893428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893428).length < 2 ^ (prefixWord ++ tailWord_3893428).sum := by decide
  have hdescent : baseEnd_3893428 < baseStart_3893428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893444 : List Nat := [2, 3, 3, 1, 2, 2, 1, 3, 6]
def baseStart_3893444 : Nat := 118140960795 + 3893444 * 2 ^ 59
def prefixEnd_3893444 : Nat := 4983230072969 + 3 ^ 40 * 3893444 * 2
def baseEnd_3893444 : Nat := 222134241484885568460487

theorem tailTrace_3893444 : CollatzResearch.WordTrace tailWord_3893444 prefixEnd_3893444 222134241484885568460487 := by
  unfold tailWord_3893444
  simp only [CollatzResearch.WordTrace]
  refine ⟨71002784453362405070575693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94670379271149873427434257 71002784453362405070575693)
  ·
    refine ⟨26626044170010901901465885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71002784453362405070575693 26626044170010901901465885)
    ·
      refine ⟨9984766563754088213049707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26626044170010901901465885 9984766563754088213049707)
      ·
        refine ⟨14977149845631132319574561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9984766563754088213049707 14977149845631132319574561)
        ·
          refine ⟨11232862384223349239680921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14977149845631132319574561 11232862384223349239680921)
          ·
            refine ⟨8424646788167511929760691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11232862384223349239680921 8424646788167511929760691)
            ·
              refine ⟨12636970182251267894641037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8424646788167511929760691 12636970182251267894641037)
              ·
                refine ⟨4738863818344225460490389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12636970182251267894641037 4738863818344225460490389)
                ·
                  refine ⟨222134241484885568460487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4738863818344225460490389 222134241484885568460487)
                  ·
                    rfl

theorem cell23_3893444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 3, 6].length) (baseStart_3893444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3893444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3893444 prefixEnd_3893444 := by exact prefixLift 3893444
  have htrace : WordTrace (prefixWord ++ tailWord_3893444) baseStart_3893444 baseEnd_3893444 := by
    simpa [prefixWord, tailWord_3893444, baseEnd_3893444] using wordTrace_append hprefix tailTrace_3893444
  have hstable : (prefixWord ++ tailWord_3893444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893444).length < 2 ^ (prefixWord ++ tailWord_3893444).sum := by decide
  have hdescent : baseEnd_3893444 < baseStart_3893444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893471 : List Nat := [1, 1, 2, 3, 2, 1, 1, 7, 1, 1, 3]
def baseStart_3893471 : Nat := 118140960795 + 3893471 * 2 ^ 59
def prefixEnd_3893471 : Nat := 4983230072969 + 3 ^ 40 * 3893471 * 2
def baseEnd_3893471 : Nat := 1999222037341641510506759

theorem tailTrace_3893471 : CollatzResearch.WordTrace tailWord_3893471 prefixEnd_3893471 1999222037341641510506759 := by
  unfold tailWord_3893471
  simp only [CollatzResearch.WordTrace]
  refine ⟨142006553677626993752384267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94671035785084662501589511 142006553677626993752384267)
  ·
    refine ⟨213009830516440490628576401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142006553677626993752384267 213009830516440490628576401)
    ·
      refine ⟨159757372887330367971432301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213009830516440490628576401 159757372887330367971432301)
      ·
        refine ⟨59909014832748887989287113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159757372887330367971432301 59909014832748887989287113)
        ·
          refine ⟨44931761124561665991965335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59909014832748887989287113 44931761124561665991965335)
          ·
            refine ⟨67397641686842498987948003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44931761124561665991965335 67397641686842498987948003)
            ·
              refine ⟨101096462530263748481922005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67397641686842498987948003 101096462530263748481922005)
              ·
                refine ⟨2369448340553056605045047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 101096462530263748481922005 2369448340553056605045047)
                ·
                  refine ⟨3554172510829584907567571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2369448340553056605045047 3554172510829584907567571)
                  ·
                    refine ⟨5331258766244377361351357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3554172510829584907567571 5331258766244377361351357)
                    ·
                      refine ⟨1999222037341641510506759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5331258766244377361351357 1999222037341641510506759)
                      ·
                        rfl

theorem cell23_3893471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 7, 1, 1, 3].length) (baseStart_3893471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3893471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3893471 prefixEnd_3893471 := by exact prefixLift 3893471
  have htrace : WordTrace (prefixWord ++ tailWord_3893471) baseStart_3893471 baseEnd_3893471 := by
    simpa [prefixWord, tailWord_3893471, baseEnd_3893471] using wordTrace_append hprefix tailTrace_3893471
  have hstable : (prefixWord ++ tailWord_3893471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893471).length < 2 ^ (prefixWord ++ tailWord_3893471).sum := by decide
  have hdescent : baseEnd_3893471 < baseStart_3893471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893494 : List Nat := [5, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4]
def baseStart_3893494 : Nat := 118140960795 + 3893494 * 2 ^ 59
def prefixEnd_3893494 : Nat := 4983230072969 + 3 ^ 40 * 3893494 * 2
def baseEnd_3893494 : Nat := 1999233847396694920519153

theorem tailTrace_3893494 : CollatzResearch.WordTrace tailWord_3893494 prefixEnd_3893494 1999233847396694920519153 := by
  unfold tailWord_3893494
  simp only [CollatzResearch.WordTrace]
  refine ⟨8875462034783979292529471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94671595037695779120314357 8875462034783979292529471)
  ·
    refine ⟨13313193052175968938794207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8875462034783979292529471 13313193052175968938794207)
    ·
      refine ⟨19969789578263953408191311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13313193052175968938794207 19969789578263953408191311)
      ·
        refine ⟨29954684367395930112286967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19969789578263953408191311 29954684367395930112286967)
        ·
          refine ⟨44932026551093895168430451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29954684367395930112286967 44932026551093895168430451)
          ·
            refine ⟨67398039826640842752645677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44932026551093895168430451 67398039826640842752645677)
            ·
              refine ⟨25274264934990316032242129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67398039826640842752645677 25274264934990316032242129)
              ·
                refine ⟨18955698701242737024181597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25274264934990316032242129 18955698701242737024181597)
                ·
                  refine ⟨7108387012966026384068099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18955698701242737024181597 7108387012966026384068099)
                  ·
                    refine ⟨10662580519449039576102149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7108387012966026384068099 10662580519449039576102149)
                    ·
                      refine ⟨1999233847396694920519153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10662580519449039576102149 1999233847396694920519153)
                      ·
                        rfl

theorem cell23_3893494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_3893494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3893494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3893494 prefixEnd_3893494 := by exact prefixLift 3893494
  have htrace : WordTrace (prefixWord ++ tailWord_3893494) baseStart_3893494 baseEnd_3893494 := by
    simpa [prefixWord, tailWord_3893494, baseEnd_3893494] using wordTrace_append hprefix tailTrace_3893494
  have hstable : (prefixWord ++ tailWord_3893494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893494).length < 2 ^ (prefixWord ++ tailWord_3893494).sum := by decide
  have hdescent : baseEnd_3893494 < baseStart_3893494 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893504 : List Nat := [2, 1, 1, 2, 1, 1, 6, 3, 2, 4]
def baseStart_3893504 : Nat := 118140960795 + 3893504 * 2 ^ 59
def prefixEnd_3893504 : Nat := 4983230072969 + 3 ^ 40 * 3893504 * 2
def baseEnd_3893504 : Nat := 666412994067746627131369

theorem tailTrace_3893504 : CollatzResearch.WordTrace tailWord_3893504 prefixEnd_3893504 666412994067746627131369 := by
  unfold tailWord_3893504
  simp only [CollatzResearch.WordTrace]
  refine ⟨71003878643253720194167783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94671838191004960258890377 71003878643253720194167783)
  ·
    refine ⟨106505817964880580291251675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71003878643253720194167783 106505817964880580291251675)
    ·
      refine ⟨159758726947320870436877513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106505817964880580291251675 159758726947320870436877513)
      ·
        refine ⟨119819045210490652827658135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159758726947320870436877513 119819045210490652827658135)
        ·
          refine ⟨179728567815735979241487203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119819045210490652827658135 179728567815735979241487203)
          ·
            refine ⟨269592851723603968862230805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179728567815735979241487203 269592851723603968862230805)
            ·
              refine ⟨12637164924543936040417069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 269592851723603968862230805 12637164924543936040417069)
              ·
                refine ⟨4738936846703976015156401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12637164924543936040417069 4738936846703976015156401)
                ·
                  refine ⟨3554202635027982011367301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4738936846703976015156401 3554202635027982011367301)
                  ·
                    refine ⟨666412994067746627131369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3554202635027982011367301 666412994067746627131369)
                    ·
                      rfl

theorem cell23_3893504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 3, 2, 4].length) (baseStart_3893504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3893504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3893504 prefixEnd_3893504 := by exact prefixLift 3893504
  have htrace : WordTrace (prefixWord ++ tailWord_3893504) baseStart_3893504 baseEnd_3893504 := by
    simpa [prefixWord, tailWord_3893504, baseEnd_3893504] using wordTrace_append hprefix tailTrace_3893504
  have hstable : (prefixWord ++ tailWord_3893504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893504).length < 2 ^ (prefixWord ++ tailWord_3893504).sum := by decide
  have hdescent : baseEnd_3893504 < baseStart_3893504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893514 : List Nat := [3, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3]
def baseStart_3893514 : Nat := 118140960795 + 3893514 * 2 ^ 59
def prefixEnd_3893514 : Nat := 4983230072969 + 3 ^ 40 * 3893514 * 2
def baseEnd_3893514 : Nat := 1999244117009784842269061

theorem tailTrace_3893514 : CollatzResearch.WordTrace tailWord_3893514 prefixEnd_3893514 1999244117009784842269061 := by
  unfold tailWord_3893514
  simp only [CollatzResearch.WordTrace]
  refine ⟨35502030504117803024049899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94672081344314141397466397 35502030504117803024049899)
  ·
    refine ⟨53253045756176704536074849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35502030504117803024049899 53253045756176704536074849)
    ·
      refine ⟨39939784317132528402056137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53253045756176704536074849 39939784317132528402056137)
      ·
        refine ⟨29954838237849396301542103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39939784317132528402056137 29954838237849396301542103)
        ·
          refine ⟨44932257356774094452313155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29954838237849396301542103 44932257356774094452313155)
          ·
            refine ⟨67398386035161141678469733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44932257356774094452313155 67398386035161141678469733)
            ·
              refine ⟨12637197381592714064713075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67398386035161141678469733 12637197381592714064713075)
              ·
                refine ⟨18955796072389071097069613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12637197381592714064713075 18955796072389071097069613)
                ·
                  refine ⟨7108423527145901661401105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18955796072389071097069613 7108423527145901661401105)
                  ·
                    refine ⟨5331317645359426246050829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7108423527145901661401105 5331317645359426246050829)
                    ·
                      refine ⟨1999244117009784842269061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5331317645359426246050829 1999244117009784842269061)
                      ·
                        rfl

theorem cell23_3893514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_3893514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3893514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3893514 prefixEnd_3893514 := by exact prefixLift 3893514
  have htrace : WordTrace (prefixWord ++ tailWord_3893514) baseStart_3893514 baseEnd_3893514 := by
    simpa [prefixWord, tailWord_3893514, baseEnd_3893514] using wordTrace_append hprefix tailTrace_3893514
  have hstable : (prefixWord ++ tailWord_3893514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893514).length < 2 ^ (prefixWord ++ tailWord_3893514).sum := by decide
  have hdescent : baseEnd_3893514 < baseStart_3893514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893531 : List Nat := [1, 1, 1, 1, 1, 1, 10, 1, 1, 2, 3]
def baseStart_3893531 : Nat := 118140960795 + 3893531 * 2 ^ 59
def prefixEnd_3893531 : Nat := 4983230072969 + 3 ^ 40 * 3893531 * 2
def baseEnd_3893531 : Nat := 1999252846180911275756483

theorem tailTrace_3893531 : CollatzResearch.WordTrace tailWord_3893531 prefixEnd_3893531 1999252846180911275756483 := by
  unfold tailWord_3893531
  simp only [CollatzResearch.WordTrace]
  refine ⟨142008742057409623999568447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94672494704939749333045631 142008742057409623999568447)
  ·
    refine ⟨213013113086114435999352671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142008742057409623999568447 213013113086114435999352671)
    ·
      refine ⟨319519669629171653999029007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213013113086114435999352671 319519669629171653999029007)
      ·
        refine ⟨479279504443757480998543511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319519669629171653999029007 479279504443757480998543511)
        ·
          refine ⟨718919256665636221497815267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 479279504443757480998543511 718919256665636221497815267)
          ·
            refine ⟨1078378884998454332246722901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 718919256665636221497815267 1078378884998454332246722901)
            ·
              refine ⟨3159313139643909176504071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1078378884998454332246722901 3159313139643909176504071)
              ·
                refine ⟨4738969709465863764756107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3159313139643909176504071 4738969709465863764756107)
                ·
                  refine ⟨7108454564198795647134161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4738969709465863764756107 7108454564198795647134161)
                  ·
                    refine ⟨5331340923149096735350621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7108454564198795647134161 5331340923149096735350621)
                    ·
                      refine ⟨1999252846180911275756483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5331340923149096735350621 1999252846180911275756483)
                      ·
                        rfl

theorem cell23_3893531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 1, 1, 2, 3].length) (baseStart_3893531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3893531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3893531 prefixEnd_3893531 := by exact prefixLift 3893531
  have htrace : WordTrace (prefixWord ++ tailWord_3893531) baseStart_3893531 baseEnd_3893531 := by
    simpa [prefixWord, tailWord_3893531, baseEnd_3893531] using wordTrace_append hprefix tailTrace_3893531
  have hstable : (prefixWord ++ tailWord_3893531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893531).length < 2 ^ (prefixWord ++ tailWord_3893531).sum := by decide
  have hdescent : baseEnd_3893531 < baseStart_3893531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893538 : List Nat := [3, 3, 1, 1, 3, 3, 1, 2, 2, 4]
def baseStart_3893538 : Nat := 118140960795 + 3893538 * 2 ^ 59
def prefixEnd_3893538 : Nat := 4983230072969 + 3 ^ 40 * 3893538 * 2
def baseEnd_3893538 : Nat := 666418813515164249456317

theorem tailTrace_3893538 : CollatzResearch.WordTrace tailWord_3893538 prefixEnd_3893538 666418813515164249456317 := by
  unfold tailWord_3893538
  simp only [CollatzResearch.WordTrace]
  refine ⟨35502249342096066048768317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94672664912256176130048845 35502249342096066048768317)
  ·
    refine ⟨13313343503286024768288119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35502249342096066048768317 13313343503286024768288119)
    ·
      refine ⟨19970015254929037152432179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13313343503286024768288119 19970015254929037152432179)
      ·
        refine ⟨29955022882393555728648269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19970015254929037152432179 29955022882393555728648269)
        ·
          refine ⟨11233133580897583398243101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29955022882393555728648269 11233133580897583398243101)
          ·
            refine ⟨4212425092836593774341163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11233133580897583398243101 4212425092836593774341163)
            ·
              refine ⟨6318637639254890661511745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4212425092836593774341163 6318637639254890661511745)
              ·
                refine ⟨4738978229441167996133809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6318637639254890661511745 4738978229441167996133809)
                ·
                  refine ⟨3554233672080875997100357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4738978229441167996133809 3554233672080875997100357)
                  ·
                    refine ⟨666418813515164249456317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3554233672080875997100357 666418813515164249456317)
                    ·
                      rfl

theorem cell23_3893538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_3893538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3893538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3893538 prefixEnd_3893538 := by exact prefixLift 3893538
  have htrace : WordTrace (prefixWord ++ tailWord_3893538) baseStart_3893538 baseEnd_3893538 := by
    simpa [prefixWord, tailWord_3893538, baseEnd_3893538] using wordTrace_append hprefix tailTrace_3893538
  have hstable : (prefixWord ++ tailWord_3893538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893538).length < 2 ^ (prefixWord ++ tailWord_3893538).sum := by decide
  have hdescent : baseEnd_3893538 < baseStart_3893538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893561 : List Nat := [1, 2, 1, 6, 1, 1, 3, 1, 1, 3, 3]
def baseStart_3893561 : Nat := 118140960795 + 3893561 * 2 ^ 59
def prefixEnd_3893561 : Nat := 4983230072969 + 3 ^ 40 * 3893561 * 2
def baseEnd_3893561 : Nat := 1999268250600546158381345

theorem tailTrace_3893561 : CollatzResearch.WordTrace tailWord_3893561 prefixEnd_3893561 1999268250600546158381345 := by
  unfold tailWord_3893561
  simp only [CollatzResearch.WordTrace]
  refine ⟨142009836247300939123160537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94673224164867292748773691 142009836247300939123160537)
  ·
    refine ⟨106507377185475704342370403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142009836247300939123160537 106507377185475704342370403)
    ·
      refine ⟨159761065778213556513555605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106507377185475704342370403 159761065778213556513555605)
      ·
        refine ⟨7488799958353760461572919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 159761065778213556513555605 7488799958353760461572919)
        ·
          refine ⟨11233199937530640692359379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7488799958353760461572919 11233199937530640692359379)
          ·
            refine ⟨16849799906295961038539069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11233199937530640692359379 16849799906295961038539069)
            ·
              refine ⟨6318674964860985389452151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16849799906295961038539069 6318674964860985389452151)
              ·
                refine ⟨9478012447291478084178227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6318674964860985389452151 9478012447291478084178227)
                ·
                  refine ⟨14217018670937217126267341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9478012447291478084178227 14217018670937217126267341)
                  ·
                    refine ⟨5331382001601456422350253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14217018670937217126267341 5331382001601456422350253)
                    ·
                      refine ⟨1999268250600546158381345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5331382001601456422350253 1999268250600546158381345)
                      ·
                        rfl

theorem cell23_3893561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_3893561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3893561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3893561 prefixEnd_3893561 := by exact prefixLift 3893561
  have htrace : WordTrace (prefixWord ++ tailWord_3893561) baseStart_3893561 baseEnd_3893561 := by
    simpa [prefixWord, tailWord_3893561, baseEnd_3893561] using wordTrace_append hprefix tailTrace_3893561
  have hstable : (prefixWord ++ tailWord_3893561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893561).length < 2 ^ (prefixWord ++ tailWord_3893561).sum := by decide
  have hdescent : baseEnd_3893561 < baseStart_3893561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893571 : List Nat := [1, 1, 1, 3, 1, 3, 3, 4, 1, 3, 2]
def baseStart_3893571 : Nat := 118140960795 + 3893571 * 2 ^ 59
def prefixEnd_3893571 : Nat := 4983230072969 + 3 ^ 40 * 3893571 * 2
def baseEnd_3893571 : Nat := 1999273385407091119256299

theorem tailTrace_3893571 : CollatzResearch.WordTrace tailWord_3893571 prefixEnd_3893571 1999273385407091119256299 := by
  unfold tailWord_3893571
  simp only [CollatzResearch.WordTrace]
  refine ⟨142010200977264710831024567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94673467318176473887349711 142010200977264710831024567)
  ·
    refine ⟨213015301465897066246536851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142010200977264710831024567 213015301465897066246536851)
    ·
      refine ⟨319522952198845599369805277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213015301465897066246536851 319522952198845599369805277)
      ·
        refine ⟨119821107074567099763676979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 319522952198845599369805277 119821107074567099763676979)
        ·
          refine ⟨179731660611850649645515469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119821107074567099763676979 179731660611850649645515469)
          ·
            refine ⟨67399372729443993617068301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179731660611850649645515469 67399372729443993617068301)
            ·
              refine ⟨25274764773541497606400613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67399372729443993617068301 25274764773541497606400613)
              ·
                refine ⟨4739018395039030801200115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25274764773541497606400613 4739018395039030801200115)
                ·
                  refine ⟨7108527592558546201800173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4739018395039030801200115 7108527592558546201800173)
                  ·
                    refine ⟨2665697847209454825675065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7108527592558546201800173 2665697847209454825675065)
                    ·
                      refine ⟨1999273385407091119256299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2665697847209454825675065 1999273385407091119256299)
                      ·
                        rfl

theorem cell23_3893571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 4, 1, 3, 2].length) (baseStart_3893571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3893571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3893571 prefixEnd_3893571 := by exact prefixLift 3893571
  have htrace : WordTrace (prefixWord ++ tailWord_3893571) baseStart_3893571 baseEnd_3893571 := by
    simpa [prefixWord, tailWord_3893571, baseEnd_3893571] using wordTrace_append hprefix tailTrace_3893571
  have hstable : (prefixWord ++ tailWord_3893571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893571).length < 2 ^ (prefixWord ++ tailWord_3893571).sum := by decide
  have hdescent : baseEnd_3893571 < baseStart_3893571 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893588 : List Nat := [2, 4, 1, 1, 2, 2, 2, 3, 1, 3, 2]
def baseStart_3893588 : Nat := 118140960795 + 3893588 * 2 ^ 59
def prefixEnd_3893588 : Nat := 4983230072969 + 3 ^ 40 * 3893588 * 2
def baseEnd_3893588 : Nat := 1999282114578217552743721

theorem tailTrace_3893588 : CollatzResearch.WordTrace tailWord_3893588 prefixEnd_3893588 1999282114578217552743721 := by
  unfold tailWord_3893588
  simp only [CollatzResearch.WordTrace]
  refine ⟨71005410509101561367196709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94673880678802081822928945 71005410509101561367196709)
  ·
    refine ⟨13313514470456542756349383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71005410509101561367196709 13313514470456542756349383)
    ·
      refine ⟨19970271705684814134524075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13313514470456542756349383 19970271705684814134524075)
      ·
        refine ⟨29955407558527221201786113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19970271705684814134524075 29955407558527221201786113)
        ·
          refine ⟨22466555668895415901339585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29955407558527221201786113 22466555668895415901339585)
          ·
            refine ⟨16849916751671561926004689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22466555668895415901339585 16849916751671561926004689)
            ·
              refine ⟨12637437563753671444503517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16849916751671561926004689 12637437563753671444503517)
              ·
                refine ⟨4739039086407626791688819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12637437563753671444503517 4739039086407626791688819)
                ·
                  refine ⟨7108558629611440187533229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4739039086407626791688819 7108558629611440187533229)
                  ·
                    refine ⟨2665709486104290070324961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7108558629611440187533229 2665709486104290070324961)
                    ·
                      refine ⟨1999282114578217552743721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2665709486104290070324961 1999282114578217552743721)
                      ·
                        rfl

theorem cell23_3893588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 3, 1, 3, 2].length) (baseStart_3893588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3893588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3893588 prefixEnd_3893588 := by exact prefixLift 3893588
  have htrace : WordTrace (prefixWord ++ tailWord_3893588) baseStart_3893588 baseEnd_3893588 := by
    simpa [prefixWord, tailWord_3893588, baseEnd_3893588] using wordTrace_append hprefix tailTrace_3893588
  have hstable : (prefixWord ++ tailWord_3893588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893588).length < 2 ^ (prefixWord ++ tailWord_3893588).sum := by decide
  have hdescent : baseEnd_3893588 < baseStart_3893588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893604 : List Nat := [2, 3, 1, 1, 3, 1, 2, 1, 2, 4, 3]
def baseStart_3893604 : Nat := 118140960795 + 3893604 * 2 ^ 59
def prefixEnd_3893604 : Nat := 4983230072969 + 3 ^ 40 * 3893604 * 2
def baseEnd_3893604 : Nat := 1999290330268689490143647

theorem tailTrace_3893604 : CollatzResearch.WordTrace tailWord_3893604 prefixEnd_3893604 1999290330268689490143647 := by
  unfold tailWord_3893604
  simp only [CollatzResearch.WordTrace]
  refine ⟨71005702293072578733487933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94674269724096771644650577 71005702293072578733487933)
  ·
    refine ⟨26627138359902217025057975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71005702293072578733487933 26627138359902217025057975)
    ·
      refine ⟨39940707539853325537586963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26627138359902217025057975 39940707539853325537586963)
      ·
        refine ⟨59911061309779988306380445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39940707539853325537586963 59911061309779988306380445)
        ·
          refine ⟨22466647991167495614892667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59911061309779988306380445 22466647991167495614892667)
          ·
            refine ⟨33699971986751243422339001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22466647991167495614892667 33699971986751243422339001)
            ·
              refine ⟨25274978990063432566754251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33699971986751243422339001 25274978990063432566754251)
              ·
                refine ⟨37912468485095148850131377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25274978990063432566754251 37912468485095148850131377)
                ·
                  refine ⟨28434351363821361637598533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37912468485095148850131377 28434351363821361637598533)
                  ·
                    refine ⟨5331440880716505307049725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28434351363821361637598533 5331440880716505307049725)
                    ·
                      refine ⟨1999290330268689490143647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5331440880716505307049725 1999290330268689490143647)
                      ·
                        rfl

theorem cell23_3893604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 2, 4, 3].length) (baseStart_3893604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3893604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3893604 prefixEnd_3893604 := by exact prefixLift 3893604
  have htrace : WordTrace (prefixWord ++ tailWord_3893604) baseStart_3893604 baseEnd_3893604 := by
    simpa [prefixWord, tailWord_3893604, baseEnd_3893604] using wordTrace_append hprefix tailTrace_3893604
  have hstable : (prefixWord ++ tailWord_3893604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893604).length < 2 ^ (prefixWord ++ tailWord_3893604).sum := by decide
  have hdescent : baseEnd_3893604 < baseStart_3893604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893612 : List Nat := [2, 2, 1, 1, 7, 1, 2, 1, 2, 1, 3]
def baseStart_3893612 : Nat := 118140960795 + 3893612 * 2 ^ 59
def prefixEnd_3893612 : Nat := 4983230072969 + 3 ^ 40 * 3893612 * 2
def baseEnd_3893612 : Nat := 1999294438113925458843611

theorem tailTrace_3893612 : CollatzResearch.WordTrace tailWord_3893612 prefixEnd_3893612 1999294438113925458843611 := by
  unfold tailWord_3893612
  simp only [CollatzResearch.WordTrace]
  refine ⟨71005848185058087416633545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94674464246744116555511393 71005848185058087416633545)
  ·
    refine ⟨53254386138793565562475159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71005848185058087416633545 53254386138793565562475159)
    ·
      refine ⟨79881579208190348343712739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53254386138793565562475159 79881579208190348343712739)
      ·
        refine ⟨119822368812285522515569109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79881579208190348343712739 119822368812285522515569109)
        ·
          refine ⟨2808336769037941933958651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 119822368812285522515569109 2808336769037941933958651)
          ·
            refine ⟨4212505153556912900937977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2808336769037941933958651 4212505153556912900937977)
            ·
              refine ⟨3159378865167684675703483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4212505153556912900937977 3159378865167684675703483)
              ·
                refine ⟨4739068297751527013555225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3159378865167684675703483 4739068297751527013555225)
                ·
                  refine ⟨3554301223313645260166419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4739068297751527013555225 3554301223313645260166419)
                  ·
                    refine ⟨5331451834970467890249629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3554301223313645260166419 5331451834970467890249629)
                    ·
                      refine ⟨1999294438113925458843611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5331451834970467890249629 1999294438113925458843611)
                      ·
                        rfl

theorem cell23_3893612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 1, 2, 1, 3].length) (baseStart_3893612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3893612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3893612 prefixEnd_3893612 := by exact prefixLift 3893612
  have htrace : WordTrace (prefixWord ++ tailWord_3893612) baseStart_3893612 baseEnd_3893612 := by
    simpa [prefixWord, tailWord_3893612, baseEnd_3893612] using wordTrace_append hprefix tailTrace_3893612
  have hstable : (prefixWord ++ tailWord_3893612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893612).length < 2 ^ (prefixWord ++ tailWord_3893612).sum := by decide
  have hdescent : baseEnd_3893612 < baseStart_3893612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893652 : List Nat := [2, 4, 2, 1, 3, 1, 2, 2, 2, 2, 2]
def baseStart_3893652 : Nat := 118140960795 + 3893652 * 2 ^ 59
def prefixEnd_3893652 : Nat := 4983230072969 + 3 ^ 40 * 3893652 * 2
def baseEnd_3893652 : Nat := 1999314977340105302343427

theorem tailTrace_3893652 : CollatzResearch.WordTrace tailWord_3893652 prefixEnd_3893652 1999314977340105302343427 := by
  unfold tailWord_3893652
  simp only [CollatzResearch.WordTrace]
  refine ⟨71006577644985630832361605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94675436859980841109815473 71006577644985630832361605)
  ·
    refine ⟨13313733308434805781067801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71006577644985630832361605 13313733308434805781067801)
    ·
      refine ⟨9985299981326104335800851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13313733308434805781067801 9985299981326104335800851)
      ·
        refine ⟨14977949971989156503701277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9985299981326104335800851 14977949971989156503701277)
        ·
          refine ⟨5616731239495933688887979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14977949971989156503701277 5616731239495933688887979)
          ·
            refine ⟨8425096859243900533331969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5616731239495933688887979 8425096859243900533331969)
            ·
              refine ⟨6318822644432925399998977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8425096859243900533331969 6318822644432925399998977)
              ·
                refine ⟨4739116983324694049999233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6318822644432925399998977 4739116983324694049999233)
                ·
                  refine ⟨3554337737493520537499425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4739116983324694049999233 3554337737493520537499425)
                  ·
                    refine ⟨2665753303120140403124569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3554337737493520537499425 2665753303120140403124569)
                    ·
                      refine ⟨1999314977340105302343427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2665753303120140403124569 1999314977340105302343427)
                      ·
                        rfl

theorem cell23_3893652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_3893652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3893652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3893652 prefixEnd_3893652 := by exact prefixLift 3893652
  have htrace : WordTrace (prefixWord ++ tailWord_3893652) baseStart_3893652 baseEnd_3893652 := by
    simpa [prefixWord, tailWord_3893652, baseEnd_3893652] using wordTrace_append hprefix tailTrace_3893652
  have hstable : (prefixWord ++ tailWord_3893652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893652).length < 2 ^ (prefixWord ++ tailWord_3893652).sum := by decide
  have hdescent : baseEnd_3893652 < baseStart_3893652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893658 : List Nat := [3, 1, 1, 4, 1, 2, 4, 2, 5]
def baseStart_3893658 : Nat := 118140960795 + 3893658 * 2 ^ 59
def prefixEnd_3893658 : Nat := 4983230072969 + 3 ^ 40 * 3893658 * 2
def baseEnd_3893658 : Nat := 222146450913781364318711

theorem tailTrace_3893658 : CollatzResearch.WordTrace tailWord_3893658 prefixEnd_3893658 222146450913781364318711 := by
  unfold tailWord_3893658
  simp only [CollatzResearch.WordTrace]
  refine ⟨35503343531987381172360407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94675582751966349792961085 35503343531987381172360407)
  ·
    refine ⟨53255015297981071758540611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35503343531987381172360407 53255015297981071758540611)
    ·
      refine ⟨79882522946971607637810917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53255015297981071758540611 79882522946971607637810917)
      ·
        refine ⟨14977973052557176432089547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79882522946971607637810917 14977973052557176432089547)
        ·
          refine ⟨22466959578835764648134321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14977973052557176432089547 22466959578835764648134321)
          ·
            refine ⟨16850219684126823486100741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22466959578835764648134321 16850219684126823486100741)
            ·
              refine ⟨3159416190773779403643889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16850219684126823486100741 3159416190773779403643889)
              ·
                refine ⟨2369562143080334552732917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3159416190773779403643889 2369562143080334552732917)
                ·
                  refine ⟨222146450913781364318711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2369562143080334552732917 222146450913781364318711)
                  ·
                    rfl

theorem cell23_3893658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 2, 5].length) (baseStart_3893658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3893658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3893658 prefixEnd_3893658 := by exact prefixLift 3893658
  have htrace : WordTrace (prefixWord ++ tailWord_3893658) baseStart_3893658 baseEnd_3893658 := by
    simpa [prefixWord, tailWord_3893658, baseEnd_3893658] using wordTrace_append hprefix tailTrace_3893658
  have hstable : (prefixWord ++ tailWord_3893658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893658).length < 2 ^ (prefixWord ++ tailWord_3893658).sum := by decide
  have hdescent : baseEnd_3893658 < baseStart_3893658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893664 : List Nat := [2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 5]
def baseStart_3893664 : Nat := 118140960795 + 3893664 * 2 ^ 59
def prefixEnd_3893664 : Nat := 4983230072969 + 3 ^ 40 * 3893664 * 2
def baseEnd_3893664 : Nat := 1999321139107959255393371

theorem tailTrace_3893664 : CollatzResearch.WordTrace tailWord_3893664 prefixEnd_3893664 1999321139107959255393371 := by
  unfold tailWord_3893664
  simp only [CollatzResearch.WordTrace]
  refine ⟨71006796482963893857080023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94675728643951858476106697 71006796482963893857080023)
  ·
    refine ⟨106510194724445840785620035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71006796482963893857080023 106510194724445840785620035)
    ·
      refine ⟨159765292086668761178430053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106510194724445840785620035 159765292086668761178430053)
      ·
        refine ⟨29955992266250392720955635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159765292086668761178430053 29955992266250392720955635)
        ·
          refine ⟨44933988399375589081433453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29955992266250392720955635 44933988399375589081433453)
          ·
            refine ⟨16850245649765845905537545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44933988399375589081433453 16850245649765845905537545)
            ·
              refine ⟨12637684237324384429153159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16850245649765845905537545 12637684237324384429153159)
              ·
                refine ⟨18956526355986576643729739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12637684237324384429153159 18956526355986576643729739)
                ·
                  refine ⟨28434789533979864965594609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18956526355986576643729739 28434789533979864965594609)
                  ·
                    refine ⟨21326092150484898724195957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28434789533979864965594609 21326092150484898724195957)
                    ·
                      refine ⟨1999321139107959255393371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21326092150484898724195957 1999321139107959255393371)
                      ·
                        rfl

theorem cell23_3893664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_3893664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3893664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3893664 prefixEnd_3893664 := by exact prefixLift 3893664
  have htrace : WordTrace (prefixWord ++ tailWord_3893664) baseStart_3893664 baseEnd_3893664 := by
    simpa [prefixWord, tailWord_3893664, baseEnd_3893664] using wordTrace_append hprefix tailTrace_3893664
  have hstable : (prefixWord ++ tailWord_3893664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893664).length < 2 ^ (prefixWord ++ tailWord_3893664).sum := by decide
  have hdescent : baseEnd_3893664 < baseStart_3893664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893704 : List Nat := [2, 1, 3, 1, 3, 2, 1, 1, 2, 1, 6]
def baseStart_3893704 : Nat := 118140960795 + 3893704 * 2 ^ 59
def prefixEnd_3893704 : Nat := 4983230072969 + 3 ^ 40 * 3893704 * 2
def baseEnd_3893704 : Nat := 1999341678334139098893187

theorem tailTrace_3893704 : CollatzResearch.WordTrace tailWord_3893704 prefixEnd_3893704 1999341678334139098893187 := by
  unfold tailWord_3893704
  simp only [CollatzResearch.WordTrace]
  refine ⟨71007525942891437272808083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94676701257188583030410777 71007525942891437272808083)
  ·
    refine ⟨106511288914337155909212125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71007525942891437272808083 106511288914337155909212125)
    ·
      refine ⟨39941733342876433465954547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106511288914337155909212125 39941733342876433465954547)
      ·
        refine ⟨59912600014314650198931821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39941733342876433465954547 59912600014314650198931821)
        ·
          refine ⟨22467225005367993824599433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59912600014314650198931821 22467225005367993824599433)
          ·
            refine ⟨16850418754025995368449575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22467225005367993824599433 16850418754025995368449575)
            ·
              refine ⟨25275628131038993052674363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16850418754025995368449575 25275628131038993052674363)
              ·
                refine ⟨37913442196558489579011545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25275628131038993052674363 37913442196558489579011545)
                ·
                  refine ⟨28435081647418867184258659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37913442196558489579011545 28435081647418867184258659)
                  ·
                    refine ⟨42652622471128300776387989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28435081647418867184258659 42652622471128300776387989)
                    ·
                      refine ⟨1999341678334139098893187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42652622471128300776387989 1999341678334139098893187)
                      ·
                        rfl

theorem cell23_3893704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_3893704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3893704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3893704 prefixEnd_3893704 := by exact prefixLift 3893704
  have htrace : WordTrace (prefixWord ++ tailWord_3893704) baseStart_3893704 baseEnd_3893704 := by
    simpa [prefixWord, tailWord_3893704, baseEnd_3893704] using wordTrace_append hprefix tailTrace_3893704
  have hstable : (prefixWord ++ tailWord_3893704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893704).length < 2 ^ (prefixWord ++ tailWord_3893704).sum := by decide
  have hdescent : baseEnd_3893704 < baseStart_3893704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893781 : List Nat := [1, 3, 2, 1, 3, 1, 2, 2, 3, 1, 4]
def baseStart_3893781 : Nat := 118140960795 + 3893781 * 2 ^ 59
def prefixEnd_3893781 : Nat := 4983230072969 + 3 ^ 40 * 3893781 * 2
def baseEnd_3893781 : Nat := 1999381216344535297630333

theorem tailTrace_3893781 : CollatzResearch.WordTrace tailWord_3893781 prefixEnd_3893781 1999381216344535297630333 := by
  unfold tailWord_3893781
  simp only [CollatzResearch.WordTrace]
  refine ⟨142017860306503916696169197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94678573537669277797446131 142017860306503916696169197)
  ·
    refine ⟨53256697614938968761063449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142017860306503916696169197 53256697614938968761063449)
    ·
      refine ⟨39942523211204226570797587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53256697614938968761063449 39942523211204226570797587)
      ·
        refine ⟨59913784816806339856196381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39942523211204226570797587 59913784816806339856196381)
        ·
          refine ⟨22467669306302377446073643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59913784816806339856196381 22467669306302377446073643)
          ·
            refine ⟨33701503959453566169110465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22467669306302377446073643 33701503959453566169110465)
            ·
              refine ⟨25276127969590174626832849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33701503959453566169110465 25276127969590174626832849)
              ·
                refine ⟨18957095977192630970124637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25276127969590174626832849 18957095977192630970124637)
                ·
                  refine ⟨7108910991447236613796739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18957095977192630970124637 7108910991447236613796739)
                  ·
                    refine ⟨10663366487170854920695109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7108910991447236613796739 10663366487170854920695109)
                    ·
                      refine ⟨1999381216344535297630333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10663366487170854920695109 1999381216344535297630333)
                      ·
                        rfl

theorem cell23_3893781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_3893781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3893781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3893781 prefixEnd_3893781 := by exact prefixLift 3893781
  have htrace : WordTrace (prefixWord ++ tailWord_3893781) baseStart_3893781 baseEnd_3893781 := by
    simpa [prefixWord, tailWord_3893781, baseEnd_3893781] using wordTrace_append hprefix tailTrace_3893781
  have hstable : (prefixWord ++ tailWord_3893781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893781).length < 2 ^ (prefixWord ++ tailWord_3893781).sum := by decide
  have hdescent : baseEnd_3893781 < baseStart_3893781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893811 : List Nat := [1, 1, 1, 2, 4, 2, 3, 2, 1, 2, 4]
def baseStart_3893811 : Nat := 118140960795 + 3893811 * 2 ^ 59
def prefixEnd_3893811 : Nat := 4983230072969 + 3 ^ 40 * 3893811 * 2
def baseEnd_3893811 : Nat := 1999396620764170180255195

theorem tailTrace_3893811 : CollatzResearch.WordTrace tailWord_3893811 prefixEnd_3893811 1999396620764170180255195 := by
  unfold tailWord_3893811
  simp only [CollatzResearch.WordTrace]
  refine ⟨142018954496395231819761287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94679302997596821213174191 142018954496395231819761287)
  ·
    refine ⟨213028431744592847729641931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142018954496395231819761287 213028431744592847729641931)
    ·
      refine ⟨319542647616889271594462897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213028431744592847729641931 319542647616889271594462897)
      ·
        refine ⟨239656985712666953695847173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319542647616889271594462897 239656985712666953695847173)
        ·
          refine ⟨44935684821125053817971345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 239656985712666953695847173 44935684821125053817971345)
          ·
            refine ⟨33701763615843790363478509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44935684821125053817971345 33701763615843790363478509)
            ·
              refine ⟨12638161355941421386304441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33701763615843790363478509 12638161355941421386304441)
              ·
                refine ⟨9478621016956066039728331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12638161355941421386304441 9478621016956066039728331)
                ·
                  refine ⟨14217931525434099059592497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9478621016956066039728331 14217931525434099059592497)
                  ·
                    refine ⟨10663448644075574294694373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14217931525434099059592497 10663448644075574294694373)
                    ·
                      refine ⟨1999396620764170180255195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10663448644075574294694373 1999396620764170180255195)
                      ·
                        rfl

theorem cell23_3893811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 2, 4].length) (baseStart_3893811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3893811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3893811 prefixEnd_3893811 := by exact prefixLift 3893811
  have htrace : WordTrace (prefixWord ++ tailWord_3893811) baseStart_3893811 baseEnd_3893811 := by
    simpa [prefixWord, tailWord_3893811, baseEnd_3893811] using wordTrace_append hprefix tailTrace_3893811
  have hstable : (prefixWord ++ tailWord_3893811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893811).length < 2 ^ (prefixWord ++ tailWord_3893811).sum := by decide
  have hdescent : baseEnd_3893811 < baseStart_3893811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893818 : List Nat := [3, 1, 1, 1, 3, 5, 1, 1, 1, 1, 5]
def baseStart_3893818 : Nat := 118140960795 + 3893818 * 2 ^ 59
def prefixEnd_3893818 : Nat := 4983230072969 + 3 ^ 40 * 3893818 * 2
def baseEnd_3893818 : Nat := 1999400215128751652867663

theorem tailTrace_3893818 : CollatzResearch.WordTrace tailWord_3893818 prefixEnd_3893818 1999400215128751652867663 := by
  unfold tailWord_3893818
  simp only [CollatzResearch.WordTrace]
  refine ⟨35504802451842468003816527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94679473204913248010177405 35504802451842468003816527)
  ·
    refine ⟨53257203677763702005724791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35504802451842468003816527 53257203677763702005724791)
    ·
      refine ⟨79885805516645553008587187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53257203677763702005724791 79885805516645553008587187)
      ·
        refine ⟨119828708274968329512880781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79885805516645553008587187 119828708274968329512880781)
        ·
          refine ⟨44935765603113123567330293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119828708274968329512880781 44935765603113123567330293)
          ·
            refine ⟨4212728025291855334437215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44935765603113123567330293 4212728025291855334437215)
            ·
              refine ⟨6319092037937783001655823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4212728025291855334437215 6319092037937783001655823)
              ·
                refine ⟨9478638056906674502483735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6319092037937783001655823 9478638056906674502483735)
                ·
                  refine ⟨14217957085360011753725603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9478638056906674502483735 14217957085360011753725603)
                  ·
                    refine ⟨21326935628040017630588405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14217957085360011753725603 21326935628040017630588405)
                    ·
                      refine ⟨1999400215128751652867663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21326935628040017630588405 1999400215128751652867663)
                      ·
                        rfl

theorem cell23_3893818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 1, 1, 5].length) (baseStart_3893818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3893818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3893818 prefixEnd_3893818 := by exact prefixLift 3893818
  have htrace : WordTrace (prefixWord ++ tailWord_3893818) baseStart_3893818 baseEnd_3893818 := by
    simpa [prefixWord, tailWord_3893818, baseEnd_3893818] using wordTrace_append hprefix tailTrace_3893818
  have hstable : (prefixWord ++ tailWord_3893818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893818).length < 2 ^ (prefixWord ++ tailWord_3893818).sum := by decide
  have hdescent : baseEnd_3893818 < baseStart_3893818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893825 : List Nat := [1, 2, 5, 1, 1, 3, 2, 2, 2, 4]
def baseStart_3893825 : Nat := 118140960795 + 3893825 * 2 ^ 59
def prefixEnd_3893825 : Nat := 4983230072969 + 3 ^ 40 * 3893825 * 2
def baseEnd_3893825 : Nat := 666467936497777708493377

theorem tailTrace_3893825 : CollatzResearch.WordTrace tailWord_3893825 prefixEnd_3893825 666467936497777708493377 := by
  unfold tailWord_3893825
  simp only [CollatzResearch.WordTrace]
  refine ⟨142019465118344512210770929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94679643412229674807180619 142019465118344512210770929)
  ·
    refine ⟨106514598838758384158078197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142019465118344512210770929 106514598838758384158078197)
    ·
      refine ⟨9985743641133598514819831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106514598838758384158078197 9985743641133598514819831)
      ·
        refine ⟨14978615461700397772229747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9985743641133598514819831 14978615461700397772229747)
        ·
          refine ⟨22467923192550596658344621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14978615461700397772229747 22467923192550596658344621)
          ·
            refine ⟨8425471197206473746879233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22467923192550596658344621 8425471197206473746879233)
            ·
              refine ⟨6319103397904855310159425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8425471197206473746879233 6319103397904855310159425)
              ·
                refine ⟨4739327548428641482619569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6319103397904855310159425 4739327548428641482619569)
                ·
                  refine ⟨3554495661321481111964677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4739327548428641482619569 3554495661321481111964677)
                  ·
                    refine ⟨666467936497777708493377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3554495661321481111964677 666467936497777708493377)
                    ·
                      rfl

theorem cell23_3893825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_3893825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3893825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3893825 prefixEnd_3893825 := by exact prefixLift 3893825
  have htrace : WordTrace (prefixWord ++ tailWord_3893825) baseStart_3893825 baseEnd_3893825 := by
    simpa [prefixWord, tailWord_3893825, baseEnd_3893825] using wordTrace_append hprefix tailTrace_3893825
  have hstable : (prefixWord ++ tailWord_3893825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893825).length < 2 ^ (prefixWord ++ tailWord_3893825).sum := by decide
  have hdescent : baseEnd_3893825 < baseStart_3893825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893881 : List Nat := [1, 2, 1, 3, 3, 2, 1, 2, 2, 6]
def baseStart_3893881 : Nat := 118140960795 + 3893881 * 2 ^ 59
def prefixEnd_3893881 : Nat := 4983230072969 + 3 ^ 40 * 3893881 * 2
def baseEnd_3893881 : Nat := 666477521469994968793291

theorem tailTrace_3893881 : CollatzResearch.WordTrace tailWord_3893881 prefixEnd_3893881 666477521469994968793291 := by
  unfold tailWord_3893881
  simp only [CollatzResearch.WordTrace]
  refine ⟨142021507606141633774809497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94681005070761089183206331 142021507606141633774809497)
  ·
    refine ⟨106516130704606225331107123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142021507606141633774809497 106516130704606225331107123)
    ·
      refine ⟨159774196056909337996660685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106516130704606225331107123 159774196056909337996660685)
      ·
        refine ⟨59915323521341001748747757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159774196056909337996660685 59915323521341001748747757)
        ·
          refine ⟨22468246320502875655780409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59915323521341001748747757 22468246320502875655780409)
          ·
            refine ⟨16851184740377156741835307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22468246320502875655780409 16851184740377156741835307)
            ·
              refine ⟨25276777110565735112752961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16851184740377156741835307 25276777110565735112752961)
              ·
                refine ⟨18957582832924301334564721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25276777110565735112752961 18957582832924301334564721)
                ·
                  refine ⟨14218187124693226000923541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18957582832924301334564721 14218187124693226000923541)
                  ·
                    refine ⟨666477521469994968793291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14218187124693226000923541 666477521469994968793291)
                    ·
                      rfl

theorem cell23_3893881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 6].length) (baseStart_3893881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3893881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3893881 prefixEnd_3893881 := by exact prefixLift 3893881
  have htrace : WordTrace (prefixWord ++ tailWord_3893881) baseStart_3893881 baseEnd_3893881 := by
    simpa [prefixWord, tailWord_3893881, baseEnd_3893881] using wordTrace_append hprefix tailTrace_3893881
  have hstable : (prefixWord ++ tailWord_3893881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893881).length < 2 ^ (prefixWord ++ tailWord_3893881).sum := by decide
  have hdescent : baseEnd_3893881 < baseStart_3893881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893891 : List Nat := [1, 1, 1, 3, 3, 1, 2, 1, 1, 6, 3]
def baseStart_3893891 : Nat := 118140960795 + 3893891 * 2 ^ 59
def prefixEnd_3893891 : Nat := 4983230072969 + 3 ^ 40 * 3893891 * 2
def baseEnd_3893891 : Nat := 1999437699216529867254827

theorem tailTrace_3893891 : CollatzResearch.WordTrace tailWord_3893891 prefixEnd_3893891 1999437699216529867254827 := by
  unfold tailWord_3893891
  simp only [CollatzResearch.WordTrace]
  refine ⟨142021872336105405482673527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94681248224070270321782351 142021872336105405482673527)
  ·
    refine ⟨213032808504158108224010291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142021872336105405482673527 213032808504158108224010291)
    ·
      refine ⟨319549212756237162336015437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213032808504158108224010291 319549212756237162336015437)
      ·
        refine ⟨119830954783588935876005789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 319549212756237162336015437 119830954783588935876005789)
        ·
          refine ⟨44936608043845850953502171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119830954783588935876005789 44936608043845850953502171)
          ·
            refine ⟨67404912065768776430253257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44936608043845850953502171 67404912065768776430253257)
            ·
              refine ⟨50553684049326582322689943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67404912065768776430253257 50553684049326582322689943)
              ·
                refine ⟨75830526073989873484034915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50553684049326582322689943 75830526073989873484034915)
                ·
                  refine ⟨113745789110984810226052373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75830526073989873484034915 113745789110984810226052373)
                  ·
                    refine ⟨5331833864577412979346205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 113745789110984810226052373 5331833864577412979346205)
                    ·
                      refine ⟨1999437699216529867254827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5331833864577412979346205 1999437699216529867254827)
                      ·
                        rfl

theorem cell23_3893891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 6, 3].length) (baseStart_3893891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3893891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3893891 prefixEnd_3893891 := by exact prefixLift 3893891
  have htrace : WordTrace (prefixWord ++ tailWord_3893891) baseStart_3893891 baseEnd_3893891 := by
    simpa [prefixWord, tailWord_3893891, baseEnd_3893891] using wordTrace_append hprefix tailTrace_3893891
  have hstable : (prefixWord ++ tailWord_3893891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893891).length < 2 ^ (prefixWord ++ tailWord_3893891).sum := by decide
  have hdescent : baseEnd_3893891 < baseStart_3893891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893911 : List Nat := [1, 1, 3, 3, 2, 1, 1, 4, 7]
def baseStart_3893911 : Nat := 118140960795 + 3893911 * 2 ^ 59
def prefixEnd_3893911 : Nat := 4983230072969 + 3 ^ 40 * 3893911 * 2
def baseEnd_3893911 : Nat := 222160885425513309889415

theorem tailTrace_3893911 : CollatzResearch.WordTrace tailWord_3893911 prefixEnd_3893911 222160885425513309889415 := by
  unfold tailWord_3893911
  simp only [CollatzResearch.WordTrace]
  refine ⟨142022601796032948898401587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94681734530688632598934391 142022601796032948898401587)
  ·
    refine ⟨213033902694049423347602381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142022601796032948898401587 213033902694049423347602381)
    ·
      refine ⟨79887713510268533755350893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213033902694049423347602381 79887713510268533755350893)
      ·
        refine ⟨29957892566350700158256585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79887713510268533755350893 29957892566350700158256585)
        ·
          refine ⟨22468419424763025118692439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29957892566350700158256585 22468419424763025118692439)
          ·
            refine ⟨33702629137144537678038659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22468419424763025118692439 33702629137144537678038659)
            ·
              refine ⟨50553943705716806517057989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33702629137144537678038659 50553943705716806517057989)
              ·
                refine ⟨9478864444821901221948373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50553943705716806517057989 9478864444821901221948373)
                ·
                  refine ⟨222160885425513309889415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9478864444821901221948373 222160885425513309889415)
                  ·
                    rfl

theorem cell23_3893911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 7].length) (baseStart_3893911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3893911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3893911 prefixEnd_3893911 := by exact prefixLift 3893911
  have htrace : WordTrace (prefixWord ++ tailWord_3893911) baseStart_3893911 baseEnd_3893911 := by
    simpa [prefixWord, tailWord_3893911, baseEnd_3893911] using wordTrace_append hprefix tailTrace_3893911
  have hstable : (prefixWord ++ tailWord_3893911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893911).length < 2 ^ (prefixWord ++ tailWord_3893911).sum := by decide
  have hdescent : baseEnd_3893911 < baseStart_3893911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893951 : List Nat := [1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 7]
def baseStart_3893951 : Nat := 118140960795 + 3893951 * 2 ^ 59
def prefixEnd_3893951 : Nat := 4983230072969 + 3 ^ 40 * 3893951 * 2
def baseEnd_3893951 : Nat := 1999468508055799632504551

theorem tailTrace_3893951 : CollatzResearch.WordTrace tailWord_3893951 prefixEnd_3893951 1999468508055799632504551 := by
  unfold tailWord_3893951
  simp only [CollatzResearch.WordTrace]
  refine ⟨142024060715888035729857707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94682707143925357153238471 142024060715888035729857707)
  ·
    refine ⟨213036091073832053594786561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142024060715888035729857707 213036091073832053594786561)
    ·
      refine ⟨159777068305374040196089921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213036091073832053594786561 159777068305374040196089921)
      ·
        refine ⟨119832801229030530147067441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159777068305374040196089921 119832801229030530147067441)
        ·
          refine ⟨89874600921772897610300581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119832801229030530147067441 89874600921772897610300581)
          ·
            refine ⟨16851487672832418301931359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89874600921772897610300581 16851487672832418301931359)
            ·
              refine ⟨25277231509248627452897039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16851487672832418301931359 25277231509248627452897039)
              ·
                refine ⟨37915847263872941179345559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25277231509248627452897039 37915847263872941179345559)
                ·
                  refine ⟨56873770895809411769018339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37915847263872941179345559 56873770895809411769018339)
                  ·
                    refine ⟨85310656343714117653527509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56873770895809411769018339 85310656343714117653527509)
                    ·
                      refine ⟨1999468508055799632504551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 85310656343714117653527509 1999468508055799632504551)
                      ·
                        rfl

theorem cell23_3893951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 7].length) (baseStart_3893951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3893951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3893951 prefixEnd_3893951 := by exact prefixLift 3893951
  have htrace : WordTrace (prefixWord ++ tailWord_3893951) baseStart_3893951 baseEnd_3893951 := by
    simpa [prefixWord, tailWord_3893951, baseEnd_3893951] using wordTrace_append hprefix tailTrace_3893951
  have hstable : (prefixWord ++ tailWord_3893951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893951).length < 2 ^ (prefixWord ++ tailWord_3893951).sum := by decide
  have hdescent : baseEnd_3893951 < baseStart_3893951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893956 : List Nat := [2, 3, 3, 1, 1, 4, 2, 1, 2, 2, 2]
def baseStart_3893956 : Nat := 118140960795 + 3893956 * 2 ^ 59
def prefixEnd_3893956 : Nat := 4983230072969 + 3 ^ 40 * 3893956 * 2
def baseEnd_3893956 : Nat := 1999471075459072112942029

theorem tailTrace_3893956 : CollatzResearch.WordTrace tailWord_3893956 prefixEnd_3893956 1999471075459072112942029 := by
  unfold tailWord_3893956
  simp only [CollatzResearch.WordTrace]
  refine ⟨71012121540434960791894861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94682828720579947722526481 71012121540434960791894861)
  ·
    refine ⟨26629545577663110296960573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71012121540434960791894861 26629545577663110296960573)
    ·
      refine ⟨9986079591623666361360215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26629545577663110296960573 9986079591623666361360215)
      ·
        refine ⟨14979119387435499542040323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9986079591623666361360215 14979119387435499542040323)
        ·
          refine ⟨22468679081153249313060485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14979119387435499542040323 22468679081153249313060485)
          ·
            refine ⟨4212877327716234246198841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22468679081153249313060485 4212877327716234246198841)
            ·
              refine ⟨3159657995787175684649131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4212877327716234246198841 3159657995787175684649131)
              ·
                refine ⟨4739486993680763526973697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3159657995787175684649131 4739486993680763526973697)
                ·
                  refine ⟨3554615245260572645230273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4739486993680763526973697 3554615245260572645230273)
                  ·
                    refine ⟨2665961433945429483922705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3554615245260572645230273 2665961433945429483922705)
                    ·
                      refine ⟨1999471075459072112942029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2665961433945429483922705 1999471075459072112942029)
                      ·
                        rfl

theorem cell23_3893956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_3893956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3893956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3893956 prefixEnd_3893956 := by exact prefixLift 3893956
  have htrace : WordTrace (prefixWord ++ tailWord_3893956) baseStart_3893956 baseEnd_3893956 := by
    simpa [prefixWord, tailWord_3893956, baseEnd_3893956] using wordTrace_append hprefix tailTrace_3893956
  have hstable : (prefixWord ++ tailWord_3893956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893956).length < 2 ^ (prefixWord ++ tailWord_3893956).sum := by decide
  have hdescent : baseEnd_3893956 < baseStart_3893956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894039 : List Nat := [1, 1, 3, 4, 3, 1, 2, 3, 1, 4]
def baseStart_3894039 : Nat := 118140960795 + 3894039 * 2 ^ 59
def prefixEnd_3894039 : Nat := 4983230072969 + 3 ^ 40 * 3894039 * 2
def baseEnd_3894039 : Nat := 666504564784465096068049

theorem tailTrace_3894039 : CollatzResearch.WordTrace tailWord_3894039 prefixEnd_3894039 666504564784465096068049 := by
  unfold tailWord_3894039
  simp only [CollatzResearch.WordTrace]
  refine ⟨142027270339569226759061171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94684846893046151172707447 142027270339569226759061171)
  ·
    refine ⟨213040905509353840138591757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142027270339569226759061171 213040905509353840138591757)
    ·
      refine ⟨79890339566007690051971909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213040905509353840138591757 79890339566007690051971909)
      ·
        refine ⟨14979438668626441884744733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79890339566007690051971909 14979438668626441884744733)
        ·
          refine ⟨5617289500734915706779275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14979438668626441884744733 5617289500734915706779275)
          ·
            refine ⟨8425934251102373560168913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5617289500734915706779275 8425934251102373560168913)
            ·
              refine ⟨6319450688326780170126685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8425934251102373560168913 6319450688326780170126685)
              ·
                refine ⟨2369794008122542563797507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6319450688326780170126685 2369794008122542563797507)
                ·
                  refine ⟨3554691012183813845696261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2369794008122542563797507 3554691012183813845696261)
                  ·
                    refine ⟨666504564784465096068049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3554691012183813845696261 666504564784465096068049)
                    ·
                      rfl

theorem cell23_3894039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 3, 1, 4].length) (baseStart_3894039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3894039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3894039 prefixEnd_3894039 := by exact prefixLift 3894039
  have htrace : WordTrace (prefixWord ++ tailWord_3894039) baseStart_3894039 baseEnd_3894039 := by
    simpa [prefixWord, tailWord_3894039, baseEnd_3894039] using wordTrace_append hprefix tailTrace_3894039
  have hstable : (prefixWord ++ tailWord_3894039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894039).length < 2 ^ (prefixWord ++ tailWord_3894039).sum := by decide
  have hdescent : baseEnd_3894039 < baseStart_3894039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894052 : List Nat := [2, 3, 1, 3, 3, 2, 1, 2, 6]
def baseStart_3894052 : Nat := 118140960795 + 3894052 * 2 ^ 59
def prefixEnd_3894052 : Nat := 4983230072969 + 3 ^ 40 * 3894052 * 2
def baseEnd_3894052 : Nat := 222168929955767081926843

theorem tailTrace_3894052 : CollatzResearch.WordTrace tailWord_3894052 prefixEnd_3894052 222168929955767081926843 := by
  unfold tailWord_3894052
  simp only [CollatzResearch.WordTrace]
  refine ⟨71013872244261064989642205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94685162992348086652856273 71013872244261064989642205)
  ·
    refine ⟨26630202091597899371115827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71013872244261064989642205 26630202091597899371115827)
    ·
      refine ⟨39945303137396849056673741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26630202091597899371115827 39945303137396849056673741)
      ·
        refine ⟨14979488676523818396252653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39945303137396849056673741 14979488676523818396252653)
        ·
          refine ⟨5617308253696431898594745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14979488676523818396252653 5617308253696431898594745)
          ·
            refine ⟨4212981190272323923946059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5617308253696431898594745 4212981190272323923946059)
            ·
              refine ⟨6319471785408485885919089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4212981190272323923946059 6319471785408485885919089)
              ·
                refine ⟨4739603839056364414439317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6319471785408485885919089 4739603839056364414439317)
                ·
                  refine ⟨222168929955767081926843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4739603839056364414439317 222168929955767081926843)
                  ·
                    rfl

theorem cell23_3894052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 2, 6].length) (baseStart_3894052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3894052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3894052 prefixEnd_3894052 := by exact prefixLift 3894052
  have htrace : WordTrace (prefixWord ++ tailWord_3894052) baseStart_3894052 baseEnd_3894052 := by
    simpa [prefixWord, tailWord_3894052, baseEnd_3894052] using wordTrace_append hprefix tailTrace_3894052
  have hstable : (prefixWord ++ tailWord_3894052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894052).length < 2 ^ (prefixWord ++ tailWord_3894052).sum := by decide
  have hdescent : baseEnd_3894052 < baseStart_3894052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894088 : List Nat := [2, 1, 3, 1, 1, 3, 1, 2, 3, 1, 5]
def baseStart_3894088 : Nat := 118140960795 + 3894088 * 2 ^ 59
def prefixEnd_3894088 : Nat := 4983230072969 + 3 ^ 40 * 3894088 * 2
def baseEnd_3894088 : Nat := 1999538854905465596491421

theorem tailTrace_3894088 : CollatzResearch.WordTrace tailWord_3894088 prefixEnd_3894088 1999538854905465596491421 := by
  unfold tailWord_3894088
  simp only [CollatzResearch.WordTrace]
  refine ⟨71014528758195854063797459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94686038344261138751729945 71014528758195854063797459)
  ·
    refine ⟨106521793137293781095696189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71014528758195854063797459 106521793137293781095696189)
    ·
      refine ⟨39945672426485167910886071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106521793137293781095696189 39945672426485167910886071)
      ·
        refine ⟨59918508639727751866329107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39945672426485167910886071 59918508639727751866329107)
        ·
          refine ⟨89877762959591627799493661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59918508639727751866329107 89877762959591627799493661)
          ·
            refine ⟨33704161109846860424810123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89877762959591627799493661 33704161109846860424810123)
            ·
              refine ⟨50556241664770290637215185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33704161109846860424810123 50556241664770290637215185)
              ·
                refine ⟨37917181248577717977911389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50556241664770290637215185 37917181248577717977911389)
                ·
                  refine ⟨14218942968216644241716771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37917181248577717977911389 14218942968216644241716771)
                  ·
                    refine ⟨21328414452324966362575157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14218942968216644241716771 21328414452324966362575157)
                    ·
                      refine ⟨1999538854905465596491421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21328414452324966362575157 1999538854905465596491421)
                      ·
                        rfl

theorem cell23_3894088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_3894088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3894088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3894088 prefixEnd_3894088 := by exact prefixLift 3894088
  have htrace : WordTrace (prefixWord ++ tailWord_3894088) baseStart_3894088 baseEnd_3894088 := by
    simpa [prefixWord, tailWord_3894088, baseEnd_3894088] using wordTrace_append hprefix tailTrace_3894088
  have hstable : (prefixWord ++ tailWord_3894088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894088).length < 2 ^ (prefixWord ++ tailWord_3894088).sum := by decide
  have hdescent : baseEnd_3894088 < baseStart_3894088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894105 : List Nat := [1, 2, 1, 2, 2, 5, 2, 1, 1, 1, 5]
def baseStart_3894105 : Nat := 118140960795 + 3894105 * 2 ^ 59
def prefixEnd_3894105 : Nat := 4983230072969 + 3 ^ 40 * 3894105 * 2
def baseEnd_3894105 : Nat := 1999547584076592029978843

theorem tailTrace_3894105 : CollatzResearch.WordTrace tailWord_3894105 prefixEnd_3894105 1999547584076592029978843 := by
  unfold tailWord_3894105
  simp only [CollatzResearch.WordTrace]
  refine ⟨142029677557330120030963769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94686451704886746687309179 142029677557330120030963769)
  ·
    refine ⟨106522258167997590023222827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142029677557330120030963769 106522258167997590023222827)
    ·
      refine ⟨159783387251996385034834241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106522258167997590023222827 159783387251996385034834241)
      ·
        refine ⟨119837540438997288776125681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159783387251996385034834241 119837540438997288776125681)
        ·
          refine ⟨89878155329247966582094261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119837540438997288776125681 89878155329247966582094261)
          ·
            refine ⟨8426077062116996867071337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89878155329247966582094261 8426077062116996867071337)
            ·
              refine ⟨6319557796587747650303503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8426077062116996867071337 6319557796587747650303503)
              ·
                refine ⟨9479336694881621475455255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6319557796587747650303503 9479336694881621475455255)
                ·
                  refine ⟨14219005042322432213182883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9479336694881621475455255 14219005042322432213182883)
                  ·
                    refine ⟨21328507563483648319774325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14219005042322432213182883 21328507563483648319774325)
                    ·
                      refine ⟨1999547584076592029978843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21328507563483648319774325 1999547584076592029978843)
                      ·
                        rfl

theorem cell23_3894105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 1, 5].length) (baseStart_3894105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3894105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3894105 prefixEnd_3894105 := by exact prefixLift 3894105
  have htrace : WordTrace (prefixWord ++ tailWord_3894105) baseStart_3894105 baseEnd_3894105 := by
    simpa [prefixWord, tailWord_3894105, baseEnd_3894105] using wordTrace_append hprefix tailTrace_3894105
  have hstable : (prefixWord ++ tailWord_3894105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894105).length < 2 ^ (prefixWord ++ tailWord_3894105).sum := by decide
  have hdescent : baseEnd_3894105 < baseStart_3894105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894119 : List Nat := [1, 1, 5, 1, 2, 2, 3, 1, 3, 2, 2]
def baseStart_3894119 : Nat := 118140960795 + 3894119 * 2 ^ 59
def prefixEnd_3894119 : Nat := 4983230072969 + 3 ^ 40 * 3894119 * 2
def baseEnd_3894119 : Nat := 1999554772805754975203779

theorem tailTrace_3894119 : CollatzResearch.WordTrace tailWord_3894119 prefixEnd_3894119 1999554772805754975203779 := by
  unfold tailWord_3894119
  simp only [CollatzResearch.WordTrace]
  refine ⟨142030188179279400421973411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94686792119519600281315607 142030188179279400421973411)
  ·
    refine ⟨213045282268919100632960117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142030188179279400421973411 213045282268919100632960117)
    ·
      refine ⟨19972995212711165684340011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 213045282268919100632960117 19972995212711165684340011)
      ·
        refine ⟨29959492819066748526510017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19972995212711165684340011 29959492819066748526510017)
        ·
          refine ⟨22469619614300061394882513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29959492819066748526510017 22469619614300061394882513)
          ·
            refine ⟨16852214710725046046161885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22469619614300061394882513 16852214710725046046161885)
            ·
              refine ⟨6319580516521892267310707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16852214710725046046161885 6319580516521892267310707)
              ·
                refine ⟨9479370774782838400966061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6319580516521892267310707 9479370774782838400966061)
                ·
                  refine ⟨3554764040543564400362273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9479370774782838400966061 3554764040543564400362273)
                  ·
                    refine ⟨2666073030407673300271705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3554764040543564400362273 2666073030407673300271705)
                    ·
                      refine ⟨1999554772805754975203779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2666073030407673300271705 1999554772805754975203779)
                      ·
                        rfl

theorem cell23_3894119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 3, 2, 2].length) (baseStart_3894119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3894119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3894119 prefixEnd_3894119 := by exact prefixLift 3894119
  have htrace : WordTrace (prefixWord ++ tailWord_3894119) baseStart_3894119 baseEnd_3894119 := by
    simpa [prefixWord, tailWord_3894119, baseEnd_3894119] using wordTrace_append hprefix tailTrace_3894119
  have hstable : (prefixWord ++ tailWord_3894119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894119).length < 2 ^ (prefixWord ++ tailWord_3894119).sum := by decide
  have hdescent : baseEnd_3894119 < baseStart_3894119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894129 : List Nat := [1, 2, 2, 2, 1, 6, 2, 1, 2, 4]
def baseStart_3894129 : Nat := 118140960795 + 3894129 * 2 ^ 59
def prefixEnd_3894129 : Nat := 4983230072969 + 3 ^ 40 * 3894129 * 2
def baseEnd_3894129 : Nat := 666519969204099978692911

theorem tailTrace_3894129 : CollatzResearch.WordTrace tailWord_3894129 prefixEnd_3894129 666519969204099978692911 := by
  unfold tailWord_3894129
  simp only [CollatzResearch.WordTrace]
  refine ⟨142030552909243172129837441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94687035272828781419891627 142030552909243172129837441)
  ·
    refine ⟨106522914681932379097378081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142030552909243172129837441 106522914681932379097378081)
    ·
      refine ⟨79892186011449284323033561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106522914681932379097378081 79892186011449284323033561)
      ·
        refine ⟨59919139508586963242275171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79892186011449284323033561 59919139508586963242275171)
        ·
          refine ⟨89878709262880444863412757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59919139508586963242275171 89878709262880444863412757)
          ·
            refine ⟨4213064496697520852972473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 89878709262880444863412757 4213064496697520852972473)
            ·
              refine ⟨3159798372523140639729355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4213064496697520852972473 3159798372523140639729355)
              ·
                refine ⟨4739697558784710959594033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3159798372523140639729355 4739697558784710959594033)
                ·
                  refine ⟨3554773169088533219695525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4739697558784710959594033 3554773169088533219695525)
                  ·
                    refine ⟨666519969204099978692911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3554773169088533219695525 666519969204099978692911)
                    ·
                      rfl

theorem cell23_3894129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 1, 2, 4].length) (baseStart_3894129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3894129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3894129 prefixEnd_3894129 := by exact prefixLift 3894129
  have htrace : WordTrace (prefixWord ++ tailWord_3894129) baseStart_3894129 baseEnd_3894129 := by
    simpa [prefixWord, tailWord_3894129, baseEnd_3894129] using wordTrace_append hprefix tailTrace_3894129
  have hstable : (prefixWord ++ tailWord_3894129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894129).length < 2 ^ (prefixWord ++ tailWord_3894129).sum := by decide
  have hdescent : baseEnd_3894129 < baseStart_3894129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894152 : List Nat := [2, 1, 3, 3, 2, 2, 1, 2, 1, 3, 3]
def baseStart_3894152 : Nat := 118140960795 + 3894152 * 2 ^ 59
def prefixEnd_3894152 : Nat := 4983230072969 + 3 ^ 40 * 3894152 * 2
def baseEnd_3894152 : Nat := 1999571717667353346091127

theorem tailTrace_3894152 : CollatzResearch.WordTrace tailWord_3894152 prefixEnd_3894152 1999571717667353346091127 := by
  unfold tailWord_3894152
  simp only [CollatzResearch.WordTrace]
  refine ⟨71015695894079923528962355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94687594525439898038616473 71015695894079923528962355)
  ·
    refine ⟨106523543841119885293443533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71015695894079923528962355 106523543841119885293443533)
    ·
      refine ⟨39946328940419956985041325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106523543841119885293443533 39946328940419956985041325)
      ·
        refine ⟨14979873352657483869390497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39946328940419956985041325 14979873352657483869390497)
        ·
          refine ⟨11234905014493112902042873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14979873352657483869390497 11234905014493112902042873)
          ·
            refine ⟨8426178760869834676532155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11234905014493112902042873 8426178760869834676532155)
            ·
              refine ⟨12639268141304752014798233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8426178760869834676532155 12639268141304752014798233)
              ·
                refine ⟨9479451105978564011098675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12639268141304752014798233 9479451105978564011098675)
                ·
                  refine ⟨14219176658967846016648013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9479451105978564011098675 14219176658967846016648013)
                  ·
                    refine ⟨5332191247112942256243005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14219176658967846016648013 5332191247112942256243005)
                    ·
                      refine ⟨1999571717667353346091127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5332191247112942256243005 1999571717667353346091127)
                      ·
                        rfl

theorem cell23_3894152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_3894152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3894152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3894152 prefixEnd_3894152 := by exact prefixLift 3894152
  have htrace : WordTrace (prefixWord ++ tailWord_3894152) baseStart_3894152 baseEnd_3894152 := by
    simpa [prefixWord, tailWord_3894152, baseEnd_3894152] using wordTrace_append hprefix tailTrace_3894152
  have hstable : (prefixWord ++ tailWord_3894152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894152).length < 2 ^ (prefixWord ++ tailWord_3894152).sum := by decide
  have hdescent : baseEnd_3894152 < baseStart_3894152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894170 : List Nat := [3, 1, 1, 4, 3, 2, 2, 2, 1, 2, 2]
def baseStart_3894170 : Nat := 118140960795 + 3894170 * 2 ^ 59
def prefixEnd_3894170 : Nat := 4983230072969 + 3 ^ 40 * 3894170 * 2
def baseEnd_3894170 : Nat := 1999580960319134275666045

theorem tailTrace_3894170 : CollatzResearch.WordTrace tailWord_3894170 prefixEnd_3894170 1999580960319134275666045 := by
  unfold tailWord_3894170
  simp only [CollatzResearch.WordTrace]
  refine ⟨35508012075523659033019991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94688032201396424088053309 35508012075523659033019991)
  ·
    refine ⟨53262018113285488549529987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35508012075523659033019991 53262018113285488549529987)
    ·
      refine ⟨79893027169928232824294981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53262018113285488549529987 79893027169928232824294981)
      ·
        refine ⟨14979942594361543654555309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79893027169928232824294981 14979942594361543654555309)
        ·
          refine ⟨5617478472885578870458241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14979942594361543654555309 5617478472885578870458241)
          ·
            refine ⟨4213108854664184152843681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5617478472885578870458241 4213108854664184152843681)
            ·
              refine ⟨3159831640998138114632761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4213108854664184152843681 3159831640998138114632761)
              ·
                refine ⟨2369873730748603585974571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3159831640998138114632761 2369873730748603585974571)
                ·
                  refine ⟨3554810596122905378961857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2369873730748603585974571 3554810596122905378961857)
                  ·
                    refine ⟨2666107947092179034221393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3554810596122905378961857 2666107947092179034221393)
                    ·
                      refine ⟨1999580960319134275666045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2666107947092179034221393 1999580960319134275666045)
                      ·
                        rfl

theorem cell23_3894170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_3894170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3894170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3894170 prefixEnd_3894170 := by exact prefixLift 3894170
  have htrace : WordTrace (prefixWord ++ tailWord_3894170) baseStart_3894170 baseEnd_3894170 := by
    simpa [prefixWord, tailWord_3894170, baseEnd_3894170] using wordTrace_append hprefix tailTrace_3894170
  have hstable : (prefixWord ++ tailWord_3894170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894170).length < 2 ^ (prefixWord ++ tailWord_3894170).sum := by decide
  have hdescent : baseEnd_3894170 < baseStart_3894170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894175 : List Nat := [1, 1, 2, 5, 2, 1, 1, 1, 2, 3, 4]
def baseStart_3894175 : Nat := 118140960795 + 3894175 * 2 ^ 59
def prefixEnd_3894175 : Nat := 4983230072969 + 3 ^ 40 * 3894175 * 2
def baseEnd_3894175 : Nat := 1999583527722406756103521

theorem tailTrace_3894175 : CollatzResearch.WordTrace tailWord_3894175 prefixEnd_3894175 1999583527722406756103521 := by
  unfold tailWord_3894175
  simp only [CollatzResearch.WordTrace]
  refine ⟨142032230667076521986011979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94688153778051014657341319 142032230667076521986011979)
  ·
    refine ⟨213048346000614782979017969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142032230667076521986011979 213048346000614782979017969)
    ·
      refine ⟨159786259500461087234263477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213048346000614782979017969 159786259500461087234263477)
      ·
        refine ⟨14979961828168226928212201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 159786259500461087234263477 14979961828168226928212201)
        ·
          refine ⟨11234971371126170196159151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14979961828168226928212201 11234971371126170196159151)
          ·
            refine ⟨16852457056689255294238727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11234971371126170196159151 16852457056689255294238727)
            ·
              refine ⟨25278685585033882941358091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16852457056689255294238727 25278685585033882941358091)
              ·
                refine ⟨37918028377550824412037137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25278685585033882941358091 37918028377550824412037137)
                ·
                  refine ⟨28438521283163118309027853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37918028377550824412037137 28438521283163118309027853)
                  ·
                    refine ⟨10664445481186169365885445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28438521283163118309027853 10664445481186169365885445)
                    ·
                      refine ⟨1999583527722406756103521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10664445481186169365885445 1999583527722406756103521)
                      ·
                        rfl

theorem cell23_3894175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_3894175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3894175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3894175 prefixEnd_3894175 := by exact prefixLift 3894175
  have htrace : WordTrace (prefixWord ++ tailWord_3894175) baseStart_3894175 baseEnd_3894175 := by
    simpa [prefixWord, tailWord_3894175, baseEnd_3894175] using wordTrace_append hprefix tailTrace_3894175
  have hstable : (prefixWord ++ tailWord_3894175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894175).length < 2 ^ (prefixWord ++ tailWord_3894175).sum := by decide
  have hdescent : baseEnd_3894175 < baseStart_3894175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894188 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 6]
def baseStart_3894188 : Nat := 118140960795 + 3894188 * 2 ^ 59
def prefixEnd_3894188 : Nat := 4983230072969 + 3 ^ 40 * 3894188 * 2
def baseEnd_3894188 : Nat := 1999590202970915205240961

theorem tailTrace_3894188 : CollatzResearch.WordTrace tailWord_3894188 prefixEnd_3894188 1999590202970915205240961 := by
  unfold tailWord_3894188
  simp only [CollatzResearch.WordTrace]
  refine ⟨71016352408014712603117609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94688469877352950137490145 71016352408014712603117609)
  ·
    refine ⟨53262264306011034452338207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71016352408014712603117609 53262264306011034452338207)
    ·
      refine ⟨79893396459016551678507311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53262264306011034452338207 79893396459016551678507311)
      ·
        refine ⟨119840094688524827517760967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79893396459016551678507311 119840094688524827517760967)
        ·
          refine ⟨179760142032787241276641451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119840094688524827517760967 179760142032787241276641451)
          ·
            refine ⟨269640213049180861914962177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179760142032787241276641451 269640213049180861914962177)
            ·
              refine ⟨202230159786885646436221633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269640213049180861914962177 202230159786885646436221633)
              ·
                refine ⟨151672619840164234827166225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202230159786885646436221633 151672619840164234827166225)
                ·
                  refine ⟨113754464880123176120374669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151672619840164234827166225 113754464880123176120374669)
                  ·
                    refine ⟨42657924330046191045140501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 113754464880123176120374669 42657924330046191045140501)
                    ·
                      refine ⟨1999590202970915205240961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42657924330046191045140501 1999590202970915205240961)
                      ·
                        rfl

theorem cell23_3894188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 6].length) (baseStart_3894188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3894188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3894188 prefixEnd_3894188 := by exact prefixLift 3894188
  have htrace : WordTrace (prefixWord ++ tailWord_3894188) baseStart_3894188 baseEnd_3894188 := by
    simpa [prefixWord, tailWord_3894188, baseEnd_3894188] using wordTrace_append hprefix tailTrace_3894188
  have hstable : (prefixWord ++ tailWord_3894188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894188).length < 2 ^ (prefixWord ++ tailWord_3894188).sum := by decide
  have hdescent : baseEnd_3894188 < baseStart_3894188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894196 : List Nat := [2, 5, 2, 1, 1, 1, 2, 1, 3, 3, 2]
def baseStart_3894196 : Nat := 118140960795 + 3894196 * 2 ^ 59
def prefixEnd_3894196 : Nat := 4983230072969 + 3 ^ 40 * 3894196 * 2
def baseEnd_3894196 : Nat := 1999594310816151173940925

theorem tailTrace_3894196 : CollatzResearch.WordTrace tailWord_3894196 prefixEnd_3894196 1999594310816151173940925 := by
  unfold tailWord_3894196
  simp only [CollatzResearch.WordTrace]
  refine ⟨71016498300000221286263221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94688664400000295048350961 71016498300000221286263221)
  ·
    refine ⟨6657796715625020745587177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71016498300000221286263221 6657796715625020745587177)
    ·
      refine ⟨4993347536718765559190383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6657796715625020745587177 4993347536718765559190383)
      ·
        refine ⟨7490021305078148338785575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4993347536718765559190383 7490021305078148338785575)
        ·
          refine ⟨11235031957617222508178363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7490021305078148338785575 11235031957617222508178363)
          ·
            refine ⟨16852547936425833762267545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11235031957617222508178363 16852547936425833762267545)
            ·
              refine ⟨12639410952319375321700659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16852547936425833762267545 12639410952319375321700659)
              ·
                refine ⟨18959116428479062982550989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12639410952319375321700659 18959116428479062982550989)
                ·
                  refine ⟨7109668660679648618456621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18959116428479062982550989 7109668660679648618456621)
                  ·
                    refine ⟨2666125747754868231921233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7109668660679648618456621 2666125747754868231921233)
                    ·
                      refine ⟨1999594310816151173940925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2666125747754868231921233 1999594310816151173940925)
                      ·
                        rfl

theorem cell23_3894196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_3894196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3894196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3894196 prefixEnd_3894196 := by exact prefixLift 3894196
  have htrace : WordTrace (prefixWord ++ tailWord_3894196) baseStart_3894196 baseEnd_3894196 := by
    simpa [prefixWord, tailWord_3894196, baseEnd_3894196] using wordTrace_append hprefix tailTrace_3894196
  have hstable : (prefixWord ++ tailWord_3894196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894196).length < 2 ^ (prefixWord ++ tailWord_3894196).sum := by decide
  have hdescent : baseEnd_3894196 < baseStart_3894196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894225 : List Nat := [1, 2, 2, 1, 2, 1, 3, 1, 4, 3, 3]
def baseStart_3894225 : Nat := 118140960795 + 3894225 * 2 ^ 59
def prefixEnd_3894225 : Nat := 4983230072969 + 3 ^ 40 * 3894225 * 2
def baseEnd_3894225 : Nat := 1999609201755131560478291

theorem tailTrace_3894225 : CollatzResearch.WordTrace tailWord_3894225 prefixEnd_3894225 1999609201755131560478291 := by
  unfold tailWord_3894225
  simp only [CollatzResearch.WordTrace]
  refine ⟨142034054316895380525332129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94689369544596920350221419 142034054316895380525332129)
  ·
    refine ⟨106525540737671535393999097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142034054316895380525332129 106525540737671535393999097)
    ·
      refine ⟨79894155553253651545499323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106525540737671535393999097 79894155553253651545499323)
      ·
        refine ⟨119841233329880477318248985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79894155553253651545499323 119841233329880477318248985)
        ·
          refine ⟨89880924997410357988686739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119841233329880477318248985 89880924997410357988686739)
          ·
            refine ⟨134821387496115536983030109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89880924997410357988686739 134821387496115536983030109)
            ·
              refine ⟨50558020311043326368636291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134821387496115536983030109 50558020311043326368636291)
              ·
                refine ⟨75837030466564989552954437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50558020311043326368636291 75837030466564989552954437)
                ·
                  refine ⟨14219443212480935541178957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75837030466564989552954437 14219443212480935541178957)
                  ·
                    refine ⟨5332291204680350827942109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14219443212480935541178957 5332291204680350827942109)
                    ·
                      refine ⟨1999609201755131560478291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5332291204680350827942109 1999609201755131560478291)
                      ·
                        rfl

theorem cell23_3894225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 3, 3].length) (baseStart_3894225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3894225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3894225 prefixEnd_3894225 := by exact prefixLift 3894225
  have htrace : WordTrace (prefixWord ++ tailWord_3894225) baseStart_3894225 baseEnd_3894225 := by
    simpa [prefixWord, tailWord_3894225, baseEnd_3894225] using wordTrace_append hprefix tailTrace_3894225
  have hstable : (prefixWord ++ tailWord_3894225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894225).length < 2 ^ (prefixWord ++ tailWord_3894225).sum := by decide
  have hdescent : baseEnd_3894225 < baseStart_3894225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894226 : List Nat := [3, 2, 2, 3, 1, 2, 1, 1, 4, 2, 2]
def baseStart_3894226 : Nat := 118140960795 + 3894226 * 2 ^ 59
def prefixEnd_3894226 : Nat := 4983230072969 + 3 ^ 40 * 3894226 * 2
def baseEnd_3894226 : Nat := 1999609715235786056565787

theorem tailTrace_3894226 : CollatzResearch.WordTrace tailWord_3894226 prefixEnd_3894226 1999609715235786056565787 := by
  unfold tailWord_3894226
  simp only [CollatzResearch.WordTrace]
  refine ⟨35508522697472939424029633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94689393859927838464079021 35508522697472939424029633)
  ·
    refine ⟨26631392023104704568022225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35508522697472939424029633 26631392023104704568022225)
    ·
      refine ⟨19973544017328528426016669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26631392023104704568022225 19973544017328528426016669)
      ·
        refine ⟨7490079006498198159756251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19973544017328528426016669 7490079006498198159756251)
        ·
          refine ⟨11235118509747297239634377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7490079006498198159756251 11235118509747297239634377)
          ·
            refine ⟨8426338882310472929725783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11235118509747297239634377 8426338882310472929725783)
            ·
              refine ⟨12639508323465709394588675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8426338882310472929725783 12639508323465709394588675)
              ·
                refine ⟨18959262485198564091883013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12639508323465709394588675 18959262485198564091883013)
                ·
                  refine ⟨3554861715974730767228065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18959262485198564091883013 3554861715974730767228065)
                  ·
                    refine ⟨2666146286981048075421049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3554861715974730767228065 2666146286981048075421049)
                    ·
                      refine ⟨1999609715235786056565787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2666146286981048075421049 1999609715235786056565787)
                      ·
                        rfl

theorem cell23_3894226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_3894226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3894226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3894226 prefixEnd_3894226 := by exact prefixLift 3894226
  have htrace : WordTrace (prefixWord ++ tailWord_3894226) baseStart_3894226 baseEnd_3894226 := by
    simpa [prefixWord, tailWord_3894226, baseEnd_3894226] using wordTrace_append hprefix tailTrace_3894226
  have hstable : (prefixWord ++ tailWord_3894226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894226).length < 2 ^ (prefixWord ++ tailWord_3894226).sum := by decide
  have hdescent : baseEnd_3894226 < baseStart_3894226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894232 : List Nat := [2, 1, 2, 2, 2, 3, 2, 4, 5]
def baseStart_3894232 : Nat := 118140960795 + 3894232 * 2 ^ 59
def prefixEnd_3894232 : Nat := 4983230072969 + 3 ^ 40 * 3894232 * 2
def baseEnd_3894232 : Nat := 222179199568857003676751

theorem tailTrace_3894232 : CollatzResearch.WordTrace tailWord_3894232 prefixEnd_3894232 222179199568857003676751 := by
  unfold tailWord_3894232
  simp only [CollatzResearch.WordTrace]
  refine ⟨71017154813935010360418475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94689539751913347147224633 71017154813935010360418475)
  ·
    refine ⟨106525732220902515540627713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71017154813935010360418475 106525732220902515540627713)
    ·
      refine ⟨79894299165676886655470785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106525732220902515540627713 79894299165676886655470785)
      ·
        refine ⟨59920724374257664991603089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79894299165676886655470785 59920724374257664991603089)
        ·
          refine ⟨44940543280693248743702317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59920724374257664991603089 44940543280693248743702317)
          ·
            refine ⟨16852703730259968278888369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44940543280693248743702317 16852703730259968278888369)
            ·
              refine ⟨12639527797694976209166277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16852703730259968278888369 12639527797694976209166277)
              ·
                refine ⟨2369911462067808039218677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12639527797694976209166277 2369911462067808039218677)
                ·
                  refine ⟨222179199568857003676751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2369911462067808039218677 222179199568857003676751)
                  ·
                    rfl

theorem cell23_3894232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 4, 5].length) (baseStart_3894232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3894232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3894232 prefixEnd_3894232 := by exact prefixLift 3894232
  have htrace : WordTrace (prefixWord ++ tailWord_3894232) baseStart_3894232 baseEnd_3894232 := by
    simpa [prefixWord, tailWord_3894232, baseEnd_3894232] using wordTrace_append hprefix tailTrace_3894232
  have hstable : (prefixWord ++ tailWord_3894232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894232).length < 2 ^ (prefixWord ++ tailWord_3894232).sum := by decide
  have hdescent : baseEnd_3894232 < baseStart_3894232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894262 : List Nat := [5, 1, 1, 1, 3, 1, 2, 1, 1, 7]
def baseStart_3894262 : Nat := 118140960795 + 3894262 * 2 ^ 59
def prefixEnd_3894262 : Nat := 4983230072969 + 3 ^ 40 * 3894262 * 2
def baseEnd_3894262 : Nat := 666542733513115971905207

theorem tailTrace_3894262 : CollatzResearch.WordTrace tailWord_3894262 prefixEnd_3894262 666542733513115971905207 := by
  unfold tailWord_3894262
  simp only [CollatzResearch.WordTrace]
  refine ⟨8877212738610083490276815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94690269211840890562952693 8877212738610083490276815)
  ·
    refine ⟨13315819107915125235415223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8877212738610083490276815 13315819107915125235415223)
    ·
      refine ⟨19973728661872687853122835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13315819107915125235415223 19973728661872687853122835)
      ·
        refine ⟨29960592992809031779684253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19973728661872687853122835 29960592992809031779684253)
        ·
          refine ⟨11235222372303386917381595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29960592992809031779684253 11235222372303386917381595)
          ·
            refine ⟨16852833558455080376072393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11235222372303386917381595 16852833558455080376072393)
            ·
              refine ⟨12639625168841310282054295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16852833558455080376072393 12639625168841310282054295)
              ·
                refine ⟨18959437753261965423081443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12639625168841310282054295 18959437753261965423081443)
                ·
                  refine ⟨28439156629892948134622165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18959437753261965423081443 28439156629892948134622165)
                  ·
                    refine ⟨666542733513115971905207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28439156629892948134622165 666542733513115971905207)
                    ·
                      rfl

theorem cell23_3894262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_3894262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3894262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3894262 prefixEnd_3894262 := by exact prefixLift 3894262
  have htrace : WordTrace (prefixWord ++ tailWord_3894262) baseStart_3894262 baseEnd_3894262 := by
    simpa [prefixWord, tailWord_3894262, baseEnd_3894262] using wordTrace_append hprefix tailTrace_3894262
  have hstable : (prefixWord ++ tailWord_3894262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894262).length < 2 ^ (prefixWord ++ tailWord_3894262).sum := by decide
  have hdescent : baseEnd_3894262 < baseStart_3894262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894265 : List Nat := [1, 2, 1, 3, 1, 3, 1, 3, 1, 3, 4]
def baseStart_3894265 : Nat := 118140960795 + 3894265 * 2 ^ 59
def prefixEnd_3894265 : Nat := 4983230072969 + 3 ^ 40 * 3894265 * 2
def baseEnd_3894265 : Nat := 1999629740981311403978107

theorem tailTrace_3894265 : CollatzResearch.WordTrace tailWord_3894265 prefixEnd_3894265 1999629740981311403978107 := by
  unfold tailWord_3894265
  simp only [CollatzResearch.WordTrace]
  refine ⟨142035513236750467356788249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94690342157833644904525499 142035513236750467356788249)
  ·
    refine ⟨106526634927562850517591187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142035513236750467356788249 106526634927562850517591187)
    ·
      refine ⟨159789952391344275776386781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106526634927562850517591187 159789952391344275776386781)
      ·
        refine ⟨59921232146754103416145043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159789952391344275776386781 59921232146754103416145043)
        ·
          refine ⟨89881848220131155124217565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59921232146754103416145043 89881848220131155124217565)
          ·
            refine ⟨33705693082549183171581587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89881848220131155124217565 33705693082549183171581587)
            ·
              refine ⟨50558539623823774757372381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33705693082549183171581587 50558539623823774757372381)
              ·
                refine ⟨18959452358933915534014643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50558539623823774757372381 18959452358933915534014643)
                ·
                  refine ⟨28439178538400873301021965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18959452358933915534014643 28439178538400873301021965)
                  ·
                    refine ⟨10664691951900327487883237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28439178538400873301021965 10664691951900327487883237)
                    ·
                      refine ⟨1999629740981311403978107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10664691951900327487883237 1999629740981311403978107)
                      ·
                        rfl

theorem cell23_3894265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_3894265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3894265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3894265 prefixEnd_3894265 := by exact prefixLift 3894265
  have htrace : WordTrace (prefixWord ++ tailWord_3894265) baseStart_3894265 baseEnd_3894265 := by
    simpa [prefixWord, tailWord_3894265, baseEnd_3894265] using wordTrace_append hprefix tailTrace_3894265
  have hstable : (prefixWord ++ tailWord_3894265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894265).length < 2 ^ (prefixWord ++ tailWord_3894265).sum := by decide
  have hdescent : baseEnd_3894265 < baseStart_3894265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894282 : List Nat := [3, 1, 2, 2, 3, 1, 1, 1, 4, 1, 4]
def baseStart_3894282 : Nat := 118140960795 + 3894282 * 2 ^ 59
def prefixEnd_3894282 : Nat := 4983230072969 + 3 ^ 40 * 3894282 * 2
def baseEnd_3894282 : Nat := 1999638470152437837465529

theorem tailTrace_3894282 : CollatzResearch.WordTrace tailWord_3894282 prefixEnd_3894282 1999638470152437837465529 := by
  unfold tailWord_3894282
  simp only [CollatzResearch.WordTrace]
  refine ⟨35509033319422219815039275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94690755518459252840104733 35509033319422219815039275)
  ·
    refine ⟨53263549979133329722558913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35509033319422219815039275 53263549979133329722558913)
    ·
      refine ⟨39947662484349997291919185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53263549979133329722558913 39947662484349997291919185)
      ·
        refine ⟨29960746863262497968939389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39947662484349997291919185 29960746863262497968939389)
        ·
          refine ⟨11235280073723436738352271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29960746863262497968939389 11235280073723436738352271)
          ·
            refine ⟨16852920110585155107528407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11235280073723436738352271 16852920110585155107528407)
            ·
              refine ⟨25279380165877732661292611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16852920110585155107528407 25279380165877732661292611)
              ·
                refine ⟨37919070248816598991938917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25279380165877732661292611 37919070248816598991938917)
                ·
                  refine ⟨7109825671653112310988547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37919070248816598991938917 7109825671653112310988547)
                  ·
                    refine ⟨10664738507479668466482821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7109825671653112310988547 10664738507479668466482821)
                    ·
                      refine ⟨1999638470152437837465529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10664738507479668466482821 1999638470152437837465529)
                      ·
                        rfl

theorem cell23_3894282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_3894282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3894282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3894282 prefixEnd_3894282 := by exact prefixLift 3894282
  have htrace : WordTrace (prefixWord ++ tailWord_3894282) baseStart_3894282 baseEnd_3894282 := by
    simpa [prefixWord, tailWord_3894282, baseEnd_3894282] using wordTrace_append hprefix tailTrace_3894282
  have hstable : (prefixWord ++ tailWord_3894282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894282).length < 2 ^ (prefixWord ++ tailWord_3894282).sum := by decide
  have hdescent : baseEnd_3894282 < baseStart_3894282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894325 : List Nat := [1, 3, 3, 1, 1, 1, 1, 2, 1, 1, 8]
def baseStart_3894325 : Nat := 118140960795 + 3894325 * 2 ^ 59
def prefixEnd_3894325 : Nat := 4983230072969 + 3 ^ 40 * 3894325 * 2
def baseEnd_3894325 : Nat := 1999660549820581169227831

theorem tailTrace_3894325 : CollatzResearch.WordTrace tailWord_3894325 prefixEnd_3894325 1999660549820581169227831 := by
  unfold tailWord_3894325
  simp only [CollatzResearch.WordTrace]
  refine ⟨142037701616533097603972429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94691801077688731735981619 142037701616533097603972429)
  ·
    refine ⟨53264138106199911601489661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142037701616533097603972429 53264138106199911601489661)
    ·
      refine ⟨19974051789824966850558623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53264138106199911601489661 19974051789824966850558623)
      ·
        refine ⟨29961077684737450275837935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19974051789824966850558623 29961077684737450275837935)
        ·
          refine ⟨44941616527106175413756903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29961077684737450275837935 44941616527106175413756903)
          ·
            refine ⟨67412424790659263120635355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44941616527106175413756903 67412424790659263120635355)
            ·
              refine ⟨101118637185988894680953033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67412424790659263120635355 101118637185988894680953033)
              ·
                refine ⟨75838977889491671010714775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101118637185988894680953033 75838977889491671010714775)
                ·
                  refine ⟨113758466834237506516072163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75838977889491671010714775 113758466834237506516072163)
                  ·
                    refine ⟨170637700251356259774108245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 113758466834237506516072163 170637700251356259774108245)
                    ·
                      refine ⟨1999660549820581169227831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 170637700251356259774108245 1999660549820581169227831)
                      ·
                        rfl

theorem cell23_3894325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_3894325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3894325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3894325 prefixEnd_3894325 := by exact prefixLift 3894325
  have htrace : WordTrace (prefixWord ++ tailWord_3894325) baseStart_3894325 baseEnd_3894325 := by
    simpa [prefixWord, tailWord_3894325, baseEnd_3894325] using wordTrace_append hprefix tailTrace_3894325
  have hstable : (prefixWord ++ tailWord_3894325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894325).length < 2 ^ (prefixWord ++ tailWord_3894325).sum := by decide
  have hdescent : baseEnd_3894325 < baseStart_3894325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894343 : List Nat := [1, 1, 4, 1, 3, 4, 2, 2, 1, 4]
def baseStart_3894343 : Nat := 118140960795 + 3894343 * 2 ^ 59
def prefixEnd_3894343 : Nat := 4983230072969 + 3 ^ 40 * 3894343 * 2
def baseEnd_3894343 : Nat := 666556597490787366267583

theorem tailTrace_3894343 : CollatzResearch.WordTrace tailWord_3894343 prefixEnd_3894343 666556597490787366267583 := by
  unfold tailWord_3894343
  simp only [CollatzResearch.WordTrace]
  refine ⟨142038358130467886678127683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94692238753645257785418455 142038358130467886678127683)
  ·
    refine ⟨213057537195701830017191525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142038358130467886678127683 213057537195701830017191525)
    ·
      refine ⟨39948288224194093128223411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213057537195701830017191525 39948288224194093128223411)
      ·
        refine ⟨59922432336291139692335117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39948288224194093128223411 59922432336291139692335117)
        ·
          refine ⟨22470912126109177384625669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59922432336291139692335117 22470912126109177384625669)
          ·
            refine ⟨4213296023645470759617313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22470912126109177384625669 4213296023645470759617313)
            ·
              refine ⟨3159972017734103069712985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4213296023645470759617313 3159972017734103069712985)
              ·
                refine ⟨2369979013300577302284739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3159972017734103069712985 2369979013300577302284739)
                ·
                  refine ⟨3554968519950865953427109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2369979013300577302284739 3554968519950865953427109)
                  ·
                    refine ⟨666556597490787366267583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3554968519950865953427109 666556597490787366267583)
                    ·
                      rfl

theorem cell23_3894343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 2, 1, 4].length) (baseStart_3894343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3894343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3894343 prefixEnd_3894343 := by exact prefixLift 3894343
  have htrace : WordTrace (prefixWord ++ tailWord_3894343) baseStart_3894343 baseEnd_3894343 := by
    simpa [prefixWord, tailWord_3894343, baseEnd_3894343] using wordTrace_append hprefix tailTrace_3894343
  have hstable : (prefixWord ++ tailWord_3894343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894343).length < 2 ^ (prefixWord ++ tailWord_3894343).sum := by decide
  have hdescent : baseEnd_3894343 < baseStart_3894343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894355 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 2, 5, 4]
def baseStart_3894355 : Nat := 118140960795 + 3894355 * 2 ^ 59
def prefixEnd_3894355 : Nat := 4983230072969 + 3 ^ 40 * 3894355 * 2
def baseEnd_3894355 : Nat := 1999675954240216051852693

theorem tailTrace_3894355 : CollatzResearch.WordTrace tailWord_3894355 prefixEnd_3894355 1999675954240216051852693 := by
  unfold tailWord_3894355
  simp only [CollatzResearch.WordTrace]
  refine ⟨142038795806424412727564519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94692530537616275151709679 142038795806424412727564519)
  ·
    refine ⟨213058193709636619091346779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142038795806424412727564519 213058193709636619091346779)
    ·
      refine ⟨319587290564454928637020169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213058193709636619091346779 319587290564454928637020169)
      ·
        refine ⟨239690467923341196477765127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319587290564454928637020169 239690467923341196477765127)
        ·
          refine ⟨359535701885011794716647691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239690467923341196477765127 359535701885011794716647691)
          ·
            refine ⟨539303552827517692074971537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359535701885011794716647691 539303552827517692074971537)
            ·
              refine ⟨404477664620638269056228653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 539303552827517692074971537 404477664620638269056228653)
              ·
                refine ⟨151679124232739350896085745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 404477664620638269056228653 151679124232739350896085745)
                ·
                  refine ⟨113759343174554513172064309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151679124232739350896085745 113759343174554513172064309)
                  ·
                    refine ⟨10664938422614485609881029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 113759343174554513172064309 10664938422614485609881029)
                    ·
                      refine ⟨1999675954240216051852693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10664938422614485609881029 1999675954240216051852693)
                      ·
                        rfl

theorem cell23_3894355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 5, 4].length) (baseStart_3894355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3894355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3894355 prefixEnd_3894355 := by exact prefixLift 3894355
  have htrace : WordTrace (prefixWord ++ tailWord_3894355) baseStart_3894355 baseEnd_3894355 := by
    simpa [prefixWord, tailWord_3894355, baseEnd_3894355] using wordTrace_append hprefix tailTrace_3894355
  have hstable : (prefixWord ++ tailWord_3894355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894355).length < 2 ^ (prefixWord ++ tailWord_3894355).sum := by decide
  have hdescent : baseEnd_3894355 < baseStart_3894355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894415 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 8]
def baseStart_3894415 : Nat := 118140960795 + 3894415 * 2 ^ 59
def prefixEnd_3894415 : Nat := 4983230072969 + 3 ^ 40 * 3894415 * 2
def baseEnd_3894415 : Nat := 1999706763079485817102417

theorem tailTrace_3894415 : CollatzResearch.WordTrace tailWord_3894415 prefixEnd_3894415 1999706763079485817102417 := by
  unfold tailWord_3894415
  simp only [CollatzResearch.WordTrace]
  refine ⟨142040984186207042974748699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94693989457471361983165799 142040984186207042974748699)
  ·
    refine ⟨213061476279310564462123049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142040984186207042974748699 213061476279310564462123049)
    ·
      refine ⟨159796107209482923346592287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213061476279310564462123049 159796107209482923346592287)
      ·
        refine ⟨239694160814224385019888431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159796107209482923346592287 239694160814224385019888431)
        ·
          refine ⟨359541241221336577529832647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239694160814224385019888431 359541241221336577529832647)
          ·
            refine ⟨539311861832004866294748971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359541241221336577529832647 539311861832004866294748971)
            ·
              refine ⟨808967792748007299442123457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 539311861832004866294748971 808967792748007299442123457)
              ·
                refine ⟨606725844561005474581592593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 808967792748007299442123457 606725844561005474581592593)
                ·
                  refine ⟨455044383420754105936194445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 606725844561005474581592593 455044383420754105936194445)
                  ·
                    refine ⟨170641643782782789726072917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 455044383420754105936194445 170641643782782789726072917)
                    ·
                      refine ⟨1999706763079485817102417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 170641643782782789726072917 1999706763079485817102417)
                      ·
                        rfl

theorem cell23_3894415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 8].length) (baseStart_3894415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3894415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3894415 prefixEnd_3894415 := by exact prefixLift 3894415
  have htrace : WordTrace (prefixWord ++ tailWord_3894415) baseStart_3894415 baseEnd_3894415 := by
    simpa [prefixWord, tailWord_3894415, baseEnd_3894415] using wordTrace_append hprefix tailTrace_3894415
  have hstable : (prefixWord ++ tailWord_3894415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894415).length < 2 ^ (prefixWord ++ tailWord_3894415).sum := by decide
  have hdescent : baseEnd_3894415 < baseStart_3894415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894426 : List Nat := [3, 1, 1, 5, 1, 1, 1, 4, 1, 2, 3]
def baseStart_3894426 : Nat := 118140960795 + 3894426 * 2 ^ 59
def prefixEnd_3894426 : Nat := 4983230072969 + 3 ^ 40 * 3894426 * 2
def baseEnd_3894426 : Nat := 1999712411366685274064867

theorem tailTrace_3894426 : CollatzResearch.WordTrace tailWord_3894426 prefixEnd_3894426 1999712411366685274064867 := by
  unfold tailWord_3894426
  simp only [CollatzResearch.WordTrace]
  refine ⟨35510346347291797963349783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94694256926111461235599421 35510346347291797963349783)
  ·
    refine ⟨53265519520937696945024675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35510346347291797963349783 53265519520937696945024675)
    ·
      refine ⟨79898279281406545417537013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53265519520937696945024675 79898279281406545417537013)
      ·
        refine ⟨7490463682631863632894095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79898279281406545417537013 7490463682631863632894095)
        ·
          refine ⟨11235695523947795449341143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7490463682631863632894095 11235695523947795449341143)
          ·
            refine ⟨16853543285921693174011715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11235695523947795449341143 16853543285921693174011715)
            ·
              refine ⟨25280314928882539761017573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16853543285921693174011715 25280314928882539761017573)
              ·
                refine ⟨4740059049165476205190795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25280314928882539761017573 4740059049165476205190795)
                ·
                  refine ⟨7110088573748214307786193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4740059049165476205190795 7110088573748214307786193)
                  ·
                    refine ⟨5332566430311160730839645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7110088573748214307786193 5332566430311160730839645)
                    ·
                      refine ⟨1999712411366685274064867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5332566430311160730839645 1999712411366685274064867)
                      ·
                        rfl

theorem cell23_3894426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_3894426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3894426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3894426 prefixEnd_3894426 := by exact prefixLift 3894426
  have htrace : WordTrace (prefixWord ++ tailWord_3894426) baseStart_3894426 baseEnd_3894426 := by
    simpa [prefixWord, tailWord_3894426, baseEnd_3894426] using wordTrace_append hprefix tailTrace_3894426
  have hstable : (prefixWord ++ tailWord_3894426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894426).length < 2 ^ (prefixWord ++ tailWord_3894426).sum := by decide
  have hdescent : baseEnd_3894426 < baseStart_3894426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894472 : List Nat := [2, 1, 3, 1, 2, 1, 2, 3, 2, 6]
def baseStart_3894472 : Nat := 118140960795 + 3894472 * 2 ^ 59
def prefixEnd_3894472 : Nat := 4983230072969 + 3 ^ 40 * 3894472 * 2
def baseEnd_3894472 : Nat := 666578677158930698029885

theorem tailTrace_3894472 : CollatzResearch.WordTrace tailWord_3894472 prefixEnd_3894472 666578677158930698029885 := by
  unfold tailWord_3894472
  simp only [CollatzResearch.WordTrace]
  refine ⟨71021531573500270854786835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94695375431333694473049113 71021531573500270854786835)
  ·
    refine ⟨106532297360250406282180253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71021531573500270854786835 106532297360250406282180253)
    ·
      refine ⟨39949611510093902355817595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106532297360250406282180253 39949611510093902355817595)
      ·
        refine ⟨59924417265140853533726393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39949611510093902355817595 59924417265140853533726393)
        ·
          refine ⟨44943312948855640150294795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59924417265140853533726393 44943312948855640150294795)
          ·
            refine ⟨67414969423283460225442193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44943312948855640150294795 67414969423283460225442193)
            ·
              refine ⟨50561227067462595169081645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67414969423283460225442193 50561227067462595169081645)
              ·
                refine ⟨18960460150298473188405617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50561227067462595169081645 18960460150298473188405617)
                ·
                  refine ⟨14220345112723854891304213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18960460150298473188405617 14220345112723854891304213)
                  ·
                    refine ⟨666578677158930698029885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14220345112723854891304213 666578677158930698029885)
                    ·
                      rfl

theorem cell23_3894472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 2, 6].length) (baseStart_3894472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3894472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3894472 prefixEnd_3894472 := by exact prefixLift 3894472
  have htrace : WordTrace (prefixWord ++ tailWord_3894472) baseStart_3894472 baseEnd_3894472 := by
    simpa [prefixWord, tailWord_3894472, baseEnd_3894472] using wordTrace_append hprefix tailTrace_3894472
  have hstable : (prefixWord ++ tailWord_3894472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894472).length < 2 ^ (prefixWord ++ tailWord_3894472).sum := by decide
  have hdescent : baseEnd_3894472 < baseStart_3894472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894477 : List Nat := [1, 6, 2, 2, 1, 2, 1, 2, 1, 2, 3]
def baseStart_3894477 : Nat := 118140960795 + 3894477 * 2 ^ 59
def prefixEnd_3894477 : Nat := 4983230072969 + 3 ^ 40 * 3894477 * 2
def baseEnd_3894477 : Nat := 1999738598880064574527133

theorem tailTrace_3894477 : CollatzResearch.WordTrace tailWord_3894477 prefixEnd_3894477 1999738598880064574527133 := by
  unfold tailWord_3894477
  simp only [CollatzResearch.WordTrace]
  refine ⟨142043245511982427563505685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94695497007988285042337123 142043245511982427563505685)
  ·
    refine ⟨6658277133374176292039329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 142043245511982427563505685 6658277133374176292039329)
    ·
      refine ⟨4993707850030632219029497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6658277133374176292039329 4993707850030632219029497)
      ·
        refine ⟨3745280887522974164272123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4993707850030632219029497 3745280887522974164272123)
        ·
          refine ⟨5617921331284461246408185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3745280887522974164272123 5617921331284461246408185)
          ·
            refine ⟨4213440998463345934806139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5617921331284461246408185 4213440998463345934806139)
            ·
              refine ⟨6320161497695018902209209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4213440998463345934806139 6320161497695018902209209)
              ·
                refine ⟨4740121123271264176656907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6320161497695018902209209 4740121123271264176656907)
                ·
                  refine ⟨7110181684906896264985361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4740121123271264176656907 7110181684906896264985361)
                  ·
                    refine ⟨5332636263680172198739021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7110181684906896264985361 5332636263680172198739021)
                    ·
                      refine ⟨1999738598880064574527133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5332636263680172198739021 1999738598880064574527133)
                      ·
                        rfl

theorem cell23_3894477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_3894477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3894477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3894477 prefixEnd_3894477 := by exact prefixLift 3894477
  have htrace : WordTrace (prefixWord ++ tailWord_3894477) baseStart_3894477 baseEnd_3894477 := by
    simpa [prefixWord, tailWord_3894477, baseEnd_3894477] using wordTrace_append hprefix tailTrace_3894477
  have hstable : (prefixWord ++ tailWord_3894477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894477).length < 2 ^ (prefixWord ++ tailWord_3894477).sum := by decide
  have hdescent : baseEnd_3894477 < baseStart_3894477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894496 : List Nat := [2, 1, 1, 3, 1, 5, 1, 2, 1, 4, 2]
def baseStart_3894496 : Nat := 118140960795 + 3894496 * 2 ^ 59
def prefixEnd_3894496 : Nat := 4983230072969 + 3 ^ 40 * 3894496 * 2
def baseEnd_3894496 : Nat := 1999748355012500000189545

theorem tailTrace_3894496 : CollatzResearch.WordTrace tailWord_3894496 prefixEnd_3894496 1999748355012500000189545 := by
  unfold tailWord_3894496
  simp only [CollatzResearch.WordTrace]
  refine ⟨71021969249456796904223671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94695958999275729205631561 71021969249456796904223671)
  ·
    refine ⟨106532953874185195356335507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71021969249456796904223671 106532953874185195356335507)
    ·
      refine ⟨159799430811277793034503261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106532953874185195356335507 159799430811277793034503261)
      ·
        refine ⟨59924786554229172387938723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159799430811277793034503261 59924786554229172387938723)
        ·
          refine ⟨89887179831343758581908085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59924786554229172387938723 89887179831343758581908085)
          ·
            refine ⟨8426923109188477367053883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89887179831343758581908085 8426923109188477367053883)
            ·
              refine ⟨12640384663782716050580825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8426923109188477367053883 12640384663782716050580825)
              ·
                refine ⟨9480288497837037037935619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12640384663782716050580825 9480288497837037037935619)
                ·
                  refine ⟨14220432746755555556903429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9480288497837037037935619 14220432746755555556903429)
                  ·
                    refine ⟨2666331140016666666919393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14220432746755555556903429 2666331140016666666919393)
                    ·
                      refine ⟨1999748355012500000189545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2666331140016666666919393 1999748355012500000189545)
                      ·
                        rfl

theorem cell23_3894496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 1, 4, 2].length) (baseStart_3894496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3894496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3894496 prefixEnd_3894496 := by exact prefixLift 3894496
  have htrace : WordTrace (prefixWord ++ tailWord_3894496) baseStart_3894496 baseEnd_3894496 := by
    simpa [prefixWord, tailWord_3894496, baseEnd_3894496] using wordTrace_append hprefix tailTrace_3894496
  have hstable : (prefixWord ++ tailWord_3894496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894496).length < 2 ^ (prefixWord ++ tailWord_3894496).sum := by decide
  have hdescent : baseEnd_3894496 < baseStart_3894496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894519 : List Nat := [1, 1, 3, 1, 1, 1, 2, 8, 5]
def baseStart_3894519 : Nat := 118140960795 + 3894519 * 2 ^ 59
def prefixEnd_3894519 : Nat := 4983230072969 + 3 ^ 40 * 3894519 * 2
def baseEnd_3894519 : Nat := 222195573896394823355771

theorem tailTrace_3894519 : CollatzResearch.WordTrace tailWord_3894519 prefixEnd_3894519 222195573896394823355771 := by
  unfold tailWord_3894519
  simp only [CollatzResearch.WordTrace]
  refine ⟨142044777377830268736534611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94696518251886845824356407 142044777377830268736534611)
  ·
    refine ⟨213067166066745403104801917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142044777377830268736534611 213067166066745403104801917)
    ·
      refine ⟨79900187275029526164300719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213067166066745403104801917 79900187275029526164300719)
      ·
        refine ⟨119850280912544289246451079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79900187275029526164300719 119850280912544289246451079)
        ·
          refine ⟨179775421368816433869676619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119850280912544289246451079 179775421368816433869676619)
          ·
            refine ⟨269663132053224650804514929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179775421368816433869676619 269663132053224650804514929)
            ·
              refine ⟨202247349039918488103386197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269663132053224650804514929 202247349039918488103386197)
              ·
                refine ⟨2370086121561544782461557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 202247349039918488103386197 2370086121561544782461557)
                ·
                  refine ⟨222195573896394823355771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2370086121561544782461557 222195573896394823355771)
                  ·
                    rfl

theorem cell23_3894519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 8, 5].length) (baseStart_3894519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3894519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3894519 prefixEnd_3894519 := by exact prefixLift 3894519
  have htrace : WordTrace (prefixWord ++ tailWord_3894519) baseStart_3894519 baseEnd_3894519 := by
    simpa [prefixWord, tailWord_3894519, baseEnd_3894519] using wordTrace_append hprefix tailTrace_3894519
  have hstable : (prefixWord ++ tailWord_3894519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894519).length < 2 ^ (prefixWord ++ tailWord_3894519).sum := by decide
  have hdescent : baseEnd_3894519 < baseStart_3894519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894526 : List Nat := [4, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4]
def baseStart_3894526 : Nat := 118140960795 + 3894526 * 2 ^ 59
def prefixEnd_3894526 : Nat := 4983230072969 + 3 ^ 40 * 3894526 * 2
def baseEnd_3894526 : Nat := 1999763759432134882814407

theorem tailTrace_3894526 : CollatzResearch.WordTrace tailWord_3894526 prefixEnd_3894526 1999763759432134882814407 := by
  unfold tailWord_3894526
  simp only [CollatzResearch.WordTrace]
  refine ⟨17755629086100613616504929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94696688459203272621359621 17755629086100613616504929)
  ·
    refine ⟨13316721814575460212378697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17755629086100613616504929 13316721814575460212378697)
    ·
      refine ⟨9987541360931595159284023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13316721814575460212378697 9987541360931595159284023)
      ·
        refine ⟨14981312041397392738926035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9987541360931595159284023 14981312041397392738926035)
        ·
          refine ⟨22471968062096089108389053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14981312041397392738926035 22471968062096089108389053)
          ·
            refine ⟨8426988023286033415645895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22471968062096089108389053 8426988023286033415645895)
            ·
              refine ⟨12640482034929050123468843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8426988023286033415645895 12640482034929050123468843)
              ·
                refine ⟨18960723052393575185203265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12640482034929050123468843 18960723052393575185203265)
                ·
                  refine ⟨14220542289295181388902449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18960723052393575185203265 14220542289295181388902449)
                  ·
                    refine ⟨10665406716971386041676837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14220542289295181388902449 10665406716971386041676837)
                    ·
                      refine ⟨1999763759432134882814407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10665406716971386041676837 1999763759432134882814407)
                      ·
                        rfl

theorem cell23_3894526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_3894526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3894526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3894526 prefixEnd_3894526 := by exact prefixLift 3894526
  have htrace : WordTrace (prefixWord ++ tailWord_3894526) baseStart_3894526 baseEnd_3894526 := by
    simpa [prefixWord, tailWord_3894526, baseEnd_3894526] using wordTrace_append hprefix tailTrace_3894526
  have hstable : (prefixWord ++ tailWord_3894526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894526).length < 2 ^ (prefixWord ++ tailWord_3894526).sum := by decide
  have hdescent : baseEnd_3894526 < baseStart_3894526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894529 : List Nat := [1, 2, 4, 1, 1, 3, 1, 1, 1, 5, 3]
def baseStart_3894529 : Nat := 118140960795 + 3894529 * 2 ^ 59
def prefixEnd_3894529 : Nat := 4983230072969 + 3 ^ 40 * 3894529 * 2
def baseEnd_3894529 : Nat := 1999765299874098371076893

theorem tailTrace_3894529 : CollatzResearch.WordTrace tailWord_3894529 prefixEnd_3894529 1999765299874098371076893 := by
  unfold tailWord_3894529
  simp only [CollatzResearch.WordTrace]
  refine ⟨142045142107794040444398641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94696761405196026962932427 142045142107794040444398641)
  ·
    refine ⟨106533856580845530333298981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142045142107794040444398641 106533856580845530333298981)
    ·
      refine ⟨19975098108908536937493559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106533856580845530333298981 19975098108908536937493559)
      ·
        refine ⟨29962647163362805406240339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19975098108908536937493559 29962647163362805406240339)
        ·
          refine ⟨44943970745044208109360509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29962647163362805406240339 44943970745044208109360509)
          ·
            refine ⟨16853989029391578041010191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44943970745044208109360509 16853989029391578041010191)
            ·
              refine ⟨25280983544087367061515287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16853989029391578041010191 25280983544087367061515287)
              ·
                refine ⟨37921475316131050592272931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25280983544087367061515287 37921475316131050592272931)
                ·
                  refine ⟨56882212974196575888409397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37921475316131050592272931 56882212974196575888409397)
                  ·
                    refine ⟨5332707466330928989538381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56882212974196575888409397 5332707466330928989538381)
                    ·
                      refine ⟨1999765299874098371076893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5332707466330928989538381 1999765299874098371076893)
                      ·
                        rfl

theorem cell23_3894529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_3894529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3894529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3894529 prefixEnd_3894529 := by exact prefixLift 3894529
  have htrace : WordTrace (prefixWord ++ tailWord_3894529) baseStart_3894529 baseEnd_3894529 := by
    simpa [prefixWord, tailWord_3894529, baseEnd_3894529] using wordTrace_append hprefix tailTrace_3894529
  have hstable : (prefixWord ++ tailWord_3894529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894529).length < 2 ^ (prefixWord ++ tailWord_3894529).sum := by decide
  have hdescent : baseEnd_3894529 < baseStart_3894529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894530 : List Nat := [3, 4, 1, 1, 3, 1, 2, 1, 1, 4, 2]
def baseStart_3894530 : Nat := 118140960795 + 3894530 * 2 ^ 59
def prefixEnd_3894530 : Nat := 4983230072969 + 3 ^ 40 * 3894530 * 2
def baseEnd_3894530 : Nat := 1999765813354752867164389

theorem tailTrace_3894530 : CollatzResearch.WordTrace tailWord_3894530 prefixEnd_3894530 1999765813354752867164389 := by
  unfold tailWord_3894530
  simp only [CollatzResearch.WordTrace]
  refine ⟨35511294645197604403796261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94696785720526945076790029 35511294645197604403796261)
  ·
    refine ⟨6658367745974550825711799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35511294645197604403796261 6658367745974550825711799)
    ·
      refine ⟨9987551618961826238567699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6658367745974550825711799 9987551618961826238567699)
      ·
        refine ⟨14981327428442739357851549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9987551618961826238567699 14981327428442739357851549)
        ·
          refine ⟨5617997785666027259194331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14981327428442739357851549 5617997785666027259194331)
          ·
            refine ⟨8426996678499040888791497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5617997785666027259194331 8426996678499040888791497)
            ·
              refine ⟨6320247508874280666593623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8426996678499040888791497 6320247508874280666593623)
              ·
                refine ⟨9480371263311420999890435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6320247508874280666593623 9480371263311420999890435)
                ·
                  refine ⟨14220556894967131499835653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9480371263311420999890435 14220556894967131499835653)
                  ·
                    refine ⟨2666354417806337156219185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14220556894967131499835653 2666354417806337156219185)
                    ·
                      refine ⟨1999765813354752867164389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2666354417806337156219185 1999765813354752867164389)
                      ·
                        rfl

theorem cell23_3894530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_3894530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3894530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3894530 prefixEnd_3894530 := by exact prefixLift 3894530
  have htrace : WordTrace (prefixWord ++ tailWord_3894530) baseStart_3894530 baseEnd_3894530 := by
    simpa [prefixWord, tailWord_3894530, baseEnd_3894530] using wordTrace_append hprefix tailTrace_3894530
  have hstable : (prefixWord ++ tailWord_3894530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894530).length < 2 ^ (prefixWord ++ tailWord_3894530).sum := by decide
  have hdescent : baseEnd_3894530 < baseStart_3894530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894586 : List Nat := [3, 1, 1, 1, 4, 1, 1, 3, 2, 4, 2]
def baseStart_3894586 : Nat := 118140960795 + 3894586 * 2 ^ 59
def prefixEnd_3894586 : Nat := 4983230072969 + 3 ^ 40 * 3894586 * 2
def baseEnd_3894586 : Nat := 1999794568271404648064131

theorem tailTrace_3894586 : CollatzResearch.WordTrace tailWord_3894586 prefixEnd_3894586 1999794568271404648064131 := by
  unfold tailWord_3894586
  simp only [CollatzResearch.WordTrace]
  refine ⟨35511805267146884794805903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94698147379058359452815741 35511805267146884794805903)
  ·
    refine ⟨53267707900720327192208855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35511805267146884794805903 53267707900720327192208855)
    ·
      refine ⟨79901561851080490788313283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53267707900720327192208855 79901561851080490788313283)
      ·
        refine ⟨119852342776620736182469925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79901561851080490788313283 119852342776620736182469925)
        ·
          refine ⟨22472314270616388034213111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119852342776620736182469925 22472314270616388034213111)
          ·
            refine ⟨33708471405924582051319667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22472314270616388034213111 33708471405924582051319667)
            ·
              refine ⟨50562707108886873076979501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33708471405924582051319667 50562707108886873076979501)
              ·
                refine ⟨18961015165832577403867313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50562707108886873076979501 18961015165832577403867313)
                ·
                  refine ⟨14220761374374433052900485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18961015165832577403867313 14220761374374433052900485)
                  ·
                    refine ⟨2666392757695206197418841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14220761374374433052900485 2666392757695206197418841)
                    ·
                      refine ⟨1999794568271404648064131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2666392757695206197418841 1999794568271404648064131)
                      ·
                        rfl

theorem cell23_3894586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 2, 4, 2].length) (baseStart_3894586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3894586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3894586 prefixEnd_3894586 := by exact prefixLift 3894586
  have htrace : WordTrace (prefixWord ++ tailWord_3894586) baseStart_3894586 baseEnd_3894586 := by
    simpa [prefixWord, tailWord_3894586, baseEnd_3894586] using wordTrace_append hprefix tailTrace_3894586
  have hstable : (prefixWord ++ tailWord_3894586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894586).length < 2 ^ (prefixWord ++ tailWord_3894586).sum := by decide
  have hdescent : baseEnd_3894586 < baseStart_3894586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894606 : List Nat := [4, 1, 1, 1, 1, 1, 4, 3, 2, 2, 3]
def baseStart_3894606 : Nat := 118140960795 + 3894606 * 2 ^ 59
def prefixEnd_3894606 : Nat := 4983230072969 + 3 ^ 40 * 3894606 * 2
def baseEnd_3894606 : Nat := 1999804837884494569814039

theorem tailTrace_3894606 : CollatzResearch.WordTrace tailWord_3894606 prefixEnd_3894606 1999804837884494569814039 := by
  unfold tailWord_3894606
  simp only [CollatzResearch.WordTrace]
  refine ⟨17755993816064385324368959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94698633685676721729967781 17755993816064385324368959)
  ·
    refine ⟨26633990724096577986553439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17755993816064385324368959 26633990724096577986553439)
    ·
      refine ⟨39950986086144866979830159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26633990724096577986553439 39950986086144866979830159)
      ·
        refine ⟨59926479129217300469745239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39950986086144866979830159 59926479129217300469745239)
        ·
          refine ⟨89889718693825950704617859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59926479129217300469745239 89889718693825950704617859)
          ·
            refine ⟨134834578040738926056926789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89889718693825950704617859 134834578040738926056926789)
            ·
              refine ⟨25281483382638548635673773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134834578040738926056926789 25281483382638548635673773)
              ·
                refine ⟨9480556268489455738377665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25281483382638548635673773 9480556268489455738377665)
                ·
                  refine ⟨7110417201367091803783249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9480556268489455738377665 7110417201367091803783249)
                  ·
                    refine ⟨5332812901025318852837437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7110417201367091803783249 5332812901025318852837437)
                    ·
                      refine ⟨1999804837884494569814039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5332812901025318852837437 1999804837884494569814039)
                      ·
                        rfl

theorem cell23_3894606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 2, 2, 3].length) (baseStart_3894606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3894606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3894606 prefixEnd_3894606 := by exact prefixLift 3894606
  have htrace : WordTrace (prefixWord ++ tailWord_3894606) baseStart_3894606 baseEnd_3894606 := by
    simpa [prefixWord, tailWord_3894606, baseEnd_3894606] using wordTrace_append hprefix tailTrace_3894606
  have hstable : (prefixWord ++ tailWord_3894606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894606).length < 2 ^ (prefixWord ++ tailWord_3894606).sum := by decide
  have hdescent : baseEnd_3894606 < baseStart_3894606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894626 : List Nat := [3, 3, 2, 1, 1, 1, 2, 4, 6]
def baseStart_3894626 : Nat := 118140960795 + 3894626 * 2 ^ 59
def prefixEnd_3894626 : Nat := 4983230072969 + 3 ^ 40 * 3894626 * 2
def baseEnd_3894626 : Nat := 222201678610842721284883

theorem tailTrace_3894626 : CollatzResearch.WordTrace tailWord_3894626 prefixEnd_3894626 222201678610842721284883 := by
  unfold tailWord_3894626
  simp only [CollatzResearch.WordTrace]
  refine ⟨35512169997110656502669933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94699119992295084007119821 35512169997110656502669933)
  ·
    refine ⟨13317063748916496188501225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35512169997110656502669933 13317063748916496188501225)
    ·
      refine ⟨9987797811687372141375919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13317063748916496188501225 9987797811687372141375919)
      ·
        refine ⟨14981696717531058212063879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9987797811687372141375919 14981696717531058212063879)
        ·
          refine ⟨22472545076296587318095819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14981696717531058212063879 22472545076296587318095819)
          ·
            refine ⟨33708817614444880977143729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22472545076296587318095819 33708817614444880977143729)
            ·
              refine ⟨25281613210833660732857797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33708817614444880977143729 25281613210833660732857797)
              ·
                refine ⟨4740302477031311387410837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25281613210833660732857797 4740302477031311387410837)
                ·
                  refine ⟨222201678610842721284883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4740302477031311387410837 222201678610842721284883)
                  ·
                    rfl

theorem cell23_3894626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 4, 6].length) (baseStart_3894626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3894626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3894626 prefixEnd_3894626 := by exact prefixLift 3894626
  have htrace : WordTrace (prefixWord ++ tailWord_3894626) baseStart_3894626 baseEnd_3894626 := by
    simpa [prefixWord, tailWord_3894626, baseEnd_3894626] using wordTrace_append hprefix tailTrace_3894626
  have hstable : (prefixWord ++ tailWord_3894626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894626).length < 2 ^ (prefixWord ++ tailWord_3894626).sum := by decide
  have hdescent : baseEnd_3894626 < baseStart_3894626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894639 : List Nat := [1, 1, 2, 1, 3, 1, 4, 2, 3, 5]
def baseStart_3894639 : Nat := 118140960795 + 3894639 * 2 ^ 59
def prefixEnd_3894639 : Nat := 4983230072969 + 3 ^ 40 * 3894639 * 2
def baseEnd_3894639 : Nat := 666607260915364313567129

theorem tailTrace_3894639 : CollatzResearch.WordTrace tailWord_3894639 prefixEnd_3894639 666607260915364313567129 := by
  unfold tailWord_3894639
  simp only [CollatzResearch.WordTrace]
  refine ⟨142049154137395529230902971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94699436091597019487268647 142049154137395529230902971)
  ·
    refine ⟨213073731206093293846354457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142049154137395529230902971 213073731206093293846354457)
    ·
      refine ⟨159805298404569970384765843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213073731206093293846354457 159805298404569970384765843)
      ·
        refine ⟨239707947606854955577148765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159805298404569970384765843 239707947606854955577148765)
        ·
          refine ⟨89890480352570608341430787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239707947606854955577148765 89890480352570608341430787)
          ·
            refine ⟨134835720528855912512146181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89890480352570608341430787 134835720528855912512146181)
            ·
              refine ⟨25281697599160483596027409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134835720528855912512146181 25281697599160483596027409)
              ·
                refine ⟨18961273199370362697020557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25281697599160483596027409 18961273199370362697020557)
                ·
                  refine ⟨7110477449763886011382709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18961273199370362697020557 7110477449763886011382709)
                  ·
                    refine ⟨666607260915364313567129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7110477449763886011382709 666607260915364313567129)
                    ·
                      rfl

theorem cell23_3894639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 3, 5].length) (baseStart_3894639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3894639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3894639 prefixEnd_3894639 := by exact prefixLift 3894639
  have htrace : WordTrace (prefixWord ++ tailWord_3894639) baseStart_3894639 baseEnd_3894639 := by
    simpa [prefixWord, tailWord_3894639, baseEnd_3894639] using wordTrace_append hprefix tailTrace_3894639
  have hstable : (prefixWord ++ tailWord_3894639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894639).length < 2 ^ (prefixWord ++ tailWord_3894639).sum := by decide
  have hdescent : baseEnd_3894639 < baseStart_3894639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894663 : List Nat := [1, 1, 4, 2, 2, 2, 1, 3, 2, 3, 2]
def baseStart_3894663 : Nat := 118140960795 + 3894663 * 2 ^ 59
def prefixEnd_3894663 : Nat := 4983230072969 + 3 ^ 40 * 3894663 * 2
def baseEnd_3894663 : Nat := 1999834106281800846801277

theorem tailTrace_3894663 : CollatzResearch.WordTrace tailWord_3894663 prefixEnd_3894663 1999834106281800846801277 := by
  unfold tailWord_3894663
  simp only [CollatzResearch.WordTrace]
  refine ⟨142050029489308581329776643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94700019659539054219851095 142050029489308581329776643)
  ·
    refine ⟨213075044233962871994664965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142050029489308581329776643 213075044233962871994664965)
    ·
      refine ⟨39951570793868038498999681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213075044233962871994664965 39951570793868038498999681)
      ·
        refine ⟨29963678095401028874249761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39951570793868038498999681 29963678095401028874249761)
        ·
          refine ⟨22472758571550771655687321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29963678095401028874249761 22472758571550771655687321)
          ·
            refine ⟨16854568928663078741765491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22472758571550771655687321 16854568928663078741765491)
            ·
              refine ⟨25281853392994618112648237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16854568928663078741765491 25281853392994618112648237)
              ·
                refine ⟨9480695022372981792243089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25281853392994618112648237 9480695022372981792243089)
                ·
                  refine ⟨7110521266779736344182317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9480695022372981792243089 7110521266779736344182317)
                  ·
                    refine ⟨2666445475042401129068369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7110521266779736344182317 2666445475042401129068369)
                    ·
                      refine ⟨1999834106281800846801277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2666445475042401129068369 1999834106281800846801277)
                      ·
                        rfl

theorem cell23_3894663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 2, 3, 2].length) (baseStart_3894663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3894663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3894663 prefixEnd_3894663 := by exact prefixLift 3894663
  have htrace : WordTrace (prefixWord ++ tailWord_3894663) baseStart_3894663 baseEnd_3894663 := by
    simpa [prefixWord, tailWord_3894663, baseEnd_3894663] using wordTrace_append hprefix tailTrace_3894663
  have hstable : (prefixWord ++ tailWord_3894663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894663).length < 2 ^ (prefixWord ++ tailWord_3894663).sum := by decide
  have hdescent : baseEnd_3894663 < baseStart_3894663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894687 : List Nat := [1, 1, 2, 5, 1, 2, 4, 2, 1, 1, 3]
def baseStart_3894687 : Nat := 118140960795 + 3894687 * 2 ^ 59
def prefixEnd_3894687 : Nat := 4983230072969 + 3 ^ 40 * 3894687 * 2
def baseEnd_3894687 : Nat := 1999846429817508752901167

theorem tailTrace_3894687 : CollatzResearch.WordTrace tailWord_3894687 prefixEnd_3894687 1999846429817508752901167 := by
  unfold tailWord_3894687
  simp only [CollatzResearch.WordTrace]
  refine ⟨142050904841221633428650315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94700603227481088952433543 142050904841221633428650315)
  ·
    refine ⟨213076357261832450142975473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142050904841221633428650315 213076357261832450142975473)
    ·
      refine ⟨159807267946374337607231605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213076357261832450142975473 159807267946374337607231605)
      ·
        refine ⟨14981931369972594150677963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 159807267946374337607231605 14981931369972594150677963)
        ·
          refine ⟨22472897054958891226016945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14981931369972594150677963 22472897054958891226016945)
          ·
            refine ⟨16854672791219168419512709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22472897054958891226016945 16854672791219168419512709)
            ·
              refine ⟨3160251148353594078658633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16854672791219168419512709 3160251148353594078658633)
              ·
                refine ⟨2370188361265195558993975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3160251148353594078658633 2370188361265195558993975)
                ·
                  refine ⟨3555282541897793338490963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2370188361265195558993975 3555282541897793338490963)
                  ·
                    refine ⟨5332923812846690007736445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3555282541897793338490963 5332923812846690007736445)
                    ·
                      refine ⟨1999846429817508752901167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5332923812846690007736445 1999846429817508752901167)
                      ·
                        rfl

theorem cell23_3894687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_3894687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3894687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3894687 prefixEnd_3894687 := by exact prefixLift 3894687
  have htrace : WordTrace (prefixWord ++ tailWord_3894687) baseStart_3894687 baseEnd_3894687 := by
    simpa [prefixWord, tailWord_3894687, baseEnd_3894687] using wordTrace_append hprefix tailTrace_3894687
  have hstable : (prefixWord ++ tailWord_3894687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894687).length < 2 ^ (prefixWord ++ tailWord_3894687).sum := by decide
  have hdescent : baseEnd_3894687 < baseStart_3894687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894727 : List Nat := [1, 1, 4, 1, 1, 3, 4, 3, 1, 2, 2]
def baseStart_3894727 : Nat := 118140960795 + 3894727 * 2 ^ 59
def prefixEnd_3894727 : Nat := 4983230072969 + 3 ^ 40 * 3894727 * 2
def baseEnd_3894727 : Nat := 1999866969043688596400983

theorem tailTrace_3894727 : CollatzResearch.WordTrace tailWord_3894727 prefixEnd_3894727 1999866969043688596400983 := by
  unfold tailWord_3894727
  simp only [CollatzResearch.WordTrace]
  refine ⟨142052363761076720260106435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94701575840717813506737623 142052363761076720260106435)
  ·
    refine ⟨213078545641615080390159653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142052363761076720260106435 213078545641615080390159653)
    ·
      refine ⟨39952227307802827573154935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213078545641615080390159653 39952227307802827573154935)
      ·
        refine ⟨59928340961704241359732403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39952227307802827573154935 59928340961704241359732403)
        ·
          refine ⟨89892511442556362039598605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59928340961704241359732403 89892511442556362039598605)
          ·
            refine ⟨33709691790958635764849477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89892511442556362039598605 33709691790958635764849477)
            ·
              refine ⟨6320567210804744205909277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33709691790958635764849477 6320567210804744205909277)
              ·
                refine ⟨2370212704051779077215979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6320567210804744205909277 2370212704051779077215979)
                ·
                  refine ⟨3555319056077668615823969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2370212704051779077215979 3555319056077668615823969)
                  ·
                    refine ⟨2666489292058251461867977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3555319056077668615823969 2666489292058251461867977)
                    ·
                      refine ⟨1999866969043688596400983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2666489292058251461867977 1999866969043688596400983)
                      ·
                        rfl

theorem cell23_3894727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 3, 1, 2, 2].length) (baseStart_3894727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3894727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3894727 prefixEnd_3894727 := by exact prefixLift 3894727
  have htrace : WordTrace (prefixWord ++ tailWord_3894727) baseStart_3894727 baseEnd_3894727 := by
    simpa [prefixWord, tailWord_3894727, baseEnd_3894727] using wordTrace_append hprefix tailTrace_3894727
  have hstable : (prefixWord ++ tailWord_3894727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894727).length < 2 ^ (prefixWord ++ tailWord_3894727).sum := by decide
  have hdescent : baseEnd_3894727 < baseStart_3894727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894730 : List Nat := [3, 1, 2, 1, 2, 3, 4, 1, 1, 2, 3]
def baseStart_3894730 : Nat := 118140960795 + 3894730 * 2 ^ 59
def prefixEnd_3894730 : Nat := 4983230072969 + 3 ^ 40 * 3894730 * 2
def baseEnd_3894730 : Nat := 1999868509485652084663469

theorem tailTrace_3894730 : CollatzResearch.WordTrace tailWord_3894730 prefixEnd_3894730 1999868509485652084663469 := by
  unfold tailWord_3894730
  simp only [CollatzResearch.WordTrace]
  refine ⟨35513118295016462943116411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94701648786710567848310429 35513118295016462943116411)
  ·
    refine ⟨53269677442524694414674617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35513118295016462943116411 53269677442524694414674617)
    ·
      refine ⟨39952258081893520811005963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53269677442524694414674617 39952258081893520811005963)
      ·
        refine ⟨59928387122840281216508945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39952258081893520811005963 59928387122840281216508945)
        ·
          refine ⟨44946290342130210912381709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59928387122840281216508945 44946290342130210912381709)
          ·
            refine ⟨16854858878298829092143141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44946290342130210912381709 16854858878298829092143141)
            ·
              refine ⟨3160286039681030454776839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16854858878298829092143141 3160286039681030454776839)
              ·
                refine ⟨4740429059521545682165259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3160286039681030454776839 4740429059521545682165259)
                ·
                  refine ⟨7110643589282318523247889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4740429059521545682165259 7110643589282318523247889)
                  ·
                    refine ⟨5332982691961738892435917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7110643589282318523247889 5332982691961738892435917)
                    ·
                      refine ⟨1999868509485652084663469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5332982691961738892435917 1999868509485652084663469)
                      ·
                        rfl

theorem cell23_3894730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 1, 1, 2, 3].length) (baseStart_3894730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3894730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3894730 prefixEnd_3894730 := by exact prefixLift 3894730
  have htrace : WordTrace (prefixWord ++ tailWord_3894730) baseStart_3894730 baseEnd_3894730 := by
    simpa [prefixWord, tailWord_3894730, baseEnd_3894730] using wordTrace_append hprefix tailTrace_3894730
  have hstable : (prefixWord ++ tailWord_3894730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894730).length < 2 ^ (prefixWord ++ tailWord_3894730).sum := by decide
  have hdescent : baseEnd_3894730 < baseStart_3894730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894773 : List Nat := [1, 3, 5, 1, 1, 1, 1, 1, 2, 2, 5]
def baseStart_3894773 : Nat := 118140960795 + 3894773 * 2 ^ 59
def prefixEnd_3894773 : Nat := 4983230072969 + 3 ^ 40 * 3894773 * 2
def baseEnd_3894773 : Nat := 1999890589153795416425771

theorem tailTrace_3894773 : CollatzResearch.WordTrace tailWord_3894773 prefixEnd_3894773 1999890589153795416425771 := by
  unfold tailWord_3894773
  simp only [CollatzResearch.WordTrace]
  refine ⟨142054041518910070116280973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94702694345940046744187315 142054041518910070116280973)
  ·
    refine ⟨53270265569591276293605365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142054041518910070116280973 53270265569591276293605365)
    ·
      refine ⟨4994087397149182152525503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53270265569591276293605365 4994087397149182152525503)
      ·
        refine ⟨7491131095723773228788255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4994087397149182152525503 7491131095723773228788255)
        ·
          refine ⟨11236696643585659843182383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7491131095723773228788255 11236696643585659843182383)
          ·
            refine ⟨16855044965378489764773575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11236696643585659843182383 16855044965378489764773575)
            ·
              refine ⟨25282567448067734647160363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16855044965378489764773575 25282567448067734647160363)
              ·
                refine ⟨37923851172101601970740545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25282567448067734647160363 37923851172101601970740545)
                ·
                  refine ⟨28442888379076201478055409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37923851172101601970740545 28442888379076201478055409)
                  ·
                    refine ⟨21332166284307151108541557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28442888379076201478055409 21332166284307151108541557)
                    ·
                      refine ⟨1999890589153795416425771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21332166284307151108541557 1999890589153795416425771)
                      ·
                        rfl

theorem cell23_3894773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_3894773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3894773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3894773 prefixEnd_3894773 := by exact prefixLift 3894773
  have htrace : WordTrace (prefixWord ++ tailWord_3894773) baseStart_3894773 baseEnd_3894773 := by
    simpa [prefixWord, tailWord_3894773, baseEnd_3894773] using wordTrace_append hprefix tailTrace_3894773
  have hstable : (prefixWord ++ tailWord_3894773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894773).length < 2 ^ (prefixWord ++ tailWord_3894773).sum := by decide
  have hdescent : baseEnd_3894773 < baseStart_3894773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894817 : List Nat := [1, 2, 3, 2, 2, 3, 1, 3, 2, 2, 2]
def baseStart_3894817 : Nat := 118140960795 + 3894817 * 2 ^ 59
def prefixEnd_3894817 : Nat := 4983230072969 + 3 ^ 40 * 3894817 * 2
def baseEnd_3894817 : Nat := 1999913182302593244275569

theorem tailTrace_3894817 : CollatzResearch.WordTrace tailWord_3894817 prefixEnd_3894817 1999913182302593244275569 := by
  unfold tailWord_3894817
  simp only [CollatzResearch.WordTrace]
  refine ⟨142055646330750665630882705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94703764220500443753921803 142055646330750665630882705)
  ·
    refine ⟨106541734748062999223162029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142055646330750665630882705 106541734748062999223162029)
    ·
      refine ⟨39953150530523624708685761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106541734748062999223162029 39953150530523624708685761)
      ·
        refine ⟨29964862897892718531514321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39953150530523624708685761 29964862897892718531514321)
        ·
          refine ⟨22473647173419538898635741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29964862897892718531514321 22473647173419538898635741)
          ·
            refine ⟨8427617690032327086988403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22473647173419538898635741 8427617690032327086988403)
            ·
              refine ⟨12641426535048490630482605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8427617690032327086988403 12641426535048490630482605)
              ·
                refine ⟨4740534950643183986430977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12641426535048490630482605 4740534950643183986430977)
                ·
                  refine ⟨3555401212982387989823233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4740534950643183986430977 3555401212982387989823233)
                  ·
                    refine ⟨2666550909736790992367425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3555401212982387989823233 2666550909736790992367425)
                    ·
                      refine ⟨1999913182302593244275569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2666550909736790992367425 1999913182302593244275569)
                      ·
                        rfl

theorem cell23_3894817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 3, 2, 2, 2].length) (baseStart_3894817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3894817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3894817 prefixEnd_3894817 := by exact prefixLift 3894817
  have htrace : WordTrace (prefixWord ++ tailWord_3894817) baseStart_3894817 baseEnd_3894817 := by
    simpa [prefixWord, tailWord_3894817, baseEnd_3894817] using wordTrace_append hprefix tailTrace_3894817
  have hstable : (prefixWord ++ tailWord_3894817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894817).length < 2 ^ (prefixWord ++ tailWord_3894817).sum := by decide
  have hdescent : baseEnd_3894817 < baseStart_3894817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894856 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 5, 3, 4]
def baseStart_3894856 : Nat := 118140960795 + 3894856 * 2 ^ 59
def prefixEnd_3894856 : Nat := 4983230072969 + 3 ^ 40 * 3894856 * 2
def baseEnd_3894856 : Nat := 1999933208048118591687889

theorem tailTrace_3894856 : CollatzResearch.WordTrace tailWord_3894856 prefixEnd_3894856 1999933208048118591687889 := by
  unfold tailWord_3894856
  simp only [CollatzResearch.WordTrace]
  refine ⟨71028534388804687645776211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94704712518406250194368281 71028534388804687645776211)
  ·
    refine ⟨106542801583207031468664317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71028534388804687645776211 106542801583207031468664317)
    ·
      refine ⟨39953550593702636800749119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106542801583207031468664317 39953550593702636800749119)
      ·
        refine ⟨59930325890553955201123679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39953550593702636800749119 59930325890553955201123679)
        ·
          refine ⟨89895488835830932801685519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59930325890553955201123679 89895488835830932801685519)
          ·
            refine ⟨134843233253746399202528279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89895488835830932801685519 134843233253746399202528279)
            ·
              refine ⟨202264849880619598803792419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134843233253746399202528279 202264849880619598803792419)
              ·
                refine ⟨303397274820929398205688629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202264849880619598803792419 303397274820929398205688629)
                ·
                  refine ⟨28443494514462131081783309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 303397274820929398205688629 28443494514462131081783309)
                  ·
                    refine ⟨10666310442923299155668741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28443494514462131081783309 10666310442923299155668741)
                    ·
                      refine ⟨1999933208048118591687889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10666310442923299155668741 1999933208048118591687889)
                      ·
                        rfl

theorem cell23_3894856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_3894856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3894856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3894856 prefixEnd_3894856 := by exact prefixLift 3894856
  have htrace : WordTrace (prefixWord ++ tailWord_3894856) baseStart_3894856 baseEnd_3894856 := by
    simpa [prefixWord, tailWord_3894856, baseEnd_3894856] using wordTrace_append hprefix tailTrace_3894856
  have hstable : (prefixWord ++ tailWord_3894856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894856).length < 2 ^ (prefixWord ++ tailWord_3894856).sum := by decide
  have hdescent : baseEnd_3894856 < baseStart_3894856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894883 : List Nat := [1, 1, 1, 5, 1, 3, 1, 1, 5, 4]
def baseStart_3894883 : Nat := 118140960795 + 3894883 * 2 ^ 59
def prefixEnd_3894883 : Nat := 4983230072969 + 3 ^ 40 * 3894883 * 2
def baseEnd_3894883 : Nat := 666649024008596662016755

theorem tailTrace_3894883 : CollatzResearch.WordTrace tailWord_3894883 prefixEnd_3894883 666649024008596662016755 := by
  unfold tailWord_3894883
  simp only [CollatzResearch.WordTrace]
  refine ⟨142058053548511558902785303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94705369032341039268523535 142058053548511558902785303)
  ·
    refine ⟨213087080322767338354177955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142058053548511558902785303 213087080322767338354177955)
    ·
      refine ⟨319630620484151007531266933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213087080322767338354177955 319630620484151007531266933)
      ·
        refine ⟨29965370670389156956056275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 319630620484151007531266933 29965370670389156956056275)
        ·
          refine ⟨44948056005583735434084413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29965370670389156956056275 44948056005583735434084413)
          ·
            refine ⟨16855521002093900787781655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44948056005583735434084413 16855521002093900787781655)
            ·
              refine ⟨25283281503140851181672483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16855521002093900787781655 25283281503140851181672483)
              ·
                refine ⟨37924922254711276772508725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25283281503140851181672483 37924922254711276772508725)
                ·
                  refine ⟨3555461461379182197422693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37924922254711276772508725 3555461461379182197422693)
                  ·
                    refine ⟨666649024008596662016755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3555461461379182197422693 666649024008596662016755)
                    ·
                      rfl

theorem cell23_3894883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 5, 4].length) (baseStart_3894883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3894883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3894883 prefixEnd_3894883 := by exact prefixLift 3894883
  have htrace : WordTrace (prefixWord ++ tailWord_3894883) baseStart_3894883 baseEnd_3894883 := by
    simpa [prefixWord, tailWord_3894883, baseEnd_3894883] using wordTrace_append hprefix tailTrace_3894883
  have hstable : (prefixWord ++ tailWord_3894883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894883).length < 2 ^ (prefixWord ++ tailWord_3894883).sum := by decide
  have hdescent : baseEnd_3894883 < baseStart_3894883 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894890 : List Nat := [3, 1, 3, 2, 1, 2, 3, 1, 2, 1, 4]
def baseStart_3894890 : Nat := 118140960795 + 3894890 * 2 ^ 59
def prefixEnd_3894890 : Nat := 4983230072969 + 3 ^ 40 * 3894890 * 2
def baseEnd_3894890 : Nat := 1999950666390371458662733

theorem tailTrace_3894890 : CollatzResearch.WordTrace tailWord_3894890 prefixEnd_3894890 1999950666390371458662733 := by
  unfold tailWord_3894890
  simp only [CollatzResearch.WordTrace]
  refine ⟨35514577214871549774572531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94705539239657466065526749 35514577214871549774572531)
  ·
    refine ⟨53271865822307324661858797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35514577214871549774572531 53271865822307324661858797)
    ·
      refine ⟨19976949683365246748197049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53271865822307324661858797 19976949683365246748197049)
      ·
        refine ⟨14982712262523935061147787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19976949683365246748197049 14982712262523935061147787)
        ·
          refine ⟨22474068393785902591721681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14982712262523935061147787 22474068393785902591721681)
          ·
            refine ⟨16855551295339426943791261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22474068393785902591721681 16855551295339426943791261)
            ·
              refine ⟨6320831735752285103921723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16855551295339426943791261 6320831735752285103921723)
              ·
                refine ⟨9481247603628427655882585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6320831735752285103921723 9481247603628427655882585)
                ·
                  refine ⟨7110935702721320741911939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9481247603628427655882585 7110935702721320741911939)
                  ·
                    refine ⟨10666403554081981112867909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7110935702721320741911939 10666403554081981112867909)
                    ·
                      refine ⟨1999950666390371458662733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10666403554081981112867909 1999950666390371458662733)
                      ·
                        rfl

theorem cell23_3894890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_3894890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3894890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3894890 prefixEnd_3894890 := by exact prefixLift 3894890
  have htrace : WordTrace (prefixWord ++ tailWord_3894890) baseStart_3894890 baseEnd_3894890 := by
    simpa [prefixWord, tailWord_3894890, baseEnd_3894890] using wordTrace_append hprefix tailTrace_3894890
  have hstable : (prefixWord ++ tailWord_3894890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894890).length < 2 ^ (prefixWord ++ tailWord_3894890).sum := by decide
  have hdescent : baseEnd_3894890 < baseStart_3894890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894913 : List Nat := [1, 2, 4, 2, 1, 3, 1, 1, 8]
def baseStart_3894913 : Nat := 118140960795 + 3894913 * 2 ^ 59
def prefixEnd_3894913 : Nat := 4983230072969 + 3 ^ 40 * 3894913 * 2
def baseEnd_3894913 : Nat := 222218052938380540963903

theorem tailTrace_3894913 : CollatzResearch.WordTrace tailWord_3894913 prefixEnd_3894913 222218052938380540963903 := by
  unfold tailWord_3894913
  simp only [CollatzResearch.WordTrace]
  refine ⟨142059147738402874026377393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94706098492268582684251595 142059147738402874026377393)
  ·
    refine ⟨106544360803802155519783045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142059147738402874026377393 106544360803802155519783045)
    ·
      refine ⟨19977067650712904159959321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106544360803802155519783045 19977067650712904159959321)
      ·
        refine ⟨14982800738034678119969491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19977067650712904159959321 14982800738034678119969491)
        ·
          refine ⟨22474201107052017179954237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14982800738034678119969491 22474201107052017179954237)
          ·
            refine ⟨8427825415144506442482839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22474201107052017179954237 8427825415144506442482839)
            ·
              refine ⟨12641738122716759663724259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8427825415144506442482839 12641738122716759663724259)
              ·
                refine ⟨18962607184075139495586389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12641738122716759663724259 18962607184075139495586389)
                ·
                  refine ⟨222218052938380540963903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18962607184075139495586389 222218052938380540963903)
                  ·
                    rfl

theorem cell23_3894913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 8].length) (baseStart_3894913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3894913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3894913 prefixEnd_3894913 := by exact prefixLift 3894913
  have htrace : WordTrace (prefixWord ++ tailWord_3894913) baseStart_3894913 baseEnd_3894913 := by
    simpa [prefixWord, tailWord_3894913, baseEnd_3894913] using wordTrace_append hprefix tailTrace_3894913
  have hstable : (prefixWord ++ tailWord_3894913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894913).length < 2 ^ (prefixWord ++ tailWord_3894913).sum := by decide
  have hdescent : baseEnd_3894913 < baseStart_3894913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894967 : List Nat := [1, 1, 3, 1, 5, 2, 1, 2, 2, 3, 2]
def baseStart_3894967 : Nat := 118140960795 + 3894967 * 2 ^ 59
def prefixEnd_3894967 : Nat := 4983230072969 + 3 ^ 40 * 3894967 * 2
def baseEnd_3894967 : Nat := 1999990204400767657399879

theorem tailTrace_3894967 : CollatzResearch.WordTrace tailWord_3894967 prefixEnd_3894967 1999990204400767657399879 := by
  unfold tailWord_3894967
  simp only [CollatzResearch.WordTrace]
  refine ⟨142061117280207241248843155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94707411520138160832562103 142061117280207241248843155)
  ·
    refine ⟨213091675920310861873264733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142061117280207241248843155 213091675920310861873264733)
    ·
      refine ⟨79909378470116573202474275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213091675920310861873264733 79909378470116573202474275)
      ·
        refine ⟨119864067705174859803711413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79909378470116573202474275 119864067705174859803711413)
        ·
          refine ⟨11237256347360143106597945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119864067705174859803711413 11237256347360143106597945)
          ·
            refine ⟨8427942260520107329948459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11237256347360143106597945 8427942260520107329948459)
            ·
              refine ⟨12641913390780160994922689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8427942260520107329948459 12641913390780160994922689)
              ·
                refine ⟨9481435043085120746192017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12641913390780160994922689 9481435043085120746192017)
                ·
                  refine ⟨7111076282313840559644013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9481435043085120746192017 7111076282313840559644013)
                  ·
                    refine ⟨2666653605867690209866505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7111076282313840559644013 2666653605867690209866505)
                    ·
                      refine ⟨1999990204400767657399879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2666653605867690209866505 1999990204400767657399879)
                      ·
                        rfl

theorem cell23_3894967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 2, 3, 2].length) (baseStart_3894967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3894967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3894967 prefixEnd_3894967 := by exact prefixLift 3894967
  have htrace : WordTrace (prefixWord ++ tailWord_3894967) baseStart_3894967 baseEnd_3894967 := by
    simpa [prefixWord, tailWord_3894967, baseEnd_3894967] using wordTrace_append hprefix tailTrace_3894967
  have hstable : (prefixWord ++ tailWord_3894967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894967).length < 2 ^ (prefixWord ++ tailWord_3894967).sum := by decide
  have hdescent : baseEnd_3894967 < baseStart_3894967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894974 : List Nat := [4, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3]
def baseStart_3894974 : Nat := 118140960795 + 3894974 * 2 ^ 59
def prefixEnd_3894974 : Nat := 4983230072969 + 3 ^ 40 * 3894974 * 2
def baseEnd_3894974 : Nat := 1999993798765349130012347

theorem tailTrace_3894974 : CollatzResearch.WordTrace tailWord_3894974 prefixEnd_3894974 1999993798765349130012347 := by
  unfold tailWord_3894974
  simp only [CollatzResearch.WordTrace]
  refine ⟨17757671573897735180543497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94707581727454587629565317 17757671573897735180543497)
  ·
    refine ⟨13318253680423301385407623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17757671573897735180543497 13318253680423301385407623)
    ·
      refine ⟨19977380520634952078111435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13318253680423301385407623 19977380520634952078111435)
      ·
        refine ⟨29966070780952428117167153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19977380520634952078111435 29966070780952428117167153)
        ·
          refine ⟨22474553085714321087875365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29966070780952428117167153 22474553085714321087875365)
          ·
            refine ⟨4213978703571435203976631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22474553085714321087875365 4213978703571435203976631)
            ·
              refine ⟨6320968055357152805964947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4213978703571435203976631 6320968055357152805964947)
              ·
                refine ⟨9481452083035729208947421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6320968055357152805964947 9481452083035729208947421)
                ·
                  refine ⟨3555544531138398453355283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9481452083035729208947421 3555544531138398453355283)
                  ·
                    refine ⟨5333316796707597680032925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3555544531138398453355283 5333316796707597680032925)
                    ·
                      refine ⟨1999993798765349130012347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5333316796707597680032925 1999993798765349130012347)
                      ·
                        rfl

theorem cell23_3894974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_3894974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3894974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3894974 prefixEnd_3894974 := by exact prefixLift 3894974
  have htrace : WordTrace (prefixWord ++ tailWord_3894974) baseStart_3894974 baseEnd_3894974 := by
    simpa [prefixWord, tailWord_3894974, baseEnd_3894974] using wordTrace_append hprefix tailTrace_3894974
  have hstable : (prefixWord ++ tailWord_3894974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894974).length < 2 ^ (prefixWord ++ tailWord_3894974).sum := by decide
  have hdescent : baseEnd_3894974 < baseStart_3894974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894980 : List Nat := [2, 3, 3, 1, 1, 1, 2, 2, 3, 1, 4]
def baseStart_3894980 : Nat := 118140960795 + 3894980 * 2 ^ 59
def prefixEnd_3894980 : Nat := 4983230072969 + 3 ^ 40 * 3894980 * 2
def baseEnd_3894980 : Nat := 1999996879649276106537319

theorem tailTrace_3894980 : CollatzResearch.WordTrace tailWord_3894980 prefixEnd_3894980 1999996879649276106537319 := by
  unfold tailWord_3894980
  simp only [CollatzResearch.WordTrace]
  refine ⟨71030795714580072234533197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94707727619440096312710929 71030795714580072234533197)
  ·
    refine ⟨26636548392967527087949949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71030795714580072234533197 26636548392967527087949949)
    ·
      refine ⟨9988705647362822657981231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26636548392967527087949949 9988705647362822657981231)
      ·
        refine ⟨14983058471044233986971847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9988705647362822657981231 14983058471044233986971847)
        ·
          refine ⟨22474587706566350980457771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14983058471044233986971847 22474587706566350980457771)
          ·
            refine ⟨33711881559849526470686657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22474587706566350980457771 33711881559849526470686657)
            ·
              refine ⟨25283911169887144853014993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33711881559849526470686657 25283911169887144853014993)
              ·
                refine ⟨18962933377415358639761245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25283911169887144853014993 18962933377415358639761245)
                ·
                  refine ⟨7111100016530759489910467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18962933377415358639761245 7111100016530759489910467)
                  ·
                    refine ⟨10666650024796139234865701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7111100016530759489910467 10666650024796139234865701)
                    ·
                      refine ⟨1999996879649276106537319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10666650024796139234865701 1999996879649276106537319)
                      ·
                        rfl

theorem cell23_3894980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_3894980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3894980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3894980 prefixEnd_3894980 := by exact prefixLift 3894980
  have htrace : WordTrace (prefixWord ++ tailWord_3894980) baseStart_3894980 baseEnd_3894980 := by
    simpa [prefixWord, tailWord_3894980, baseEnd_3894980] using wordTrace_append hprefix tailTrace_3894980
  have hstable : (prefixWord ++ tailWord_3894980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894980).length < 2 ^ (prefixWord ++ tailWord_3894980).sum := by decide
  have hdescent : baseEnd_3894980 < baseStart_3894980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894983 : List Nat := [1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 5]
def baseStart_3894983 : Nat := 118140960795 + 3894983 * 2 ^ 59
def prefixEnd_3894983 : Nat := 4983230072969 + 3 ^ 40 * 3894983 * 2
def baseEnd_3894983 : Nat := 1999998420091239594799805

theorem tailTrace_3894983 : CollatzResearch.WordTrace tailWord_3894983 prefixEnd_3894983 1999998420091239594799805 := by
  unfold tailWord_3894983
  simp only [CollatzResearch.WordTrace]
  refine ⟨142061700848149275981425603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94707800565432850654283735 142061700848149275981425603)
  ·
    refine ⟨213092551272223913972138405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142061700848149275981425603 213092551272223913972138405)
    ·
      refine ⟨39954853363541983869775951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213092551272223913972138405 39954853363541983869775951)
      ·
        refine ⟨59932280045312975804663927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39954853363541983869775951 59932280045312975804663927)
        ·
          refine ⟨89898420067969463706995891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59932280045312975804663927 89898420067969463706995891)
          ·
            refine ⟨134847630101954195560493837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89898420067969463706995891 134847630101954195560493837)
            ·
              refine ⟨50567861288232823335185189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134847630101954195560493837 50567861288232823335185189)
              ·
                refine ⟨9481473991543654375347223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50567861288232823335185189 9481473991543654375347223)
                ·
                  refine ⟨14222210987315481563020835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9481473991543654375347223 14222210987315481563020835)
                  ·
                    refine ⟨21333316480973222344531253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14222210987315481563020835 21333316480973222344531253)
                    ·
                      refine ⟨1999998420091239594799805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21333316480973222344531253 1999998420091239594799805)
                      ·
                        rfl

theorem cell23_3894983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_3894983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3894983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3894983 prefixEnd_3894983 := by exact prefixLift 3894983
  have htrace : WordTrace (prefixWord ++ tailWord_3894983) baseStart_3894983 baseEnd_3894983 := by
    simpa [prefixWord, tailWord_3894983, baseEnd_3894983] using wordTrace_append hprefix tailTrace_3894983
  have hstable : (prefixWord ++ tailWord_3894983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894983).length < 2 ^ (prefixWord ++ tailWord_3894983).sum := by decide
  have hdescent : baseEnd_3894983 < baseStart_3894983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894993 : List Nat := [1, 2, 2, 1, 2, 4, 2, 1, 1, 1, 6]
def baseStart_3894993 : Nat := 118140960795 + 3894993 * 2 ^ 59
def prefixEnd_3894993 : Nat := 4983230072969 + 3 ^ 40 * 3894993 * 2
def baseEnd_3894993 : Nat := 2000003554897784555674759

theorem tailTrace_3894993 : CollatzResearch.WordTrace tailWord_3894993 prefixEnd_3894993 2000003554897784555674759 := by
  unfold tailWord_3894993
  simp only [CollatzResearch.WordTrace]
  refine ⟨142062065578113047689289633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94708043718742031792859755 142062065578113047689289633)
  ·
    refine ⟨106546549183584785766967225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142062065578113047689289633 106546549183584785766967225)
    ·
      refine ⟨79909911887688589325225419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106546549183584785766967225 79909911887688589325225419)
      ·
        refine ⟨119864867831532883987838129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79909911887688589325225419 119864867831532883987838129)
        ·
          refine ⟨89898650873649662990878597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119864867831532883987838129 89898650873649662990878597)
          ·
            refine ⟨16855997038809311810789737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89898650873649662990878597 16855997038809311810789737)
            ·
              refine ⟨12641997779106983858092303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16855997038809311810789737 12641997779106983858092303)
              ·
                refine ⟨18962996668660475787138455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12641997779106983858092303 18962996668660475787138455)
                ·
                  refine ⟨28444495002990713680707683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18962996668660475787138455 28444495002990713680707683)
                  ·
                    refine ⟨42666742504486070521061525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28444495002990713680707683 42666742504486070521061525)
                    ·
                      refine ⟨2000003554897784555674759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42666742504486070521061525 2000003554897784555674759)
                      ·
                        rfl

theorem cell23_3894993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 1, 6].length) (baseStart_3894993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3894993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3894993 prefixEnd_3894993 := by exact prefixLift 3894993
  have htrace : WordTrace (prefixWord ++ tailWord_3894993) baseStart_3894993 baseEnd_3894993 := by
    simpa [prefixWord, tailWord_3894993, baseEnd_3894993] using wordTrace_append hprefix tailTrace_3894993
  have hstable : (prefixWord ++ tailWord_3894993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894993).length < 2 ^ (prefixWord ++ tailWord_3894993).sum := by decide
  have hdescent : baseEnd_3894993 < baseStart_3894993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895000 : List Nat := [2, 1, 2, 2, 3, 1, 3, 1, 3, 2, 3]
def baseStart_3895000 : Nat := 118140960795 + 3895000 * 2 ^ 59
def prefixEnd_3895000 : Nat := 4983230072969 + 3 ^ 40 * 3895000 * 2
def baseEnd_3895000 : Nat := 2000007149262366028287227

theorem tailTrace_3895000 : CollatzResearch.WordTrace tailWord_3895000 prefixEnd_3895000 2000007149262366028287227 := by
  unfold tailWord_3895000
  simp only [CollatzResearch.WordTrace]
  refine ⟨71031160444543843942397227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94708213926058458589862969 71031160444543843942397227)
  ·
    refine ⟨106546740666815765913595841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71031160444543843942397227 106546740666815765913595841)
    ·
      refine ⟨79910055500111824435196881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106546740666815765913595841 79910055500111824435196881)
      ·
        refine ⟨59932541625083868326397661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79910055500111824435196881 59932541625083868326397661)
        ·
          refine ⟨22474703109406450622399123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59932541625083868326397661 22474703109406450622399123)
          ·
            refine ⟨33712054664109675933598685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22474703109406450622399123 33712054664109675933598685)
            ·
              refine ⟨12642020499041128475099507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33712054664109675933598685 12642020499041128475099507)
              ·
                refine ⟨18963030748561692712649261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12642020499041128475099507 18963030748561692712649261)
                ·
                  refine ⟨7111136530710634767243473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18963030748561692712649261 7111136530710634767243473)
                  ·
                    refine ⟨5333352398032976075432605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7111136530710634767243473 5333352398032976075432605)
                    ·
                      refine ⟨2000007149262366028287227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5333352398032976075432605 2000007149262366028287227)
                      ·
                        rfl

theorem cell23_3895000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 3, 2, 3].length) (baseStart_3895000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3895000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3895000 prefixEnd_3895000 := by exact prefixLift 3895000
  have htrace : WordTrace (prefixWord ++ tailWord_3895000) baseStart_3895000 baseEnd_3895000 := by
    simpa [prefixWord, tailWord_3895000, baseEnd_3895000] using wordTrace_append hprefix tailTrace_3895000
  have hstable : (prefixWord ++ tailWord_3895000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895000).length < 2 ^ (prefixWord ++ tailWord_3895000).sum := by decide
  have hdescent : baseEnd_3895000 < baseStart_3895000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895031 : List Nat := [1, 1, 3, 1, 1, 1, 8, 2, 1, 2, 2]
def baseStart_3895031 : Nat := 118140960795 + 3895031 * 2 ^ 59
def prefixEnd_3895031 : Nat := 4983230072969 + 3 ^ 40 * 3895031 * 2
def baseEnd_3895031 : Nat := 2000023067162655406999585

theorem tailTrace_3895031 : CollatzResearch.WordTrace tailWord_3895031 prefixEnd_3895031 2000023067162655406999585 := by
  unfold tailWord_3895031
  simp only [CollatzResearch.WordTrace]
  refine ⟨142063451551975380179172947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94708967701316920119448631 142063451551975380179172947)
  ·
    refine ⟨213095177327963070268759421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142063451551975380179172947 213095177327963070268759421)
    ·
      refine ⟨79910691497986151350784783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213095177327963070268759421 79910691497986151350784783)
      ·
        refine ⟨119866037246979227026177175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79910691497986151350784783 119866037246979227026177175)
        ·
          refine ⟨179799055870468840539265763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119866037246979227026177175 179799055870468840539265763)
          ·
            refine ⟨269698583805703260808898645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179799055870468840539265763 269698583805703260808898645)
            ·
              refine ⟨3160530278973085087604281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 269698583805703260808898645 3160530278973085087604281)
              ·
                refine ⟨2370397709229813815703211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3160530278973085087604281 2370397709229813815703211)
                ·
                  refine ⟨3555596563844720723554817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2370397709229813815703211 3555596563844720723554817)
                  ·
                    refine ⟨2666697422883540542666113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3555596563844720723554817 2666697422883540542666113)
                    ·
                      refine ⟨2000023067162655406999585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2666697422883540542666113 2000023067162655406999585)
                      ·
                        rfl

theorem cell23_3895031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 2, 1, 2, 2].length) (baseStart_3895031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3895031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3895031 prefixEnd_3895031 := by exact prefixLift 3895031
  have htrace : WordTrace (prefixWord ++ tailWord_3895031) baseStart_3895031 baseEnd_3895031 := by
    simpa [prefixWord, tailWord_3895031, baseEnd_3895031] using wordTrace_append hprefix tailTrace_3895031
  have hstable : (prefixWord ++ tailWord_3895031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895031).length < 2 ^ (prefixWord ++ tailWord_3895031).sum := by decide
  have hdescent : baseEnd_3895031 < baseStart_3895031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895057 : List Nat := [1, 2, 2, 1, 1, 3, 1, 6, 1, 3, 2]
def baseStart_3895057 : Nat := 118140960795 + 3895057 * 2 ^ 59
def prefixEnd_3895057 : Nat := 4983230072969 + 3 ^ 40 * 3895057 * 2
def baseEnd_3895057 : Nat := 2000036417659672305274465

theorem tailTrace_3895057 : CollatzResearch.WordTrace tailWord_3895057 prefixEnd_3895057 2000036417659672305274465 := by
  unfold tailWord_3895057
  simp only [CollatzResearch.WordTrace]
  refine ⟨142064399849881186619619425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94709599899920791079746283 142064399849881186619619425)
  ·
    refine ⟨106548299887410889964714569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142064399849881186619619425 106548299887410889964714569)
    ·
      refine ⟨79911224915558167473535927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106548299887410889964714569 79911224915558167473535927)
      ·
        refine ⟨119866837373337251210303891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79911224915558167473535927 119866837373337251210303891)
        ·
          refine ⟨179800256060005876815455837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119866837373337251210303891 179800256060005876815455837)
          ·
            refine ⟨67425096022502203805795939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179800256060005876815455837 67425096022502203805795939)
            ·
              refine ⟨101137644033753305708693909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67425096022502203805795939 101137644033753305708693909)
              ·
                refine ⟨4740827064082186205095027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 101137644033753305708693909 4740827064082186205095027)
                ·
                  refine ⟨7111240596123279307642541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4740827064082186205095027 7111240596123279307642541)
                  ·
                    refine ⟨2666715223546229740365953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7111240596123279307642541 2666715223546229740365953)
                    ·
                      refine ⟨2000036417659672305274465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2666715223546229740365953 2000036417659672305274465)
                      ·
                        rfl

theorem cell23_3895057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 3, 2].length) (baseStart_3895057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3895057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3895057 prefixEnd_3895057 := by exact prefixLift 3895057
  have htrace : WordTrace (prefixWord ++ tailWord_3895057) baseStart_3895057 baseEnd_3895057 := by
    simpa [prefixWord, tailWord_3895057, baseEnd_3895057] using wordTrace_append hprefix tailTrace_3895057
  have hstable : (prefixWord ++ tailWord_3895057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895057).length < 2 ^ (prefixWord ++ tailWord_3895057).sum := by decide
  have hdescent : baseEnd_3895057 < baseStart_3895057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895074 : List Nat := [3, 3, 1, 1, 2, 1, 3, 3, 1, 3, 2]
def baseStart_3895074 : Nat := 118140960795 + 3895074 * 2 ^ 59
def prefixEnd_3895074 : Nat := 4983230072969 + 3 ^ 40 * 3895074 * 2
def baseEnd_3895074 : Nat := 2000045146830798738761887

theorem tailTrace_3895074 : CollatzResearch.WordTrace tailWord_3895074 prefixEnd_3895074 2000045146830798738761887 := by
  unfold tailWord_3895074
  simp only [CollatzResearch.WordTrace]
  refine ⟨35516254972704899630747069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94710013260546399015325517 35516254972704899630747069)
  ·
    refine ⟨13318595614764337361530151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35516254972704899630747069 13318595614764337361530151)
    ·
      refine ⟨19977893422146506042295227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13318595614764337361530151 19977893422146506042295227)
      ·
        refine ⟨29966840133219759063442841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19977893422146506042295227 29966840133219759063442841)
        ·
          refine ⟨22475130099914819297582131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29966840133219759063442841 22475130099914819297582131)
          ·
            refine ⟨33712695149872228946373197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22475130099914819297582131 33712695149872228946373197)
            ·
              refine ⟨12642260681202085854889949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33712695149872228946373197 12642260681202085854889949)
              ·
                refine ⟨4740847755450782195583731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12642260681202085854889949 4740847755450782195583731)
                ·
                  refine ⟨7111271633176173293375597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4740847755450782195583731 7111271633176173293375597)
                  ·
                    refine ⟨2666726862441064985015849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7111271633176173293375597 2666726862441064985015849)
                    ·
                      refine ⟨2000045146830798738761887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2666726862441064985015849 2000045146830798738761887)
                      ·
                        rfl

theorem cell23_3895074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 3, 1, 3, 2].length) (baseStart_3895074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3895074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3895074 prefixEnd_3895074 := by exact prefixLift 3895074
  have htrace : WordTrace (prefixWord ++ tailWord_3895074) baseStart_3895074 baseEnd_3895074 := by
    simpa [prefixWord, tailWord_3895074, baseEnd_3895074] using wordTrace_append hprefix tailTrace_3895074
  have hstable : (prefixWord ++ tailWord_3895074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895074).length < 2 ^ (prefixWord ++ tailWord_3895074).sum := by decide
  have hdescent : baseEnd_3895074 < baseStart_3895074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895080 : List Nat := [2, 1, 5, 1, 1, 2, 1, 2, 2, 6]
def baseStart_3895080 : Nat := 118140960795 + 3895080 * 2 ^ 59
def prefixEnd_3895080 : Nat := 4983230072969 + 3 ^ 40 * 3895080 * 2
def baseEnd_3895080 : Nat := 666682742571575238428953

theorem tailTrace_3895080 : CollatzResearch.WordTrace tailWord_3895080 prefixEnd_3895080 666682742571575238428953 := by
  unfold tailWord_3895080
  simp only [CollatzResearch.WordTrace]
  refine ⟨71032619364398930773853347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94710159152531907698471129 71032619364398930773853347)
  ·
    refine ⟨106548929046598396160780021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71032619364398930773853347 106548929046598396160780021)
    ·
      refine ⟨9988962098118599640073127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106548929046598396160780021 9988962098118599640073127)
      ·
        refine ⟨14983443147177899460109691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9988962098118599640073127 14983443147177899460109691)
        ·
          refine ⟨22475164720766849190164537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14983443147177899460109691 22475164720766849190164537)
          ·
            refine ⟨16856373540575136892623403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22475164720766849190164537 16856373540575136892623403)
            ·
              refine ⟨25284560310862705338935105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16856373540575136892623403 25284560310862705338935105)
              ·
                refine ⟨18963420233147029004201329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25284560310862705338935105 18963420233147029004201329)
                ·
                  refine ⟨14222565174860271753150997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18963420233147029004201329 14222565174860271753150997)
                  ·
                    refine ⟨666682742571575238428953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14222565174860271753150997 666682742571575238428953)
                    ·
                      rfl

theorem cell23_3895080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_3895080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3895080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3895080 prefixEnd_3895080 := by exact prefixLift 3895080
  have htrace : WordTrace (prefixWord ++ tailWord_3895080) baseStart_3895080 baseEnd_3895080 := by
    simpa [prefixWord, tailWord_3895080, baseEnd_3895080] using wordTrace_append hprefix tailTrace_3895080
  have hstable : (prefixWord ++ tailWord_3895080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895080).length < 2 ^ (prefixWord ++ tailWord_3895080).sum := by decide
  have hdescent : baseEnd_3895080 < baseStart_3895080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895087 : List Nat := [1, 1, 2, 1, 2, 1, 2, 5, 4, 2, 2]
def baseStart_3895087 : Nat := 118140960795 + 3895087 * 2 ^ 59
def prefixEnd_3895087 : Nat := 4983230072969 + 3 ^ 40 * 3895087 * 2
def baseEnd_3895087 : Nat := 2000051822079307187899327

theorem tailTrace_3895087 : CollatzResearch.WordTrace tailWord_3895087 prefixEnd_3895087 2000051822079307187899327 := by
  unfold tailWord_3895087
  simp only [CollatzResearch.WordTrace]
  refine ⟨142065494039772501743211515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94710329359848334495474343 142065494039772501743211515)
  ·
    refine ⟨213098241059658752614817273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142065494039772501743211515 213098241059658752614817273)
    ·
      refine ⟨159823680794744064461112955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213098241059658752614817273 159823680794744064461112955)
      ·
        refine ⟨239735521192116096691669433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159823680794744064461112955 239735521192116096691669433)
        ·
          refine ⟨179801640894087072518752075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239735521192116096691669433 179801640894087072518752075)
          ·
            refine ⟨269702461341130608778128113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179801640894087072518752075 269702461341130608778128113)
            ·
              refine ⟨202276846005847956583596085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269702461341130608778128113 202276846005847956583596085)
              ·
                refine ⟨18963454313048245929712133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 202276846005847956583596085 18963454313048245929712133)
                ·
                  refine ⟨3555647683696546111821025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18963454313048245929712133 3555647683696546111821025)
                  ·
                    refine ⟨2666735762772409583865769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3555647683696546111821025 2666735762772409583865769)
                    ·
                      refine ⟨2000051822079307187899327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2666735762772409583865769 2000051822079307187899327)
                      ·
                        rfl

theorem cell23_3895087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 4, 2, 2].length) (baseStart_3895087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3895087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3895087 prefixEnd_3895087 := by exact prefixLift 3895087
  have htrace : WordTrace (prefixWord ++ tailWord_3895087) baseStart_3895087 baseEnd_3895087 := by
    simpa [prefixWord, tailWord_3895087, baseEnd_3895087] using wordTrace_append hprefix tailTrace_3895087
  have hstable : (prefixWord ++ tailWord_3895087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895087).length < 2 ^ (prefixWord ++ tailWord_3895087).sum := by decide
  have hdescent : baseEnd_3895087 < baseStart_3895087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895100 : List Nat := [2, 2, 2, 2, 1, 1, 4, 1, 2, 2, 4]
def baseStart_3895100 : Nat := 118140960795 + 3895100 * 2 ^ 59
def prefixEnd_3895100 : Nat := 4983230072969 + 3 ^ 40 * 3895100 * 2
def baseEnd_3895100 : Nat := 2000058497327815637036767

theorem tailTrace_3895100 : CollatzResearch.WordTrace tailWord_3895100 prefixEnd_3895100 2000058497327815637036767 := by
  unfold tailWord_3895100
  simp only [CollatzResearch.WordTrace]
  refine ⟨71032984094362702481717377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94710645459150269975623169 71032984094362702481717377)
  ·
    refine ⟨53274738070772026861288033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71032984094362702481717377 53274738070772026861288033)
    ·
      refine ⟨39956053553079020145966025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53274738070772026861288033 39956053553079020145966025)
      ·
        refine ⟨29967040164809265109474519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39956053553079020145966025 29967040164809265109474519)
        ·
          refine ⟨44950560247213897664211779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29967040164809265109474519 44950560247213897664211779)
          ·
            refine ⟨67425840370820846496317669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44950560247213897664211779 67425840370820846496317669)
            ·
              refine ⟨12642345069528908718059563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67425840370820846496317669 12642345069528908718059563)
              ·
                refine ⟨18963517604293363077089345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12642345069528908718059563 18963517604293363077089345)
                ·
                  refine ⟨14222638203220022307817009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18963517604293363077089345 14222638203220022307817009)
                  ·
                    refine ⟨10666978652415016730862757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14222638203220022307817009 10666978652415016730862757)
                    ·
                      refine ⟨2000058497327815637036767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10666978652415016730862757 2000058497327815637036767)
                      ·
                        rfl

theorem cell23_3895100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_3895100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3895100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3895100 prefixEnd_3895100 := by exact prefixLift 3895100
  have htrace : WordTrace (prefixWord ++ tailWord_3895100) baseStart_3895100 baseEnd_3895100 := by
    simpa [prefixWord, tailWord_3895100, baseEnd_3895100] using wordTrace_append hprefix tailTrace_3895100
  have hstable : (prefixWord ++ tailWord_3895100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895100).length < 2 ^ (prefixWord ++ tailWord_3895100).sum := by decide
  have hdescent : baseEnd_3895100 < baseStart_3895100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895144 : List Nat := [2, 1, 4, 2, 1, 1, 5, 2, 5]
def baseStart_3895144 : Nat := 118140960795 + 3895144 * 2 ^ 59
def prefixEnd_3895144 : Nat := 4983230072969 + 3 ^ 40 * 3895144 * 2
def baseEnd_3895144 : Nat := 222231232275179273876285

theorem tailTrace_3895144 : CollatzResearch.WordTrace tailWord_3895144 prefixEnd_3895144 222231232275179273876285 := by
  unfold tailWord_3895144
  simp only [CollatzResearch.WordTrace]
  refine ⟨71033786500283000239018243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94711715333710666985357657 71033786500283000239018243)
  ·
    refine ⟨106550679750424500358527365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71033786500283000239018243 106550679750424500358527365)
    ·
      refine ⟨19978252453204593817223881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106550679750424500358527365 19978252453204593817223881)
      ·
        refine ⟨14983689339903445362917911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19978252453204593817223881 14983689339903445362917911)
        ·
          refine ⟨22475534009855168044376867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14983689339903445362917911 22475534009855168044376867)
          ·
            refine ⟨33713301014782752066565301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22475534009855168044376867 33713301014782752066565301)
            ·
              refine ⟨3160621970135883006240497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33713301014782752066565301 3160621970135883006240497)
              ·
                refine ⟨2370466477601912254680373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3160621970135883006240497 2370466477601912254680373)
                ·
                  refine ⟨222231232275179273876285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2370466477601912254680373 222231232275179273876285)
                  ·
                    rfl

theorem cell23_3895144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 2, 5].length) (baseStart_3895144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3895144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3895144 prefixEnd_3895144 := by exact prefixLift 3895144
  have htrace : WordTrace (prefixWord ++ tailWord_3895144) baseStart_3895144 baseEnd_3895144 := by
    simpa [prefixWord, tailWord_3895144, baseEnd_3895144] using wordTrace_append hprefix tailTrace_3895144
  have hstable : (prefixWord ++ tailWord_3895144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895144).length < 2 ^ (prefixWord ++ tailWord_3895144).sum := by decide
  have hdescent : baseEnd_3895144 < baseStart_3895144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895177 : List Nat := [1, 2, 1, 1, 5, 1, 4, 1, 2, 1, 4]
def baseStart_3895177 : Nat := 118140960795 + 3895177 * 2 ^ 59
def prefixEnd_3895177 : Nat := 4983230072969 + 3 ^ 40 * 3895177 * 2
def baseEnd_3895177 : Nat := 2000098035338211835773913

theorem tailTrace_3895177 : CollatzResearch.WordTrace tailWord_3895177 prefixEnd_3895177 2000098035338211835773913 := by
  unfold tailWord_3895177
  simp only [CollatzResearch.WordTrace]
  refine ⟨142068776609446447113987785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94712517739630964742658523 142068776609446447113987785)
  ·
    refine ⟨106551582457084835335490839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142068776609446447113987785 106551582457084835335490839)
    ·
      refine ⟨159827373685627253003236259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106551582457084835335490839 159827373685627253003236259)
      ·
        refine ⟨239741060528440879504854389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159827373685627253003236259 239741060528440879504854389)
        ·
          refine ⟨22475724424541332453580099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 239741060528440879504854389 22475724424541332453580099)
          ·
            refine ⟨33713586636811998680370149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22475724424541332453580099 33713586636811998680370149)
            ·
              refine ⟨6321297494402249752569403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33713586636811998680370149 6321297494402249752569403)
              ·
                refine ⟨9481946241603374628854105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6321297494402249752569403 9481946241603374628854105)
                ·
                  refine ⟨7111459681202530971640579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9481946241603374628854105 7111459681202530971640579)
                  ·
                    refine ⟨10667189521803796457460869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7111459681202530971640579 10667189521803796457460869)
                    ·
                      refine ⟨2000098035338211835773913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10667189521803796457460869 2000098035338211835773913)
                      ·
                        rfl

theorem cell23_3895177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 2, 1, 4].length) (baseStart_3895177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3895177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3895177 prefixEnd_3895177 := by exact prefixLift 3895177
  have htrace : WordTrace (prefixWord ++ tailWord_3895177) baseStart_3895177 baseEnd_3895177 := by
    simpa [prefixWord, tailWord_3895177, baseEnd_3895177] using wordTrace_append hprefix tailTrace_3895177
  have hstable : (prefixWord ++ tailWord_3895177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895177).length < 2 ^ (prefixWord ++ tailWord_3895177).sum := by decide
  have hdescent : baseEnd_3895177 < baseStart_3895177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895217 : List Nat := [1, 2, 2, 4, 2, 1, 2, 3, 6]
def baseStart_3895217 : Nat := 118140960795 + 3895217 * 2 ^ 59
def prefixEnd_3895217 : Nat := 4983230072969 + 3 ^ 40 * 3895217 * 2
def baseEnd_3895217 : Nat := 222235397173821297697081

theorem tailTrace_3895217 : CollatzResearch.WordTrace tailWord_3895217 prefixEnd_3895217 222235397173821297697081 := by
  unfold tailWord_3895217
  simp only [CollatzResearch.WordTrace]
  refine ⟨142070235529301533945443905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94713490352867689296962603 142070235529301533945443905)
  ·
    refine ⟨106552676646976150459082929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142070235529301533945443905 106552676646976150459082929)
    ·
      refine ⟨79914507485232112844312197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106552676646976150459082929 79914507485232112844312197)
      ·
        refine ⟨14983970153481021158308537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79914507485232112844312197 14983970153481021158308537)
        ·
          refine ⟨11237977615110765868731403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14983970153481021158308537 11237977615110765868731403)
          ·
            refine ⟨16856966422666148803097105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11237977615110765868731403 16856966422666148803097105)
            ·
              refine ⟨12642724816999611602322829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16856966422666148803097105 12642724816999611602322829)
              ·
                refine ⟨4741021806374854350871061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12642724816999611602322829 4741021806374854350871061)
                ·
                  refine ⟨222235397173821297697081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4741021806374854350871061 222235397173821297697081)
                  ·
                    rfl

theorem cell23_3895217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 3, 6].length) (baseStart_3895217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3895217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3895217 prefixEnd_3895217 := by exact prefixLift 3895217
  have htrace : WordTrace (prefixWord ++ tailWord_3895217) baseStart_3895217 baseEnd_3895217 := by
    simpa [prefixWord, tailWord_3895217, baseEnd_3895217] using wordTrace_append hprefix tailTrace_3895217
  have hstable : (prefixWord ++ tailWord_3895217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895217).length < 2 ^ (prefixWord ++ tailWord_3895217).sum := by decide
  have hdescent : baseEnd_3895217 < baseStart_3895217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895227 : List Nat := [1, 1, 1, 1, 1, 2, 2, 5, 5, 1, 3]
def baseStart_3895227 : Nat := 118140960795 + 3895227 * 2 ^ 59
def prefixEnd_3895227 : Nat := 4983230072969 + 3 ^ 40 * 3895227 * 2
def baseEnd_3895227 : Nat := 2000123709370936640148683

theorem tailTrace_3895227 : CollatzResearch.WordTrace tailWord_3895227 prefixEnd_3895227 2000123709370936640148683 := by
  unfold tailWord_3895227
  simp only [CollatzResearch.WordTrace]
  refine ⟨142070600259265305653307935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94713733506176870435538623 142070600259265305653307935)
  ·
    refine ⟨213105900388897958479961903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142070600259265305653307935 213105900388897958479961903)
    ·
      refine ⟨319658850583346937719942855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213105900388897958479961903 319658850583346937719942855)
      ·
        refine ⟨479488275875020406579914283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319658850583346937719942855 479488275875020406579914283)
        ·
          refine ⟨719232413812530609869871425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 479488275875020406579914283 719232413812530609869871425)
          ·
            refine ⟨539424310359397957402403569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 719232413812530609869871425 539424310359397957402403569)
            ·
              refine ⟨404568232769548468051802677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 539424310359397957402403569 404568232769548468051802677)
              ·
                refine ⟨37928271822145168879856501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 404568232769548468051802677 37928271822145168879856501)
                ·
                  refine ⟨3555775483326109582486547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37928271822145168879856501 3555775483326109582486547)
                  ·
                    refine ⟨5333663224989164373729821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3555775483326109582486547 5333663224989164373729821)
                    ·
                      refine ⟨2000123709370936640148683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5333663224989164373729821 2000123709370936640148683)
                      ·
                        rfl

theorem cell23_3895227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5, 1, 3].length) (baseStart_3895227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3895227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3895227 prefixEnd_3895227 := by exact prefixLift 3895227
  have htrace : WordTrace (prefixWord ++ tailWord_3895227) baseStart_3895227 baseEnd_3895227 := by
    simpa [prefixWord, tailWord_3895227, baseEnd_3895227] using wordTrace_append hprefix tailTrace_3895227
  have hstable : (prefixWord ++ tailWord_3895227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895227).length < 2 ^ (prefixWord ++ tailWord_3895227).sum := by decide
  have hdescent : baseEnd_3895227 < baseStart_3895227 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895228 : List Nat := [2, 2, 2, 5, 2, 1, 1, 1, 2, 1, 4]
def baseStart_3895228 : Nat := 118140960795 + 3895228 * 2 ^ 59
def prefixEnd_3895228 : Nat := 4983230072969 + 3 ^ 40 * 3895228 * 2
def baseEnd_3895228 : Nat := 2000124222851591136236179

theorem tailTrace_3895228 : CollatzResearch.WordTrace tailWord_3895228 prefixEnd_3895228 2000124222851591136236179 := by
  unfold tailWord_3895228
  simp only [CollatzResearch.WordTrace]
  refine ⟨71035318366130841412047169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94713757821507788549396225 71035318366130841412047169)
  ·
    refine ⟨53276488774598131059035377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71035318366130841412047169 53276488774598131059035377)
    ·
      refine ⟨39957366580948598294276533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53276488774598131059035377 39957366580948598294276533)
      ·
        refine ⟨3746003116963931090088425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39957366580948598294276533 3746003116963931090088425)
        ·
          refine ⟨2809502337722948317566319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3746003116963931090088425 2809502337722948317566319)
          ·
            refine ⟨4214253506584422476349479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2809502337722948317566319 4214253506584422476349479)
            ·
              refine ⟨6321380259876633714524219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4214253506584422476349479 6321380259876633714524219)
              ·
                refine ⟨9482070389814950571786329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6321380259876633714524219 9482070389814950571786329)
                ·
                  refine ⟨7111552792361212928839747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9482070389814950571786329 7111552792361212928839747)
                  ·
                    refine ⟨10667329188541819393259621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7111552792361212928839747 10667329188541819393259621)
                    ·
                      refine ⟨2000124222851591136236179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10667329188541819393259621 2000124222851591136236179)
                      ·
                        rfl

theorem cell23_3895228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_3895228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3895228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3895228 prefixEnd_3895228 := by exact prefixLift 3895228
  have htrace : WordTrace (prefixWord ++ tailWord_3895228) baseStart_3895228 baseEnd_3895228 := by
    simpa [prefixWord, tailWord_3895228, baseEnd_3895228] using wordTrace_append hprefix tailTrace_3895228
  have hstable : (prefixWord ++ tailWord_3895228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895228).length < 2 ^ (prefixWord ++ tailWord_3895228).sum := by decide
  have hdescent : baseEnd_3895228 < baseStart_3895228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895247 : List Nat := [1, 1, 2, 1, 1, 5, 3, 3, 1, 5]
def baseStart_3895247 : Nat := 118140960795 + 3895247 * 2 ^ 59
def prefixEnd_3895247 : Nat := 4983230072969 + 3 ^ 40 * 3895247 * 2
def baseEnd_3895247 : Nat := 666711326328008853966197

theorem tailTrace_3895247 : CollatzResearch.WordTrace tailWord_3895247 prefixEnd_3895247 666711326328008853966197 := by
  unfold tailWord_3895247
  simp only [CollatzResearch.WordTrace]
  refine ⟨142071329719192849069035995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94714219812795232712690663 142071329719192849069035995)
  ·
    refine ⟨213106994578789273603553993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142071329719192849069035995 213106994578789273603553993)
    ·
      refine ⟨159830245934091955202665495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213106994578789273603553993 159830245934091955202665495)
      ·
        refine ⟨239745368901137932803998243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159830245934091955202665495 239745368901137932803998243)
        ·
          refine ⟨359618053351706899205997365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239745368901137932803998243 359618053351706899205997365)
          ·
            refine ⟨33714192501722521800562253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 359618053351706899205997365 33714192501722521800562253)
            ·
              refine ⟨12642822188145945675210845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33714192501722521800562253 12642822188145945675210845)
              ·
                refine ⟨4741058320554729628204067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12642822188145945675210845 4741058320554729628204067)
                ·
                  refine ⟨7111587480832094442306101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4741058320554729628204067 7111587480832094442306101)
                  ·
                    refine ⟨666711326328008853966197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7111587480832094442306101 666711326328008853966197)
                    ·
                      rfl

theorem cell23_3895247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 3, 1, 5].length) (baseStart_3895247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3895247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3895247 prefixEnd_3895247 := by exact prefixLift 3895247
  have htrace : WordTrace (prefixWord ++ tailWord_3895247) baseStart_3895247 baseEnd_3895247 := by
    simpa [prefixWord, tailWord_3895247, baseEnd_3895247] using wordTrace_append hprefix tailTrace_3895247
  have hstable : (prefixWord ++ tailWord_3895247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895247).length < 2 ^ (prefixWord ++ tailWord_3895247).sum := by decide
  have hdescent : baseEnd_3895247 < baseStart_3895247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895297 : List Nat := [1, 2, 4, 1, 2, 1, 2, 1, 3, 2, 4]
def baseStart_3895297 : Nat := 118140960795 + 3895297 * 2 ^ 59
def prefixEnd_3895297 : Nat := 4983230072969 + 3 ^ 40 * 3895297 * 2
def baseEnd_3895297 : Nat := 2000159653016751366273361

theorem tailTrace_3895297 : CollatzResearch.WordTrace tailWord_3895297 prefixEnd_3895297 2000159653016751366273361 := by
  unfold tailWord_3895297
  simp only [CollatzResearch.WordTrace]
  refine ⟨142073153369011707608356145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94715435579341138405570763 142073153369011707608356145)
  ·
    refine ⟨106554865026758780706267109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142073153369011707608356145 106554865026758780706267109)
    ·
      refine ⟨19979037192517271382425083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106554865026758780706267109 19979037192517271382425083)
      ·
        refine ⟨29968555788775907073637625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19979037192517271382425083 29968555788775907073637625)
        ·
          refine ⟨22476416841581930305228219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29968555788775907073637625 22476416841581930305228219)
          ·
            refine ⟨33714625262372895457842329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22476416841581930305228219 33714625262372895457842329)
            ·
              refine ⟨25285968946779671593381747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33714625262372895457842329 25285968946779671593381747)
              ·
                refine ⟨37928953420169507390072621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25285968946779671593381747 37928953420169507390072621)
                ·
                  refine ⟨14223357532563565271277233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37928953420169507390072621 14223357532563565271277233)
                  ·
                    refine ⟨10667518149422673953457925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14223357532563565271277233 10667518149422673953457925)
                    ·
                      refine ⟨2000159653016751366273361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10667518149422673953457925 2000159653016751366273361)
                      ·
                        rfl

theorem cell23_3895297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_3895297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3895297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3895297 prefixEnd_3895297 := by exact prefixLift 3895297
  have htrace : WordTrace (prefixWord ++ tailWord_3895297) baseStart_3895297 baseEnd_3895297 := by
    simpa [prefixWord, tailWord_3895297, baseEnd_3895297] using wordTrace_append hprefix tailTrace_3895297
  have hstable : (prefixWord ++ tailWord_3895297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895297).length < 2 ^ (prefixWord ++ tailWord_3895297).sum := by decide
  have hdescent : baseEnd_3895297 < baseStart_3895297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895304 : List Nat := [2, 1, 3, 2, 1, 2, 1, 5, 1, 2, 3]
def baseStart_3895304 : Nat := 118140960795 + 3895304 * 2 ^ 59
def prefixEnd_3895304 : Nat := 4983230072969 + 3 ^ 40 * 3895304 * 2
def baseEnd_3895304 : Nat := 2000163247381332838885829

theorem tailTrace_3895304 : CollatzResearch.WordTrace tailWord_3895304 prefixEnd_3895304 2000163247381332838885829 := by
  unfold tailWord_3895304
  simp only [CollatzResearch.WordTrace]
  refine ⟨71036704339993173901930483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94715605786657565202573977 71036704339993173901930483)
  ·
    refine ⟨106555056509989760852895725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71036704339993173901930483 106555056509989760852895725)
    ·
      refine ⟨39958146191246160319835897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106555056509989760852895725 39958146191246160319835897)
      ·
        refine ⟨29968609643434620239876923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39958146191246160319835897 29968609643434620239876923)
        ·
          refine ⟨44952914465151930359815385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29968609643434620239876923 44952914465151930359815385)
          ·
            refine ⟨33714685848863947769861539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44952914465151930359815385 33714685848863947769861539)
            ·
              refine ⟨50572028773295921654792309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33714685848863947769861539 50572028773295921654792309)
              ·
                refine ⟨4741127697496492655136779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50572028773295921654792309 4741127697496492655136779)
                ·
                  refine ⟨7111691546244738982705169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4741127697496492655136779 7111691546244738982705169)
                  ·
                    refine ⟨5333768659683554237028877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7111691546244738982705169 5333768659683554237028877)
                    ·
                      refine ⟨2000163247381332838885829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5333768659683554237028877 2000163247381332838885829)
                      ·
                        rfl

theorem cell23_3895304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_3895304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3895304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3895304 prefixEnd_3895304 := by exact prefixLift 3895304
  have htrace : WordTrace (prefixWord ++ tailWord_3895304) baseStart_3895304 baseEnd_3895304 := by
    simpa [prefixWord, tailWord_3895304, baseEnd_3895304] using wordTrace_append hprefix tailTrace_3895304
  have hstable : (prefixWord ++ tailWord_3895304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895304).length < 2 ^ (prefixWord ++ tailWord_3895304).sum := by decide
  have hdescent : baseEnd_3895304 < baseStart_3895304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895335 : List Nat := [1, 1, 7, 1, 3, 1, 1, 2, 1, 1, 4]
def baseStart_3895335 : Nat := 118140960795 + 3895335 * 2 ^ 59
def prefixEnd_3895335 : Nat := 4983230072969 + 3 ^ 40 * 3895335 * 2
def baseEnd_3895335 : Nat := 2000179165281622217598187

theorem tailTrace_3895335 : CollatzResearch.WordTrace tailWord_3895335 prefixEnd_3895335 2000179165281622217598187 := by
  unfold tailWord_3895335
  simp only [CollatzResearch.WordTrace]
  refine ⟨142074539342874040098239459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94716359561916026732159639 142074539342874040098239459)
  ·
    refine ⟨213111809014311060147359189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142074539342874040098239459 213111809014311060147359189)
    ·
      refine ⟨4994808023772915472203731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 213111809014311060147359189 4994808023772915472203731)
      ·
        refine ⟨7492212035659373208305597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4994808023772915472203731 7492212035659373208305597)
        ·
          refine ⟨2809579513372264953114599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7492212035659373208305597 2809579513372264953114599)
          ·
            refine ⟨4214369270058397429671899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2809579513372264953114599 4214369270058397429671899)
            ·
              refine ⟨6321553905087596144507849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4214369270058397429671899 6321553905087596144507849)
              ·
                refine ⟨4741165428815697108380887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6321553905087596144507849 4741165428815697108380887)
                ·
                  refine ⟨7111748143223545662571331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4741165428815697108380887 7111748143223545662571331)
                  ·
                    refine ⟨10667622214835318493856997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7111748143223545662571331 10667622214835318493856997)
                    ·
                      refine ⟨2000179165281622217598187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10667622214835318493856997 2000179165281622217598187)
                      ·
                        rfl

theorem cell23_3895335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_3895335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3895335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3895335 prefixEnd_3895335 := by exact prefixLift 3895335
  have htrace : WordTrace (prefixWord ++ tailWord_3895335) baseStart_3895335 baseEnd_3895335 := by
    simpa [prefixWord, tailWord_3895335, baseEnd_3895335] using wordTrace_append hprefix tailTrace_3895335
  have hstable : (prefixWord ++ tailWord_3895335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895335).length < 2 ^ (prefixWord ++ tailWord_3895335).sum := by decide
  have hdescent : baseEnd_3895335 < baseStart_3895335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895338 : List Nat := [3, 1, 4, 1, 2, 3, 1, 2, 1, 2, 3]
def baseStart_3895338 : Nat := 118140960795 + 3895338 * 2 ^ 59
def prefixEnd_3895338 : Nat := 4983230072969 + 3 ^ 40 * 3895338 * 2
def baseEnd_3895338 : Nat := 2000180705723585705860673

theorem tailTrace_3895338 : CollatzResearch.WordTrace tailWord_3895338 prefixEnd_3895338 2000180705723585705860673 := by
  unfold tailWord_3895338
  simp only [CollatzResearch.WordTrace]
  refine ⟨35518662190465792902649667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94716432507908781073732445 35518662190465792902649667)
  ·
    refine ⟨53277993285698689353974501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35518662190465792902649667 53277993285698689353974501)
    ·
      refine ⟨9989623741068504253870219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53277993285698689353974501 9989623741068504253870219)
      ·
        refine ⟨14984435611602756380805329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9989623741068504253870219 14984435611602756380805329)
        ·
          refine ⟨11238326708702067285603997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14984435611602756380805329 11238326708702067285603997)
          ·
            refine ⟨4214372515763275232101499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11238326708702067285603997 4214372515763275232101499)
            ·
              refine ⟨6321558773644912848152249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4214372515763275232101499 6321558773644912848152249)
              ·
                refine ⟨4741169080233684636114187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6321558773644912848152249 4741169080233684636114187)
                ·
                  refine ⟨7111753620350526954171281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4741169080233684636114187 7111753620350526954171281)
                  ·
                    refine ⟨5333815215262895215628461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7111753620350526954171281 5333815215262895215628461)
                    ·
                      refine ⟨2000180705723585705860673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5333815215262895215628461 2000180705723585705860673)
                      ·
                        rfl

theorem cell23_3895338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_3895338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3895338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3895338 prefixEnd_3895338 := by exact prefixLift 3895338
  have htrace : WordTrace (prefixWord ++ tailWord_3895338) baseStart_3895338 baseEnd_3895338 := by
    simpa [prefixWord, tailWord_3895338, baseEnd_3895338] using wordTrace_append hprefix tailTrace_3895338
  have hstable : (prefixWord ++ tailWord_3895338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895338).length < 2 ^ (prefixWord ++ tailWord_3895338).sum := by decide
  have hdescent : baseEnd_3895338 < baseStart_3895338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895367 : List Nat := [1, 1, 4, 1, 3, 1, 2, 2, 2, 6]
def baseStart_3895367 : Nat := 118140960795 + 3895367 * 2 ^ 59
def prefixEnd_3895367 : Nat := 4983230072969 + 3 ^ 40 * 3895367 * 2
def baseEnd_3895367 : Nat := 666731865554188697466013

theorem tailTrace_3895367 : CollatzResearch.WordTrace tailWord_3895367 prefixEnd_3895367 666731865554188697466013 := by
  unfold tailWord_3895367
  simp only [CollatzResearch.WordTrace]
  refine ⟨142075706478758109563404355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94717137652505406375602903 142075706478758109563404355)
  ·
    refine ⟨213113559718137164345106533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142075706478758109563404355 213113559718137164345106533)
    ·
      refine ⟨39958792447150718314707475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213113559718137164345106533 39958792447150718314707475)
      ·
        refine ⟨59938188670726077472061213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39958792447150718314707475 59938188670726077472061213)
        ·
          refine ⟨22476820751522279052022955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59938188670726077472061213 22476820751522279052022955)
          ·
            refine ⟨33715231127283418578034433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22476820751522279052022955 33715231127283418578034433)
            ·
              refine ⟨25286423345462563933525825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33715231127283418578034433 25286423345462563933525825)
              ·
                refine ⟨18964817509096922950144369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25286423345462563933525825 18964817509096922950144369)
                ·
                  refine ⟨14223613131822692212608277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18964817509096922950144369 14223613131822692212608277)
                  ·
                    refine ⟨666731865554188697466013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14223613131822692212608277 666731865554188697466013)
                    ·
                      rfl

theorem cell23_3895367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 6].length) (baseStart_3895367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3895367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3895367 prefixEnd_3895367 := by exact prefixLift 3895367
  have htrace : WordTrace (prefixWord ++ tailWord_3895367) baseStart_3895367 baseEnd_3895367 := by
    simpa [prefixWord, tailWord_3895367, baseEnd_3895367] using wordTrace_append hprefix tailTrace_3895367
  have hstable : (prefixWord ++ tailWord_3895367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895367).length < 2 ^ (prefixWord ++ tailWord_3895367).sum := by decide
  have hdescent : baseEnd_3895367 < baseStart_3895367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895397 : List Nat := [1, 3, 1, 3, 2, 2, 1, 1, 9]
def baseStart_3895397 : Nat := 118140960795 + 3895397 * 2 ^ 59
def prefixEnd_3895397 : Nat := 4983230072969 + 3 ^ 40 * 3895397 * 2
def baseEnd_3895397 : Nat := 222245666786911219446989

theorem tailTrace_3895397 : CollatzResearch.WordTrace tailWord_3895397 prefixEnd_3895397 222245666786911219446989 := by
  unfold tailWord_3895397
  simp only [CollatzResearch.WordTrace]
  refine ⟨142076800668649424686996445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94717867112432949791330963 142076800668649424686996445)
  ·
    refine ⟨53278800250743534257623667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142076800668649424686996445 53278800250743534257623667)
    ·
      refine ⟨79918200376115301386435501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53278800250743534257623667 79918200376115301386435501)
      ·
        refine ⟨29969325141043238019913313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79918200376115301386435501 29969325141043238019913313)
        ·
          refine ⟨22476993855782428514934985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29969325141043238019913313 22476993855782428514934985)
          ·
            refine ⟨16857745391836821386201239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22476993855782428514934985 16857745391836821386201239)
            ·
              refine ⟨25286618087755232079301859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16857745391836821386201239 25286618087755232079301859)
              ·
                refine ⟨37929927131632848118952789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25286618087755232079301859 37929927131632848118952789)
                ·
                  refine ⟨222245666786911219446989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 37929927131632848118952789 222245666786911219446989)
                  ·
                    rfl

theorem cell23_3895397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 9].length) (baseStart_3895397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3895397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3895397 prefixEnd_3895397 := by exact prefixLift 3895397
  have htrace : WordTrace (prefixWord ++ tailWord_3895397) baseStart_3895397 baseEnd_3895397 := by
    simpa [prefixWord, tailWord_3895397, baseEnd_3895397] using wordTrace_append hprefix tailTrace_3895397
  have hstable : (prefixWord ++ tailWord_3895397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895397).length < 2 ^ (prefixWord ++ tailWord_3895397).sum := by decide
  have hdescent : baseEnd_3895397 < baseStart_3895397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895446 : List Nat := [5, 3, 2, 1, 1, 1, 2, 2, 1, 3, 2]
def baseStart_3895446 : Nat := 118140960795 + 3895446 * 2 ^ 59
def prefixEnd_3895446 : Nat := 4983230072969 + 3 ^ 40 * 3895446 * 2
def baseEnd_3895446 : Nat := 2000236161634271283310177

theorem tailTrace_3895446 : CollatzResearch.WordTrace tailWord_3895446 prefixEnd_3895446 2000236161634271283310177 := by
  unfold tailWord_3895446
  simp only [CollatzResearch.WordTrace]
  refine ⟨8879911740341994128470637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94719058563647937370353461 8879911740341994128470637)
  ·
    refine ⟨3329966902628247798176489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8879911740341994128470637 3329966902628247798176489)
    ·
      refine ⟨2497475176971185848632367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3329966902628247798176489 2497475176971185848632367)
      ·
        refine ⟨3746212765456778772948551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2497475176971185848632367 3746212765456778772948551)
        ·
          refine ⟨5619319148185168159422827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3746212765456778772948551 5619319148185168159422827)
          ·
            refine ⟨8428978722277752239134241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5619319148185168159422827 8428978722277752239134241)
            ·
              refine ⟨6321734041708314179350681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8428978722277752239134241 6321734041708314179350681)
              ·
                refine ⟨4741300531281235634513011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6321734041708314179350681 4741300531281235634513011)
                ·
                  refine ⟨7111950796921853451769517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4741300531281235634513011 7111950796921853451769517)
                  ·
                    refine ⟨2666981548845695044413569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7111950796921853451769517 2666981548845695044413569)
                    ·
                      refine ⟨2000236161634271283310177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2666981548845695044413569 2000236161634271283310177)
                      ·
                        rfl

theorem cell23_3895446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_3895446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3895446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3895446 prefixEnd_3895446 := by exact prefixLift 3895446
  have htrace : WordTrace (prefixWord ++ tailWord_3895446) baseStart_3895446 baseEnd_3895446 := by
    simpa [prefixWord, tailWord_3895446, baseEnd_3895446] using wordTrace_append hprefix tailTrace_3895446
  have hstable : (prefixWord ++ tailWord_3895446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895446).length < 2 ^ (prefixWord ++ tailWord_3895446).sum := by decide
  have hdescent : baseEnd_3895446 < baseStart_3895446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895514 : List Nat := [3, 1, 1, 2, 2, 1, 2, 1, 2, 5, 3]
def baseStart_3895514 : Nat := 118140960795 + 3895514 * 2 ^ 59
def prefixEnd_3895514 : Nat := 4983230072969 + 3 ^ 40 * 3895514 * 2
def baseEnd_3895514 : Nat := 2000271078318777017259863

theorem tailTrace_3895514 : CollatzResearch.WordTrace tailWord_3895514 prefixEnd_3895514 2000271078318777017259863 := by
  unfold tailWord_3895514
  simp only [CollatzResearch.WordTrace]
  refine ⟨35520267002306388417251399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94720712006150369112670397 35520267002306388417251399)
  ·
    refine ⟨53280400503459582625877099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35520267002306388417251399 53280400503459582625877099)
    ·
      refine ⟨79920600755189373938815649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53280400503459582625877099 79920600755189373938815649)
      ·
        refine ⟨59940450566392030454111737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79920600755189373938815649 59940450566392030454111737)
        ·
          refine ⟨44955337924794022840583803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59940450566392030454111737 44955337924794022840583803)
          ·
            refine ⟨67433006887191034260875705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44955337924794022840583803 67433006887191034260875705)
            ·
              refine ⟨50574755165393275695656779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67433006887191034260875705 50574755165393275695656779)
              ·
                refine ⟨75862132748089913543485169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50574755165393275695656779 75862132748089913543485169)
                ·
                  refine ⟨56896599561067435157613877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75862132748089913543485169 56896599561067435157613877)
                  ·
                    refine ⟨5334056208850072046026301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56896599561067435157613877 5334056208850072046026301)
                    ·
                      refine ⟨2000271078318777017259863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5334056208850072046026301 2000271078318777017259863)
                      ·
                        rfl

theorem cell23_3895514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 2, 5, 3].length) (baseStart_3895514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3895514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3895514 prefixEnd_3895514 := by exact prefixLift 3895514
  have htrace : WordTrace (prefixWord ++ tailWord_3895514) baseStart_3895514 baseEnd_3895514 := by
    simpa [prefixWord, tailWord_3895514, baseEnd_3895514] using wordTrace_append hprefix tailTrace_3895514
  have hstable : (prefixWord ++ tailWord_3895514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895514).length < 2 ^ (prefixWord ++ tailWord_3895514).sum := by decide
  have hdescent : baseEnd_3895514 < baseStart_3895514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895575 : List Nat := [1, 1, 3, 4, 1, 4, 1, 1, 2, 3, 2]
def baseStart_3895575 : Nat := 118140960795 + 3895575 * 2 ^ 59
def prefixEnd_3895575 : Nat := 4983230072969 + 3 ^ 40 * 3895575 * 2
def baseEnd_3895575 : Nat := 2000302400638701278597083

theorem tailTrace_3895575 : CollatzResearch.WordTrace tailWord_3895575 prefixEnd_3895575 2000302400638701278597083 := by
  unfold tailWord_3895575
  simp only [CollatzResearch.WordTrace]
  refine ⟨142083292862004561086976179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94722195241336374057984119 142083292862004561086976179)
  ·
    refine ⟨213124939293006841630464269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142083292862004561086976179 213124939293006841630464269)
    ·
      refine ⟨79921852234877565611424101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213124939293006841630464269 79921852234877565611424101)
      ·
        refine ⟨14985347294039543552142019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79921852234877565611424101 14985347294039543552142019)
        ·
          refine ⟨22478020941059315328213029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14985347294039543552142019 22478020941059315328213029)
          ·
            refine ⟨4214628926448621624039943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22478020941059315328213029 4214628926448621624039943)
            ·
              refine ⟨6321943389672932436059915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4214628926448621624039943 6321943389672932436059915)
              ·
                refine ⟨9482915084509398654089873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6321943389672932436059915 9482915084509398654089873)
                ·
                  refine ⟨7112186313382048990567405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9482915084509398654089873 7112186313382048990567405)
                  ·
                    refine ⟨2667069867518268371462777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7112186313382048990567405 2667069867518268371462777)
                    ·
                      refine ⟨2000302400638701278597083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2667069867518268371462777 2000302400638701278597083)
                      ·
                        rfl

theorem cell23_3895575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_3895575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3895575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3895575 prefixEnd_3895575 := by exact prefixLift 3895575
  have htrace : WordTrace (prefixWord ++ tailWord_3895575) baseStart_3895575 baseEnd_3895575 := by
    simpa [prefixWord, tailWord_3895575, baseEnd_3895575] using wordTrace_append hprefix tailTrace_3895575
  have hstable : (prefixWord ++ tailWord_3895575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895575).length < 2 ^ (prefixWord ++ tailWord_3895575).sum := by decide
  have hdescent : baseEnd_3895575 < baseStart_3895575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895588 : List Nat := [2, 3, 1, 3, 1, 3, 1, 3, 1, 1, 4]
def baseStart_3895588 : Nat := 118140960795 + 3895588 * 2 ^ 59
def prefixEnd_3895588 : Nat := 4983230072969 + 3 ^ 40 * 3895588 * 2
def baseEnd_3895588 : Nat := 2000309075887209727734523

theorem tailTrace_3895588 : CollatzResearch.WordTrace tailWord_3895588 prefixEnd_3895588 2000309075887209727734523 := by
  unfold tailWord_3895588
  simp only [CollatzResearch.WordTrace]
  refine ⟨71041883505478732153599709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94722511340638309538132945 71041883505478732153599709)
  ·
    refine ⟨26640706314554524557599891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71041883505478732153599709 26640706314554524557599891)
    ·
      refine ⟨39961059471831786836399837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26640706314554524557599891 39961059471831786836399837)
      ·
        refine ⟨14985397301936920063649939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39961059471831786836399837 14985397301936920063649939)
        ·
          refine ⟨22478095952905380095474909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14985397301936920063649939 22478095952905380095474909)
          ·
            refine ⟨8429285982339517535803091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22478095952905380095474909 8429285982339517535803091)
            ·
              refine ⟨12643928973509276303704637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8429285982339517535803091 12643928973509276303704637)
              ·
                refine ⟨4741473365065978613889239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12643928973509276303704637 4741473365065978613889239)
                ·
                  refine ⟨7112210047598967920833859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4741473365065978613889239 7112210047598967920833859)
                  ·
                    refine ⟨10668315071398451881250789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7112210047598967920833859 10668315071398451881250789)
                    ·
                      refine ⟨2000309075887209727734523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10668315071398451881250789 2000309075887209727734523)
                      ·
                        rfl

theorem cell23_3895588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_3895588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3895588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3895588 prefixEnd_3895588 := by exact prefixLift 3895588
  have htrace : WordTrace (prefixWord ++ tailWord_3895588) baseStart_3895588 baseEnd_3895588 := by
    simpa [prefixWord, tailWord_3895588, baseEnd_3895588] using wordTrace_append hprefix tailTrace_3895588
  have hstable : (prefixWord ++ tailWord_3895588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895588).length < 2 ^ (prefixWord ++ tailWord_3895588).sum := by decide
  have hdescent : baseEnd_3895588 < baseStart_3895588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895605 : List Nat := [1, 3, 3, 1, 2, 1, 4, 1, 3, 2, 2]
def baseStart_3895605 : Nat := 118140960795 + 3895605 * 2 ^ 59
def prefixEnd_3895605 : Nat := 4983230072969 + 3 ^ 40 * 3895605 * 2
def baseEnd_3895605 : Nat := 2000317805058336161221945

theorem tailTrace_3895605 : CollatzResearch.WordTrace tailWord_3895605 prefixEnd_3895605 2000317805058336161221945 := by
  unfold tailWord_3895605
  simp only [CollatzResearch.WordTrace]
  refine ⟨142084387051895876210568269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94722924701263917473712179 142084387051895876210568269)
  ·
    refine ⟨53281645144460953578963101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142084387051895876210568269 53281645144460953578963101)
    ·
      refine ⟨19980616929172857592111163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53281645144460953578963101 19980616929172857592111163)
      ·
        refine ⟨29970925393759286388166745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19980616929172857592111163 29970925393759286388166745)
        ·
          refine ⟨22478194045319464791125059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29970925393759286388166745 22478194045319464791125059)
          ·
            refine ⟨33717291067979197186687589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22478194045319464791125059 33717291067979197186687589)
            ·
              refine ⟨6321992075246099472503923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33717291067979197186687589 6321992075246099472503923)
              ·
                refine ⟨9482988112869149208755885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6321992075246099472503923 9482988112869149208755885)
                ·
                  refine ⟨3556120542325930953283457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9482988112869149208755885 3556120542325930953283457)
                  ·
                    refine ⟨2667090406744448214962593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3556120542325930953283457 2667090406744448214962593)
                    ·
                      refine ⟨2000317805058336161221945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2667090406744448214962593 2000317805058336161221945)
                      ·
                        rfl

theorem cell23_3895605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 3, 2, 2].length) (baseStart_3895605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3895605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3895605 prefixEnd_3895605 := by exact prefixLift 3895605
  have htrace : WordTrace (prefixWord ++ tailWord_3895605) baseStart_3895605 baseEnd_3895605 := by
    simpa [prefixWord, tailWord_3895605, baseEnd_3895605] using wordTrace_append hprefix tailTrace_3895605
  have hstable : (prefixWord ++ tailWord_3895605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895605).length < 2 ^ (prefixWord ++ tailWord_3895605).sum := by decide
  have hdescent : baseEnd_3895605 < baseStart_3895605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895624 : List Nat := [2, 1, 3, 1, 1, 2, 2, 2, 2, 7]
def baseStart_3895624 : Nat := 118140960795 + 3895624 * 2 ^ 59
def prefixEnd_3895624 : Nat := 4983230072969 + 3 ^ 40 * 3895624 * 2
def baseEnd_3895624 : Nat := 666775853730257195628119

theorem tailTrace_3895624 : CollatzResearch.WordTrace tailWord_3895624 prefixEnd_3895624 666775853730257195628119 := by
  unfold tailWord_3895624
  simp only [CollatzResearch.WordTrace]
  refine ⟨71042540019413521227754963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94723386692551361637006617 71042540019413521227754963)
  ·
    refine ⟨106563810029120281841632445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71042540019413521227754963 106563810029120281841632445)
    ·
      refine ⟨39961428760920105690612167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106563810029120281841632445 39961428760920105690612167)
      ·
        refine ⟨59942143141380158535918251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39961428760920105690612167 59942143141380158535918251)
        ·
          refine ⟨89913214712070237803877377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59942143141380158535918251 89913214712070237803877377)
          ·
            refine ⟨67434911034052678352908033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89913214712070237803877377 67434911034052678352908033)
            ·
              refine ⟨50576183275539508764681025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67434911034052678352908033 50576183275539508764681025)
              ·
                refine ⟨37932137456654631573510769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50576183275539508764681025 37932137456654631573510769)
                ·
                  refine ⟨28449103092490973680133077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37932137456654631573510769 28449103092490973680133077)
                  ·
                    refine ⟨666775853730257195628119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28449103092490973680133077 666775853730257195628119)
                    ·
                      rfl

theorem cell23_3895624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 2, 7].length) (baseStart_3895624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3895624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3895624 prefixEnd_3895624 := by exact prefixLift 3895624
  have htrace : WordTrace (prefixWord ++ tailWord_3895624) baseStart_3895624 baseEnd_3895624 := by
    simpa [prefixWord, tailWord_3895624, baseEnd_3895624] using wordTrace_append hprefix tailTrace_3895624
  have hstable : (prefixWord ++ tailWord_3895624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895624).length < 2 ^ (prefixWord ++ tailWord_3895624).sum := by decide
  have hdescent : baseEnd_3895624 < baseStart_3895624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895661 : List Nat := [1, 5, 1, 1, 1, 2, 2, 1, 2, 3, 4]
def baseStart_3895661 : Nat := 118140960795 + 3895661 * 2 ^ 59
def prefixEnd_3895661 : Nat := 4983230072969 + 3 ^ 40 * 3895661 * 2
def baseEnd_3895661 : Nat := 2000346559974987942121687

theorem tailTrace_3895661 : CollatzResearch.WordTrace tailWord_3895661 prefixEnd_3895661 2000346559974987942121687 := by
  unfold tailWord_3895661
  simp only [CollatzResearch.WordTrace]
  refine ⟨142086429539692997774606837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94724286359795331849737891 142086429539692997774606837)
  ·
    refine ⟨13320602769346218541369391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 142086429539692997774606837 13320602769346218541369391)
    ·
      refine ⟨19980904154019327812054087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13320602769346218541369391 19980904154019327812054087)
      ·
        refine ⟨29971356231028991718081131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19980904154019327812054087 29971356231028991718081131)
        ·
          refine ⟨44957034346543487577121697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29971356231028991718081131 44957034346543487577121697)
          ·
            refine ⟨33717775759907615682841273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44957034346543487577121697 33717775759907615682841273)
            ·
              refine ⟨25288331819930711762130955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33717775759907615682841273 25288331819930711762130955)
              ·
                refine ⟨37932497729896067643196433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25288331819930711762130955 37932497729896067643196433)
                ·
                  refine ⟨28449373297422050732397325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37932497729896067643196433 28449373297422050732397325)
                  ·
                    refine ⟨10668514986533269024648997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28449373297422050732397325 10668514986533269024648997)
                    ·
                      refine ⟨2000346559974987942121687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10668514986533269024648997 2000346559974987942121687)
                      ·
                        rfl

theorem cell23_3895661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_3895661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3895661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3895661 prefixEnd_3895661 := by exact prefixLift 3895661
  have htrace : WordTrace (prefixWord ++ tailWord_3895661) baseStart_3895661 baseEnd_3895661 := by
    simpa [prefixWord, tailWord_3895661, baseEnd_3895661] using wordTrace_append hprefix tailTrace_3895661
  have hstable : (prefixWord ++ tailWord_3895661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895661).length < 2 ^ (prefixWord ++ tailWord_3895661).sum := by decide
  have hdescent : baseEnd_3895661 < baseStart_3895661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895712 : List Nat := [2, 1, 1, 4, 1, 4, 2, 2, 2, 2, 2]
def baseStart_3895712 : Nat := 118140960795 + 3895712 * 2 ^ 59
def prefixEnd_3895712 : Nat := 4983230072969 + 3 ^ 40 * 3895712 * 2
def baseEnd_3895712 : Nat := 2000372747488367242583953

theorem tailTrace_3895712 : CollatzResearch.WordTrace tailWord_3895712 prefixEnd_3895712 2000372747488367242583953 := by
  unfold tailWord_3895712
  simp only [CollatzResearch.WordTrace]
  refine ⟨71044144831254116742356695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94725526441672155656475593 71044144831254116742356695)
  ·
    refine ⟨106566217246881175113535043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71044144831254116742356695 106566217246881175113535043)
    ·
      refine ⟨159849325870321762670302565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106566217246881175113535043 159849325870321762670302565)
      ·
        refine ⟨29971748600685330500681731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159849325870321762670302565 29971748600685330500681731)
        ·
          refine ⟨44957622901027995751022597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29971748600685330500681731 44957622901027995751022597)
          ·
            refine ⟨8429554293942749203316737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44957622901027995751022597 8429554293942749203316737)
            ·
              refine ⟨6322165720457061902487553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8429554293942749203316737 6322165720457061902487553)
              ·
                refine ⟨4741624290342796426865665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6322165720457061902487553 4741624290342796426865665)
                ·
                  refine ⟨3556218217757097320149249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4741624290342796426865665 3556218217757097320149249)
                  ·
                    refine ⟨2667163663317822990111937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3556218217757097320149249 2667163663317822990111937)
                    ·
                      refine ⟨2000372747488367242583953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2667163663317822990111937 2000372747488367242583953)
                      ·
                        rfl

theorem cell23_3895712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 2, 2, 2, 2].length) (baseStart_3895712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3895712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3895712 prefixEnd_3895712 := by exact prefixLift 3895712
  have htrace : WordTrace (prefixWord ++ tailWord_3895712) baseStart_3895712 baseEnd_3895712 := by
    simpa [prefixWord, tailWord_3895712, baseEnd_3895712] using wordTrace_append hprefix tailTrace_3895712
  have hstable : (prefixWord ++ tailWord_3895712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895712).length < 2 ^ (prefixWord ++ tailWord_3895712).sum := by decide
  have hdescent : baseEnd_3895712 < baseStart_3895712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895722 : List Nat := [3, 1, 6, 1, 1, 1, 1, 1, 2, 6]
def baseStart_3895722 : Nat := 118140960795 + 3895722 * 2 ^ 59
def prefixEnd_3895722 : Nat := 4983230072969 + 3 ^ 40 * 3895722 * 2
def baseEnd_3895722 : Nat := 666792627431637401152969

theorem tailTrace_3895722 : CollatzResearch.WordTrace tailWord_3895722 prefixEnd_3895722 666792627431637401152969 := by
  unfold tailWord_3895722
  simp only [CollatzResearch.WordTrace]
  refine ⟨35522163598118001298144355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94725769594981336795051613 35522163598118001298144355)
  ·
    refine ⟨53283245397177001947216533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35522163598118001298144355 53283245397177001947216533)
    ·
      refine ⟨2497652127992671966275775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 53283245397177001947216533 2497652127992671966275775)
      ·
        refine ⟨3746478191989007949413663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2497652127992671966275775 3746478191989007949413663)
        ·
          refine ⟨5619717287983511924120495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3746478191989007949413663 5619717287983511924120495)
          ·
            refine ⟨8429575931975267886180743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5619717287983511924120495 8429575931975267886180743)
            ·
              refine ⟨12644363897962901829271115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8429575931975267886180743 12644363897962901829271115)
              ·
                refine ⟨18966545846944352743906673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12644363897962901829271115 18966545846944352743906673)
                ·
                  refine ⟨14224909385208264557930005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18966545846944352743906673 14224909385208264557930005)
                  ·
                    refine ⟨666792627431637401152969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14224909385208264557930005 666792627431637401152969)
                    ·
                      rfl

theorem cell23_3895722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_3895722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3895722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3895722 prefixEnd_3895722 := by exact prefixLift 3895722
  have htrace : WordTrace (prefixWord ++ tailWord_3895722) baseStart_3895722 baseEnd_3895722 := by
    simpa [prefixWord, tailWord_3895722, baseEnd_3895722] using wordTrace_append hprefix tailTrace_3895722
  have hstable : (prefixWord ++ tailWord_3895722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895722).length < 2 ^ (prefixWord ++ tailWord_3895722).sum := by decide
  have hdescent : baseEnd_3895722 < baseStart_3895722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
