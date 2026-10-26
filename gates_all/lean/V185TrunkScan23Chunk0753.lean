import V185TrunkScan23Chunk0752

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4452607 : List Nat := [1, 1, 2, 2, 1, 4, 1, 3, 3, 2, 3]
def baseStart_4452607 : Nat := 118140960795 + 4452607 * 2 ^ 59
def prefixEnd_4452607 : Nat := 4983230072969 + 3 ^ 40 * 4452607 * 2
def baseEnd_4452607 : Nat := 2286327556573965888335339

theorem tailTrace_4452607 : CollatzResearch.WordTrace tailWord_4452607 prefixEnd_4452607 2286327556573965888335339 := by
  unfold tailWord_4452607
  simp only [CollatzResearch.WordTrace]
  refine ⟨162399918979972758578612075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108266612653315172385741383 162399918979972758578612075)
  ·
    refine ⟨243599878469959137867918113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162399918979972758578612075 243599878469959137867918113)
    ·
      refine ⟨182699908852469353400938585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243599878469959137867918113 182699908852469353400938585)
      ·
        refine ⟨137024931639352015050703939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182699908852469353400938585 137024931639352015050703939)
        ·
          refine ⟨205537397459028022576055909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137024931639352015050703939 205537397459028022576055909)
          ·
            refine ⟨38538262023567754233010483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 205537397459028022576055909 38538262023567754233010483)
            ·
              refine ⟨57807393035351631349515725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38538262023567754233010483 57807393035351631349515725)
              ·
                refine ⟨21677772388256861756068397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57807393035351631349515725 21677772388256861756068397)
                ·
                  refine ⟨8129164645596323158525649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21677772388256861756068397 8129164645596323158525649)
                  ·
                    refine ⟨6096873484197242368894237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8129164645596323158525649 6096873484197242368894237)
                    ·
                      refine ⟨2286327556573965888335339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6096873484197242368894237 2286327556573965888335339)
                      ·
                        rfl

theorem cell23_4452607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 3, 2, 3].length) (baseStart_4452607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4452607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4452607 prefixEnd_4452607 := by exact prefixLift 4452607
  have htrace : WordTrace (prefixWord ++ tailWord_4452607) baseStart_4452607 baseEnd_4452607 := by
    simpa [prefixWord, tailWord_4452607, baseEnd_4452607] using wordTrace_append hprefix tailTrace_4452607
  have hstable : (prefixWord ++ tailWord_4452607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4452607).length < 2 ^ (prefixWord ++ tailWord_4452607).sum := by decide
  have hdescent : baseEnd_4452607 < baseStart_4452607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4452607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4452615 : List Nat := [1, 1, 4, 5, 1, 1, 2, 3, 1, 1, 3]
def baseStart_4452615 : Nat := 118140960795 + 4452615 * 2 ^ 59
def prefixEnd_4452615 : Nat := 4983230072969 + 3 ^ 40 * 4452615 * 2
def baseEnd_4452615 : Nat := 2286331664419201857035303

theorem tailTrace_4452615 : CollatzResearch.WordTrace tailWord_4452615 prefixEnd_4452615 2286331664419201857035303 := by
  unfold tailWord_4452615
  simp only [CollatzResearch.WordTrace]
  refine ⟨162400210763943775944903299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108266807175962517296602199 162400210763943775944903299)
  ·
    refine ⟨243600316145915663917354949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162400210763943775944903299 243600316145915663917354949)
    ·
      refine ⟨45675059277359186984504053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 243600316145915663917354949 45675059277359186984504053)
      ·
        refine ⟨4282036807252423779797255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45675059277359186984504053 4282036807252423779797255)
        ·
          refine ⟨6423055210878635669695883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4282036807252423779797255 6423055210878635669695883)
          ·
            refine ⟨9634582816317953504543825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6423055210878635669695883 9634582816317953504543825)
            ·
              refine ⟨7225937112238465128407869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9634582816317953504543825 7225937112238465128407869)
              ·
                refine ⟨2709726417089424423152951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7225937112238465128407869 2709726417089424423152951)
                ·
                  refine ⟨4064589625634136634729427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2709726417089424423152951 4064589625634136634729427)
                  ·
                    refine ⟨6096884438451204952094141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4064589625634136634729427 6096884438451204952094141)
                    ·
                      refine ⟨2286331664419201857035303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6096884438451204952094141 2286331664419201857035303)
                      ·
                        rfl

theorem cell23_4452615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_4452615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4452615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4452615 prefixEnd_4452615 := by exact prefixLift 4452615
  have htrace : WordTrace (prefixWord ++ tailWord_4452615) baseStart_4452615 baseEnd_4452615 := by
    simpa [prefixWord, tailWord_4452615, baseEnd_4452615] using wordTrace_append hprefix tailTrace_4452615
  have hstable : (prefixWord ++ tailWord_4452615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4452615).length < 2 ^ (prefixWord ++ tailWord_4452615).sum := by decide
  have hdescent : baseEnd_4452615 < baseStart_4452615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4452615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4452617 : List Nat := [1, 2, 1, 1, 3, 4, 2, 2, 1, 2, 4]
def baseStart_4452617 : Nat := 118140960795 + 4452617 * 2 ^ 59
def prefixEnd_4452617 : Nat := 4983230072969 + 3 ^ 40 * 4452617 * 2
def baseEnd_4452617 : Nat := 2286332691380510849210293

theorem tailTrace_4452617 : CollatzResearch.WordTrace tailWord_4452617 prefixEnd_4452617 2286332691380510849210293 := by
  unfold tailWord_4452617
  simp only [CollatzResearch.WordTrace]
  refine ⟨162400283709936530286476105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108266855806624353524317403 162400283709936530286476105)
  ·
    refine ⟨121800212782452397714857079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162400283709936530286476105 121800212782452397714857079)
    ·
      refine ⟨182700319173678596572285619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121800212782452397714857079 182700319173678596572285619)
      ·
        refine ⟨274050478760517894858428429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182700319173678596572285619 274050478760517894858428429)
        ·
          refine ⟨102768929535194210571910661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 274050478760517894858428429 102768929535194210571910661)
          ·
            refine ⟨19269174287848914482233249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102768929535194210571910661 19269174287848914482233249)
            ·
              refine ⟨14451880715886685861674937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19269174287848914482233249 14451880715886685861674937)
              ·
                refine ⟨10838910536915014396256203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14451880715886685861674937 10838910536915014396256203)
                ·
                  refine ⟨16258365805372521594384305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10838910536915014396256203 16258365805372521594384305)
                  ·
                    refine ⟨12193774354029391195788229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16258365805372521594384305 12193774354029391195788229)
                    ·
                      refine ⟨2286332691380510849210293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12193774354029391195788229 2286332691380510849210293)
                      ·
                        rfl

theorem cell23_4452617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 2, 4].length) (baseStart_4452617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4452617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4452617 prefixEnd_4452617 := by exact prefixLift 4452617
  have htrace : WordTrace (prefixWord ++ tailWord_4452617) baseStart_4452617 baseEnd_4452617 := by
    simpa [prefixWord, tailWord_4452617, baseEnd_4452617] using wordTrace_append hprefix tailTrace_4452617
  have hstable : (prefixWord ++ tailWord_4452617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4452617).length < 2 ^ (prefixWord ++ tailWord_4452617).sum := by decide
  have hdescent : baseEnd_4452617 < baseStart_4452617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4452617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4452631 : List Nat := [1, 1, 3, 4, 1, 4, 1, 2, 2, 4]
def baseStart_4452631 : Nat := 118140960795 + 4452631 * 2 ^ 59
def prefixEnd_4452631 : Nat := 4983230072969 + 3 ^ 40 * 4452631 * 2
def baseEnd_4452631 : Nat := 762113293369891264811743

theorem tailTrace_4452631 : CollatzResearch.WordTrace tailWord_4452631 prefixEnd_4452631 762113293369891264811743 := by
  unfold tailWord_4452631
  simp only [CollatzResearch.WordTrace]
  refine ⟨162400794331885810677485747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108267196221257207118323831 162400794331885810677485747)
  ·
    refine ⟨243601191497828716016228621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162400794331885810677485747 243601191497828716016228621)
    ·
      refine ⟨91350446811685768506085733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 243601191497828716016228621 91350446811685768506085733)
      ·
        refine ⟨17128208777191081594891075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91350446811685768506085733 17128208777191081594891075)
        ·
          refine ⟨25692313165786622392336613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17128208777191081594891075 25692313165786622392336613)
          ·
            refine ⟨4817308718584991698563115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25692313165786622392336613 4817308718584991698563115)
            ·
              refine ⟨7225963077877487547844673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4817308718584991698563115 7225963077877487547844673)
              ·
                refine ⟨5419472308408115660883505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7225963077877487547844673 5419472308408115660883505)
                ·
                  refine ⟨4064604231306086745662629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5419472308408115660883505 4064604231306086745662629)
                  ·
                    refine ⟨762113293369891264811743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4064604231306086745662629 762113293369891264811743)
                    ·
                      rfl

theorem cell23_4452631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 2, 2, 4].length) (baseStart_4452631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4452631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4452631 prefixEnd_4452631 := by exact prefixLift 4452631
  have htrace : WordTrace (prefixWord ++ tailWord_4452631) baseStart_4452631 baseEnd_4452631 := by
    simpa [prefixWord, tailWord_4452631, baseEnd_4452631] using wordTrace_append hprefix tailTrace_4452631
  have hstable : (prefixWord ++ tailWord_4452631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4452631).length < 2 ^ (prefixWord ++ tailWord_4452631).sum := by decide
  have hdescent : baseEnd_4452631 < baseStart_4452631 := by decide
  rcases family_descends (prefixWord ++ tailWord_4452631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4452648 : List Nat := [2, 1, 5, 1, 3, 1, 3, 1, 2, 4]
def baseStart_4452648 : Nat := 118140960795 + 4452648 * 2 ^ 59
def prefixEnd_4452648 : Nat := 4983230072969 + 3 ^ 40 * 4452648 * 2
def baseEnd_4452648 : Nat := 762116203093600075974217

theorem tailTrace_4452648 : CollatzResearch.WordTrace tailWord_4452648 prefixEnd_4452648 762116203093600075974217 := by
  unfold tailWord_4452648
  simp only [CollatzResearch.WordTrace]
  refine ⟨81200707186412111290427299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108267609581882815053903065 81200707186412111290427299)
  ·
    refine ⟨121801060779618166935640949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81200707186412111290427299 121801060779618166935640949)
    ·
      refine ⟨11418849448089203150216339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 121801060779618166935640949 11418849448089203150216339)
      ·
        refine ⟨17128274172133804725324509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11418849448089203150216339 17128274172133804725324509)
        ·
          refine ⟨6423102814550176771996691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17128274172133804725324509 6423102814550176771996691)
          ·
            refine ⟨9634654221825265157995037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6423102814550176771996691 9634654221825265157995037)
            ·
              refine ⟨3612995333184474434248139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9634654221825265157995037 3612995333184474434248139)
              ·
                refine ⟨5419492999776711651372209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3612995333184474434248139 5419492999776711651372209)
                ·
                  refine ⟨4064619749832533738529157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5419492999776711651372209 4064619749832533738529157)
                  ·
                    refine ⟨762116203093600075974217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4064619749832533738529157 762116203093600075974217)
                    ·
                      rfl

theorem cell23_4452648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_4452648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4452648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4452648 prefixEnd_4452648 := by exact prefixLift 4452648
  have htrace : WordTrace (prefixWord ++ tailWord_4452648) baseStart_4452648 baseEnd_4452648 := by
    simpa [prefixWord, tailWord_4452648, baseEnd_4452648] using wordTrace_append hprefix tailTrace_4452648
  have hstable : (prefixWord ++ tailWord_4452648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4452648).length < 2 ^ (prefixWord ++ tailWord_4452648).sum := by decide
  have hdescent : baseEnd_4452648 < baseStart_4452648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4452648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4452664 : List Nat := [2, 1, 2, 1, 3, 1, 2, 3, 3, 3, 2]
def baseStart_4452664 : Nat := 118140960795 + 4452664 * 2 ^ 59
def prefixEnd_4452664 : Nat := 4983230072969 + 3 ^ 40 * 4452664 * 2
def baseEnd_4452664 : Nat := 2286356824971272165322577

theorem tailTrace_4452664 : CollatzResearch.WordTrace tailWord_4452664 prefixEnd_4452664 2286356824971272165322577 := by
  unfold tailWord_4452664
  simp only [CollatzResearch.WordTrace]
  refine ⟨81200998970383128656718523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108267998627177504875624697 81200998970383128656718523)
  ·
    refine ⟨121801498455574692985077785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81200998970383128656718523 121801498455574692985077785)
    ·
      refine ⟨91351123841681019738808339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121801498455574692985077785 91351123841681019738808339)
      ·
        refine ⟨137026685762521529608212509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91351123841681019738808339 137026685762521529608212509)
        ·
          refine ⟨51385007160945573603079691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137026685762521529608212509 51385007160945573603079691)
          ·
            refine ⟨77077510741418360404619537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51385007160945573603079691 77077510741418360404619537)
            ·
              refine ⟨57808133056063770303464653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77077510741418360404619537 57808133056063770303464653)
              ·
                refine ⟨21678049896023913863799245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57808133056063770303464653 21678049896023913863799245)
                ·
                  refine ⟨8129268711008967698924717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21678049896023913863799245 8129268711008967698924717)
                  ·
                    refine ⟨3048475766628362887096769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8129268711008967698924717 3048475766628362887096769)
                    ·
                      refine ⟨2286356824971272165322577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3048475766628362887096769 2286356824971272165322577)
                      ·
                        rfl

theorem cell23_4452664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 3, 3, 2].length) (baseStart_4452664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4452664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4452664 prefixEnd_4452664 := by exact prefixLift 4452664
  have htrace : WordTrace (prefixWord ++ tailWord_4452664) baseStart_4452664 baseEnd_4452664 := by
    simpa [prefixWord, tailWord_4452664, baseEnd_4452664] using wordTrace_append hprefix tailTrace_4452664
  have hstable : (prefixWord ++ tailWord_4452664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4452664).length < 2 ^ (prefixWord ++ tailWord_4452664).sum := by decide
  have hdescent : baseEnd_4452664 < baseStart_4452664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4452664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4452697 : List Nat := [1, 2, 1, 2, 2, 2, 1, 3, 2, 4, 3]
def baseStart_4452697 : Nat := 118140960795 + 4452697 * 2 ^ 59
def prefixEnd_4452697 : Nat := 4983230072969 + 3 ^ 40 * 4452697 * 2
def baseEnd_4452697 : Nat := 2286373769832870536209925

theorem tailTrace_4452697 : CollatzResearch.WordTrace tailWord_4452697 prefixEnd_4452697 2286373769832870536209925 := by
  unfold tailWord_4452697
  simp only [CollatzResearch.WordTrace]
  refine ⟨162403201549646703949388345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108268801033097802632925563 162403201549646703949388345)
  ·
    refine ⟨121802401162235027962041259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162403201549646703949388345 121802401162235027962041259)
    ·
      refine ⟨182703601743352541943061889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121802401162235027962041259 182703601743352541943061889)
      ·
        refine ⟨137027701307514406457296417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182703601743352541943061889 137027701307514406457296417)
        ·
          refine ⟨102770775980635804842972313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137027701307514406457296417 102770775980635804842972313)
          ·
            refine ⟨77078081985476853632229235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102770775980635804842972313 77078081985476853632229235)
            ·
              refine ⟨115617122978215280448343853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77078081985476853632229235 115617122978215280448343853)
              ·
                refine ⟨43356421116830730168128945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115617122978215280448343853 43356421116830730168128945)
                ·
                  refine ⟨32517315837623047626096709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43356421116830730168128945 32517315837623047626096709)
                  ·
                    refine ⟨6096996719554321429893133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32517315837623047626096709 6096996719554321429893133)
                    ·
                      refine ⟨2286373769832870536209925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6096996719554321429893133 2286373769832870536209925)
                      ·
                        rfl

theorem cell23_4452697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 4, 3].length) (baseStart_4452697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4452697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4452697 prefixEnd_4452697 := by exact prefixLift 4452697
  have htrace : WordTrace (prefixWord ++ tailWord_4452697) baseStart_4452697 baseEnd_4452697 := by
    simpa [prefixWord, tailWord_4452697, baseEnd_4452697] using wordTrace_append hprefix tailTrace_4452697
  have hstable : (prefixWord ++ tailWord_4452697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4452697).length < 2 ^ (prefixWord ++ tailWord_4452697).sum := by decide
  have hdescent : baseEnd_4452697 < baseStart_4452697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4452697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4452707 : List Nat := [1, 1, 1, 5, 2, 1, 2, 1, 1, 4, 4]
def baseStart_4452707 : Nat := 118140960795 + 4452707 * 2 ^ 59
def prefixEnd_4452707 : Nat := 4983230072969 + 3 ^ 40 * 4452707 * 2
def baseEnd_4452707 : Nat := 2286378904639415497084879

theorem tailTrace_4452707 : CollatzResearch.WordTrace tailWord_4452707 prefixEnd_4452707 2286378904639415497084879 := by
  unfold tailWord_4452707
  simp only [CollatzResearch.WordTrace]
  refine ⟨162403566279610475657252375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108269044186406983771501583 162403566279610475657252375)
  ·
    refine ⟨243605349419415713485878563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162403566279610475657252375 243605349419415713485878563)
    ·
      refine ⟨365408024129123570228817845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243605349419415713485878563 365408024129123570228817845)
      ·
        refine ⟨34257002262105334708951673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 365408024129123570228817845 34257002262105334708951673)
        ·
          refine ⟨25692751696579001031713755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34257002262105334708951673 25692751696579001031713755)
          ·
            refine ⟨38539127544868501547570633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25692751696579001031713755 38539127544868501547570633)
            ·
              refine ⟨28904345658651376160677975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38539127544868501547570633 28904345658651376160677975)
              ·
                refine ⟨43356518487977064241016963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28904345658651376160677975 43356518487977064241016963)
                ·
                  refine ⟨65034777731965596361525445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43356518487977064241016963 65034777731965596361525445)
                  ·
                    refine ⟨12194020824743549317786021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 65034777731965596361525445 12194020824743549317786021)
                    ·
                      refine ⟨2286378904639415497084879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12194020824743549317786021 2286378904639415497084879)
                      ·
                        rfl

theorem cell23_4452707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_4452707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4452707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4452707 prefixEnd_4452707 := by exact prefixLift 4452707
  have htrace : WordTrace (prefixWord ++ tailWord_4452707) baseStart_4452707 baseEnd_4452707 := by
    simpa [prefixWord, tailWord_4452707, baseEnd_4452707] using wordTrace_append hprefix tailTrace_4452707
  have hstable : (prefixWord ++ tailWord_4452707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4452707).length < 2 ^ (prefixWord ++ tailWord_4452707).sum := by decide
  have hdescent : baseEnd_4452707 < baseStart_4452707 := by decide
  rcases family_descends (prefixWord ++ tailWord_4452707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4452714 : List Nat := [3, 1, 3, 3, 1, 1, 1, 2, 2, 1, 5]
def baseStart_4452714 : Nat := 118140960795 + 4452714 * 2 ^ 59
def prefixEnd_4452714 : Nat := 4983230072969 + 3 ^ 40 * 4452714 * 2
def baseEnd_4452714 : Nat := 2286382499003996969697347

theorem tailTrace_4452714 : CollatzResearch.WordTrace tailWord_4452714 prefixEnd_4452714 2286382499003996969697347 := by
  unfold tailWord_4452714
  simp only [CollatzResearch.WordTrace]
  refine ⟨40600955397646278963189299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108269214393723410568504797 40600955397646278963189299)
  ·
    refine ⟨60901433096469418444783949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40600955397646278963189299 60901433096469418444783949)
    ·
      refine ⟨22838037411176031916793981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60901433096469418444783949 22838037411176031916793981)
      ·
        refine ⟨8564264029191011968797743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22838037411176031916793981 8564264029191011968797743)
        ·
          refine ⟨12846396043786517953196615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8564264029191011968797743 12846396043786517953196615)
          ·
            refine ⟨19269594065679776929794923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12846396043786517953196615 19269594065679776929794923)
            ·
              refine ⟨28904391098519665394692385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19269594065679776929794923 28904391098519665394692385)
              ·
                refine ⟨21678293323889749046019289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28904391098519665394692385 21678293323889749046019289)
                ·
                  refine ⟨16258719992917311784514467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21678293323889749046019289 16258719992917311784514467)
                  ·
                    refine ⟨24388079989375967676771701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16258719992917311784514467 24388079989375967676771701)
                    ·
                      refine ⟨2286382499003996969697347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24388079989375967676771701 2286382499003996969697347)
                      ·
                        rfl

theorem cell23_4452714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_4452714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4452714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4452714 prefixEnd_4452714 := by exact prefixLift 4452714
  have htrace : WordTrace (prefixWord ++ tailWord_4452714) baseStart_4452714 baseEnd_4452714 := by
    simpa [prefixWord, tailWord_4452714, baseEnd_4452714] using wordTrace_append hprefix tailTrace_4452714
  have hstable : (prefixWord ++ tailWord_4452714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4452714).length < 2 ^ (prefixWord ++ tailWord_4452714).sum := by decide
  have hdescent : baseEnd_4452714 < baseStart_4452714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4452714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4452717 : List Nat := [1, 5, 1, 1, 1, 2, 2, 1, 9]
def baseStart_4452717 : Nat := 118140960795 + 4452717 * 2 ^ 59
def prefixEnd_4452717 : Nat := 4983230072969 + 3 ^ 40 * 4452717 * 2
def baseEnd_4452717 : Nat := 254042671049551161995537

theorem tailTrace_4452717 : CollatzResearch.WordTrace tailWord_4452717 prefixEnd_4452717 254042671049551161995537 := by
  unfold tailWord_4452717
  simp only [CollatzResearch.WordTrace]
  refine ⟨162403931009574247365116405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108269287339716164910077603 162403931009574247365116405)
  ·
    refine ⟨15225368532147585690479663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 162403931009574247365116405 15225368532147585690479663)
    ·
      refine ⟨22838052798221378535719495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15225368532147585690479663 22838052798221378535719495)
      ·
        refine ⟨34257079197332067803579243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22838052798221378535719495 34257079197332067803579243)
        ·
          refine ⟨51385618795998101705368865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34257079197332067803579243 51385618795998101705368865)
          ·
            refine ⟨38539214096998576279026649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51385618795998101705368865 38539214096998576279026649)
            ·
              refine ⟨28904410572748932209269987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38539214096998576279026649 28904410572748932209269987)
              ·
                refine ⟨43356615859123398313904981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28904410572748932209269987 43356615859123398313904981)
                ·
                  refine ⟨254042671049551161995537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 43356615859123398313904981 254042671049551161995537)
                  ·
                    rfl

theorem cell23_4452717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 9].length) (baseStart_4452717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4452717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4452717 prefixEnd_4452717 := by exact prefixLift 4452717
  have htrace : WordTrace (prefixWord ++ tailWord_4452717) baseStart_4452717 baseEnd_4452717 := by
    simpa [prefixWord, tailWord_4452717, baseEnd_4452717] using wordTrace_append hprefix tailTrace_4452717
  have hstable : (prefixWord ++ tailWord_4452717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4452717).length < 2 ^ (prefixWord ++ tailWord_4452717).sum := by decide
  have hdescent : baseEnd_4452717 < baseStart_4452717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4452717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4452727 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 3, 5, 3]
def baseStart_4452727 : Nat := 118140960795 + 4452727 * 2 ^ 59
def prefixEnd_4452727 : Nat := 4983230072969 + 3 ^ 40 * 4452727 * 2
def baseEnd_4452727 : Nat := 2286389174252505418834787

theorem tailTrace_4452727 : CollatzResearch.WordTrace tailWord_4452727 prefixEnd_4452727 2286389174252505418834787 := by
  unfold tailWord_4452727
  simp only [CollatzResearch.WordTrace]
  refine ⟨162404295739538019072980435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108269530493025346048653623 162404295739538019072980435)
  ·
    refine ⟨243606443609307028609470653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162404295739538019072980435 243606443609307028609470653)
    ·
      refine ⟨91352416353490135728551495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 243606443609307028609470653 91352416353490135728551495)
      ·
        refine ⟨137028624530235203592827243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91352416353490135728551495 137028624530235203592827243)
        ·
          refine ⟨205542936795352805389240865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137028624530235203592827243 205542936795352805389240865)
          ·
            refine ⟨154157202596514604041930649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 205542936795352805389240865 154157202596514604041930649)
            ·
              refine ⟨115617901947385953031447987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154157202596514604041930649 115617901947385953031447987)
              ·
                refine ⟨173426852921078929547171981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115617901947385953031447987 173426852921078929547171981)
                ·
                  refine ⟨65035069845404598580189493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 173426852921078929547171981 65035069845404598580189493)
                  ·
                    refine ⟨6097037798006681116892765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 65035069845404598580189493 6097037798006681116892765)
                    ·
                      refine ⟨2286389174252505418834787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6097037798006681116892765 2286389174252505418834787)
                      ·
                        rfl

theorem cell23_4452727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 5, 3].length) (baseStart_4452727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4452727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4452727 prefixEnd_4452727 := by exact prefixLift 4452727
  have htrace : WordTrace (prefixWord ++ tailWord_4452727) baseStart_4452727 baseEnd_4452727 := by
    simpa [prefixWord, tailWord_4452727, baseEnd_4452727] using wordTrace_append hprefix tailTrace_4452727
  have hstable : (prefixWord ++ tailWord_4452727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4452727).length < 2 ^ (prefixWord ++ tailWord_4452727).sum := by decide
  have hdescent : baseEnd_4452727 < baseStart_4452727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4452727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4452744 : List Nat := [2, 1, 3, 3, 1, 1, 2, 2, 2, 3, 3]
def baseStart_4452744 : Nat := 118140960795 + 4452744 * 2 ^ 59
def prefixEnd_4452744 : Nat := 4983230072969 + 3 ^ 40 * 4452744 * 2
def baseEnd_4452744 : Nat := 2286397903423631852322209

theorem tailTrace_4452744 : CollatzResearch.WordTrace tailWord_4452744 prefixEnd_4452744 2286397903423631852322209 := by
  unfold tailWord_4452744
  simp only [CollatzResearch.WordTrace]
  refine ⟨81202457890238215488174643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108269943853650953984232857 81202457890238215488174643)
  ·
    refine ⟨121803686835357323232261965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81202457890238215488174643 121803686835357323232261965)
    ·
      refine ⟨45676382563258996212098237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121803686835357323232261965 45676382563258996212098237)
      ·
        refine ⟨17128643461222123579536839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45676382563258996212098237 17128643461222123579536839)
        ·
          refine ⟨25692965191833185369305259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17128643461222123579536839 25692965191833185369305259)
          ·
            refine ⟨38539447787749778053957889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25692965191833185369305259 38539447787749778053957889)
            ·
              refine ⟨28904585840812333540468417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38539447787749778053957889 28904585840812333540468417)
              ·
                refine ⟨21678439380609250155351313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28904585840812333540468417 21678439380609250155351313)
                ·
                  refine ⟨16258829535456937616513485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21678439380609250155351313 16258829535456937616513485)
                  ·
                    refine ⟨6097061075796351606192557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16258829535456937616513485 6097061075796351606192557)
                    ·
                      refine ⟨2286397903423631852322209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6097061075796351606192557 2286397903423631852322209)
                      ·
                        rfl

theorem cell23_4452744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_4452744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4452744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4452744 prefixEnd_4452744 := by exact prefixLift 4452744
  have htrace : WordTrace (prefixWord ++ tailWord_4452744) baseStart_4452744 baseEnd_4452744 := by
    simpa [prefixWord, tailWord_4452744, baseEnd_4452744] using wordTrace_append hprefix tailTrace_4452744
  have hstable : (prefixWord ++ tailWord_4452744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4452744).length < 2 ^ (prefixWord ++ tailWord_4452744).sum := by decide
  have hdescent : baseEnd_4452744 < baseStart_4452744 := by decide
  rcases family_descends (prefixWord ++ tailWord_4452744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4452781 : List Nat := [1, 5, 2, 2, 2, 1, 1, 1, 1, 7]
def baseStart_4452781 : Nat := 118140960795 + 4452781 * 2 ^ 59
def prefixEnd_4452781 : Nat := 4983230072969 + 3 ^ 40 * 4452781 * 2
def baseEnd_4452781 : Nat := 762138967402616069186513

theorem tailTrace_4452781 : CollatzResearch.WordTrace tailWord_4452781 prefixEnd_4452781 762138967402616069186513 := by
  unfold tailWord_4452781
  simp only [CollatzResearch.WordTrace]
  refine ⟨162406265281342386295446197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108270843520894924196964131 162406265281342386295446197)
  ·
    refine ⟨15225587370125848715198081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 162406265281342386295446197 15225587370125848715198081)
    ·
      refine ⟨11419190527594386536398561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15225587370125848715198081 11419190527594386536398561)
      ·
        refine ⟨8564392895695789902298921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11419190527594386536398561 8564392895695789902298921)
        ·
          refine ⟨6423294671771842426724191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8564392895695789902298921 6423294671771842426724191)
          ·
            refine ⟨9634942007657763640086287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6423294671771842426724191 9634942007657763640086287)
            ·
              refine ⟨14452413011486645460129431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9634942007657763640086287 14452413011486645460129431)
              ·
                refine ⟨21678619517229968190194147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14452413011486645460129431 21678619517229968190194147)
                ·
                  refine ⟨32517929275844952285291221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21678619517229968190194147 32517929275844952285291221)
                  ·
                    refine ⟨762138967402616069186513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32517929275844952285291221 762138967402616069186513)
                    ·
                      rfl

theorem cell23_4452781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_4452781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4452781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4452781 prefixEnd_4452781 := by exact prefixLift 4452781
  have htrace : WordTrace (prefixWord ++ tailWord_4452781) baseStart_4452781 baseEnd_4452781 := by
    simpa [prefixWord, tailWord_4452781, baseEnd_4452781] using wordTrace_append hprefix tailTrace_4452781
  have hstable : (prefixWord ++ tailWord_4452781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4452781).length < 2 ^ (prefixWord ++ tailWord_4452781).sum := by decide
  have hdescent : baseEnd_4452781 < baseStart_4452781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4452781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4452845 : List Nat := [1, 5, 1, 3, 1, 1, 3, 3, 1, 4]
def baseStart_4452845 : Nat := 118140960795 + 4452845 * 2 ^ 59
def prefixEnd_4452845 : Nat := 4983230072969 + 3 ^ 40 * 4452845 * 2
def baseEnd_4452845 : Nat := 762149921656578652386415

theorem tailTrace_4452845 : CollatzResearch.WordTrace tailWord_4452845 prefixEnd_4452845 762149921656578652386415 := by
  unfold tailWord_4452845
  simp only [CollatzResearch.WordTrace]
  refine ⟨162408599553110525225775989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108272399702073683483850659 162408599553110525225775989)
  ·
    refine ⟨15225806208104111739916499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 162408599553110525225775989 15225806208104111739916499)
    ·
      refine ⟨22838709312156167609874749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15225806208104111739916499 22838709312156167609874749)
      ·
        refine ⟨8564515992058562853703031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22838709312156167609874749 8564515992058562853703031)
        ·
          refine ⟨12846773988087844280554547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8564515992058562853703031 12846773988087844280554547)
          ·
            refine ⟨19270160982131766420831821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12846773988087844280554547 19270160982131766420831821)
            ·
              refine ⟨7226310368299412407811933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19270160982131766420831821 7226310368299412407811933)
              ·
                refine ⟨2709866388112279652929475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7226310368299412407811933 2709866388112279652929475)
                ·
                  refine ⟨4064799582168419479394213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2709866388112279652929475 4064799582168419479394213)
                  ·
                    refine ⟨762149921656578652386415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4064799582168419479394213 762149921656578652386415)
                    ·
                      rfl

theorem cell23_4452845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_4452845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4452845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4452845 prefixEnd_4452845 := by exact prefixLift 4452845
  have htrace : WordTrace (prefixWord ++ tailWord_4452845) baseStart_4452845 baseEnd_4452845 := by
    simpa [prefixWord, tailWord_4452845, baseEnd_4452845] using wordTrace_append hprefix tailTrace_4452845
  have hstable : (prefixWord ++ tailWord_4452845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4452845).length < 2 ^ (prefixWord ++ tailWord_4452845).sum := by decide
  have hdescent : baseEnd_4452845 < baseStart_4452845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4452845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4452888 : List Nat := [2, 1, 2, 3, 3, 3, 1, 2, 1, 5]
def baseStart_4452888 : Nat := 118140960795 + 4452888 * 2 ^ 59
def prefixEnd_4452888 : Nat := 4983230072969 + 3 ^ 40 * 4452888 * 2
def baseEnd_4452888 : Nat := 762157281545959762973849

theorem tailTrace_4452888 : CollatzResearch.WordTrace tailWord_4452888 prefixEnd_4452888 762157281545959762973849 := by
  unfold tailWord_4452888
  simp only [CollatzResearch.WordTrace]
  refine ⟨81205083945977371784795659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108273445261303162379727545 81205083945977371784795659)
  ·
    refine ⟨121807625918966057677193489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81205083945977371784795659 121807625918966057677193489)
    ·
      refine ⟨91355719439224543257895117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121807625918966057677193489 91355719439224543257895117)
      ·
        refine ⟨34258394789709203721710669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91355719439224543257895117 34258394789709203721710669)
        ·
          refine ⟨12846898046140951395641501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34258394789709203721710669 12846898046140951395641501)
          ·
            refine ⟨4817586767302856773365563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12846898046140951395641501 4817586767302856773365563)
            ·
              refine ⟨7226380150954285160048345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4817586767302856773365563 7226380150954285160048345)
              ·
                refine ⟨5419785113215713870036259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7226380150954285160048345 5419785113215713870036259)
                ·
                  refine ⟨8129677669823570805054389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5419785113215713870036259 8129677669823570805054389)
                  ·
                    refine ⟨762157281545959762973849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8129677669823570805054389 762157281545959762973849)
                    ·
                      rfl

theorem cell23_4452888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 2, 1, 5].length) (baseStart_4452888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4452888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4452888 prefixEnd_4452888 := by exact prefixLift 4452888
  have htrace : WordTrace (prefixWord ++ tailWord_4452888) baseStart_4452888 baseEnd_4452888 := by
    simpa [prefixWord, tailWord_4452888, baseEnd_4452888] using wordTrace_append hprefix tailTrace_4452888
  have hstable : (prefixWord ++ tailWord_4452888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4452888).length < 2 ^ (prefixWord ++ tailWord_4452888).sum := by decide
  have hdescent : baseEnd_4452888 < baseStart_4452888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4452888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4452962 : List Nat := [3, 3, 2, 3, 1, 1, 1, 3, 1, 2, 3]
def baseStart_4452962 : Nat := 118140960795 + 4452962 * 2 ^ 59
def prefixEnd_4452962 : Nat := 4983230072969 + 3 ^ 40 * 4452962 * 2
def baseEnd_4452962 : Nat := 2286509842206311999396207

theorem tailTrace_4452962 : CollatzResearch.WordTrace tailWord_4452962 prefixEnd_4452962 2286509842206311999396207 := by
  unfold tailWord_4452962
  simp only [CollatzResearch.WordTrace]
  refine ⟨40603216723421663551946285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108275244595791102805190093 40603216723421663551946285)
  ·
    refine ⟨15226206271283123831979857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40603216723421663551946285 15226206271283123831979857)
    ·
      refine ⟨11419654703462342873984893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15226206271283123831979857 11419654703462342873984893)
      ·
        refine ⟨4282370513798378577744335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11419654703462342873984893 4282370513798378577744335)
        ·
          refine ⟨6423555770697567866616503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4282370513798378577744335 6423555770697567866616503)
          ·
            refine ⟨9635333656046351799924755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6423555770697567866616503 9635333656046351799924755)
            ·
              refine ⟨14453000484069527699887133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9635333656046351799924755 14453000484069527699887133)
              ·
                refine ⟨5419875181526072887457675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14453000484069527699887133 5419875181526072887457675)
                ·
                  refine ⟨8129812772289109331186513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5419875181526072887457675 8129812772289109331186513)
                  ·
                    refine ⟨6097359579216831998389885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8129812772289109331186513 6097359579216831998389885)
                    ·
                      refine ⟨2286509842206311999396207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6097359579216831998389885 2286509842206311999396207)
                      ·
                        rfl

theorem cell23_4452962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_4452962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4452962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4452962 prefixEnd_4452962 := by exact prefixLift 4452962
  have htrace : WordTrace (prefixWord ++ tailWord_4452962) baseStart_4452962 baseEnd_4452962 := by
    simpa [prefixWord, tailWord_4452962, baseEnd_4452962] using wordTrace_append hprefix tailTrace_4452962
  have hstable : (prefixWord ++ tailWord_4452962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4452962).length < 2 ^ (prefixWord ++ tailWord_4452962).sum := by decide
  have hdescent : baseEnd_4452962 < baseStart_4452962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4452962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4452984 : List Nat := [2, 1, 2, 1, 1, 1, 2, 4, 1, 3, 5]
def baseStart_4452984 : Nat := 118140960795 + 4452984 * 2 ^ 59
def prefixEnd_4452984 : Nat := 4983230072969 + 3 ^ 40 * 4452984 * 2
def baseEnd_4452984 : Nat := 2286521138780710913321105

theorem tailTrace_4452984 : CollatzResearch.WordTrace tailWord_4452984 prefixEnd_4452984 2286521138780710913321105 := by
  unfold tailWord_4452984
  simp only [CollatzResearch.WordTrace]
  refine ⟨81206834649803475982543003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108275779533071301310057337 81206834649803475982543003)
  ·
    refine ⟨121810251974705213973814505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81206834649803475982543003 121810251974705213973814505)
    ·
      refine ⟨91357688981028910480360879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121810251974705213973814505 91357688981028910480360879)
      ·
        refine ⟨137036533471543365720541319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91357688981028910480360879 137036533471543365720541319)
        ·
          refine ⟨205554800207315048580811979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137036533471543365720541319 205554800207315048580811979)
          ·
            refine ⟨308332200310972572871217969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205554800207315048580811979 308332200310972572871217969)
            ·
              refine ⟨231249150233229429653413477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 308332200310972572871217969 231249150233229429653413477)
              ·
                refine ⟨43359215668730518060015027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 231249150233229429653413477 43359215668730518060015027)
                ·
                  refine ⟨65038823503095777090022541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43359215668730518060015027 65038823503095777090022541)
                  ·
                    refine ⟨24389558813660916408758453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 65038823503095777090022541 24389558813660916408758453)
                    ·
                      refine ⟨2286521138780710913321105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24389558813660916408758453 2286521138780710913321105)
                      ·
                        rfl

theorem cell23_4452984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 1, 3, 5].length) (baseStart_4452984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4452984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4452984 prefixEnd_4452984 := by exact prefixLift 4452984
  have htrace : WordTrace (prefixWord ++ tailWord_4452984) baseStart_4452984 baseEnd_4452984 := by
    simpa [prefixWord, tailWord_4452984, baseEnd_4452984] using wordTrace_append hprefix tailTrace_4452984
  have hstable : (prefixWord ++ tailWord_4452984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4452984).length < 2 ^ (prefixWord ++ tailWord_4452984).sum := by decide
  have hdescent : baseEnd_4452984 < baseStart_4452984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4452984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4453002 : List Nat := [3, 1, 2, 3, 3, 1, 2, 2, 1, 3, 2]
def baseStart_4453002 : Nat := 118140960795 + 4453002 * 2 ^ 59
def prefixEnd_4453002 : Nat := 4983230072969 + 3 ^ 40 * 4453002 * 2
def baseEnd_4453002 : Nat := 2286530381432491842896023

theorem tailTrace_4453002 : CollatzResearch.WordTrace tailWord_4453002 prefixEnd_4453002 2286530381432491842896023 := by
  unfold tailWord_4453002
  simp only [CollatzResearch.WordTrace]
  refine ⟨40603581453385435259810315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108276217209027827359494173 40603581453385435259810315)
  ·
    refine ⟨60905372180078152889715473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40603581453385435259810315 60905372180078152889715473)
    ·
      refine ⟨45679029135058614667286605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60905372180078152889715473 45679029135058614667286605)
      ·
        refine ⟨17129635925646980500232477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45679029135058614667286605 17129635925646980500232477)
        ·
          refine ⟨6423613472117617687587179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17129635925646980500232477 6423613472117617687587179)
          ·
            refine ⟨9635420208176426531380769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6423613472117617687587179 9635420208176426531380769)
            ·
              refine ⟨7226565156132319898535577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9635420208176426531380769 7226565156132319898535577)
              ·
                refine ⟨5419923867099239923901683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7226565156132319898535577 5419923867099239923901683)
                ·
                  refine ⟨8129885800648859885852525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5419923867099239923901683 8129885800648859885852525)
                  ·
                    refine ⟨3048707175243322457194697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8129885800648859885852525 3048707175243322457194697)
                    ·
                      refine ⟨2286530381432491842896023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3048707175243322457194697 2286530381432491842896023)
                      ·
                        rfl

theorem cell23_4453002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_4453002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4453002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4453002 prefixEnd_4453002 := by exact prefixLift 4453002
  have htrace : WordTrace (prefixWord ++ tailWord_4453002) baseStart_4453002 baseEnd_4453002 := by
    simpa [prefixWord, tailWord_4453002, baseEnd_4453002] using wordTrace_append hprefix tailTrace_4453002
  have hstable : (prefixWord ++ tailWord_4453002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4453002).length < 2 ^ (prefixWord ++ tailWord_4453002).sum := by decide
  have hdescent : baseEnd_4453002 < baseStart_4453002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4453002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4453004 : List Nat := [2, 2, 1, 2, 1, 1, 2, 3, 9]
def baseStart_4453004 : Nat := 118140960795 + 4453004 * 2 ^ 59
def prefixEnd_4453004 : Nat := 4983230072969 + 3 ^ 40 * 4453004 * 2
def baseEnd_4453004 : Nat := 254059045377088981674557

theorem tailTrace_4453004 : CollatzResearch.WordTrace tailWord_4453004 prefixEnd_4453004 254059045377088981674557 := by
  unfold tailWord_4453004
  simp only [CollatzResearch.WordTrace]
  refine ⟨81207199379767247690407033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108276265839689663587209377 81207199379767247690407033)
  ·
    refine ⟨60905399534825435767805275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81207199379767247690407033 60905399534825435767805275)
    ·
      refine ⟨91358099302238153651707913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60905399534825435767805275 91358099302238153651707913)
      ·
        refine ⟨68518574476678615238780935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91358099302238153651707913 68518574476678615238780935)
        ·
          refine ⟨102777861715017922858171403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68518574476678615238780935 102777861715017922858171403)
          ·
            refine ⟨154166792572526884287257105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102777861715017922858171403 154166792572526884287257105)
            ·
              refine ⟨115625094429395163215442829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154166792572526884287257105 115625094429395163215442829)
              ·
                refine ⟨43359410411023186205791061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115625094429395163215442829 43359410411023186205791061)
                ·
                  refine ⟨254059045377088981674557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 43359410411023186205791061 254059045377088981674557)
                  ·
                    rfl

theorem cell23_4453004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 9].length) (baseStart_4453004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4453004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4453004 prefixEnd_4453004 := by exact prefixLift 4453004
  have htrace : WordTrace (prefixWord ++ tailWord_4453004) baseStart_4453004 baseEnd_4453004 := by
    simpa [prefixWord, tailWord_4453004, baseEnd_4453004] using wordTrace_append hprefix tailTrace_4453004
  have hstable : (prefixWord ++ tailWord_4453004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4453004).length < 2 ^ (prefixWord ++ tailWord_4453004).sum := by decide
  have hdescent : baseEnd_4453004 < baseStart_4453004 := by decide
  rcases family_descends (prefixWord ++ tailWord_4453004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4453068 : List Nat := [2, 2, 1, 5, 1, 1, 1, 3, 2, 5]
def baseStart_4453068 : Nat := 118140960795 + 4453068 * 2 ^ 59
def prefixEnd_4453068 : Nat := 4983230072969 + 3 ^ 40 * 4453068 * 2
def baseEnd_4453068 : Nat := 762188090385229528223573

theorem tailTrace_4453068 : CollatzResearch.WordTrace tailWord_4453068 prefixEnd_4453068 762188090385229528223573 := by
  unfold tailWord_4453068
  simp only [CollatzResearch.WordTrace]
  refine ⟨81208366515651317155571929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108277822020868422874095905 81208366515651317155571929)
  ·
    refine ⟨60906274886738487866678947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81208366515651317155571929 60906274886738487866678947)
    ·
      refine ⟨91359412330107731800018421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60906274886738487866678947 91359412330107731800018421)
      ·
        refine ⟨8564944905947599856251727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 91359412330107731800018421 8564944905947599856251727)
        ·
          refine ⟨12847417358921399784377591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8564944905947599856251727 12847417358921399784377591)
          ·
            refine ⟨19271126038382099676566387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12847417358921399784377591 19271126038382099676566387)
            ·
              refine ⟨28906689057573149514849581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19271126038382099676566387 28906689057573149514849581)
              ·
                refine ⟨10840008396589931068068593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28906689057573149514849581 10840008396589931068068593)
                ·
                  refine ⟨8130006297442448301051445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10840008396589931068068593 8130006297442448301051445)
                  ·
                    refine ⟨762188090385229528223573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8130006297442448301051445 762188090385229528223573)
                    ·
                      rfl

theorem cell23_4453068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 2, 5].length) (baseStart_4453068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4453068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4453068 prefixEnd_4453068 := by exact prefixLift 4453068
  have htrace : WordTrace (prefixWord ++ tailWord_4453068) baseStart_4453068 baseEnd_4453068 := by
    simpa [prefixWord, tailWord_4453068, baseEnd_4453068] using wordTrace_append hprefix tailTrace_4453068
  have hstable : (prefixWord ++ tailWord_4453068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4453068).length < 2 ^ (prefixWord ++ tailWord_4453068).sum := by decide
  have hdescent : baseEnd_4453068 < baseStart_4453068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4453068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4453088 : List Nat := [2, 1, 1, 3, 1, 2, 1, 4, 2, 4, 2]
def baseStart_4453088 : Nat := 118140960795 + 4453088 * 2 ^ 59
def prefixEnd_4453088 : Nat := 4983230072969 + 3 ^ 40 * 4453088 * 2
def baseEnd_4453088 : Nat := 2286574540768778506420627

theorem tailTrace_4453088 : CollatzResearch.WordTrace tailWord_4453088 prefixEnd_4453088 2286574540768778506420627 := by
  unfold tailWord_4453088
  simp only [CollatzResearch.WordTrace]
  refine ⟨81208731245615088863435959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108278308327486785151247945 81208731245615088863435959)
  ·
    refine ⟨121813096868422633295153939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81208731245615088863435959 121813096868422633295153939)
    ·
      refine ⟨182719645302633949942730909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121813096868422633295153939 182719645302633949942730909)
      ·
        refine ⟨68519866988487731228524091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 182719645302633949942730909 68519866988487731228524091)
        ·
          refine ⟨102779800482731596842786137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68519866988487731228524091 102779800482731596842786137)
          ·
            refine ⟨77084850362048697632089603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102779800482731596842786137 77084850362048697632089603)
            ·
              refine ⟨115627275543073046448134405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77084850362048697632089603 115627275543073046448134405)
              ·
                refine ⟨21680114164326196209025201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 115627275543073046448134405 21680114164326196209025201)
                ·
                  refine ⟨16260085623244647156768901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21680114164326196209025201 16260085623244647156768901)
                  ·
                    refine ⟨3048766054358371341894169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16260085623244647156768901 3048766054358371341894169)
                    ·
                      refine ⟨2286574540768778506420627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3048766054358371341894169 2286574540768778506420627)
                      ·
                        rfl

theorem cell23_4453088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 2, 4, 2].length) (baseStart_4453088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4453088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4453088 prefixEnd_4453088 := by exact prefixLift 4453088
  have htrace : WordTrace (prefixWord ++ tailWord_4453088) baseStart_4453088 baseEnd_4453088 := by
    simpa [prefixWord, tailWord_4453088, baseEnd_4453088] using wordTrace_append hprefix tailTrace_4453088
  have hstable : (prefixWord ++ tailWord_4453088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4453088).length < 2 ^ (prefixWord ++ tailWord_4453088).sum := by decide
  have hdescent : baseEnd_4453088 < baseStart_4453088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4453088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4453098 : List Nat := [3, 1, 3, 1, 1, 1, 1, 5, 3, 4]
def baseStart_4453098 : Nat := 118140960795 + 4453098 * 2 ^ 59
def prefixEnd_4453098 : Nat := 4983230072969 + 3 ^ 40 * 4453098 * 2
def baseEnd_4453098 : Nat := 762193225191774489098527

theorem tailTrace_4453098 : CollatzResearch.WordTrace tailWord_4453098 prefixEnd_4453098 762193225191774489098527 := by
  unfold tailWord_4453098
  simp only [CollatzResearch.WordTrace]
  refine ⟨40604456805298487358683987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108278551480795966289823965 40604456805298487358683987)
  ·
    refine ⟨60906685207947731038025981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40604456805298487358683987 60906685207947731038025981)
    ·
      refine ⟨22840006952980399139259743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60906685207947731038025981 22840006952980399139259743)
      ·
        refine ⟨34260010429470598708889615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22840006952980399139259743 34260010429470598708889615)
        ·
          refine ⟨51390015644205898063334423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34260010429470598708889615 51390015644205898063334423)
          ·
            refine ⟨77085023466308847095001635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51390015644205898063334423 77085023466308847095001635)
            ·
              refine ⟨115627535199463270642502453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77085023466308847095001635 115627535199463270642502453)
              ·
                refine ⟨10840081424949681622734605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 115627535199463270642502453 10840081424949681622734605)
                ·
                  refine ⟨4065030534356130608525477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10840081424949681622734605 4065030534356130608525477)
                  ·
                    refine ⟨762193225191774489098527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4065030534356130608525477 762193225191774489098527)
                    ·
                      rfl

theorem cell23_4453098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_4453098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4453098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4453098 prefixEnd_4453098 := by exact prefixLift 4453098
  have htrace : WordTrace (prefixWord ++ tailWord_4453098) baseStart_4453098 baseEnd_4453098 := by
    simpa [prefixWord, tailWord_4453098, baseEnd_4453098] using wordTrace_append hprefix tailTrace_4453098
  have hstable : (prefixWord ++ tailWord_4453098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4453098).length < 2 ^ (prefixWord ++ tailWord_4453098).sum := by decide
  have hdescent : baseEnd_4453098 < baseStart_4453098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4453098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4453122 : List Nat := [3, 4, 1, 1, 1, 4, 1, 1, 2, 1, 4]
def baseStart_4453122 : Nat := 118140960795 + 4453122 * 2 ^ 59
def prefixEnd_4453122 : Nat := 4983230072969 + 3 ^ 40 * 4453122 * 2
def baseEnd_4453122 : Nat := 2286591999111031373395471

theorem tailTrace_4453122 : CollatzResearch.WordTrace tailWord_4453122 prefixEnd_4453122 2286591999111031373395471 := by
  unfold tailWord_4453122
  simp only [CollatzResearch.WordTrace]
  refine ⟨40604675643276750383402405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108279135048738001022406413 40604675643276750383402405)
  ·
    refine ⟨7613376683114390696887951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40604675643276750383402405 7613376683114390696887951)
    ·
      refine ⟨11420065024671586045331927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7613376683114390696887951 11420065024671586045331927)
      ·
        refine ⟨17130097537007379067997891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11420065024671586045331927 17130097537007379067997891)
        ·
          refine ⟨25695146305511068601996837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17130097537007379067997891 25695146305511068601996837)
          ·
            refine ⟨4817839932283325362874407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25695146305511068601996837 4817839932283325362874407)
            ·
              refine ⟨7226759898424988044311611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4817839932283325362874407 7226759898424988044311611)
              ·
                refine ⟨10840139847637482066467417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7226759898424988044311611 10840139847637482066467417)
                ·
                  refine ⟨8130104885728111549850563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10840139847637482066467417 8130104885728111549850563)
                  ·
                    refine ⟨12195157328592167324775845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8130104885728111549850563 12195157328592167324775845)
                    ·
                      refine ⟨2286591999111031373395471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12195157328592167324775845 2286591999111031373395471)
                      ·
                        rfl

theorem cell23_4453122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_4453122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4453122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4453122 prefixEnd_4453122 := by exact prefixLift 4453122
  have htrace : WordTrace (prefixWord ++ tailWord_4453122) baseStart_4453122 baseEnd_4453122 := by
    simpa [prefixWord, tailWord_4453122, baseEnd_4453122] using wordTrace_append hprefix tailTrace_4453122
  have hstable : (prefixWord ++ tailWord_4453122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4453122).length < 2 ^ (prefixWord ++ tailWord_4453122).sum := by decide
  have hdescent : baseEnd_4453122 < baseStart_4453122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4453122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4453205 : List Nat := [1, 3, 2, 2, 2, 1, 2, 4, 2, 4]
def baseStart_4453205 : Nat := 118140960795 + 4453205 * 2 ^ 59
def prefixEnd_4453205 : Nat := 4983230072969 + 3 ^ 40 * 4453205 * 2
def baseEnd_4453205 : Nat := 762211539335118182885863

theorem tailTrace_4453205 : CollatzResearch.WordTrace tailWord_4453205 prefixEnd_4453205 762211539335118182885863 := by
  unfold tailWord_4453205
  simp only [CollatzResearch.WordTrace]
  refine ⟨162421729831806306708881069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108281153221204204472587379 162421729831806306708881069)
  ·
    refine ⟨60908148686927365015830401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162421729831806306708881069 60908148686927365015830401)
    ·
      refine ⟨45681111515195523761872801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60908148686927365015830401 45681111515195523761872801)
      ·
        refine ⟨34260833636396642821404601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45681111515195523761872801 34260833636396642821404601)
        ·
          refine ⟨25695625227297482116053451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34260833636396642821404601 25695625227297482116053451)
          ·
            refine ⟨38543437840946223174080177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25695625227297482116053451 38543437840946223174080177)
            ·
              refine ⟨28907578380709667380560133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38543437840946223174080177 28907578380709667380560133)
              ·
                refine ⟨5420170946383062633855025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28907578380709667380560133 5420170946383062633855025)
                ·
                  refine ⟨4065128209787296975391269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5420170946383062633855025 4065128209787296975391269)
                  ·
                    refine ⟨762211539335118182885863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4065128209787296975391269 762211539335118182885863)
                    ·
                      rfl

theorem cell23_4453205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 4, 2, 4].length) (baseStart_4453205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4453205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4453205 prefixEnd_4453205 := by exact prefixLift 4453205
  have htrace : WordTrace (prefixWord ++ tailWord_4453205) baseStart_4453205 baseEnd_4453205 := by
    simpa [prefixWord, tailWord_4453205, baseEnd_4453205] using wordTrace_append hprefix tailTrace_4453205
  have hstable : (prefixWord ++ tailWord_4453205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4453205).length < 2 ^ (prefixWord ++ tailWord_4453205).sum := by decide
  have hdescent : baseEnd_4453205 < baseStart_4453205 := by decide
  rcases family_descends (prefixWord ++ tailWord_4453205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4453245 : List Nat := [1, 4, 1, 1, 2, 1, 2, 1, 6, 1, 3]
def baseStart_4453245 : Nat := 118140960795 + 4453245 * 2 ^ 59
def prefixEnd_4453245 : Nat := 4983230072969 + 3 ^ 40 * 4453245 * 2
def baseEnd_4453245 : Nat := 2286655157231534392157405

theorem tailTrace_4453245 : CollatzResearch.WordTrace tailWord_4453245 prefixEnd_4453245 2286655157231534392157405 := by
  unfold tailWord_4453245
  simp only [CollatzResearch.WordTrace]
  refine ⟨162423188751661393540337189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108282125834440929026891459 162423188751661393540337189)
  ·
    refine ⟨30454347890936511288813223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 162423188751661393540337189 30454347890936511288813223)
    ·
      refine ⟨45681521836404766933219835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30454347890936511288813223 45681521836404766933219835)
      ·
        refine ⟨68522282754607150399829753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45681521836404766933219835 68522282754607150399829753)
        ·
          refine ⟨51391712065955362799872315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68522282754607150399829753 51391712065955362799872315)
          ·
            refine ⟨77087568098933044199808473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51391712065955362799872315 77087568098933044199808473)
            ·
              refine ⟨57815676074199783149856355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77087568098933044199808473 57815676074199783149856355)
              ·
                refine ⟨86723514111299674724784533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57815676074199783149856355 86723514111299674724784533)
                ·
                  refine ⟨4065164723967172252724275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 86723514111299674724784533 4065164723967172252724275)
                  ·
                    refine ⟨6097747085950758379086413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4065164723967172252724275 6097747085950758379086413)
                    ·
                      refine ⟨2286655157231534392157405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6097747085950758379086413 2286655157231534392157405)
                      ·
                        rfl

theorem cell23_4453245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 6, 1, 3].length) (baseStart_4453245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4453245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4453245 prefixEnd_4453245 := by exact prefixLift 4453245
  have htrace : WordTrace (prefixWord ++ tailWord_4453245) baseStart_4453245 baseEnd_4453245 := by
    simpa [prefixWord, tailWord_4453245, baseEnd_4453245] using wordTrace_append hprefix tailTrace_4453245
  have hstable : (prefixWord ++ tailWord_4453245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4453245).length < 2 ^ (prefixWord ++ tailWord_4453245).sum := by decide
  have hdescent : baseEnd_4453245 < baseStart_4453245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4453245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4453246 : List Nat := [4, 2, 3, 1, 2, 1, 3, 1, 1, 1, 4]
def baseStart_4453246 : Nat := 118140960795 + 4453246 * 2 ^ 59
def prefixEnd_4453246 : Nat := 4983230072969 + 3 ^ 40 * 4453246 * 2
def baseEnd_4453246 : Nat := 2286655670712188888244901

theorem tailTrace_4453246 : CollatzResearch.WordTrace tailWord_4453246 prefixEnd_4453246 2286655670712188888244901 := by
  unfold tailWord_4453246
  simp only [CollatzResearch.WordTrace]
  refine ⟨20302903153082221338890449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108282150149771847140749061 20302903153082221338890449)
  ·
    refine ⟨15227177364811666004167837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20302903153082221338890449 15227177364811666004167837)
    ·
      refine ⟨5710191511804374751562939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15227177364811666004167837 5710191511804374751562939)
      ·
        refine ⟨8565287267706562127344409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5710191511804374751562939 8565287267706562127344409)
        ·
          refine ⟨6423965450779921595508307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8565287267706562127344409 6423965450779921595508307)
          ·
            refine ⟨9635948176169882393262461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6423965450779921595508307 9635948176169882393262461)
            ·
              refine ⟨3613480566063705897473423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9635948176169882393262461 3613480566063705897473423)
              ·
                refine ⟨5420220849095558846210135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3613480566063705897473423 5420220849095558846210135)
                ·
                  refine ⟨8130331273643338269315203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5420220849095558846210135 8130331273643338269315203)
                  ·
                    refine ⟨12195496910465007403972805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8130331273643338269315203 12195496910465007403972805)
                    ·
                      refine ⟨2286655670712188888244901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12195496910465007403972805 2286655670712188888244901)
                      ·
                        rfl

theorem cell23_4453246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_4453246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4453246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4453246 prefixEnd_4453246 := by exact prefixLift 4453246
  have htrace : WordTrace (prefixWord ++ tailWord_4453246) baseStart_4453246 baseEnd_4453246 := by
    simpa [prefixWord, tailWord_4453246, baseEnd_4453246] using wordTrace_append hprefix tailTrace_4453246
  have hstable : (prefixWord ++ tailWord_4453246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4453246).length < 2 ^ (prefixWord ++ tailWord_4453246).sum := by decide
  have hdescent : baseEnd_4453246 < baseStart_4453246 := by decide
  rcases family_descends (prefixWord ++ tailWord_4453246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4453319 : List Nat := [1, 1, 4, 1, 1, 2, 5, 2, 2, 2, 2]
def baseStart_4453319 : Nat := 118140960795 + 4453319 * 2 ^ 59
def prefixEnd_4453319 : Nat := 4983230072969 + 3 ^ 40 * 4453319 * 2
def baseEnd_4453319 : Nat := 2286693154799967102632065

theorem tailTrace_4453319 : CollatzResearch.WordTrace tailWord_4453319 prefixEnd_4453319 2286693154799967102632065 := by
  unfold tailWord_4453319
  simp only [CollatzResearch.WordTrace]
  refine ⟨162425887753393304178531011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108283925168928869452354007 162425887753393304178531011)
  ·
    refine ⟨243638831630089956267796517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162425887753393304178531011 243638831630089956267796517)
    ·
      refine ⟨45682280930641866800211847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 243638831630089956267796517 45682280930641866800211847)
      ·
        refine ⟨68523421395962800200317771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45682280930641866800211847 68523421395962800200317771)
        ·
          refine ⟨102785132093944200300476657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68523421395962800200317771 102785132093944200300476657)
          ·
            refine ⟨77088849070458150225357493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102785132093944200300476657 77088849070458150225357493)
            ·
              refine ⟨7227079600355451583627265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 77088849070458150225357493 7227079600355451583627265)
              ·
                refine ⟨5420309700266588687720449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7227079600355451583627265 5420309700266588687720449)
                ·
                  refine ⟨4065232275199941515790337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5420309700266588687720449 4065232275199941515790337)
                  ·
                    refine ⟨3048924206399956136842753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4065232275199941515790337 3048924206399956136842753)
                    ·
                      refine ⟨2286693154799967102632065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3048924206399956136842753 2286693154799967102632065)
                      ·
                        rfl

theorem cell23_4453319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 2, 2, 2, 2].length) (baseStart_4453319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4453319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4453319 prefixEnd_4453319 := by exact prefixLift 4453319
  have htrace : WordTrace (prefixWord ++ tailWord_4453319) baseStart_4453319 baseEnd_4453319 := by
    simpa [prefixWord, tailWord_4453319, baseEnd_4453319] using wordTrace_append hprefix tailTrace_4453319
  have hstable : (prefixWord ++ tailWord_4453319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4453319).length < 2 ^ (prefixWord ++ tailWord_4453319).sum := by decide
  have hdescent : baseEnd_4453319 < baseStart_4453319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4453319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4453336 : List Nat := [2, 1, 2, 2, 2, 4, 3, 1, 2, 2, 2]
def baseStart_4453336 : Nat := 118140960795 + 4453336 * 2 ^ 59
def prefixEnd_4453336 : Nat := 4983230072969 + 3 ^ 40 * 4453336 * 2
def baseEnd_4453336 : Nat := 2286701883971093536119487

theorem tailTrace_4453336 : CollatzResearch.WordTrace tailWord_4453336 prefixEnd_4453336 2286701883971093536119487 := by
  unfold tailWord_4453336
  simp only [CollatzResearch.WordTrace]
  refine ⟨81213253897165858040949931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108284338529554477387933241 81213253897165858040949931)
  ·
    refine ⟨121819880845748787061424897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81213253897165858040949931 121819880845748787061424897)
    ·
      refine ⟨91364910634311590296068673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121819880845748787061424897 91364910634311590296068673)
      ·
        refine ⟨68523682975733692722051505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91364910634311590296068673 68523682975733692722051505)
        ·
          refine ⟨51392762231800269541538629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68523682975733692722051505 51392762231800269541538629)
          ·
            refine ⟨9636142918462550539038493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51392762231800269541538629 9636142918462550539038493)
            ·
              refine ⟨3613553594423456452139435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9636142918462550539038493 3613553594423456452139435)
              ·
                refine ⟨5420330391635184678209153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3613553594423456452139435 5420330391635184678209153)
                ·
                  refine ⟨4065247793726388508656865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5420330391635184678209153 4065247793726388508656865)
                  ·
                    refine ⟨3048935845294791381492649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4065247793726388508656865 3048935845294791381492649)
                    ·
                      refine ⟨2286701883971093536119487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3048935845294791381492649 2286701883971093536119487)
                      ·
                        rfl

theorem cell23_4453336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 1, 2, 2, 2].length) (baseStart_4453336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4453336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4453336 prefixEnd_4453336 := by exact prefixLift 4453336
  have htrace : WordTrace (prefixWord ++ tailWord_4453336) baseStart_4453336 baseEnd_4453336 := by
    simpa [prefixWord, tailWord_4453336, baseEnd_4453336] using wordTrace_append hprefix tailTrace_4453336
  have hstable : (prefixWord ++ tailWord_4453336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4453336).length < 2 ^ (prefixWord ++ tailWord_4453336).sum := by decide
  have hdescent : baseEnd_4453336 < baseStart_4453336 := by decide
  rcases family_descends (prefixWord ++ tailWord_4453336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4453348 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 3, 1, 7]
def baseStart_4453348 : Nat := 118140960795 + 4453348 * 2 ^ 59
def prefixEnd_4453348 : Nat := 4983230072969 + 3 ^ 40 * 4453348 * 2
def baseEnd_4453348 : Nat := 2286708045738947489169431

theorem tailTrace_4453348 : CollatzResearch.WordTrace tailWord_4453348 prefixEnd_4453348 2286708045738947489169431 := by
  unfold tailWord_4453348
  simp only [CollatzResearch.WordTrace]
  refine ⟨81213472735144121065668349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108284630313525494754224465 81213472735144121065668349)
  ·
    refine ⟨30455052275679045399625631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81213472735144121065668349 30455052275679045399625631)
    ·
      refine ⟨45682578413518568099438447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30455052275679045399625631 45682578413518568099438447)
      ·
        refine ⟨68523867620277852149157671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45682578413518568099438447 68523867620277852149157671)
        ·
          refine ⟨102785801430416778223736507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68523867620277852149157671 102785801430416778223736507)
          ·
            refine ⟨154178702145625167335604761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102785801430416778223736507 154178702145625167335604761)
            ·
              refine ⟨115634026609218875501703571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154178702145625167335604761 115634026609218875501703571)
              ·
                refine ⟨173451039913828313252555357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115634026609218875501703571 173451039913828313252555357)
                ·
                  refine ⟨65044139967685617469708259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 173451039913828313252555357 65044139967685617469708259)
                  ·
                    refine ⟨97566209951528426204562389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 65044139967685617469708259 97566209951528426204562389)
                    ·
                      refine ⟨2286708045738947489169431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 97566209951528426204562389 2286708045738947489169431)
                      ·
                        rfl

theorem cell23_4453348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_4453348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4453348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4453348 prefixEnd_4453348 := by exact prefixLift 4453348
  have htrace : WordTrace (prefixWord ++ tailWord_4453348) baseStart_4453348 baseEnd_4453348 := by
    simpa [prefixWord, tailWord_4453348, baseEnd_4453348] using wordTrace_append hprefix tailTrace_4453348
  have hstable : (prefixWord ++ tailWord_4453348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4453348).length < 2 ^ (prefixWord ++ tailWord_4453348).sum := by decide
  have hdescent : baseEnd_4453348 < baseStart_4453348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4453348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4453395 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 6, 2, 3]
def baseStart_4453395 : Nat := 118140960795 + 4453395 * 2 ^ 59
def prefixEnd_4453395 : Nat := 4983230072969 + 3 ^ 40 * 4453395 * 2
def baseEnd_4453395 : Nat := 2286732179329708805281715

theorem tailTrace_4453395 : CollatzResearch.WordTrace tailWord_4453395 prefixEnd_4453395 2286732179329708805281715 := by
  unfold tailWord_4453395
  simp only [CollatzResearch.WordTrace]
  refine ⟨162428659701117969158297639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108285773134078646105531759 162428659701117969158297639)
  ·
    refine ⟨243642989551676953737446459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162428659701117969158297639 243642989551676953737446459)
    ·
      refine ⟨365464484327515430606169689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243642989551676953737446459 365464484327515430606169689)
      ·
        refine ⟨274098363245636572954627267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 365464484327515430606169689 274098363245636572954627267)
        ·
          refine ⟨411147544868454859431940901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 274098363245636572954627267 411147544868454859431940901)
          ·
            refine ⟨77090164662835286143488919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 411147544868454859431940901 77090164662835286143488919)
            ·
              refine ⟨115635246994252929215233379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77090164662835286143488919 115635246994252929215233379)
              ·
                refine ⟨173452870491379393822850069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115635246994252929215233379 173452870491379393822850069)
                ·
                  refine ⟨8130603304283409085446097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 173452870491379393822850069 8130603304283409085446097)
                  ·
                    refine ⟨6097952478212556814084573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8130603304283409085446097 6097952478212556814084573)
                    ·
                      refine ⟨2286732179329708805281715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6097952478212556814084573 2286732179329708805281715)
                      ·
                        rfl

theorem cell23_4453395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 6, 2, 3].length) (baseStart_4453395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4453395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4453395 prefixEnd_4453395 := by exact prefixLift 4453395
  have htrace : WordTrace (prefixWord ++ tailWord_4453395) baseStart_4453395 baseEnd_4453395 := by
    simpa [prefixWord, tailWord_4453395, baseEnd_4453395] using wordTrace_append hprefix tailTrace_4453395
  have hstable : (prefixWord ++ tailWord_4453395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4453395).length < 2 ^ (prefixWord ++ tailWord_4453395).sum := by decide
  have hdescent : baseEnd_4453395 < baseStart_4453395 := by decide
  rcases family_descends (prefixWord ++ tailWord_4453395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4453432 : List Nat := [2, 1, 2, 1, 5, 2, 2, 2, 6]
def baseStart_4453432 : Nat := 118140960795 + 4453432 * 2 ^ 59
def prefixEnd_4453432 : Nat := 4983230072969 + 3 ^ 40 * 4453432 * 2
def baseEnd_4453432 : Nat := 254083464234880573391005

theorem tailTrace_4453432 : CollatzResearch.WordTrace tailWord_4453432 prefixEnd_4453432 254083464234880573391005 := by
  unfold tailWord_4453432
  simp only [CollatzResearch.WordTrace]
  refine ⟨81215004600991962238697275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108286672801322616318263033 81215004600991962238697275)
  ·
    refine ⟨121822506901487943358045913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81215004600991962238697275 121822506901487943358045913)
    ·
      refine ⟨91366880176115957518534435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121822506901487943358045913 91366880176115957518534435)
      ·
        refine ⟨137050320264173936277801653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91366880176115957518534435 137050320264173936277801653)
        ·
          refine ⟨12848467524766306526043905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 137050320264173936277801653 12848467524766306526043905)
          ·
            refine ⟨9636350643574729894532929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12848467524766306526043905 9636350643574729894532929)
            ·
              refine ⟨7227262982681047420899697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9636350643574729894532929 7227262982681047420899697)
              ·
                refine ⟨5420447237010785565674773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7227262982681047420899697 5420447237010785565674773)
                ·
                  refine ⟨254083464234880573391005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5420447237010785565674773 254083464234880573391005)
                  ·
                    rfl

theorem cell23_4453432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 2, 6].length) (baseStart_4453432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4453432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4453432 prefixEnd_4453432 := by exact prefixLift 4453432
  have htrace : WordTrace (prefixWord ++ tailWord_4453432) baseStart_4453432 baseEnd_4453432 := by
    simpa [prefixWord, tailWord_4453432, baseEnd_4453432] using wordTrace_append hprefix tailTrace_4453432
  have hstable : (prefixWord ++ tailWord_4453432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4453432).length < 2 ^ (prefixWord ++ tailWord_4453432).sum := by decide
  have hdescent : baseEnd_4453432 < baseStart_4453432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4453432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4453436 : List Nat := [2, 2, 2, 2, 2, 2, 4, 2, 1, 4]
def baseStart_4453436 : Nat := 118140960795 + 4453436 * 2 ^ 59
def prefixEnd_4453436 : Nat := 4983230072969 + 3 ^ 40 * 4453436 * 2
def baseEnd_4453436 : Nat := 762251077345514381623009

theorem tailTrace_4453436 : CollatzResearch.WordTrace tailWord_4453436 prefixEnd_4453436 762251077345514381623009 := by
  unfold tailWord_4453436
  simp only [CollatzResearch.WordTrace]
  refine ⟨81215077546984716580270081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108286770062646288773693441 81215077546984716580270081)
  ·
    refine ⟨60911308160238537435202561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81215077546984716580270081 60911308160238537435202561)
    ·
      refine ⟨45683481120178903076401921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60911308160238537435202561 45683481120178903076401921)
      ·
        refine ⟨34262610840134177307301441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45683481120178903076401921 34262610840134177307301441)
        ·
          refine ⟨25696958130100632980476081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34262610840134177307301441 25696958130100632980476081)
          ·
            refine ⟨19272718597575474735357061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25696958130100632980476081 19272718597575474735357061)
            ·
              refine ⟨3613634737045401512879449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19272718597575474735357061 3613634737045401512879449)
              ·
                refine ⟨2710226052784051134659587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3613634737045401512879449 2710226052784051134659587)
                ·
                  refine ⟨4065339079176076701989381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2710226052784051134659587 4065339079176076701989381)
                  ·
                    refine ⟨762251077345514381623009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4065339079176076701989381 762251077345514381623009)
                    ·
                      rfl

theorem cell23_4453436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 2, 1, 4].length) (baseStart_4453436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4453436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4453436 prefixEnd_4453436 := by exact prefixLift 4453436
  have htrace : WordTrace (prefixWord ++ tailWord_4453436) baseStart_4453436 baseEnd_4453436 := by
    simpa [prefixWord, tailWord_4453436, baseEnd_4453436] using wordTrace_append hprefix tailTrace_4453436
  have hstable : (prefixWord ++ tailWord_4453436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4453436).length < 2 ^ (prefixWord ++ tailWord_4453436).sum := by decide
  have hdescent : baseEnd_4453436 < baseStart_4453436 := by decide
  rcases family_descends (prefixWord ++ tailWord_4453436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4453445 : List Nat := [1, 3, 1, 1, 1, 3, 3, 2, 3, 5]
def baseStart_4453445 : Nat := 118140960795 + 4453445 * 2 ^ 59
def prefixEnd_4453445 : Nat := 4983230072969 + 3 ^ 40 * 4453445 * 2
def baseEnd_4453445 : Nat := 762252617787477869885495

theorem tailTrace_4453445 : CollatzResearch.WordTrace tailWord_4453445 prefixEnd_4453445 762252617787477869885495 := by
  unfold tailWord_4453445
  simp only [CollatzResearch.WordTrace]
  refine ⟨162430483350936827697617789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108286988900624551798411859 162430483350936827697617789)
  ·
    refine ⟨60911431256601310386606671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162430483350936827697617789 60911431256601310386606671)
    ·
      refine ⟨91367146884901965579910007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60911431256601310386606671 91367146884901965579910007)
      ·
        refine ⟨137050720327352948369865011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91367146884901965579910007 137050720327352948369865011)
        ·
          refine ⟨205576080491029422554797517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137050720327352948369865011 205576080491029422554797517)
          ·
            refine ⟨77091030184136033458049069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 205576080491029422554797517 77091030184136033458049069)
            ·
              refine ⟨28909136319051012546768401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77091030184136033458049069 28909136319051012546768401)
              ·
                refine ⟨21681852239288259410076301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28909136319051012546768401 21681852239288259410076301)
                ·
                  refine ⟨8130694589733097278778613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21681852239288259410076301 8130694589733097278778613)
                  ·
                    refine ⟨762252617787477869885495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8130694589733097278778613 762252617787477869885495)
                    ·
                      rfl

theorem cell23_4453445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 3, 5].length) (baseStart_4453445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4453445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4453445 prefixEnd_4453445 := by exact prefixLift 4453445
  have htrace : WordTrace (prefixWord ++ tailWord_4453445) baseStart_4453445 baseEnd_4453445 := by
    simpa [prefixWord, tailWord_4453445, baseEnd_4453445] using wordTrace_append hprefix tailTrace_4453445
  have hstable : (prefixWord ++ tailWord_4453445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4453445).length < 2 ^ (prefixWord ++ tailWord_4453445).sum := by decide
  have hdescent : baseEnd_4453445 < baseStart_4453445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4453445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4453452 : List Nat := [2, 2, 1, 3, 1, 1, 1, 4, 1, 5, 2]
def baseStart_4453452 : Nat := 118140960795 + 4453452 * 2 ^ 59
def prefixEnd_4453452 : Nat := 4983230072969 + 3 ^ 40 * 4453452 * 2
def baseEnd_4453452 : Nat := 2286761447727015082268953

theorem tailTrace_4453452 : CollatzResearch.WordTrace tailWord_4453452 prefixEnd_4453452 2286761447727015082268953 := by
  unfold tailWord_4453452
  simp only [CollatzResearch.WordTrace]
  refine ⟨81215369330955733946561305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108287159107940978595415073 81215369330955733946561305)
  ·
    refine ⟨60911526998216800459920979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81215369330955733946561305 60911526998216800459920979)
    ·
      refine ⟨91367290497325200689881469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60911526998216800459920979 91367290497325200689881469)
      ·
        refine ⟨34262733936496950258705551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91367290497325200689881469 34262733936496950258705551)
        ·
          refine ⟨51394100904745425388058327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34262733936496950258705551 51394100904745425388058327)
          ·
            refine ⟨77091151357118138082087491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51394100904745425388058327 77091151357118138082087491)
            ·
              refine ⟨115636727035677207123131237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77091151357118138082087491 115636727035677207123131237)
              ·
                refine ⟨21681886319189476335587107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 115636727035677207123131237 21681886319189476335587107)
                ·
                  refine ⟨32522829478784214503380661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21681886319189476335587107 32522829478784214503380661)
                  ·
                    refine ⟨3049015263636020109691937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32522829478784214503380661 3049015263636020109691937)
                    ·
                      refine ⟨2286761447727015082268953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3049015263636020109691937 2286761447727015082268953)
                      ·
                        rfl

theorem cell23_4453452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 1, 5, 2].length) (baseStart_4453452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4453452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4453452 prefixEnd_4453452 := by exact prefixLift 4453452
  have htrace : WordTrace (prefixWord ++ tailWord_4453452) baseStart_4453452 baseEnd_4453452 := by
    simpa [prefixWord, tailWord_4453452, baseEnd_4453452] using wordTrace_append hprefix tailTrace_4453452
  have hstable : (prefixWord ++ tailWord_4453452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4453452).length < 2 ^ (prefixWord ++ tailWord_4453452).sum := by decide
  have hdescent : baseEnd_4453452 < baseStart_4453452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4453452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4453470 : List Nat := [4, 4, 1, 1, 1, 2, 2, 3, 1, 4]
def baseStart_4453470 : Nat := 118140960795 + 4453470 * 2 ^ 59
def prefixEnd_4453470 : Nat := 4983230072969 + 3 ^ 40 * 4453470 * 2
def baseEnd_4453470 : Nat := 762256896792932003947957

theorem tailTrace_4453470 : CollatzResearch.WordTrace tailWord_4453470 prefixEnd_4453470 762256896792932003947957 := by
  unfold tailWord_4453470
  simp only [CollatzResearch.WordTrace]
  refine ⟨20303924396980782120909733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108287596783897504644851909 20303924396980782120909733)
  ·
    refine ⟨3806985824433896647670575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20303924396980782120909733 3806985824433896647670575)
    ·
      refine ⟨5710478736650844971505863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3806985824433896647670575 5710478736650844971505863)
      ·
        refine ⟨8565718104976267457258795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5710478736650844971505863 8565718104976267457258795)
        ·
          refine ⟨12848577157464401185888193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8565718104976267457258795 12848577157464401185888193)
          ·
            refine ⟨9636432868098300889416145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12848577157464401185888193 9636432868098300889416145)
            ·
              refine ⟨7227324651073725667062109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9636432868098300889416145 7227324651073725667062109)
              ·
                refine ⟨2710246744152647125148291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7227324651073725667062109 2710246744152647125148291)
                ·
                  refine ⟨4065370116228970687722437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2710246744152647125148291 4065370116228970687722437)
                  ·
                    refine ⟨762256896792932003947957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4065370116228970687722437 762256896792932003947957)
                    ·
                      rfl

theorem cell23_4453470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_4453470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4453470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4453470 prefixEnd_4453470 := by exact prefixLift 4453470
  have htrace : WordTrace (prefixWord ++ tailWord_4453470) baseStart_4453470 baseEnd_4453470 := by
    simpa [prefixWord, tailWord_4453470, baseEnd_4453470] using wordTrace_append hprefix tailTrace_4453470
  have hstable : (prefixWord ++ tailWord_4453470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4453470).length < 2 ^ (prefixWord ++ tailWord_4453470).sum := by decide
  have hdescent : baseEnd_4453470 < baseStart_4453470 := by decide
  rcases family_descends (prefixWord ++ tailWord_4453470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4453479 : List Nat := [1, 1, 5, 1, 1, 3, 4, 1, 1, 5]
def baseStart_4453479 : Nat := 118140960795 + 4453479 * 2 ^ 59
def prefixEnd_4453479 : Nat := 4983230072969 + 3 ^ 40 * 4453479 * 2
def baseEnd_4453479 : Nat := 762258437234895492210443

theorem tailTrace_4453479 : CollatzResearch.WordTrace tailWord_4453479 prefixEnd_4453479 762258437234895492210443 := by
  unfold tailWord_4453479
  simp only [CollatzResearch.WordTrace]
  refine ⟨162431723432813651504355491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108287815621875767669570327 162431723432813651504355491)
  ·
    refine ⟨243647585149220477256533237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162431723432813651504355491 243647585149220477256533237)
    ·
      refine ⟨22841961107739419742799991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 243647585149220477256533237 22841961107739419742799991)
      ·
        refine ⟨34262941661609129614199987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22841961107739419742799991 34262941661609129614199987)
        ·
          refine ⟨51394412492413694421299981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34262941661609129614199987 51394412492413694421299981)
          ·
            refine ⟨19272904684655135407987493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51394412492413694421299981 19272904684655135407987493)
            ·
              refine ⟨3613669628372837888997655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19272904684655135407987493 3613669628372837888997655)
              ·
                refine ⟨5420504442559256833496483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3613669628372837888997655 5420504442559256833496483)
                ·
                  refine ⟨8130756663838885250244725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5420504442559256833496483 8130756663838885250244725)
                  ·
                    refine ⟨762258437234895492210443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8130756663838885250244725 762258437234895492210443)
                    ·
                      rfl

theorem cell23_4453479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_4453479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4453479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4453479 prefixEnd_4453479 := by exact prefixLift 4453479
  have htrace : WordTrace (prefixWord ++ tailWord_4453479) baseStart_4453479 baseEnd_4453479 := by
    simpa [prefixWord, tailWord_4453479, baseEnd_4453479] using wordTrace_append hprefix tailTrace_4453479
  have hstable : (prefixWord ++ tailWord_4453479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4453479).length < 2 ^ (prefixWord ++ tailWord_4453479).sum := by decide
  have hdescent : baseEnd_4453479 < baseStart_4453479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4453479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4453493 : List Nat := [1, 3, 4, 3, 1, 1, 2, 1, 3, 1, 3]
def baseStart_4453493 : Nat := 118140960795 + 4453493 * 2 ^ 59
def prefixEnd_4453493 : Nat := 4983230072969 + 3 ^ 40 * 4453493 * 2
def baseEnd_4453493 : Nat := 2286782500433849421856265

theorem tailTrace_4453493 : CollatzResearch.WordTrace tailWord_4453493 prefixEnd_4453493 2286782500433849421856265 := by
  unfold tailWord_4453493
  simp only [CollatzResearch.WordTrace]
  refine ⟨162432234054762931895365133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108288156036508621263576755 162432234054762931895365133)
  ·
    refine ⟨60912087770536099460761925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162432234054762931895365133 60912087770536099460761925)
    ·
      refine ⟨11421016456975518648892861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60912087770536099460761925 11421016456975518648892861)
      ·
        refine ⟨4282881171365819493334823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11421016456975518648892861 4282881171365819493334823)
        ·
          refine ⟨6424321757048729240002235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4282881171365819493334823 6424321757048729240002235)
          ·
            refine ⟨9636482635573093860003353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6424321757048729240002235 9636482635573093860003353)
            ·
              refine ⟨7227361976679820395002515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9636482635573093860003353 7227361976679820395002515)
              ·
                refine ⟨10841042965019730592503773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7227361976679820395002515 10841042965019730592503773)
                ·
                  refine ⟨4065391111882398972188915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10841042965019730592503773 4065391111882398972188915)
                  ·
                    refine ⟨6098086667823598458283373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4065391111882398972188915 6098086667823598458283373)
                    ·
                      refine ⟨2286782500433849421856265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6098086667823598458283373 2286782500433849421856265)
                      ·
                        rfl

theorem cell23_4453493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_4453493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4453493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4453493 prefixEnd_4453493 := by exact prefixLift 4453493
  have htrace : WordTrace (prefixWord ++ tailWord_4453493) baseStart_4453493 baseEnd_4453493 := by
    simpa [prefixWord, tailWord_4453493, baseEnd_4453493] using wordTrace_append hprefix tailTrace_4453493
  have hstable : (prefixWord ++ tailWord_4453493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4453493).length < 2 ^ (prefixWord ++ tailWord_4453493).sum := by decide
  have hdescent : baseEnd_4453493 < baseStart_4453493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4453493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4453495 : List Nat := [1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 6]
def baseStart_4453495 : Nat := 118140960795 + 4453495 * 2 ^ 59
def prefixEnd_4453495 : Nat := 4983230072969 + 3 ^ 40 * 4453495 * 2
def baseEnd_4453495 : Nat := 2286783527395158414031255

theorem tailTrace_4453495 : CollatzResearch.WordTrace tailWord_4453495 prefixEnd_4453495 2286783527395158414031255 := by
  unfold tailWord_4453495
  simp only [CollatzResearch.WordTrace]
  refine ⟨162432307000755686236937939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108288204667170457491291959 162432307000755686236937939)
  ·
    refine ⟨243648460501133529355406909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162432307000755686236937939 243648460501133529355406909)
    ·
      refine ⟨91368172687925073508277591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 243648460501133529355406909 91368172687925073508277591)
      ·
        refine ⟨137052259031887610262416387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91368172687925073508277591 137052259031887610262416387)
        ·
          refine ⟨205578388547831415393624581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137052259031887610262416387 205578388547831415393624581)
          ·
            refine ⟨38545947852718390386304609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 205578388547831415393624581 38545947852718390386304609)
            ·
              refine ⟨28909460889538792789728457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38545947852718390386304609 28909460889538792789728457)
              ·
                refine ⟨21682095667154094592296343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28909460889538792789728457 21682095667154094592296343)
                ·
                  refine ⟨32523143500731141888444515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21682095667154094592296343 32523143500731141888444515)
                  ·
                    refine ⟨48784715251096712832666773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32523143500731141888444515 48784715251096712832666773)
                    ·
                      refine ⟨2286783527395158414031255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48784715251096712832666773 2286783527395158414031255)
                      ·
                        rfl

theorem cell23_4453495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 6].length) (baseStart_4453495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4453495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4453495 prefixEnd_4453495 := by exact prefixLift 4453495
  have htrace : WordTrace (prefixWord ++ tailWord_4453495) baseStart_4453495 baseEnd_4453495 := by
    simpa [prefixWord, tailWord_4453495, baseEnd_4453495] using wordTrace_append hprefix tailTrace_4453495
  have hstable : (prefixWord ++ tailWord_4453495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4453495).length < 2 ^ (prefixWord ++ tailWord_4453495).sum := by decide
  have hdescent : baseEnd_4453495 < baseStart_4453495 := by decide
  rcases family_descends (prefixWord ++ tailWord_4453495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4453509 : List Nat := [1, 3, 1, 1, 6, 2, 1, 1, 1, 6]
def baseStart_4453509 : Nat := 118140960795 + 4453509 * 2 ^ 59
def prefixEnd_4453509 : Nat := 4983230072969 + 3 ^ 40 * 4453509 * 2
def baseEnd_4453509 : Nat := 762263572041440453085397

theorem tailTrace_4453509 : CollatzResearch.WordTrace tailWord_4453509 prefixEnd_4453509 762263572041440453085397 := by
  unfold tailWord_4453509
  simp only [CollatzResearch.WordTrace]
  refine ⟨162432817622704966627947581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108288545081803311085298387 162432817622704966627947581)
  ·
    refine ⟨60912306608514362485480343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162432817622704966627947581 60912306608514362485480343)
    ·
      refine ⟨91368459912771543728220515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60912306608514362485480343 91368459912771543728220515)
      ·
        refine ⟨137052689869157315592330773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91368459912771543728220515 137052689869157315592330773)
        ·
          refine ⟨6424344837616749168390505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 137052689869157315592330773 6424344837616749168390505)
          ·
            refine ⟨4818258628212561876292879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6424344837616749168390505 4818258628212561876292879)
            ·
              refine ⟨7227387942318842814439319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4818258628212561876292879 7227387942318842814439319)
              ·
                refine ⟨10841081913478264221658979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7227387942318842814439319 10841081913478264221658979)
                ·
                  refine ⟨16261622870217396332488469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10841081913478264221658979 16261622870217396332488469)
                  ·
                    refine ⟨762263572041440453085397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16261622870217396332488469 762263572041440453085397)
                    ·
                      rfl

theorem cell23_4453509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 6].length) (baseStart_4453509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4453509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4453509 prefixEnd_4453509 := by exact prefixLift 4453509
  have htrace : WordTrace (prefixWord ++ tailWord_4453509) baseStart_4453509 baseEnd_4453509 := by
    simpa [prefixWord, tailWord_4453509, baseEnd_4453509] using wordTrace_append hprefix tailTrace_4453509
  have hstable : (prefixWord ++ tailWord_4453509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4453509).length < 2 ^ (prefixWord ++ tailWord_4453509).sum := by decide
  have hdescent : baseEnd_4453509 < baseStart_4453509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4453509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4453522 : List Nat := [3, 2, 3, 1, 1, 3, 1, 9]
def baseStart_4453522 : Nat := 118140960795 + 4453522 * 2 ^ 59
def prefixEnd_4453522 : Nat := 4983230072969 + 3 ^ 40 * 4453522 * 2
def baseEnd_4453522 : Nat := 84696199680475178088653

theorem tailTrace_4453522 : CollatzResearch.WordTrace tailWord_4453522 prefixEnd_4453522 84696199680475178088653 := by
  unfold tailWord_4453522
  simp only [CollatzResearch.WordTrace]
  refine ⟨40608322942914467462042705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108288861181105246565447213 40608322942914467462042705)
  ·
    refine ⟨30456242207185850596532029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40608322942914467462042705 30456242207185850596532029)
    ·
      refine ⟨11421090827694693973699511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30456242207185850596532029 11421090827694693973699511)
      ·
        refine ⟨17131636241542040960549267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11421090827694693973699511 17131636241542040960549267)
        ·
          refine ⟨25697454362313061440823901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17131636241542040960549267 25697454362313061440823901)
          ·
            refine ⟨9636545385867398040308963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25697454362313061440823901 9636545385867398040308963)
            ·
              refine ⟨14454818078801097060463445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9636545385867398040308963 14454818078801097060463445)
              ·
                refine ⟨84696199680475178088653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14454818078801097060463445 84696199680475178088653)
                ·
                  rfl

theorem cell23_4453522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 9].length) (baseStart_4453522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4453522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4453522 prefixEnd_4453522 := by exact prefixLift 4453522
  have htrace : WordTrace (prefixWord ++ tailWord_4453522) baseStart_4453522 baseEnd_4453522 := by
    simpa [prefixWord, tailWord_4453522, baseEnd_4453522] using wordTrace_append hprefix tailTrace_4453522
  have hstable : (prefixWord ++ tailWord_4453522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4453522).length < 2 ^ (prefixWord ++ tailWord_4453522).sum := by decide
  have hdescent : baseEnd_4453522 < baseStart_4453522 := by decide
  rcases family_descends (prefixWord ++ tailWord_4453522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4453559 : List Nat := [1, 1, 3, 1, 4, 1, 2, 2, 3, 3, 2]
def baseStart_4453559 : Nat := 118140960795 + 4453559 * 2 ^ 59
def prefixEnd_4453559 : Nat := 4983230072969 + 3 ^ 40 * 4453559 * 2
def baseEnd_4453559 : Nat := 2286816390157046163630961

theorem tailTrace_4453559 : CollatzResearch.WordTrace tailWord_4453559 prefixEnd_4453559 2286816390157046163630961 := by
  unfold tailWord_4453559
  simp only [CollatzResearch.WordTrace]
  refine ⟨162434641272523825167267731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108289760848349216778178487 162434641272523825167267731)
  ·
    refine ⟨243651961908785737750901597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162434641272523825167267731 243651961908785737750901597)
    ·
      refine ⟨91369485715794651656588099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 243651961908785737750901597 91369485715794651656588099)
      ·
        refine ⟨137054228573691977484882149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91369485715794651656588099 137054228573691977484882149)
        ·
          refine ⟨25697667857567245778415403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 137054228573691977484882149 25697667857567245778415403)
          ·
            refine ⟨38546501786350868667623105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25697667857567245778415403 38546501786350868667623105)
            ·
              refine ⟨28909876339763151500717329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38546501786350868667623105 28909876339763151500717329)
              ·
                refine ⟨21682407254822363625537997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28909876339763151500717329 21682407254822363625537997)
                ·
                  refine ⟨8130902720558386359576749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21682407254822363625537997 8130902720558386359576749)
                  ·
                    refine ⟨3049088520209394884841281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8130902720558386359576749 3049088520209394884841281)
                    ·
                      refine ⟨2286816390157046163630961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3049088520209394884841281 2286816390157046163630961)
                      ·
                        rfl

theorem cell23_4453559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 3, 3, 2].length) (baseStart_4453559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4453559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4453559 prefixEnd_4453559 := by exact prefixLift 4453559
  have htrace : WordTrace (prefixWord ++ tailWord_4453559) baseStart_4453559 baseEnd_4453559 := by
    simpa [prefixWord, tailWord_4453559, baseEnd_4453559] using wordTrace_append hprefix tailTrace_4453559
  have hstable : (prefixWord ++ tailWord_4453559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4453559).length < 2 ^ (prefixWord ++ tailWord_4453559).sum := by decide
  have hdescent : baseEnd_4453559 < baseStart_4453559 := by decide
  rcases family_descends (prefixWord ++ tailWord_4453559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4453576 : List Nat := [2, 1, 3, 1, 2, 1, 5, 2, 1, 3, 2]
def baseStart_4453576 : Nat := 118140960795 + 4453576 * 2 ^ 59
def prefixEnd_4453576 : Nat := 4983230072969 + 3 ^ 40 * 4453576 * 2
def baseEnd_4453576 : Nat := 2286825119328172597118383

theorem tailTrace_4453576 : CollatzResearch.WordTrace tailWord_4453576 prefixEnd_4453576 2286825119328172597118383 := by
  unfold tailWord_4453576
  simp only [CollatzResearch.WordTrace]
  refine ⟨81217630656731118535318291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108290174208974824713757721 81217630656731118535318291)
  ·
    refine ⟨121826445985096677802977437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81217630656731118535318291 121826445985096677802977437)
    ·
      refine ⟨45684917244411254176116539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121826445985096677802977437 45684917244411254176116539)
      ·
        refine ⟨68527375866616881264174809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45684917244411254176116539 68527375866616881264174809)
        ·
          refine ⟨51395531899962660948131107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68527375866616881264174809 51395531899962660948131107)
          ·
            refine ⟨77093297849943991422196661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51395531899962660948131107 77093297849943991422196661)
            ·
              refine ⟨7227496673432249195830937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 77093297849943991422196661 7227496673432249195830937)
              ·
                refine ⟨5420622505074186896873203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7227496673432249195830937 5420622505074186896873203)
                ·
                  refine ⟨8130933757611280345309805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5420622505074186896873203 8130933757611280345309805)
                  ·
                    refine ⟨3049100159104230129491177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8130933757611280345309805 3049100159104230129491177)
                    ·
                      refine ⟨2286825119328172597118383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3049100159104230129491177 2286825119328172597118383)
                      ·
                        rfl

theorem cell23_4453576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 2, 1, 3, 2].length) (baseStart_4453576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4453576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4453576 prefixEnd_4453576 := by exact prefixLift 4453576
  have htrace : WordTrace (prefixWord ++ tailWord_4453576) baseStart_4453576 baseEnd_4453576 := by
    simpa [prefixWord, tailWord_4453576, baseEnd_4453576] using wordTrace_append hprefix tailTrace_4453576
  have hstable : (prefixWord ++ tailWord_4453576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4453576).length < 2 ^ (prefixWord ++ tailWord_4453576).sum := by decide
  have hdescent : baseEnd_4453576 < baseStart_4453576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4453576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4453646 : List Nat := [4, 1, 1, 2, 1, 4, 2, 3, 5]
def baseStart_4453646 : Nat := 118140960795 + 4453646 * 2 ^ 59
def prefixEnd_4453646 : Nat := 4983230072969 + 3 ^ 40 * 4453646 * 2
def baseEnd_4453646 : Nat := 254095673663776369249229

theorem tailTrace_4453646 : CollatzResearch.WordTrace tailWord_4453646 prefixEnd_4453646 254095673663776369249229 := by
  unfold tailWord_4453646
  simp only [CollatzResearch.WordTrace]
  refine ⟨20304726802901079878210599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108291876282139092683789861 20304726802901079878210599)
  ·
    refine ⟨30457090204351619817315899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20304726802901079878210599 30457090204351619817315899)
    ·
      refine ⟨45685635306527429725973849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30457090204351619817315899 45685635306527429725973849)
      ·
        refine ⟨34264226479895572294480387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45685635306527429725973849 34264226479895572294480387)
        ·
          refine ⟨51396339719843358441720581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34264226479895572294480387 51396339719843358441720581)
          ·
            refine ⟨9636813697470629707822609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51396339719843358441720581 9636813697470629707822609)
            ·
              refine ⟨7227610273102972280866957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9636813697470629707822609 7227610273102972280866957)
              ·
                refine ⟨2710353852413614605325109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7227610273102972280866957 2710353852413614605325109)
                ·
                  refine ⟨254095673663776369249229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2710353852413614605325109 254095673663776369249229)
                  ·
                    rfl

theorem cell23_4453646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 3, 5].length) (baseStart_4453646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4453646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4453646 prefixEnd_4453646 := by exact prefixLift 4453646
  have htrace : WordTrace (prefixWord ++ tailWord_4453646) baseStart_4453646 baseEnd_4453646 := by
    simpa [prefixWord, tailWord_4453646, baseEnd_4453646] using wordTrace_append hprefix tailTrace_4453646
  have hstable : (prefixWord ++ tailWord_4453646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4453646).length < 2 ^ (prefixWord ++ tailWord_4453646).sum := by decide
  have hdescent : baseEnd_4453646 < baseStart_4453646 := by decide
  rcases family_descends (prefixWord ++ tailWord_4453646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4453699 : List Nat := [1, 1, 1, 3, 1, 3, 1, 5, 2, 2, 3]
def baseStart_4453699 : Nat := 118140960795 + 4453699 * 2 ^ 59
def prefixEnd_4453699 : Nat := 4983230072969 + 3 ^ 40 * 4453699 * 2
def baseEnd_4453699 : Nat := 2286888277448675615880317

theorem tailTrace_4453699 : CollatzResearch.WordTrace tailWord_4453699 prefixEnd_4453699 2286888277448675615880317 := by
  unfold tailWord_4453699
  simp only [CollatzResearch.WordTrace]
  refine ⟨162439747492016629077364151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108293164994677752718242767 162439747492016629077364151)
  ·
    refine ⟨243659621238024943616046227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162439747492016629077364151 243659621238024943616046227)
    ·
      refine ⟨365489431857037415424069341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243659621238024943616046227 365489431857037415424069341)
      ·
        refine ⟨137058536946389030784026003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 365489431857037415424069341 137058536946389030784026003)
        ·
          refine ⟨205587805419583546176039005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137058536946389030784026003 205587805419583546176039005)
          ·
            refine ⟨77095427032343829816014627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 205587805419583546176039005 77095427032343829816014627)
            ·
              refine ⟨115643140548515744724021941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77095427032343829816014627 115643140548515744724021941)
              ·
                refine ⟨10841544426423351067877057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 115643140548515744724021941 10841544426423351067877057)
                ·
                  refine ⟨8131158319817513300907793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10841544426423351067877057 8131158319817513300907793)
                  ·
                    refine ⟨6098368739863134975680845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8131158319817513300907793 6098368739863134975680845)
                    ·
                      refine ⟨2286888277448675615880317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6098368739863134975680845 2286888277448675615880317)
                      ·
                        rfl

theorem cell23_4453699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 2, 2, 3].length) (baseStart_4453699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4453699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4453699 prefixEnd_4453699 := by exact prefixLift 4453699
  have htrace : WordTrace (prefixWord ++ tailWord_4453699) baseStart_4453699 baseEnd_4453699 := by
    simpa [prefixWord, tailWord_4453699, baseEnd_4453699] using wordTrace_append hprefix tailTrace_4453699
  have hstable : (prefixWord ++ tailWord_4453699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4453699).length < 2 ^ (prefixWord ++ tailWord_4453699).sum := by decide
  have hdescent : baseEnd_4453699 < baseStart_4453699 := by decide
  rcases family_descends (prefixWord ++ tailWord_4453699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4453716 : List Nat := [2, 4, 1, 1, 2, 1, 3, 2, 2, 2, 3]
def baseStart_4453716 : Nat := 118140960795 + 4453716 * 2 ^ 59
def prefixEnd_4453716 : Nat := 4983230072969 + 3 ^ 40 * 4453716 * 2
def baseEnd_4453716 : Nat := 2286897006619802049367739

theorem tailTrace_4453716 : CollatzResearch.WordTrace tailWord_4453716 prefixEnd_4453716 2286897006619802049367739 := by
  unfold tailWord_4453716
  simp only [CollatzResearch.WordTrace]
  refine ⟨81220183766477520490366501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108293578355303360653822001 81220183766477520490366501)
  ·
    refine ⟨15228784456214535091943719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81220183766477520490366501 15228784456214535091943719)
    ·
      refine ⟨22843176684321802637915579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15228784456214535091943719 22843176684321802637915579)
      ·
        refine ⟨34264765026482703956873369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22843176684321802637915579 34264765026482703956873369)
        ·
          refine ⟨25698573769862027967655027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34264765026482703956873369 25698573769862027967655027)
          ·
            refine ⟨38547860654793041951482541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25698573769862027967655027 38547860654793041951482541)
            ·
              refine ⟨14455447745547390731805953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38547860654793041951482541 14455447745547390731805953)
              ·
                refine ⟨10841585809160543048854465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14455447745547390731805953 10841585809160543048854465)
                ·
                  refine ⟨8131189356870407286640849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10841585809160543048854465 8131189356870407286640849)
                  ·
                    refine ⟨6098392017652805464980637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8131189356870407286640849 6098392017652805464980637)
                    ·
                      refine ⟨2286897006619802049367739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6098392017652805464980637 2286897006619802049367739)
                      ·
                        rfl

theorem cell23_4453716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_4453716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4453716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4453716 prefixEnd_4453716 := by exact prefixLift 4453716
  have htrace : WordTrace (prefixWord ++ tailWord_4453716) baseStart_4453716 baseEnd_4453716 := by
    simpa [prefixWord, tailWord_4453716, baseEnd_4453716] using wordTrace_append hprefix tailTrace_4453716
  have hstable : (prefixWord ++ tailWord_4453716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4453716).length < 2 ^ (prefixWord ++ tailWord_4453716).sum := by decide
  have hdescent : baseEnd_4453716 < baseStart_4453716 := by decide
  rcases family_descends (prefixWord ++ tailWord_4453716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4453722 : List Nat := [3, 1, 1, 2, 1, 2, 2, 1, 1, 1, 8]
def baseStart_4453722 : Nat := 118140960795 + 4453722 * 2 ^ 59
def prefixEnd_4453722 : Nat := 4983230072969 + 3 ^ 40 * 4453722 * 2
def baseEnd_4453722 : Nat := 2286900087503729025892711

theorem tailTrace_4453722 : CollatzResearch.WordTrace tailWord_4453722 prefixEnd_4453722 2286900087503729025892711 := by
  unfold tailWord_4453722
  simp only [CollatzResearch.WordTrace]
  refine ⟨40610146592733326001362855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108293724247288869336967613 40610146592733326001362855)
  ·
    refine ⟨60915219889099989002044283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40610146592733326001362855 60915219889099989002044283)
    ·
      refine ⟨91372829833649983503066425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60915219889099989002044283 91372829833649983503066425)
      ·
        refine ⟨68529622375237487627299819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91372829833649983503066425 68529622375237487627299819)
        ·
          refine ⟨102794433562856231440949729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68529622375237487627299819 102794433562856231440949729)
          ·
            refine ⟨77095825172142173580712297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102794433562856231440949729 77095825172142173580712297)
            ·
              refine ⟨57821868879106630185534223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77095825172142173580712297 57821868879106630185534223)
              ·
                refine ⟨86732803318659945278301335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57821868879106630185534223 86732803318659945278301335)
                ·
                  refine ⟨130099204977989917917452003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86732803318659945278301335 130099204977989917917452003)
                  ·
                    refine ⟨195148807466984876876178005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 130099204977989917917452003 195148807466984876876178005)
                    ·
                      refine ⟨2286900087503729025892711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 195148807466984876876178005 2286900087503729025892711)
                      ·
                        rfl

theorem cell23_4453722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_4453722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4453722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4453722 prefixEnd_4453722 := by exact prefixLift 4453722
  have htrace : WordTrace (prefixWord ++ tailWord_4453722) baseStart_4453722 baseEnd_4453722 := by
    simpa [prefixWord, tailWord_4453722, baseEnd_4453722] using wordTrace_append hprefix tailTrace_4453722
  have hstable : (prefixWord ++ tailWord_4453722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4453722).length < 2 ^ (prefixWord ++ tailWord_4453722).sum := by decide
  have hdescent : baseEnd_4453722 < baseStart_4453722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4453722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4453736 : List Nat := [2, 1, 4, 2, 3, 1, 1, 3, 6]
def baseStart_4453736 : Nat := 118140960795 + 4453736 * 2 ^ 59
def prefixEnd_4453736 : Nat := 4983230072969 + 3 ^ 40 * 4453736 * 2
def baseEnd_4453736 : Nat := 254100808470321330124183

theorem tailTrace_4453736 : CollatzResearch.WordTrace tailWord_4453736 prefixEnd_4453736 254100808470321330124183 := by
  unfold tailWord_4453736
  simp only [CollatzResearch.WordTrace]
  refine ⟨81220548496441292198230531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108294064661921722930974041 81220548496441292198230531)
  ·
    refine ⟨121830822744661938297345797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81220548496441292198230531 121830822744661938297345797)
    ·
      refine ⟨22843279264624113430752337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121830822744661938297345797 22843279264624113430752337)
      ·
        refine ⟨17132459448468085073064253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22843279264624113430752337 17132459448468085073064253)
        ·
          refine ⟨6424672293175531902399095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17132459448468085073064253 6424672293175531902399095)
          ·
            refine ⟨9637008439763297853598643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6424672293175531902399095 9637008439763297853598643)
            ·
              refine ⟨14455512659644946780397965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9637008439763297853598643 14455512659644946780397965)
              ·
                refine ⟨5420817247366855042649237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14455512659644946780397965 5420817247366855042649237)
                ·
                  refine ⟨254100808470321330124183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5420817247366855042649237 254100808470321330124183)
                  ·
                    rfl

theorem cell23_4453736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 3, 6].length) (baseStart_4453736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4453736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4453736 prefixEnd_4453736 := by exact prefixLift 4453736
  have htrace : WordTrace (prefixWord ++ tailWord_4453736) baseStart_4453736 baseEnd_4453736 := by
    simpa [prefixWord, tailWord_4453736, baseEnd_4453736] using wordTrace_append hprefix tailTrace_4453736
  have hstable : (prefixWord ++ tailWord_4453736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4453736).length < 2 ^ (prefixWord ++ tailWord_4453736).sum := by decide
  have hdescent : baseEnd_4453736 < baseStart_4453736 := by decide
  rcases family_descends (prefixWord ++ tailWord_4453736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4453746 : List Nat := [3, 2, 1, 2, 1, 2, 2, 1, 5, 1, 3]
def baseStart_4453746 : Nat := 118140960795 + 4453746 * 2 ^ 59
def prefixEnd_4453746 : Nat := 4983230072969 + 3 ^ 40 * 4453746 * 2
def baseEnd_4453746 : Nat := 2286912411039436931992601

theorem tailTrace_4453746 : CollatzResearch.WordTrace tailWord_4453746 prefixEnd_4453746 2286912411039436931992601 := by
  unfold tailWord_4453746
  simp only [CollatzResearch.WordTrace]
  refine ⟨40610365430711589026081273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108294307815230904069550061 40610365430711589026081273)
  ·
    refine ⟨30457774073033691769560955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40610365430711589026081273 30457774073033691769560955)
    ·
      refine ⟨45686661109550537654341433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30457774073033691769560955 45686661109550537654341433)
      ·
        refine ⟨34264995832162903240756075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45686661109550537654341433 34264995832162903240756075)
        ·
          refine ⟨51397493748244354861134113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34264995832162903240756075 51397493748244354861134113)
          ·
            refine ⟨38548120311183266145850585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51397493748244354861134113 38548120311183266145850585)
            ·
              refine ⟨28911090233387449609387939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38548120311183266145850585 28911090233387449609387939)
              ·
                refine ⟨43366635350081174414081909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28911090233387449609387939 43366635350081174414081909)
                ·
                  refine ⟨4065622064070110101320179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43366635350081174414081909 4065622064070110101320179)
                  ·
                    refine ⟨6098433096105165151980269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4065622064070110101320179 6098433096105165151980269)
                    ·
                      refine ⟨2286912411039436931992601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6098433096105165151980269 2286912411039436931992601)
                      ·
                        rfl

theorem cell23_4453746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_4453746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4453746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4453746 prefixEnd_4453746 := by exact prefixLift 4453746
  have htrace : WordTrace (prefixWord ++ tailWord_4453746) baseStart_4453746 baseEnd_4453746 := by
    simpa [prefixWord, tailWord_4453746, baseEnd_4453746] using wordTrace_append hprefix tailTrace_4453746
  have hstable : (prefixWord ++ tailWord_4453746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4453746).length < 2 ^ (prefixWord ++ tailWord_4453746).sum := by decide
  have hdescent : baseEnd_4453746 < baseStart_4453746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4453746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4453774 : List Nat := [4, 1, 1, 4, 3, 1, 2, 2, 1, 4]
def baseStart_4453774 : Nat := 118140960795 + 4453774 * 2 ^ 59
def prefixEnd_4453774 : Nat := 4983230072969 + 3 ^ 40 * 4453774 * 2
def baseEnd_4453774 : Nat := 762308929499254274147491

theorem tailTrace_4453774 : CollatzResearch.WordTrace tailWord_4453774 prefixEnd_4453774 762308929499254274147491 := by
  unfold tailWord_4453774
  simp only [CollatzResearch.WordTrace]
  refine ⟨20305310370843114610793047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108294988644496611257562917 20305310370843114610793047)
  ·
    refine ⟨30457965556264671916189571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20305310370843114610793047 30457965556264671916189571)
    ·
      refine ⟨45686948334397007874284357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30457965556264671916189571 45686948334397007874284357)
      ·
        refine ⟨8566302812699438976428317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45686948334397007874284357 8566302812699438976428317)
        ·
          refine ⟨3212363554762289616160619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8566302812699438976428317 3212363554762289616160619)
          ·
            refine ⟨4818545332143434424240929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3212363554762289616160619 4818545332143434424240929)
            ·
              refine ⟨3613908999107575818180697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4818545332143434424240929 3613908999107575818180697)
              ·
                refine ⟨2710431749330681863635523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3613908999107575818180697 2710431749330681863635523)
                ·
                  refine ⟨4065647623996022795453285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2710431749330681863635523 4065647623996022795453285)
                  ·
                    refine ⟨762308929499254274147491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4065647623996022795453285 762308929499254274147491)
                    ·
                      rfl

theorem cell23_4453774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 2, 1, 4].length) (baseStart_4453774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4453774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4453774 prefixEnd_4453774 := by exact prefixLift 4453774
  have htrace : WordTrace (prefixWord ++ tailWord_4453774) baseStart_4453774 baseEnd_4453774 := by
    simpa [prefixWord, tailWord_4453774, baseEnd_4453774] using wordTrace_append hprefix tailTrace_4453774
  have hstable : (prefixWord ++ tailWord_4453774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4453774).length < 2 ^ (prefixWord ++ tailWord_4453774).sum := by decide
  have hdescent : baseEnd_4453774 < baseStart_4453774 := by decide
  rcases family_descends (prefixWord ++ tailWord_4453774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4453853 : List Nat := [1, 4, 3, 1, 1, 2, 3, 1, 1, 3, 3]
def baseStart_4453853 : Nat := 118140960795 + 4453853 * 2 ^ 59
def prefixEnd_4453853 : Nat := 4983230072969 + 3 ^ 40 * 4453853 * 2
def baseEnd_4453853 : Nat := 2286967353469468013354609

theorem tailTrace_4453853 : CollatzResearch.WordTrace tailWord_4453853 prefixEnd_4453853 2286967353469468013354609 := by
  unfold tailWord_4453853
  simp only [CollatzResearch.WordTrace]
  refine ⟨162445364333458713378470213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108296909555639142252313475 162445364333458713378470213)
  ·
    refine ⟨30458505812523508758463165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 162445364333458713378470213 30458505812523508758463165)
    ·
      refine ⟨11421939679696315784423687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30458505812523508758463165 11421939679696315784423687)
      ·
        refine ⟨17132909519544473676635531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11421939679696315784423687 17132909519544473676635531)
        ·
          refine ⟨25699364279316710514953297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17132909519544473676635531 25699364279316710514953297)
          ·
            refine ⟨19274523209487532886214973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25699364279316710514953297 19274523209487532886214973)
            ·
              refine ⟨7227946203557824832330615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19274523209487532886214973 7227946203557824832330615)
              ·
                refine ⟨10841919305336737248495923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7227946203557824832330615 10841919305336737248495923)
                ·
                  refine ⟨16262878958005105872743885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10841919305336737248495923 16262878958005105872743885)
                  ·
                    refine ⟨6098579609251914702278957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16262878958005105872743885 6098579609251914702278957)
                    ·
                      refine ⟨2286967353469468013354609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6098579609251914702278957 2286967353469468013354609)
                      ·
                        rfl

theorem cell23_4453853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_4453853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4453853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4453853 prefixEnd_4453853 := by exact prefixLift 4453853
  have htrace : WordTrace (prefixWord ++ tailWord_4453853) baseStart_4453853 baseEnd_4453853 := by
    simpa [prefixWord, tailWord_4453853, baseEnd_4453853] using wordTrace_append hprefix tailTrace_4453853
  have hstable : (prefixWord ++ tailWord_4453853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4453853).length < 2 ^ (prefixWord ++ tailWord_4453853).sum := by decide
  have hdescent : baseEnd_4453853 < baseStart_4453853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4453853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4453946 : List Nat := [3, 1, 1, 1, 3, 2, 1, 4, 2, 5]
def baseStart_4453946 : Nat := 118140960795 + 4453946 * 2 ^ 59
def prefixEnd_4453946 : Nat := 4983230072969 + 3 ^ 40 * 4453946 * 2
def baseEnd_4453946 : Nat := 762338369056778716497227

theorem tailTrace_4453946 : CollatzResearch.WordTrace tailWord_4453946 prefixEnd_4453946 762338369056778716497227 := by
  unfold tailWord_4453946
  simp only [CollatzResearch.WordTrace]
  refine ⟨40612189080530447565401423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108299170881414526841070461 40612189080530447565401423)
  ·
    refine ⟨60918283620795671348102135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40612189080530447565401423 60918283620795671348102135)
    ·
      refine ⟨91377425431193507022153203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60918283620795671348102135 91377425431193507022153203)
      ·
        refine ⟨137066138146790260533229805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91377425431193507022153203 137066138146790260533229805)
        ·
          refine ⟨51399801805046347699961177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137066138146790260533229805 51399801805046347699961177)
          ·
            refine ⟨38549851353784760774970883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51399801805046347699961177 38549851353784760774970883)
            ·
              refine ⟨57824777030677141162456325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38549851353784760774970883 57824777030677141162456325)
              ·
                refine ⟨10842145693251963967960561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57824777030677141162456325 10842145693251963967960561)
                ·
                  refine ⟨8131609269938972975970421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10842145693251963967960561 8131609269938972975970421)
                  ·
                    refine ⟨762338369056778716497227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8131609269938972975970421 762338369056778716497227)
                    ·
                      rfl

theorem cell23_4453946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 2, 5].length) (baseStart_4453946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4453946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4453946 prefixEnd_4453946 := by exact prefixLift 4453946
  have htrace : WordTrace (prefixWord ++ tailWord_4453946) baseStart_4453946 baseEnd_4453946 := by
    simpa [prefixWord, tailWord_4453946, baseEnd_4453946] using wordTrace_append hprefix tailTrace_4453946
  have hstable : (prefixWord ++ tailWord_4453946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4453946).length < 2 ^ (prefixWord ++ tailWord_4453946).sum := by decide
  have hdescent : baseEnd_4453946 < baseStart_4453946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4453946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4453953 : List Nat := [1, 2, 5, 1, 1, 1, 1, 1, 1, 7, 2]
def baseStart_4453953 : Nat := 118140960795 + 4453953 * 2 ^ 59
def prefixEnd_4453953 : Nat := 4983230072969 + 3 ^ 40 * 4453953 * 2
def baseEnd_4453953 : Nat := 2287018701534917622104149

theorem tailTrace_4453953 : CollatzResearch.WordTrace tailWord_4453953 prefixEnd_4453953 2287018701534917622104149 := by
  unfold tailWord_4453953
  simp only [CollatzResearch.WordTrace]
  refine ⟨162449011633096430457110513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108299341088730953638073675 162449011633096430457110513)
  ·
    refine ⟨121836758724822322842832885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162449011633096430457110513 121836758724822322842832885)
    ·
      refine ⟨11422196130452092766515583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 121836758724822322842832885 11422196130452092766515583)
      ·
        refine ⟨17133294195678139149773375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11422196130452092766515583 17133294195678139149773375)
        ·
          refine ⟨25699941293517208724660063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17133294195678139149773375 25699941293517208724660063)
          ·
            refine ⟨38549911940275813086990095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25699941293517208724660063 38549911940275813086990095)
            ·
              refine ⟨57824867910413719630485143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38549911940275813086990095 57824867910413719630485143)
              ·
                refine ⟨86737301865620579445727715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57824867910413719630485143 86737301865620579445727715)
                ·
                  refine ⟨130105952798430869168591573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86737301865620579445727715 130105952798430869168591573)
                  ·
                    refine ⟨3049358268713223496138865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 130105952798430869168591573 3049358268713223496138865)
                    ·
                      refine ⟨2287018701534917622104149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3049358268713223496138865 2287018701534917622104149)
                      ·
                        rfl

theorem cell23_4453953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_4453953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4453953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4453953 prefixEnd_4453953 := by exact prefixLift 4453953
  have htrace : WordTrace (prefixWord ++ tailWord_4453953) baseStart_4453953 baseEnd_4453953 := by
    simpa [prefixWord, tailWord_4453953, baseEnd_4453953] using wordTrace_append hprefix tailTrace_4453953
  have hstable : (prefixWord ++ tailWord_4453953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4453953).length < 2 ^ (prefixWord ++ tailWord_4453953).sum := by decide
  have hdescent : baseEnd_4453953 < baseStart_4453953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4453953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4453966 : List Nat := [4, 1, 1, 1, 1, 2, 1, 4, 1, 3, 4]
def baseStart_4453966 : Nat := 118140960795 + 4453966 * 2 ^ 59
def prefixEnd_4453966 : Nat := 4983230072969 + 3 ^ 40 * 4453966 * 2
def baseEnd_4453966 : Nat := 2287025376783426071241589

theorem tailTrace_4453966 : CollatzResearch.WordTrace tailWord_4453966 prefixEnd_4453966 2287025376783426071241589 := by
  unfold tailWord_4453966
  simp only [CollatzResearch.WordTrace]
  refine ⟨20306185722756166709666719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108299657188032889118222501 20306185722756166709666719)
  ·
    refine ⟨30459278584134250064500079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20306185722756166709666719 30459278584134250064500079)
    ·
      refine ⟨45688917876201375096750119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30459278584134250064500079 45688917876201375096750119)
      ·
        refine ⟨68533376814302062645125179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45688917876201375096750119 68533376814302062645125179)
        ·
          refine ⟨102800065221453093967687769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68533376814302062645125179 102800065221453093967687769)
          ·
            refine ⟨77100048916089820475765827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102800065221453093967687769 77100048916089820475765827)
            ·
              refine ⟨115650073374134730713648741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77100048916089820475765827 115650073374134730713648741)
              ·
                refine ⟨21684388757650262008809139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 115650073374134730713648741 21684388757650262008809139)
                ·
                  refine ⟨32526583136475393013213709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21684388757650262008809139 32526583136475393013213709)
                  ·
                    refine ⟨12197468676178272379955141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32526583136475393013213709 12197468676178272379955141)
                    ·
                      refine ⟨2287025376783426071241589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12197468676178272379955141 2287025376783426071241589)
                      ·
                        rfl

theorem cell23_4453966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_4453966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4453966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4453966 prefixEnd_4453966 := by exact prefixLift 4453966
  have htrace : WordTrace (prefixWord ++ tailWord_4453966) baseStart_4453966 baseEnd_4453966 := by
    simpa [prefixWord, tailWord_4453966, baseEnd_4453966] using wordTrace_append hprefix tailTrace_4453966
  have hstable : (prefixWord ++ tailWord_4453966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4453966).length < 2 ^ (prefixWord ++ tailWord_4453966).sum := by decide
  have hdescent : baseEnd_4453966 < baseStart_4453966 := by decide
  rcases family_descends (prefixWord ++ tailWord_4453966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4453980 : List Nat := [2, 2, 4, 1, 2, 3, 1, 1, 2, 5]
def baseStart_4453980 : Nat := 118140960795 + 4453980 * 2 ^ 59
def prefixEnd_4453980 : Nat := 4983230072969 + 3 ^ 40 * 4453980 * 2
def baseEnd_4453980 : Nat := 762344188504196338822175

theorem tailTrace_4453980 : CollatzResearch.WordTrace tailWord_4453980 prefixEnd_4453980 762344188504196338822175 := by
  unfold tailWord_4453980
  simp only [CollatzResearch.WordTrace]
  refine ⟨81224998201999307034171697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108299997602665742712228929 81224998201999307034171697)
  ·
    refine ⟨60918748651499480275628773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81224998201999307034171697 60918748651499480275628773)
    ·
      refine ⟨11422265372156152551680395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60918748651499480275628773 11422265372156152551680395)
      ·
        refine ⟨17133398058234228827520593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11422265372156152551680395 17133398058234228827520593)
        ·
          refine ⟨12850048543675671620640445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17133398058234228827520593 12850048543675671620640445)
          ·
            refine ⟨4818768203878376857740167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12850048543675671620640445 4818768203878376857740167)
            ·
              refine ⟨7228152305817565286610251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4818768203878376857740167 7228152305817565286610251)
              ·
                refine ⟨10842228458726347929915377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7228152305817565286610251 10842228458726347929915377)
                ·
                  refine ⟨8131671344044760947436533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10842228458726347929915377 8131671344044760947436533)
                  ·
                    refine ⟨762344188504196338822175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8131671344044760947436533 762344188504196338822175)
                    ·
                      rfl

theorem cell23_4453980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_4453980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4453980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4453980 prefixEnd_4453980 := by exact prefixLift 4453980
  have htrace : WordTrace (prefixWord ++ tailWord_4453980) baseStart_4453980 baseEnd_4453980 := by
    simpa [prefixWord, tailWord_4453980, baseEnd_4453980] using wordTrace_append hprefix tailTrace_4453980
  have hstable : (prefixWord ++ tailWord_4453980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4453980).length < 2 ^ (prefixWord ++ tailWord_4453980).sum := by decide
  have hdescent : baseEnd_4453980 < baseStart_4453980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4453980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4454033 : List Nat := [1, 2, 2, 1, 1, 1, 1, 5, 5, 1, 3]
def baseStart_4454033 : Nat := 118140960795 + 4454033 * 2 ^ 59
def prefixEnd_4454033 : Nat := 4983230072969 + 3 ^ 40 * 4454033 * 2
def baseEnd_4454033 : Nat := 2287059779987277309103781

theorem tailTrace_4454033 : CollatzResearch.WordTrace tailWord_4454033 prefixEnd_4454033 2287059779987277309103781 := by
  unfold tailWord_4454033
  simp only [CollatzResearch.WordTrace]
  refine ⟨162451929472806604120022753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108301286315204402746681835 162451929472806604120022753)
  ·
    refine ⟨121838947104604953090017065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162451929472806604120022753 121838947104604953090017065)
    ·
      refine ⟨91379210328453714817512799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121838947104604953090017065 91379210328453714817512799)
      ·
        refine ⟨137068815492680572226269199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91379210328453714817512799 137068815492680572226269199)
        ·
          refine ⟨205603223239020858339403799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137068815492680572226269199 205603223239020858339403799)
          ·
            refine ⟨308404834858531287509105699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205603223239020858339403799 308404834858531287509105699)
            ·
              refine ⟨462607252287796931263658549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 308404834858531287509105699 462607252287796931263658549)
              ·
                refine ⟨43369429901980962305967989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 462607252287796931263658549 43369429901980962305967989)
                ·
                  refine ⟨4065884053310715216184499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43369429901980962305967989 4065884053310715216184499)
                  ·
                    refine ⟨6098826079966072824276749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4065884053310715216184499 6098826079966072824276749)
                    ·
                      refine ⟨2287059779987277309103781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6098826079966072824276749 2287059779987277309103781)
                      ·
                        rfl

theorem cell23_4454033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 5, 1, 3].length) (baseStart_4454033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4454033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4454033 prefixEnd_4454033 := by exact prefixLift 4454033
  have htrace : WordTrace (prefixWord ++ tailWord_4454033) baseStart_4454033 baseEnd_4454033 := by
    simpa [prefixWord, tailWord_4454033, baseEnd_4454033] using wordTrace_append hprefix tailTrace_4454033
  have hstable : (prefixWord ++ tailWord_4454033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4454033).length < 2 ^ (prefixWord ++ tailWord_4454033).sum := by decide
  have hdescent : baseEnd_4454033 < baseStart_4454033 := by decide
  rcases family_descends (prefixWord ++ tailWord_4454033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4454044 : List Nat := [2, 2, 3, 2, 3, 2, 1, 3, 1, 4]
def baseStart_4454044 : Nat := 118140960795 + 4454044 * 2 ^ 59
def prefixEnd_4454044 : Nat := 4983230072969 + 3 ^ 40 * 4454044 * 2
def baseEnd_4454044 : Nat := 762355142758158922022077

theorem tailTrace_4454044 : CollatzResearch.WordTrace tailWord_4454044 prefixEnd_4454044 762355142758158922022077 := by
  unfold tailWord_4454044
  simp only [CollatzResearch.WordTrace]
  refine ⟨81226165337883376499336593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108301553783844501999115457 81226165337883376499336593)
  ·
    refine ⟨60919624003412532374502445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81226165337883376499336593 60919624003412532374502445)
    ·
      refine ⟨22844859001279699640438417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60919624003412532374502445 22844859001279699640438417)
      ·
        refine ⟨17133644250959774730328813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22844859001279699640438417 17133644250959774730328813)
        ·
          refine ⟨6425116594109915523873305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17133644250959774730328813 6425116594109915523873305)
          ·
            refine ⟨4818837445582436642904979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6425116594109915523873305 4818837445582436642904979)
            ·
              refine ⟨7228256168373654964357469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4818837445582436642904979 7228256168373654964357469)
              ·
                refine ⟨2710596063140120611634051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7228256168373654964357469 2710596063140120611634051)
                ·
                  refine ⟨4065894094710180917451077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2710596063140120611634051 4065894094710180917451077)
                  ·
                    refine ⟨762355142758158922022077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4065894094710180917451077 762355142758158922022077)
                    ·
                      rfl

theorem cell23_4454044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_4454044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4454044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4454044 prefixEnd_4454044 := by exact prefixLift 4454044
  have htrace : WordTrace (prefixWord ++ tailWord_4454044) baseStart_4454044 baseEnd_4454044 := by
    simpa [prefixWord, tailWord_4454044, baseEnd_4454044] using wordTrace_append hprefix tailTrace_4454044
  have hstable : (prefixWord ++ tailWord_4454044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4454044).length < 2 ^ (prefixWord ++ tailWord_4454044).sum := by decide
  have hdescent : baseEnd_4454044 < baseStart_4454044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4454044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4454053 : List Nat := [1, 3, 1, 2, 1, 2, 4, 3, 1, 5]
def baseStart_4454053 : Nat := 118140960795 + 4454053 * 2 ^ 59
def prefixEnd_4454053 : Nat := 4983230072969 + 3 ^ 40 * 4454053 * 2
def baseEnd_4454053 : Nat := 762356683200122410284563

theorem tailTrace_4454053 : CollatzResearch.WordTrace tailWord_4454053 prefixEnd_4454053 762356683200122410284563 := by
  unfold tailWord_4454053
  simp only [CollatzResearch.WordTrace]
  refine ⟨162452658932734147535750813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108301772621822765023833875 162452658932734147535750813)
  ·
    refine ⟨60919747099775305325906555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162452658932734147535750813 60919747099775305325906555)
    ·
      refine ⟨91379620649662957988859833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60919747099775305325906555 91379620649662957988859833)
      ·
        refine ⟨68534715487247218491644875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91379620649662957988859833 68534715487247218491644875)
        ·
          refine ⟨102802073230870827737467313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68534715487247218491644875 102802073230870827737467313)
          ·
            refine ⟨77101554923153120803100485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102802073230870827737467313 77101554923153120803100485)
            ·
              refine ⟨14456541548091210150581341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77101554923153120803100485 14456541548091210150581341)
              ·
                refine ⟨5421203080534203806468003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14456541548091210150581341 5421203080534203806468003)
                ·
                  refine ⟨8131804620801305709702005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5421203080534203806468003 8131804620801305709702005)
                  ·
                    refine ⟨762356683200122410284563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8131804620801305709702005 762356683200122410284563)
                    ·
                      rfl

theorem cell23_4454053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 3, 1, 5].length) (baseStart_4454053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4454053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4454053 prefixEnd_4454053 := by exact prefixLift 4454053
  have htrace : WordTrace (prefixWord ++ tailWord_4454053) baseStart_4454053 baseEnd_4454053 := by
    simpa [prefixWord, tailWord_4454053, baseEnd_4454053] using wordTrace_append hprefix tailTrace_4454053
  have hstable : (prefixWord ++ tailWord_4454053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4454053).length < 2 ^ (prefixWord ++ tailWord_4454053).sum := by decide
  have hdescent : baseEnd_4454053 < baseStart_4454053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4454053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4454090 : List Nat := [3, 1, 2, 1, 5, 1, 1, 1, 3, 1, 4]
def baseStart_4454090 : Nat := 118140960795 + 4454090 * 2 ^ 59
def prefixEnd_4454090 : Nat := 4983230072969 + 3 ^ 40 * 4454090 * 2
def baseEnd_4454090 : Nat := 2287089048384583586091019

theorem tailTrace_4454090 : CollatzResearch.WordTrace tailWord_4454090 prefixEnd_4454090 2287089048384583586091019 := by
  unfold tailWord_4454090
  simp only [CollatzResearch.WordTrace]
  refine ⟨40613502108400025713711931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108302672289066735236565149 40613502108400025713711931)
  ·
    refine ⟨60920253162600038570567897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40613502108400025713711931 60920253162600038570567897)
    ·
      refine ⟨45690189871950028927925923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60920253162600038570567897 45690189871950028927925923)
      ·
        refine ⟨68535284807925043391888885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45690189871950028927925923 68535284807925043391888885)
        ·
          refine ⟨6425182950742972817989583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68535284807925043391888885 6425182950742972817989583)
          ·
            refine ⟨9637774426114459226984375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6425182950742972817989583 9637774426114459226984375)
            ·
              refine ⟨14456661639171688840476563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9637774426114459226984375 14456661639171688840476563)
              ·
                refine ⟨21684992458757533260714845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14456661639171688840476563 21684992458757533260714845)
                ·
                  refine ⟨8131872172034074972768067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21684992458757533260714845 8131872172034074972768067)
                  ·
                    refine ⟨12197808258051112459152101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8131872172034074972768067 12197808258051112459152101)
                    ·
                      refine ⟨2287089048384583586091019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12197808258051112459152101 2287089048384583586091019)
                      ·
                        rfl

theorem cell23_4454090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 3, 1, 4].length) (baseStart_4454090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4454090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4454090 prefixEnd_4454090 := by exact prefixLift 4454090
  have htrace : WordTrace (prefixWord ++ tailWord_4454090) baseStart_4454090 baseEnd_4454090 := by
    simpa [prefixWord, tailWord_4454090, baseEnd_4454090] using wordTrace_append hprefix tailTrace_4454090
  have hstable : (prefixWord ++ tailWord_4454090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4454090).length < 2 ^ (prefixWord ++ tailWord_4454090).sum := by decide
  have hdescent : baseEnd_4454090 < baseStart_4454090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4454090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4454100 : List Nat := [2, 4, 1, 3, 1, 2, 1, 2, 1, 6]
def baseStart_4454100 : Nat := 118140960795 + 4454100 * 2 ^ 59
def prefixEnd_4454100 : Nat := 4983230072969 + 3 ^ 40 * 4454100 * 2
def baseEnd_4454100 : Nat := 762364727730376182321991

theorem tailTrace_4454100 : CollatzResearch.WordTrace tailWord_4454100 prefixEnd_4454100 762364727730376182321991 := by
  unfold tailWord_4454100
  simp only [CollatzResearch.WordTrace]
  refine ⟨81227186581781937281355877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108302915442375916375141169 81227186581781937281355877)
  ·
    refine ⟨15230097484084113240254227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81227186581781937281355877 15230097484084113240254227)
    ·
      refine ⟨22845146226126169860381341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15230097484084113240254227 22845146226126169860381341)
      ·
        refine ⟨8566929834797313697643003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22845146226126169860381341 8566929834797313697643003)
        ·
          refine ⟨12850394752195970546464505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8566929834797313697643003 12850394752195970546464505)
          ·
            refine ⟨9637796064146977909848379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12850394752195970546464505 9637796064146977909848379)
            ·
              refine ⟨14456694096220466864772569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9637796064146977909848379 14456694096220466864772569)
              ·
                refine ⟨10842520572165350148579427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14456694096220466864772569 10842520572165350148579427)
                ·
                  refine ⟨16263780858248025222869141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10842520572165350148579427 16263780858248025222869141)
                  ·
                    refine ⟨762364727730376182321991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16263780858248025222869141 762364727730376182321991)
                    ·
                      rfl

theorem cell23_4454100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_4454100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4454100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4454100 prefixEnd_4454100 := by exact prefixLift 4454100
  have htrace : WordTrace (prefixWord ++ tailWord_4454100) baseStart_4454100 baseEnd_4454100 := by
    simpa [prefixWord, tailWord_4454100, baseEnd_4454100] using wordTrace_append hprefix tailTrace_4454100
  have hstable : (prefixWord ++ tailWord_4454100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4454100).length < 2 ^ (prefixWord ++ tailWord_4454100).sum := by decide
  have hdescent : baseEnd_4454100 < baseStart_4454100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4454100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4454103 : List Nat := [1, 1, 3, 2, 1, 3, 3, 2, 1, 2, 4]
def baseStart_4454103 : Nat := 118140960795 + 4454103 * 2 ^ 59
def prefixEnd_4454103 : Nat := 4983230072969 + 3 ^ 40 * 4454103 * 2
def baseEnd_4454103 : Nat := 2287095723633092035228459

theorem tailTrace_4454103 : CollatzResearch.WordTrace tailWord_4454103 prefixEnd_4454103 2287095723633092035228459 := by
  unfold tailWord_4454103
  simp only [CollatzResearch.WordTrace]
  refine ⟨162454482582553006075070963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108302988388368670716713975 162454482582553006075070963)
  ·
    refine ⟨243681723873829509112606445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162454482582553006075070963 243681723873829509112606445)
    ·
      refine ⟨91380646452686065917227417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 243681723873829509112606445 91380646452686065917227417)
      ·
        refine ⟨68535484839514549437920563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91380646452686065917227417 68535484839514549437920563)
        ·
          refine ⟨102803227259271824156880845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68535484839514549437920563 102803227259271824156880845)
          ·
            refine ⟨38551210222226934058830317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102803227259271824156880845 38551210222226934058830317)
            ·
              refine ⟨14456703833335100272061369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38551210222226934058830317 14456703833335100272061369)
              ·
                refine ⟨10842527875001325204046027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14456703833335100272061369 10842527875001325204046027)
                ·
                  refine ⟨16263791812501987806069041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10842527875001325204046027 16263791812501987806069041)
                  ·
                    refine ⟨12197843859376490854551781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16263791812501987806069041 12197843859376490854551781)
                    ·
                      refine ⟨2287095723633092035228459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12197843859376490854551781 2287095723633092035228459)
                      ·
                        rfl

theorem cell23_4454103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_4454103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4454103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4454103 prefixEnd_4454103 := by exact prefixLift 4454103
  have htrace : WordTrace (prefixWord ++ tailWord_4454103) baseStart_4454103 baseEnd_4454103 := by
    simpa [prefixWord, tailWord_4454103, baseEnd_4454103] using wordTrace_append hprefix tailTrace_4454103
  have hstable : (prefixWord ++ tailWord_4454103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4454103).length < 2 ^ (prefixWord ++ tailWord_4454103).sum := by decide
  have hdescent : baseEnd_4454103 < baseStart_4454103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4454103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4454113 : List Nat := [1, 2, 3, 1, 6, 10]
def baseStart_4454113 : Nat := 118140960795 + 4454113 * 2 ^ 59
def prefixEnd_4454113 : Nat := 4983230072969 + 3 ^ 40 * 4454113 * 2
def baseEnd_4454113 : Nat := 9411937689052004099191

theorem tailTrace_4454113 : CollatzResearch.WordTrace tailWord_4454113 prefixEnd_4454113 9411937689052004099191 := by
  unfold tailWord_4454113
  simp only [CollatzResearch.WordTrace]
  refine ⟨162454847312516777782934993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108303231541677851855289995 162454847312516777782934993)
  ·
    refine ⟨121841135484387583337201245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162454847312516777782934993 121841135484387583337201245)
    ·
      refine ⟨45690425806645343751450467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121841135484387583337201245 45690425806645343751450467)
      ·
        refine ⟨68535638709968015627175701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45690425806645343751450467 68535638709968015627175701)
        ·
          refine ⟨3212608064529750732523861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 68535638709968015627175701 3212608064529750732523861)
          ·
            refine ⟨9411937689052004099191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3212608064529750732523861 9411937689052004099191)
            ·
              rfl

theorem cell23_4454113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 10].length) (baseStart_4454113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4454113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4454113 prefixEnd_4454113 := by exact prefixLift 4454113
  have htrace : WordTrace (prefixWord ++ tailWord_4454113) baseStart_4454113 baseEnd_4454113 := by
    simpa [prefixWord, tailWord_4454113, baseEnd_4454113] using wordTrace_append hprefix tailTrace_4454113
  have hstable : (prefixWord ++ tailWord_4454113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4454113).length < 2 ^ (prefixWord ++ tailWord_4454113).sum := by decide
  have hdescent : baseEnd_4454113 < baseStart_4454113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4454113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4454140 : List Nat := [2, 2, 2, 1, 3, 1, 4, 1, 1, 3, 3]
def baseStart_4454140 : Nat := 118140960795 + 4454140 * 2 ^ 59
def prefixEnd_4454140 : Nat := 4983230072969 + 3 ^ 40 * 4454140 * 2
def baseEnd_4454140 : Nat := 2287114722417308390465789

theorem tailTrace_4454140 : CollatzResearch.WordTrace tailWord_4454140 prefixEnd_4454140 2287114722417308390465789 := by
  unfold tailWord_4454140
  simp only [CollatzResearch.WordTrace]
  refine ⟨81227916041709480697083937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108303888055612640929445249 81227916041709480697083937)
  ·
    refine ⟨60920937031282110522812953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81227916041709480697083937 60920937031282110522812953)
    ·
      refine ⟨45690702773461582892109715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60920937031282110522812953 45690702773461582892109715)
      ·
        refine ⟨68536054160192374338164573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45690702773461582892109715 68536054160192374338164573)
        ·
          refine ⟨25701020310072140376811715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68536054160192374338164573 25701020310072140376811715)
          ·
            refine ⟨38551530465108210565217573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25701020310072140376811715 38551530465108210565217573)
            ·
              refine ⟨7228411962207789480978295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38551530465108210565217573 7228411962207789480978295)
              ·
                refine ⟨10842617943311684221467443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7228411962207789480978295 10842617943311684221467443)
                ·
                  refine ⟨16263926914967526332201165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10842617943311684221467443 16263926914967526332201165)
                  ·
                    refine ⟨6098972593112822374575437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16263926914967526332201165 6098972593112822374575437)
                    ·
                      refine ⟨2287114722417308390465789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6098972593112822374575437 2287114722417308390465789)
                      ·
                        rfl

theorem cell23_4454140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 1, 3, 3].length) (baseStart_4454140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4454140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4454140 prefixEnd_4454140 := by exact prefixLift 4454140
  have htrace : WordTrace (prefixWord ++ tailWord_4454140) baseStart_4454140 baseEnd_4454140 := by
    simpa [prefixWord, tailWord_4454140, baseEnd_4454140] using wordTrace_append hprefix tailTrace_4454140
  have hstable : (prefixWord ++ tailWord_4454140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4454140).length < 2 ^ (prefixWord ++ tailWord_4454140).sum := by decide
  have hdescent : baseEnd_4454140 < baseStart_4454140 := by decide
  rcases family_descends (prefixWord ++ tailWord_4454140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4454201 : List Nat := [1, 2, 1, 7, 1, 1, 2, 2, 1, 3, 2]
def baseStart_4454201 : Nat := 118140960795 + 4454201 * 2 ^ 59
def prefixEnd_4454201 : Nat := 4983230072969 + 3 ^ 40 * 4454201 * 2
def baseEnd_4454201 : Nat := 2287146044737232651803009

theorem tailTrace_4454201 : CollatzResearch.WordTrace tailWord_4454201 prefixEnd_4454201 2287146044737232651803009 := by
  unfold tailWord_4454201
  simp only [CollatzResearch.WordTrace]
  refine ⟨162458056936197968812138457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108305371290798645874758971 162458056936197968812138457)
  ·
    refine ⟨121843542702148476609103843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162458056936197968812138457 121843542702148476609103843)
    ·
      refine ⟨182765314053222714913655765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121843542702148476609103843 182765314053222714913655765)
      ·
        refine ⟨4283562048122407380788807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 182765314053222714913655765 4283562048122407380788807)
        ·
          refine ⟨6425343072183611071183211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4283562048122407380788807 6425343072183611071183211)
          ·
            refine ⟨9638014608275416606774817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6425343072183611071183211 9638014608275416606774817)
            ·
              refine ⟨7228510956206562455081113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9638014608275416606774817 7228510956206562455081113)
              ·
                refine ⟨5421383217154921841310835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7228510956206562455081113 5421383217154921841310835)
                ·
                  refine ⟨8132074825732382761966253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5421383217154921841310835 8132074825732382761966253)
                  ·
                    refine ⟨3049528059649643535737345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8132074825732382761966253 3049528059649643535737345)
                    ·
                      refine ⟨2287146044737232651803009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3049528059649643535737345 2287146044737232651803009)
                      ·
                        rfl

theorem cell23_4454201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_4454201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4454201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4454201 prefixEnd_4454201 := by exact prefixLift 4454201
  have htrace : WordTrace (prefixWord ++ tailWord_4454201) baseStart_4454201 baseEnd_4454201 := by
    simpa [prefixWord, tailWord_4454201, baseEnd_4454201] using wordTrace_append hprefix tailTrace_4454201
  have hstable : (prefixWord ++ tailWord_4454201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4454201).length < 2 ^ (prefixWord ++ tailWord_4454201).sum := by decide
  have hdescent : baseEnd_4454201 < baseStart_4454201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4454201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4454283 : List Nat := [1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 6]
def baseStart_4454283 : Nat := 118140960795 + 4454283 * 2 ^ 59
def prefixEnd_4454283 : Nat := 4983230072969 + 3 ^ 40 * 4454283 * 2
def baseEnd_4454283 : Nat := 2287188150150901330977631

theorem tailTrace_4454283 : CollatzResearch.WordTrace tailWord_4454283 prefixEnd_4454283 2287188150150901330977631 := by
  unfold tailWord_4454283
  simp only [CollatzResearch.WordTrace]
  refine ⟨162461047721900896816623503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108307365147933931211082335 162461047721900896816623503)
  ·
    refine ⟨243691571582851345224935255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162461047721900896816623503 243691571582851345224935255)
    ·
      refine ⟨365537357374277017837402883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243691571582851345224935255 365537357374277017837402883)
      ·
        refine ⟨548306036061415526756104325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 365537357374277017837402883 548306036061415526756104325)
        ·
          refine ⟨102807381761515411266769561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 548306036061415526756104325 102807381761515411266769561)
          ·
            refine ⟨77105536321136558450077171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102807381761515411266769561 77105536321136558450077171)
            ·
              refine ⟨115658304481704837675115757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77105536321136558450077171 115658304481704837675115757)
              ·
                refine ⟨43371864180639314128168409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115658304481704837675115757 43371864180639314128168409)
                ·
                  refine ⟨32528898135479485596126307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43371864180639314128168409 32528898135479485596126307)
                  ·
                    refine ⟨48793347203219228394189461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32528898135479485596126307 48793347203219228394189461)
                    ·
                      refine ⟨2287188150150901330977631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48793347203219228394189461 2287188150150901330977631)
                      ·
                        rfl

theorem cell23_4454283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 6].length) (baseStart_4454283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4454283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4454283 prefixEnd_4454283 := by exact prefixLift 4454283
  have htrace : WordTrace (prefixWord ++ tailWord_4454283) baseStart_4454283 baseEnd_4454283 := by
    simpa [prefixWord, tailWord_4454283, baseEnd_4454283] using wordTrace_append hprefix tailTrace_4454283
  have hstable : (prefixWord ++ tailWord_4454283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4454283).length < 2 ^ (prefixWord ++ tailWord_4454283).sum := by decide
  have hdescent : baseEnd_4454283 < baseStart_4454283 := by decide
  rcases family_descends (prefixWord ++ tailWord_4454283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4454313 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 3, 2, 6]
def baseStart_4454313 : Nat := 118140960795 + 4454313 * 2 ^ 59
def prefixEnd_4454313 : Nat := 4983230072969 + 3 ^ 40 * 4454313 * 2
def baseEnd_4454313 : Nat := 2287203554570536213602493

theorem tailTrace_4454313 : CollatzResearch.WordTrace tailWord_4454313 prefixEnd_4454313 2287203554570536213602493 := by
  unfold tailWord_4454313
  simp only [CollatzResearch.WordTrace]
  refine ⟨162462141911792211940215593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108308094607861474626810395 162462141911792211940215593)
  ·
    refine ⟨121846606433844158955161695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162462141911792211940215593 121846606433844158955161695)
    ·
      refine ⟨182769909650766238432742543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121846606433844158955161695 182769909650766238432742543)
      ·
        refine ⟨274154864476149357649113815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182769909650766238432742543 274154864476149357649113815)
        ·
          refine ⟨411232296714224036473670723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 274154864476149357649113815 411232296714224036473670723)
          ·
            refine ⟨616848445071336054710506085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 411232296714224036473670723 616848445071336054710506085)
            ·
              refine ⟨115659083450875510258219891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 616848445071336054710506085 115659083450875510258219891)
              ·
                refine ⟨173488625176313265387329837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115659083450875510258219891 173488625176313265387329837)
                ·
                  refine ⟨65058234441117474520248689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 173488625176313265387329837 65058234441117474520248689)
                  ·
                    refine ⟨48793675830838105890186517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 65058234441117474520248689 48793675830838105890186517)
                    ·
                      refine ⟨2287203554570536213602493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48793675830838105890186517 2287203554570536213602493)
                      ·
                        rfl

theorem cell23_4454313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 2, 6].length) (baseStart_4454313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4454313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4454313 prefixEnd_4454313 := by exact prefixLift 4454313
  have htrace : WordTrace (prefixWord ++ tailWord_4454313) baseStart_4454313 baseEnd_4454313 := by
    simpa [prefixWord, tailWord_4454313, baseEnd_4454313] using wordTrace_append hprefix tailTrace_4454313
  have hstable : (prefixWord ++ tailWord_4454313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4454313).length < 2 ^ (prefixWord ++ tailWord_4454313).sum := by decide
  have hdescent : baseEnd_4454313 < baseStart_4454313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4454313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4454318 : List Nat := [4, 1, 5, 1, 1, 2, 1, 1, 2, 5]
def baseStart_4454318 : Nat := 118140960795 + 4454318 * 2 ^ 59
def prefixEnd_4454318 : Nat := 4983230072969 + 3 ^ 40 * 4454318 * 2
def baseEnd_4454318 : Nat := 762402040657936231346657

theorem tailTrace_4454318 : CollatzResearch.WordTrace tailWord_4454318 prefixEnd_4454318 762402040657936231346657 := by
  unfold tailWord_4454318
  simp only [CollatzResearch.WordTrace]
  refine ⟨20307790534596762224268451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108308216184516065196098405 20307790534596762224268451)
  ·
    refine ⟨30461685801895143336402677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20307790534596762224268451 30461685801895143336402677)
    ·
      refine ⟨2855783043927669687787751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30461685801895143336402677 2855783043927669687787751)
      ·
        refine ⟨4283674565891504531681627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2855783043927669687787751 4283674565891504531681627)
        ·
          refine ⟨6425511848837256797522441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4283674565891504531681627 6425511848837256797522441)
          ·
            refine ⟨4819133886627942598141831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6425511848837256797522441 4819133886627942598141831)
            ·
              refine ⟨7228700829941913897212747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4819133886627942598141831 7228700829941913897212747)
              ·
                refine ⟨10843051244912870845819121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7228700829941913897212747 10843051244912870845819121)
                ·
                  refine ⟨8132288433684653134364341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10843051244912870845819121 8132288433684653134364341)
                  ·
                    refine ⟨762402040657936231346657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8132288433684653134364341 762402040657936231346657)
                    ·
                      rfl

theorem cell23_4454318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_4454318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4454318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4454318 prefixEnd_4454318 := by exact prefixLift 4454318
  have htrace : WordTrace (prefixWord ++ tailWord_4454318) baseStart_4454318 baseEnd_4454318 := by
    simpa [prefixWord, tailWord_4454318, baseEnd_4454318] using wordTrace_append hprefix tailTrace_4454318
  have hstable : (prefixWord ++ tailWord_4454318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4454318).length < 2 ^ (prefixWord ++ tailWord_4454318).sum := by decide
  have hdescent : baseEnd_4454318 < baseStart_4454318 := by decide
  rcases family_descends (prefixWord ++ tailWord_4454318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4454347 : List Nat := [1, 1, 1, 1, 3, 4, 2, 1, 4, 3, 2]
def baseStart_4454347 : Nat := 118140960795 + 4454347 * 2 ^ 59
def prefixEnd_4454347 : Nat := 4983230072969 + 3 ^ 40 * 4454347 * 2
def baseEnd_4454347 : Nat := 2287221012912789080577337

theorem tailTrace_4454347 : CollatzResearch.WordTrace tailWord_4454347 prefixEnd_4454347 2287221012912789080577337 := by
  unfold tailWord_4454347
  simp only [CollatzResearch.WordTrace]
  refine ⟨162463381993669035746953295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108308921329112690497968863 162463381993669035746953295)
  ·
    refine ⟨243695072990503553620429943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162463381993669035746953295 243695072990503553620429943)
    ·
      refine ⟨365542609485755330430644915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243695072990503553620429943 365542609485755330430644915)
      ·
        refine ⟨548313914228632995645967373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 365542609485755330430644915 548313914228632995645967373)
        ·
          refine ⟨205617717835737373367237765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 548313914228632995645967373 205617717835737373367237765)
          ·
            refine ⟨38553322094200757506357081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 205617717835737373367237765 38553322094200757506357081)
            ·
              refine ⟨28914991570650568129767811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38553322094200757506357081 28914991570650568129767811)
              ·
                refine ⟨43372487355975852194651717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28914991570650568129767811 43372487355975852194651717)
                ·
                  refine ⟨8132341379245472286497197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43372487355975852194651717 8132341379245472286497197)
                  ·
                    refine ⟨3049628017217052107436449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8132341379245472286497197 3049628017217052107436449)
                    ·
                      refine ⟨2287221012912789080577337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3049628017217052107436449 2287221012912789080577337)
                      ·
                        rfl

theorem cell23_4454347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 4, 3, 2].length) (baseStart_4454347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4454347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4454347 prefixEnd_4454347 := by exact prefixLift 4454347
  have htrace : WordTrace (prefixWord ++ tailWord_4454347) baseStart_4454347 baseEnd_4454347 := by
    simpa [prefixWord, tailWord_4454347, baseEnd_4454347] using wordTrace_append hprefix tailTrace_4454347
  have hstable : (prefixWord ++ tailWord_4454347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4454347).length < 2 ^ (prefixWord ++ tailWord_4454347).sum := by decide
  have hdescent : baseEnd_4454347 < baseStart_4454347 := by decide
  rcases family_descends (prefixWord ++ tailWord_4454347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4454380 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 3]
def baseStart_4454380 : Nat := 118140960795 + 4454380 * 2 ^ 59
def prefixEnd_4454380 : Nat := 4983230072969 + 3 ^ 40 * 4454380 * 2
def baseEnd_4454380 : Nat := 2287237957774387451464685

theorem tailTrace_4454380 : CollatzResearch.WordTrace tailWord_4454380 prefixEnd_4454380 2287237957774387451464685 := by
  unfold tailWord_4454380
  simp only [CollatzResearch.WordTrace]
  refine ⟨81232292801274741191452297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108309723735032988255269729 81232292801274741191452297)
  ·
    refine ⟨60924219600956055893589223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81232292801274741191452297 60924219600956055893589223)
    ·
      refine ⟨91386329401434083840383835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60924219600956055893589223 91386329401434083840383835)
      ·
        refine ⟨137079494102151125760575753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91386329401434083840383835 137079494102151125760575753)
        ·
          refine ⟨102809620576613344320431815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137079494102151125760575753 102809620576613344320431815)
          ·
            refine ⟨154214430864920016480647723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102809620576613344320431815 154214430864920016480647723)
            ·
              refine ⟨231321646297380024720971585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154214430864920016480647723 231321646297380024720971585)
              ·
                refine ⟨173491234723035018540728689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 231321646297380024720971585 173491234723035018540728689)
                ·
                  refine ⟨130118426042276263905546517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 173491234723035018540728689 130118426042276263905546517)
                  ·
                    refine ⟨6099301220731699870572493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 130118426042276263905546517 6099301220731699870572493)
                    ·
                      refine ⟨2287237957774387451464685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6099301220731699870572493 2287237957774387451464685)
                      ·
                        rfl

theorem cell23_4454380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 3].length) (baseStart_4454380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4454380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4454380 prefixEnd_4454380 := by exact prefixLift 4454380
  have htrace : WordTrace (prefixWord ++ tailWord_4454380) baseStart_4454380 baseEnd_4454380 := by
    simpa [prefixWord, tailWord_4454380, baseEnd_4454380] using wordTrace_append hprefix tailTrace_4454380
  have hstable : (prefixWord ++ tailWord_4454380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4454380).length < 2 ^ (prefixWord ++ tailWord_4454380).sum := by decide
  have hdescent : baseEnd_4454380 < baseStart_4454380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4454380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4454427 : List Nat := [1, 1, 1, 1, 1, 1, 3, 4, 6, 1, 3]
def baseStart_4454427 : Nat := 118140960795 + 4454427 * 2 ^ 59
def prefixEnd_4454427 : Nat := 4983230072969 + 3 ^ 40 * 4454427 * 2
def baseEnd_4454427 : Nat := 2287262091365148767576969

theorem tailTrace_4454427 : CollatzResearch.WordTrace tailWord_4454427 prefixEnd_4454427 2287262091365148767576969 := by
  unfold tailWord_4454427
  simp only [CollatzResearch.WordTrace]
  refine ⟨162466299833379209409865535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108310866555586139606577023 162466299833379209409865535)
  ·
    refine ⟨243699449750068814114798303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162466299833379209409865535 243699449750068814114798303)
    ·
      refine ⟨365549174625103221172197455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243699449750068814114798303 365549174625103221172197455)
      ·
        refine ⟨548323761937654831758296183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 365549174625103221172197455 548323761937654831758296183)
        ·
          refine ⟨822485642906482247637444275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 548323761937654831758296183 822485642906482247637444275)
          ·
            refine ⟨1233728464359723371456166413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 822485642906482247637444275 1233728464359723371456166413)
            ·
              refine ⟨462648174134896264296062405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1233728464359723371456166413 462648174134896264296062405)
              ·
                refine ⟨86746532650293049555511701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 462648174134896264296062405 86746532650293049555511701)
                ·
                  refine ⟨4066243717982486697914611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 86746532650293049555511701 4066243717982486697914611)
                  ·
                    refine ⟨6099365576973730046871917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4066243717982486697914611 6099365576973730046871917)
                    ·
                      refine ⟨2287262091365148767576969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6099365576973730046871917 2287262091365148767576969)
                      ·
                        rfl

theorem cell23_4454427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6, 1, 3].length) (baseStart_4454427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4454427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4454427 prefixEnd_4454427 := by exact prefixLift 4454427
  have htrace : WordTrace (prefixWord ++ tailWord_4454427) baseStart_4454427 baseEnd_4454427 := by
    simpa [prefixWord, tailWord_4454427, baseEnd_4454427] using wordTrace_append hprefix tailTrace_4454427
  have hstable : (prefixWord ++ tailWord_4454427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4454427).length < 2 ^ (prefixWord ++ tailWord_4454427).sum := by decide
  have hdescent : baseEnd_4454427 < baseStart_4454427 := by decide
  rcases family_descends (prefixWord ++ tailWord_4454427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4454461 : List Nat := [1, 4, 1, 3, 1, 1, 4, 2, 2, 1, 3]
def baseStart_4454461 : Nat := 118140960795 + 4454461 * 2 ^ 59
def prefixEnd_4454461 : Nat := 4983230072969 + 3 ^ 40 * 4454461 * 2
def baseEnd_4454461 : Nat := 2287279549707401634551813

theorem tailTrace_4454461 : CollatzResearch.WordTrace tailWord_4454461 prefixEnd_4454461 2287279549707401634551813 := by
  unfold tailWord_4454461
  simp only [CollatzResearch.WordTrace]
  refine ⟨162467539915256033216603237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108311693276837355477735491 162467539915256033216603237)
  ·
    refine ⟨30462663734110506228113107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 162467539915256033216603237 30462663734110506228113107)
    ·
      refine ⟨45693995601165759342169661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30462663734110506228113107 45693995601165759342169661)
      ·
        refine ⟨17135248350437159753313623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45693995601165759342169661 17135248350437159753313623)
        ·
          refine ⟨25702872525655739629970435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17135248350437159753313623 25702872525655739629970435)
          ·
            refine ⟨38554308788483609444955653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25702872525655739629970435 38554308788483609444955653)
            ·
              refine ⟨7228932897840676770929185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38554308788483609444955653 7228932897840676770929185)
              ·
                refine ⟨5421699673380507578196889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7228932897840676770929185 5421699673380507578196889)
                ·
                  refine ⟨4066274755035380683647667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5421699673380507578196889 4066274755035380683647667)
                  ·
                    refine ⟨6099412132553071025471501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4066274755035380683647667 6099412132553071025471501)
                    ·
                      refine ⟨2287279549707401634551813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6099412132553071025471501 2287279549707401634551813)
                      ·
                        rfl

theorem cell23_4454461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_4454461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4454461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4454461 prefixEnd_4454461 := by exact prefixLift 4454461
  have htrace : WordTrace (prefixWord ++ tailWord_4454461) baseStart_4454461 baseEnd_4454461 := by
    simpa [prefixWord, tailWord_4454461, baseEnd_4454461] using wordTrace_append hprefix tailTrace_4454461
  have hstable : (prefixWord ++ tailWord_4454461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4454461).length < 2 ^ (prefixWord ++ tailWord_4454461).sum := by decide
  have hdescent : baseEnd_4454461 < baseStart_4454461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4454461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4454518 : List Nat := [5, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2]
def baseStart_4454518 : Nat := 118140960795 + 4454518 * 2 ^ 59
def prefixEnd_4454518 : Nat := 4983230072969 + 3 ^ 40 * 4454518 * 2
def baseEnd_4454518 : Nat := 2287308818104707911539051

theorem tailTrace_4454518 : CollatzResearch.WordTrace tailWord_4454518 prefixEnd_4454518 2287308818104707911539051 := by
  unfold tailWord_4454518
  simp only [CollatzResearch.WordTrace]
  refine ⟨10154351179753095746964263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 108313079250699687967618805 10154351179753095746964263)
  ·
    refine ⟨15231526769629643620446395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10154351179753095746964263 15231526769629643620446395)
    ·
      refine ⟨22847290154444465430669593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15231526769629643620446395 22847290154444465430669593)
      ·
        refine ⟨17135467615833349073002195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22847290154444465430669593 17135467615833349073002195)
        ·
          refine ⟨25703201423750023609503293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17135467615833349073002195 25703201423750023609503293)
          ·
            refine ⟨9638700533906258853563735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25703201423750023609503293 9638700533906258853563735)
            ·
              refine ⟨14458050800859388280345603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9638700533906258853563735 14458050800859388280345603)
              ·
                refine ⟨21687076201289082420518405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14458050800859388280345603 21687076201289082420518405)
                ·
                  refine ⟨4066326787741702953847201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21687076201289082420518405 4066326787741702953847201)
                  ·
                    refine ⟨3049745090806277215385401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4066326787741702953847201 3049745090806277215385401)
                    ·
                      refine ⟨2287308818104707911539051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3049745090806277215385401 2287308818104707911539051)
                      ·
                        rfl

theorem cell23_4454518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_4454518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4454518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4454518 prefixEnd_4454518 := by exact prefixLift 4454518
  have htrace : WordTrace (prefixWord ++ tailWord_4454518) baseStart_4454518 baseEnd_4454518 := by
    simpa [prefixWord, tailWord_4454518, baseEnd_4454518] using wordTrace_append hprefix tailTrace_4454518
  have hstable : (prefixWord ++ tailWord_4454518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4454518).length < 2 ^ (prefixWord ++ tailWord_4454518).sum := by decide
  have hdescent : baseEnd_4454518 < baseStart_4454518 := by decide
  rcases family_descends (prefixWord ++ tailWord_4454518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4454524 : List Nat := [2, 2, 2, 1, 1, 4, 2, 4, 5]
def baseStart_4454524 : Nat := 118140960795 + 4454524 * 2 ^ 59
def prefixEnd_4454524 : Nat := 4983230072969 + 3 ^ 40 * 4454524 * 2
def baseEnd_4454524 : Nat := 254145766554292765340447

theorem tailTrace_4454524 : CollatzResearch.WordTrace tailWord_4454524 prefixEnd_4454524 254145766554292765340447 := by
  unfold tailWord_4454524
  simp only [CollatzResearch.WordTrace]
  refine ⟨81234918857013897488073313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108313225142685196650764417 81234918857013897488073313)
  ·
    refine ⟨60926189142760423116054985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81234918857013897488073313 60926189142760423116054985)
    ·
      refine ⟨45694641857070317337041239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60926189142760423116054985 45694641857070317337041239)
      ·
        refine ⟨68541962785605476005561859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45694641857070317337041239 68541962785605476005561859)
        ·
          refine ⟨102812944178408214008342789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68541962785605476005561859 102812944178408214008342789)
          ·
            refine ⟨19277427033451540126564273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102812944178408214008342789 19277427033451540126564273)
            ·
              refine ⟨14458070275088655094923205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19277427033451540126564273 14458070275088655094923205)
              ·
                refine ⟨2710888176579122830298101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14458070275088655094923205 2710888176579122830298101)
                ·
                  refine ⟨254145766554292765340447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2710888176579122830298101 254145766554292765340447)
                  ·
                    rfl

theorem cell23_4454524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 4, 5].length) (baseStart_4454524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4454524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4454524 prefixEnd_4454524 := by exact prefixLift 4454524
  have htrace : WordTrace (prefixWord ++ tailWord_4454524) baseStart_4454524 baseEnd_4454524 := by
    simpa [prefixWord, tailWord_4454524, baseEnd_4454524] using wordTrace_append hprefix tailTrace_4454524
  have hstable : (prefixWord ++ tailWord_4454524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4454524).length < 2 ^ (prefixWord ++ tailWord_4454524).sum := by decide
  have hdescent : baseEnd_4454524 < baseStart_4454524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4454524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4454581 : List Nat := [1, 3, 3, 4, 1, 1, 1, 1, 1, 2, 5]
def baseStart_4454581 : Nat := 118140960795 + 4454581 * 2 ^ 59
def prefixEnd_4454581 : Nat := 4983230072969 + 3 ^ 40 * 4454581 * 2
def baseEnd_4454581 : Nat := 2287341167385941165051261

theorem tailTrace_4454581 : CollatzResearch.WordTrace tailWord_4454581 prefixEnd_4454581 2287341167385941165051261 := by
  unfold tailWord_4454581
  simp only [CollatzResearch.WordTrace]
  refine ⟨162471916674821293710971597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108314611116547529140647731 162471916674821293710971597)
  ·
    refine ⟨60926968753057985141614349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162471916674821293710971597 60926968753057985141614349)
    ·
      refine ⟨22847613282396744428105381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60926968753057985141614349 22847613282396744428105381)
      ·
        refine ⟨4283927490449389580269759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22847613282396744428105381 4283927490449389580269759)
        ·
          refine ⟨6425891235674084370404639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4283927490449389580269759 6425891235674084370404639)
          ·
            refine ⟨9638836853511126555606959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6425891235674084370404639 9638836853511126555606959)
            ·
              refine ⟨14458255280266689833410439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9638836853511126555606959 14458255280266689833410439)
              ·
                refine ⟨21687382920400034750115659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14458255280266689833410439 21687382920400034750115659)
                ·
                  refine ⟨32531074380600052125173489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21687382920400034750115659 32531074380600052125173489)
                  ·
                    refine ⟨24398305785450039093880117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32531074380600052125173489 24398305785450039093880117)
                    ·
                      refine ⟨2287341167385941165051261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24398305785450039093880117 2287341167385941165051261)
                      ·
                        rfl

theorem cell23_4454581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_4454581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4454581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4454581 prefixEnd_4454581 := by exact prefixLift 4454581
  have htrace : WordTrace (prefixWord ++ tailWord_4454581) baseStart_4454581 baseEnd_4454581 := by
    simpa [prefixWord, tailWord_4454581, baseEnd_4454581] using wordTrace_append hprefix tailTrace_4454581
  have hstable : (prefixWord ++ tailWord_4454581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4454581).length < 2 ^ (prefixWord ++ tailWord_4454581).sum := by decide
  have hdescent : baseEnd_4454581 < baseStart_4454581 := by decide
  rcases family_descends (prefixWord ++ tailWord_4454581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4454631 : List Nat := [1, 1, 5, 3, 1, 2, 2, 2, 6]
def baseStart_4454631 : Nat := 118140960795 + 4454631 * 2 ^ 59
def prefixEnd_4454631 : Nat := 4983230072969 + 3 ^ 40 * 4454631 * 2
def baseEnd_4454631 : Nat := 254151871268740663269559

theorem tailTrace_4454631 : CollatzResearch.WordTrace tailWord_4454631 prefixEnd_4454631 254151871268740663269559 := by
  unfold tailWord_4454631
  simp only [CollatzResearch.WordTrace]
  refine ⟨162473740324640152250291747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108315826883093434833527831 162473740324640152250291747)
  ·
    refine ⟨243710610486960228375437621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162473740324640152250291747 243710610486960228375437621)
    ·
      refine ⟨22847869733152521410197277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 243710610486960228375437621 22847869733152521410197277)
      ·
        refine ⟨8567951149932195528823979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22847869733152521410197277 8567951149932195528823979)
        ·
          refine ⟨12851926724898293293235969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8567951149932195528823979 12851926724898293293235969)
          ·
            refine ⟨9638945043673719969926977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12851926724898293293235969 9638945043673719969926977)
            ·
              refine ⟨7229208782755289977445233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9638945043673719969926977 7229208782755289977445233)
              ·
                refine ⟨5421906587066467483083925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7229208782755289977445233 5421906587066467483083925)
                ·
                  refine ⟨254151871268740663269559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5421906587066467483083925 254151871268740663269559)
                  ·
                    rfl

theorem cell23_4454631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 2, 6].length) (baseStart_4454631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4454631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4454631 prefixEnd_4454631 := by exact prefixLift 4454631
  have htrace : WordTrace (prefixWord ++ tailWord_4454631) baseStart_4454631 baseEnd_4454631 := by
    simpa [prefixWord, tailWord_4454631, baseEnd_4454631] using wordTrace_append hprefix tailTrace_4454631
  have hstable : (prefixWord ++ tailWord_4454631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4454631).length < 2 ^ (prefixWord ++ tailWord_4454631).sum := by decide
  have hdescent : baseEnd_4454631 < baseStart_4454631 := by decide
  rcases family_descends (prefixWord ++ tailWord_4454631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4454647 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 1, 7, 4]
def baseStart_4454647 : Nat := 118140960795 + 4454647 * 2 ^ 59
def prefixEnd_4454647 : Nat := 4983230072969 + 3 ^ 40 * 4454647 * 2
def baseEnd_4454647 : Nat := 2287375057109137906825957

theorem tailTrace_4454647 : CollatzResearch.WordTrace tailWord_4454647 prefixEnd_4454647 2287375057109137906825957 := by
  unfold tailWord_4454647
  simp only [CollatzResearch.WordTrace]
  refine ⟨162474323892582186982874195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108316215928388124655249463 162474323892582186982874195)
  ·
    refine ⟨243711485838873280474311293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162474323892582186982874195 243711485838873280474311293)
    ·
      refine ⟨91391807189577480177866735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 243711485838873280474311293 91391807189577480177866735)
      ·
        refine ⟨137087710784366220266800103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91391807189577480177866735 137087710784366220266800103)
        ·
          refine ⟨205631566176549330400200155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137087710784366220266800103 205631566176549330400200155)
          ·
            refine ⟨308447349264823995600300233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205631566176549330400200155 308447349264823995600300233)
            ·
              refine ⟨231335511948617996700225175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 308447349264823995600300233 231335511948617996700225175)
              ·
                refine ⟨347003267922926995050337763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 231335511948617996700225175 347003267922926995050337763)
                ·
                  refine ⟨520504901884390492575506645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 347003267922926995050337763 520504901884390492575506645)
                  ·
                    refine ⟨12199333637915402169738437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 520504901884390492575506645 12199333637915402169738437)
                    ·
                      refine ⟨2287375057109137906825957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12199333637915402169738437 2287375057109137906825957)
                      ·
                        rfl

theorem cell23_4454647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 7, 4].length) (baseStart_4454647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4454647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4454647 prefixEnd_4454647 := by exact prefixLift 4454647
  have htrace : WordTrace (prefixWord ++ tailWord_4454647) baseStart_4454647 baseEnd_4454647 := by
    simpa [prefixWord, tailWord_4454647, baseEnd_4454647] using wordTrace_append hprefix tailTrace_4454647
  have hstable : (prefixWord ++ tailWord_4454647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4454647).length < 2 ^ (prefixWord ++ tailWord_4454647).sum := by decide
  have hdescent : baseEnd_4454647 < baseStart_4454647 := by decide
  rcases family_descends (prefixWord ++ tailWord_4454647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4454654 : List Nat := [4, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7]
def baseStart_4454654 : Nat := 118140960795 + 4454654 * 2 ^ 59
def prefixEnd_4454654 : Nat := 4983230072969 + 3 ^ 40 * 4454654 * 2
def baseEnd_4454654 : Nat := 2287378651473719379438425

theorem tailTrace_4454654 : CollatzResearch.WordTrace tailWord_4454654 prefixEnd_4454654 2287378651473719379438425 := by
  unfold tailWord_4454654
  simp only [CollatzResearch.WordTrace]
  refine ⟨20309322400444603397297377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108316386135704551452252677 20309322400444603397297377)
  ·
    refine ⟨15231991800333452547973033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20309322400444603397297377 15231991800333452547973033)
    ·
      refine ⟨11423993850250089410979775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15231991800333452547973033 11423993850250089410979775)
      ·
        refine ⟨17135990775375134116469663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11423993850250089410979775 17135990775375134116469663)
        ·
          refine ⟨25703986163062701174704495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17135990775375134116469663 25703986163062701174704495)
          ·
            refine ⟨38555979244594051762056743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25703986163062701174704495 38555979244594051762056743)
            ·
              refine ⟨57833968866891077643085115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38555979244594051762056743 57833968866891077643085115)
              ·
                refine ⟨86750953300336616464627673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57833968866891077643085115 86750953300336616464627673)
                ·
                  refine ⟨65063214975252462348470755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86750953300336616464627673 65063214975252462348470755)
                  ·
                    refine ⟨97594822462878693522706133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 65063214975252462348470755 97594822462878693522706133)
                    ·
                      refine ⟨2287378651473719379438425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 97594822462878693522706133 2287378651473719379438425)
                      ·
                        rfl

theorem cell23_4454654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_4454654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4454654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4454654 prefixEnd_4454654 := by exact prefixLift 4454654
  have htrace : WordTrace (prefixWord ++ tailWord_4454654) baseStart_4454654 baseEnd_4454654 := by
    simpa [prefixWord, tailWord_4454654, baseEnd_4454654] using wordTrace_append hprefix tailTrace_4454654
  have hstable : (prefixWord ++ tailWord_4454654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4454654).length < 2 ^ (prefixWord ++ tailWord_4454654).sum := by decide
  have hdescent : baseEnd_4454654 < baseStart_4454654 := by decide
  rcases family_descends (prefixWord ++ tailWord_4454654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4454658 : List Nat := [3, 4, 1, 1, 2, 1, 1, 1, 5, 1, 3]
def baseStart_4454658 : Nat := 118140960795 + 4454658 * 2 ^ 59
def prefixEnd_4454658 : Nat := 4983230072969 + 3 ^ 40 * 4454658 * 2
def baseEnd_4454658 : Nat := 2287380705396337363788407

theorem tailTrace_4454658 : CollatzResearch.WordTrace tailWord_4454658 prefixEnd_4454658 2287380705396337363788407 := by
  unfold tailWord_4454658
  simp only [CollatzResearch.WordTrace]
  refine ⟨40618681273885583965381157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108316483397028223907683085 40618681273885583965381157)
  ·
    refine ⟨7616002738853546993508967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40618681273885583965381157 7616002738853546993508967)
    ·
      refine ⟨11424004108280320490263451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7616002738853546993508967 11424004108280320490263451)
      ·
        refine ⟨17136006162420480735395177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11424004108280320490263451 17136006162420480735395177)
        ·
          refine ⟨12852004621815360551546383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17136006162420480735395177 12852004621815360551546383)
          ·
            refine ⟨19278006932723040827319575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12852004621815360551546383 19278006932723040827319575)
            ·
              refine ⟨28917010399084561240979363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19278006932723040827319575 28917010399084561240979363)
              ·
                refine ⟨43375515598626841861469045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28917010399084561240979363 43375515598626841861469045)
                ·
                  refine ⟨4066454587371266424512723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43375515598626841861469045 4066454587371266424512723)
                  ·
                    refine ⟨6099681881056899636769085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4066454587371266424512723 6099681881056899636769085)
                    ·
                      refine ⟨2287380705396337363788407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6099681881056899636769085 2287380705396337363788407)
                      ·
                        rfl

theorem cell23_4454658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_4454658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4454658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4454658 prefixEnd_4454658 := by exact prefixLift 4454658
  have htrace : WordTrace (prefixWord ++ tailWord_4454658) baseStart_4454658 baseEnd_4454658 := by
    simpa [prefixWord, tailWord_4454658, baseEnd_4454658] using wordTrace_append hprefix tailTrace_4454658
  have hstable : (prefixWord ++ tailWord_4454658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4454658).length < 2 ^ (prefixWord ++ tailWord_4454658).sum := by decide
  have hdescent : baseEnd_4454658 < baseStart_4454658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4454658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4454684 : List Nat := [2, 2, 3, 1, 1, 1, 1, 5, 1, 1, 5]
def baseStart_4454684 : Nat := 118140960795 + 4454684 * 2 ^ 59
def prefixEnd_4454684 : Nat := 4983230072969 + 3 ^ 40 * 4454684 * 2
def baseEnd_4454684 : Nat := 2287394055893354262063287

theorem tailTrace_4454684 : CollatzResearch.WordTrace tailWord_4454684 prefixEnd_4454684 2287394055893354262063287 := by
  unfold tailWord_4454684
  simp only [CollatzResearch.WordTrace]
  refine ⟨81237836696724071150985553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108317115595632094867980737 81237836696724071150985553)
  ·
    refine ⟨60928377522543053363239165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81237836696724071150985553 60928377522543053363239165)
    ·
      refine ⟨22848141570953645011214687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60928377522543053363239165 22848141570953645011214687)
      ·
        refine ⟨34272212356430467516822031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22848141570953645011214687 34272212356430467516822031)
        ·
          refine ⟨51408318534645701275233047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34272212356430467516822031 51408318534645701275233047)
          ·
            refine ⟨77112477801968551912849571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51408318534645701275233047 77112477801968551912849571)
            ·
              refine ⟨115668716702952827869274357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77112477801968551912849571 115668716702952827869274357)
              ·
                refine ⟨10843942190901827612744471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 115668716702952827869274357 10843942190901827612744471)
                ·
                  refine ⟨16265913286352741419116707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10843942190901827612744471 16265913286352741419116707)
                  ·
                    refine ⟨24398869929529112128675061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16265913286352741419116707 24398869929529112128675061)
                    ·
                      refine ⟨2287394055893354262063287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24398869929529112128675061 2287394055893354262063287)
                      ·
                        rfl

theorem cell23_4454684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_4454684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4454684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4454684 prefixEnd_4454684 := by exact prefixLift 4454684
  have htrace : WordTrace (prefixWord ++ tailWord_4454684) baseStart_4454684 baseEnd_4454684 := by
    simpa [prefixWord, tailWord_4454684, baseEnd_4454684] using wordTrace_append hprefix tailTrace_4454684
  have hstable : (prefixWord ++ tailWord_4454684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4454684).length < 2 ^ (prefixWord ++ tailWord_4454684).sum := by decide
  have hdescent : baseEnd_4454684 < baseStart_4454684 := by decide
  rcases family_descends (prefixWord ++ tailWord_4454684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4454708 : List Nat := [2, 5, 1, 1, 1, 4, 1, 1, 1, 6]
def baseStart_4454708 : Nat := 118140960795 + 4454708 * 2 ^ 59
def prefixEnd_4454708 : Nat := 4983230072969 + 3 ^ 40 * 4454708 * 2
def baseEnd_4454708 : Nat := 762468793143020722721059

theorem tailTrace_4454708 : CollatzResearch.WordTrace tailWord_4454708 prefixEnd_4454708 762468793143020722721059 := by
  unfold tailWord_4454708
  simp only [CollatzResearch.WordTrace]
  refine ⟨81238274372680597200422389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108317699163574129600563185 81238274372680597200422389)
  ·
    refine ⟨7616088222438805987539599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 81238274372680597200422389 7616088222438805987539599)
    ·
      refine ⟨11424132333658208981309399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7616088222438805987539599 11424132333658208981309399)
      ·
        refine ⟨17136198500487313471964099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11424132333658208981309399 17136198500487313471964099)
        ·
          refine ⟨25704297750730970207946149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17136198500487313471964099 25704297750730970207946149)
          ·
            refine ⟨4819555828262056913989903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25704297750730970207946149 4819555828262056913989903)
            ·
              refine ⟨7229333742393085370984855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4819555828262056913989903 7229333742393085370984855)
              ·
                refine ⟨10844000613589628056477283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7229333742393085370984855 10844000613589628056477283)
                ·
                  refine ⟨16266000920384442084715925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10844000613589628056477283 16266000920384442084715925)
                  ·
                    refine ⟨762468793143020722721059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16266000920384442084715925 762468793143020722721059)
                    ·
                      rfl

theorem cell23_4454708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_4454708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4454708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4454708 prefixEnd_4454708 := by exact prefixLift 4454708
  have htrace : WordTrace (prefixWord ++ tailWord_4454708) baseStart_4454708 baseEnd_4454708 := by
    simpa [prefixWord, tailWord_4454708, baseEnd_4454708] using wordTrace_append hprefix tailTrace_4454708
  have hstable : (prefixWord ++ tailWord_4454708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4454708).length < 2 ^ (prefixWord ++ tailWord_4454708).sum := by decide
  have hdescent : baseEnd_4454708 < baseStart_4454708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4454708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4454718 : List Nat := [4, 2, 1, 2, 1, 2, 1, 4, 1, 2, 3]
def baseStart_4454718 : Nat := 118140960795 + 4454718 * 2 ^ 59
def prefixEnd_4454718 : Nat := 4983230072969 + 3 ^ 40 * 4454718 * 2
def baseEnd_4454718 : Nat := 2287411514235607129038131

theorem tailTrace_4454718 : CollatzResearch.WordTrace tailWord_4454718 prefixEnd_4454718 2287411514235607129038131 := by
  unfold tailWord_4454718
  simp only [CollatzResearch.WordTrace]
  refine ⟨20309614184415620763588601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108317942316883310739139205 20309614184415620763588601)
  ·
    refine ⟨15232210638311715572691451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20309614184415620763588601 15232210638311715572691451)
    ·
      refine ⟨22848315957467573359037177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15232210638311715572691451 22848315957467573359037177)
      ·
        refine ⟨17136236968100680019277883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22848315957467573359037177 17136236968100680019277883)
        ·
          refine ⟨25704355452151020028916825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17136236968100680019277883 25704355452151020028916825)
          ·
            refine ⟨19278266589113265021687619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25704355452151020028916825 19278266589113265021687619)
            ·
              refine ⟨28917399883669897532531429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19278266589113265021687619 28917399883669897532531429)
              ·
                refine ⟨5422012478188105787349643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28917399883669897532531429 5422012478188105787349643)
                ·
                  refine ⟨8133018717282158681024465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5422012478188105787349643 8133018717282158681024465)
                  ·
                    refine ⟨6099764037961619010768349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8133018717282158681024465 6099764037961619010768349)
                    ·
                      refine ⟨2287411514235607129038131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6099764037961619010768349 2287411514235607129038131)
                      ·
                        rfl

theorem cell23_4454718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_4454718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4454718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4454718 prefixEnd_4454718 := by exact prefixLift 4454718
  have htrace : WordTrace (prefixWord ++ tailWord_4454718) baseStart_4454718 baseEnd_4454718 := by
    simpa [prefixWord, tailWord_4454718, baseEnd_4454718] using wordTrace_append hprefix tailTrace_4454718
  have hstable : (prefixWord ++ tailWord_4454718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4454718).length < 2 ^ (prefixWord ++ tailWord_4454718).sum := by decide
  have hdescent : baseEnd_4454718 < baseStart_4454718 := by decide
  rcases family_descends (prefixWord ++ tailWord_4454718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4454721 : List Nat := [1, 2, 5, 2, 2, 1, 1, 9]
def baseStart_4454721 : Nat := 118140960795 + 4454721 * 2 ^ 59
def prefixEnd_4454721 : Nat := 4983230072969 + 3 ^ 40 * 4454721 * 2
def baseEnd_4454721 : Nat := 84719002025095208048171

theorem tailTrace_4454721 : CollatzResearch.WordTrace tailWord_4454721 prefixEnd_4454721 84719002025095208048171 := by
  unfold tailWord_4454721
  simp only [CollatzResearch.WordTrace]
  refine ⟨162477022894314097621068017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108318015262876065080712011 162477022894314097621068017)
  ·
    refine ⟨121857767170735573215801013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162477022894314097621068017 121857767170735573215801013)
    ·
      refine ⟨11424165672256459988981345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 121857767170735573215801013 11424165672256459988981345)
      ·
        refine ⟨8568124254192344991736009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11424165672256459988981345 8568124254192344991736009)
        ·
          refine ⟨6426093190644258743802007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8568124254192344991736009 6426093190644258743802007)
          ·
            refine ⟨9639139785966388115703011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6426093190644258743802007 9639139785966388115703011)
            ·
              refine ⟨14458709678949582173554517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9639139785966388115703011 14458709678949582173554517)
              ·
                refine ⟨84719002025095208048171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14458709678949582173554517 84719002025095208048171)
                ·
                  rfl

theorem cell23_4454721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 9].length) (baseStart_4454721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4454721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4454721 prefixEnd_4454721 := by exact prefixLift 4454721
  have htrace : WordTrace (prefixWord ++ tailWord_4454721) baseStart_4454721 baseEnd_4454721 := by
    simpa [prefixWord, tailWord_4454721, baseEnd_4454721] using wordTrace_append hprefix tailTrace_4454721
  have hstable : (prefixWord ++ tailWord_4454721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4454721).length < 2 ^ (prefixWord ++ tailWord_4454721).sum := by decide
  have hdescent : baseEnd_4454721 < baseStart_4454721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4454721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4454784 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 4]
def baseStart_4454784 : Nat := 118140960795 + 4454784 * 2 ^ 59
def prefixEnd_4454784 : Nat := 4983230072969 + 3 ^ 40 * 4454784 * 2
def baseEnd_4454784 : Nat := 2287445403958803870812827

theorem tailTrace_4454784 : CollatzResearch.WordTrace tailWord_4454784 prefixEnd_4454784 2287445403958803870812827 := by
  unfold tailWord_4454784
  simp only [CollatzResearch.WordTrace]
  refine ⟨81239660346542929690305703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108319547128723906253740937 81239660346542929690305703)
  ·
    refine ⟨121859490519814394535458555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81239660346542929690305703 121859490519814394535458555)
    ·
      refine ⟨182789235779721591803187833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121859490519814394535458555 182789235779721591803187833)
      ·
        refine ⟨137091926834791193852390875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182789235779721591803187833 137091926834791193852390875)
        ·
          refine ⟨205637890252186790778586313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137091926834791193852390875 205637890252186790778586313)
          ·
            refine ⟨154228417689140093083939735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 205637890252186790778586313 154228417689140093083939735)
            ·
              refine ⟨231342626533710139625909603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154228417689140093083939735 231342626533710139625909603)
              ·
                refine ⟨347013939800565209438864405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 231342626533710139625909603 347013939800565209438864405)
                ·
                  refine ⟨16266278428151494192446769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 347013939800565209438864405 16266278428151494192446769)
                  ·
                    refine ⟨12199708821113620644335077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16266278428151494192446769 12199708821113620644335077)
                    ·
                      refine ⟨2287445403958803870812827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12199708821113620644335077 2287445403958803870812827)
                      ·
                        rfl

theorem cell23_4454784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 4].length) (baseStart_4454784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4454784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4454784 prefixEnd_4454784 := by exact prefixLift 4454784
  have htrace : WordTrace (prefixWord ++ tailWord_4454784) baseStart_4454784 baseEnd_4454784 := by
    simpa [prefixWord, tailWord_4454784, baseEnd_4454784] using wordTrace_append hprefix tailTrace_4454784
  have hstable : (prefixWord ++ tailWord_4454784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4454784).length < 2 ^ (prefixWord ++ tailWord_4454784).sum := by decide
  have hdescent : baseEnd_4454784 < baseStart_4454784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4454784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4454788 : List Nat := [2, 3, 2, 1, 1, 2, 3, 2, 1, 4, 2]
def baseStart_4454788 : Nat := 118140960795 + 4454788 * 2 ^ 59
def prefixEnd_4454788 : Nat := 4983230072969 + 3 ^ 40 * 4454788 * 2
def baseEnd_4454788 : Nat := 2287447457881421855162809

theorem tailTrace_4454788 : CollatzResearch.WordTrace tailWord_4454788 prefixEnd_4454788 2287447457881421855162809 := by
  unfold tailWord_4454788
  simp only [CollatzResearch.WordTrace]
  refine ⟨81239733292535684031878509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108319644390047578709171345 81239733292535684031878509)
  ·
    refine ⟨30464899984700881511954441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81239733292535684031878509 30464899984700881511954441)
    ·
      refine ⟨22848674988525661133965831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30464899984700881511954441 22848674988525661133965831)
      ·
        refine ⟨34273012482788491700948747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22848674988525661133965831 34273012482788491700948747)
        ·
          refine ⟨51409518724182737551423121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34273012482788491700948747 51409518724182737551423121)
          ·
            refine ⟨38557139043137053163567341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51409518724182737551423121 38557139043137053163567341)
            ·
              refine ⟨14458927141176394936337753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38557139043137053163567341 14458927141176394936337753)
              ·
                refine ⟨10844195355882296202253315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14458927141176394936337753 10844195355882296202253315)
                ·
                  refine ⟨16266293033823444303379973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10844195355882296202253315 16266293033823444303379973)
                  ·
                    refine ⟨3049929943841895806883745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16266293033823444303379973 3049929943841895806883745)
                    ·
                      refine ⟨2287447457881421855162809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3049929943841895806883745 2287447457881421855162809)
                      ·
                        rfl

theorem cell23_4454788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 1, 4, 2].length) (baseStart_4454788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4454788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4454788 prefixEnd_4454788 := by exact prefixLift 4454788
  have htrace : WordTrace (prefixWord ++ tailWord_4454788) baseStart_4454788 baseEnd_4454788 := by
    simpa [prefixWord, tailWord_4454788, baseEnd_4454788] using wordTrace_append hprefix tailTrace_4454788
  have hstable : (prefixWord ++ tailWord_4454788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4454788).length < 2 ^ (prefixWord ++ tailWord_4454788).sum := by decide
  have hdescent : baseEnd_4454788 < baseStart_4454788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4454788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4454821 : List Nat := [1, 3, 1, 2, 1, 1, 5, 1, 2, 3, 3]
def baseStart_4454821 : Nat := 118140960795 + 4454821 * 2 ^ 59
def prefixEnd_4454821 : Nat := 4983230072969 + 3 ^ 40 * 4454821 * 2
def baseEnd_4454821 : Nat := 2287464402743020226050157

theorem tailTrace_4454821 : CollatzResearch.WordTrace tailWord_4454821 prefixEnd_4454821 2287464402743020226050157 := by
  unfold tailWord_4454821
  simp only [CollatzResearch.WordTrace]
  refine ⟨162480670193951814699708317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108320446795967876466472211 162480670193951814699708317)
  ·
    refine ⟨60930251322731930512390619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162480670193951814699708317 60930251322731930512390619)
    ·
      refine ⟨91395376984097895768585929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60930251322731930512390619 91395376984097895768585929)
      ·
        refine ⟨68546532738073421826439447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91395376984097895768585929 68546532738073421826439447)
        ·
          refine ⟨102819799107110132739659171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68546532738073421826439447 102819799107110132739659171)
          ·
            refine ⟨154229698660665199109488757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102819799107110132739659171 154229698660665199109488757)
            ·
              refine ⟨14459034249437362416514571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 154229698660665199109488757 14459034249437362416514571)
              ·
                refine ⟨21688551374156043624771857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14459034249437362416514571 21688551374156043624771857)
                ·
                  refine ⟨16266413530617032718578893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21688551374156043624771857 16266413530617032718578893)
                  ·
                    refine ⟨6099905073981387269467085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16266413530617032718578893 6099905073981387269467085)
                    ·
                      refine ⟨2287464402743020226050157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6099905073981387269467085 2287464402743020226050157)
                      ·
                        rfl

theorem cell23_4454821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 3, 3].length) (baseStart_4454821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4454821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4454821 prefixEnd_4454821 := by exact prefixLift 4454821
  have htrace : WordTrace (prefixWord ++ tailWord_4454821) baseStart_4454821 baseEnd_4454821 := by
    simpa [prefixWord, tailWord_4454821, baseEnd_4454821] using wordTrace_append hprefix tailTrace_4454821
  have hstable : (prefixWord ++ tailWord_4454821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4454821).length < 2 ^ (prefixWord ++ tailWord_4454821).sum := by decide
  have hdescent : baseEnd_4454821 < baseStart_4454821 := by decide
  rcases family_descends (prefixWord ++ tailWord_4454821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4454841 : List Nat := [1, 2, 1, 4, 3, 2, 1, 1, 1, 7]
def baseStart_4454841 : Nat := 118140960795 + 4454841 * 2 ^ 59
def prefixEnd_4454841 : Nat := 4983230072969 + 3 ^ 40 * 4454841 * 2
def baseEnd_4454841 : Nat := 762491557452036715933355

theorem tailTrace_4454841 : CollatzResearch.WordTrace tailWord_4454841 prefixEnd_4454841 762491557452036715933355 := by
  unfold tailWord_4454841
  simp only [CollatzResearch.WordTrace]
  refine ⟨162481399653879358115436377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108320933102586238743624251 162481399653879358115436377)
  ·
    refine ⟨121861049740409518586577283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162481399653879358115436377 121861049740409518586577283)
    ·
      refine ⟨182791574610614277879865925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121861049740409518586577283 182791574610614277879865925)
      ·
        refine ⟨34273420239490177102474861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 182791574610614277879865925 34273420239490177102474861)
        ·
          refine ⟨12852532589808816413428073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34273420239490177102474861 12852532589808816413428073)
          ·
            refine ⟨9639399442356612310071055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12852532589808816413428073 9639399442356612310071055)
            ·
              refine ⟨14459099163534918465106583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9639399442356612310071055 14459099163534918465106583)
              ·
                refine ⟨21688648745302377697659875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14459099163534918465106583 21688648745302377697659875)
                ·
                  refine ⟨32532973117953566546489813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21688648745302377697659875 32532973117953566546489813)
                  ·
                    refine ⟨762491557452036715933355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32532973117953566546489813 762491557452036715933355)
                    ·
                      rfl

theorem cell23_4454841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 7].length) (baseStart_4454841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4454841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4454841 prefixEnd_4454841 := by exact prefixLift 4454841
  have htrace : WordTrace (prefixWord ++ tailWord_4454841) baseStart_4454841 baseEnd_4454841 := by
    simpa [prefixWord, tailWord_4454841, baseEnd_4454841] using wordTrace_append hprefix tailTrace_4454841
  have hstable : (prefixWord ++ tailWord_4454841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4454841).length < 2 ^ (prefixWord ++ tailWord_4454841).sum := by decide
  have hdescent : baseEnd_4454841 < baseStart_4454841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4454841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4454881 : List Nat := [1, 2, 3, 1, 2, 2, 1, 1, 3, 4, 3]
def baseStart_4454881 : Nat := 118140960795 + 4454881 * 2 ^ 59
def prefixEnd_4454881 : Nat := 4983230072969 + 3 ^ 40 * 4454881 * 2
def baseEnd_4454881 : Nat := 2287495211582289991299881

theorem tailTrace_4454881 : CollatzResearch.WordTrace tailWord_4454881 prefixEnd_4454881 2287495211582289991299881 := by
  unfold tailWord_4454881
  simp only [CollatzResearch.WordTrace]
  refine ⟨162482858573734444946892497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108321905715822963297928331 162482858573734444946892497)
  ·
    refine ⟨121862143930300833710169373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162482858573734444946892497 121862143930300833710169373)
    ·
      refine ⟨45698303973862812641313515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121862143930300833710169373 45698303973862812641313515)
      ·
        refine ⟨68547455960794218961970273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45698303973862812641313515 68547455960794218961970273)
        ·
          refine ⟨51410591970595664221477705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68547455960794218961970273 51410591970595664221477705)
          ·
            refine ⟨38557943977946748166108279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51410591970595664221477705 38557943977946748166108279)
            ·
              refine ⟨57836915966920122249162419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38557943977946748166108279 57836915966920122249162419)
              ·
                refine ⟨86755373950380183373743629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57836915966920122249162419 86755373950380183373743629)
                ·
                  refine ⟨32533265231392568765153861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86755373950380183373743629 32533265231392568765153861)
                  ·
                    refine ⟨6099987230886106643466349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32533265231392568765153861 6099987230886106643466349)
                    ·
                      refine ⟨2287495211582289991299881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6099987230886106643466349 2287495211582289991299881)
                      ·
                        rfl

theorem cell23_4454881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 4, 3].length) (baseStart_4454881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4454881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4454881 prefixEnd_4454881 := by exact prefixLift 4454881
  have htrace : WordTrace (prefixWord ++ tailWord_4454881) baseStart_4454881 baseEnd_4454881 := by
    simpa [prefixWord, tailWord_4454881, baseEnd_4454881] using wordTrace_append hprefix tailTrace_4454881
  have hstable : (prefixWord ++ tailWord_4454881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4454881).length < 2 ^ (prefixWord ++ tailWord_4454881).sum := by decide
  have hdescent : baseEnd_4454881 < baseStart_4454881 := by decide
  rcases family_descends (prefixWord ++ tailWord_4454881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4454888 : List Nat := [2, 1, 4, 1, 1, 3, 2, 2, 3, 4]
def baseStart_4454888 : Nat := 118140960795 + 4454888 * 2 ^ 59
def prefixEnd_4454888 : Nat := 4983230072969 + 3 ^ 40 * 4454888 * 2
def baseEnd_4454888 : Nat := 762499601982290487970783

theorem tailTrace_4454888 : CollatzResearch.WordTrace tailWord_4454888 prefixEnd_4454888 762499601982290487970783 := by
  unfold tailWord_4454888
  simp only [CollatzResearch.WordTrace]
  refine ⟨81241556942354542571198659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108322075923139390094931545 81241556942354542571198659)
  ·
    refine ⟨121862335413531813856797989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81241556942354542571198659 121862335413531813856797989)
    ·
      refine ⟨22849187890037215098149623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121862335413531813856797989 22849187890037215098149623)
      ·
        refine ⟨34273781835055822647224435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22849187890037215098149623 34273781835055822647224435)
        ·
          refine ⟨51410672752583733970836653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34273781835055822647224435 51410672752583733970836653)
          ·
            refine ⟨19279002282218900239063745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51410672752583733970836653 19279002282218900239063745)
            ·
              refine ⟨14459251711664175179297809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19279002282218900239063745 14459251711664175179297809)
              ·
                refine ⟨10844438783748131384473357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14459251711664175179297809 10844438783748131384473357)
                ·
                  refine ⟨4066664543905549269177509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10844438783748131384473357 4066664543905549269177509)
                  ·
                    refine ⟨762499601982290487970783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4066664543905549269177509 762499601982290487970783)
                    ·
                      rfl

theorem cell23_4454888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_4454888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4454888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4454888 prefixEnd_4454888 := by exact prefixLift 4454888
  have htrace : WordTrace (prefixWord ++ tailWord_4454888) baseStart_4454888 baseEnd_4454888 := by
    simpa [prefixWord, tailWord_4454888, baseEnd_4454888] using wordTrace_append hprefix tailTrace_4454888
  have hstable : (prefixWord ++ tailWord_4454888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4454888).length < 2 ^ (prefixWord ++ tailWord_4454888).sum := by decide
  have hdescent : baseEnd_4454888 < baseStart_4454888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4454888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4454905 : List Nat := [1, 2, 1, 3, 1, 2, 5, 3, 1, 4]
def baseStart_4454905 : Nat := 118140960795 + 4454905 * 2 ^ 59
def prefixEnd_4454905 : Nat := 4983230072969 + 3 ^ 40 * 4454905 * 2
def baseEnd_4454905 : Nat := 762502511705999299133257

theorem tailTrace_4454905 : CollatzResearch.WordTrace tailWord_4454905 prefixEnd_4454905 762502511705999299133257 := by
  unfold tailWord_4454905
  simp only [CollatzResearch.WordTrace]
  refine ⟨162483733925647497045766169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108322489283764998030510779 162483733925647497045766169)
  ·
    refine ⟨121862800444235622784324627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162483733925647497045766169 121862800444235622784324627)
    ·
      refine ⟨182794200666353434176486941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121862800444235622784324627 182794200666353434176486941)
      ·
        refine ⟨68547825249882537816182603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 182794200666353434176486941 68547825249882537816182603)
        ·
          refine ⟨102821737874823806724273905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68547825249882537816182603 102821737874823806724273905)
          ·
            refine ⟨77116303406117855043205429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102821737874823806724273905 77116303406117855043205429)
            ·
              refine ⟨7229653444323548910300509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 77116303406117855043205429 7229653444323548910300509)
              ·
                refine ⟨2711120041621330841362691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7229653444323548910300509 2711120041621330841362691)
                ·
                  refine ⟨4066680062431996262044037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2711120041621330841362691 4066680062431996262044037)
                  ·
                    refine ⟨762502511705999299133257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4066680062431996262044037 762502511705999299133257)
                    ·
                      rfl

theorem cell23_4454905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 3, 1, 4].length) (baseStart_4454905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4454905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4454905 prefixEnd_4454905 := by exact prefixLift 4454905
  have htrace : WordTrace (prefixWord ++ tailWord_4454905) baseStart_4454905 baseEnd_4454905 := by
    simpa [prefixWord, tailWord_4454905, baseEnd_4454905] using wordTrace_append hprefix tailTrace_4454905
  have hstable : (prefixWord ++ tailWord_4454905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4454905).length < 2 ^ (prefixWord ++ tailWord_4454905).sum := by decide
  have hdescent : baseEnd_4454905 < baseStart_4454905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4454905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4454922 : List Nat := [3, 1, 2, 2, 2, 1, 5, 2, 1, 4]
def baseStart_4454922 : Nat := 118140960795 + 4454922 * 2 ^ 59
def prefixEnd_4454922 : Nat := 4983230072969 + 3 ^ 40 * 4454922 * 2
def baseEnd_4454922 : Nat := 762505421429708110295731

theorem tailTrace_4454922 : CollatzResearch.WordTrace tailWord_4454922 prefixEnd_4454922 762505421429708110295731 := by
  unfold tailWord_4454922
  simp only [CollatzResearch.WordTrace]
  refine ⟨40621088491646477237283755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108322902644390605966090013 40621088491646477237283755)
  ·
    refine ⟨60931632737469715855925633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40621088491646477237283755 60931632737469715855925633)
    ·
      refine ⟨45698724553102286891944225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60931632737469715855925633 45698724553102286891944225)
      ·
        refine ⟨34274043414826715168958169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45698724553102286891944225 34274043414826715168958169)
        ·
          refine ⟨25705532561120036376718627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34274043414826715168958169 25705532561120036376718627)
          ·
            refine ⟨38558298841680054565077941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25705532561120036376718627 38558298841680054565077941)
            ·
              refine ⟨3614840516407505115476057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38558298841680054565077941 3614840516407505115476057)
              ·
                refine ⟨2711130387305628836607043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3614840516407505115476057 2711130387305628836607043)
                ·
                  refine ⟨4066695580958443254910565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2711130387305628836607043 4066695580958443254910565)
                  ·
                    refine ⟨762505421429708110295731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4066695580958443254910565 762505421429708110295731)
                    ·
                      rfl

theorem cell23_4454922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 2, 1, 4].length) (baseStart_4454922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4454922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4454922 prefixEnd_4454922 := by exact prefixLift 4454922
  have htrace : WordTrace (prefixWord ++ tailWord_4454922) baseStart_4454922 baseEnd_4454922 := by
    simpa [prefixWord, tailWord_4454922, baseEnd_4454922] using wordTrace_append hprefix tailTrace_4454922
  have hstable : (prefixWord ++ tailWord_4454922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4454922).length < 2 ^ (prefixWord ++ tailWord_4454922).sum := by decide
  have hdescent : baseEnd_4454922 < baseStart_4454922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4454922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4454931 : List Nat := [1, 1, 1, 2, 1, 5, 2, 2, 3, 5]
def baseStart_4454931 : Nat := 118140960795 + 4454931 * 2 ^ 59
def prefixEnd_4454931 : Nat := 4983230072969 + 3 ^ 40 * 4454931 * 2
def baseEnd_4454931 : Nat := 762506961871671598558217

theorem tailTrace_4454931 : CollatzResearch.WordTrace tailWord_4454931 prefixEnd_4454931 762506961871671598558217 := by
  unfold tailWord_4454931
  simp only [CollatzResearch.WordTrace]
  refine ⟨162484682223553303486212647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108323121482368868990808431 162484682223553303486212647)
  ·
    refine ⟨243727023335329955229318971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162484682223553303486212647 243727023335329955229318971)
    ·
      refine ⟨365590535002994932843978457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243727023335329955229318971 365590535002994932843978457)
      ·
        refine ⟨274192901252246199632983843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 365590535002994932843978457 274192901252246199632983843)
        ·
          refine ⟨411289351878369299449475765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 274192901252246199632983843 411289351878369299449475765)
          ·
            refine ⟨38558376738597121823388353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 411289351878369299449475765 38558376738597121823388353)
            ·
              refine ⟨28918782553947841367541265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38558376738597121823388353 28918782553947841367541265)
              ·
                refine ⟨21689086915460881025655949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28918782553947841367541265 21689086915460881025655949)
                ·
                  refine ⟨8133407593297830384620981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21689086915460881025655949 8133407593297830384620981)
                  ·
                    refine ⟨762506961871671598558217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8133407593297830384620981 762506961871671598558217)
                    ·
                      rfl

theorem cell23_4454931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 3, 5].length) (baseStart_4454931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4454931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4454931 prefixEnd_4454931 := by exact prefixLift 4454931
  have htrace : WordTrace (prefixWord ++ tailWord_4454931) baseStart_4454931 baseEnd_4454931 := by
    simpa [prefixWord, tailWord_4454931, baseEnd_4454931] using wordTrace_append hprefix tailTrace_4454931
  have hstable : (prefixWord ++ tailWord_4454931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4454931).length < 2 ^ (prefixWord ++ tailWord_4454931).sum := by decide
  have hdescent : baseEnd_4454931 < baseStart_4454931 := by decide
  rcases family_descends (prefixWord ++ tailWord_4454931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4454935 : List Nat := [1, 1, 3, 6, 1, 1, 1, 3, 6]
def baseStart_4454935 : Nat := 118140960795 + 4454935 * 2 ^ 59
def prefixEnd_4454935 : Nat := 4983230072969 + 3 ^ 40 * 4454935 * 2
def baseEnd_4454935 : Nat := 254169215504181420002737

theorem tailTrace_4454935 : CollatzResearch.WordTrace tailWord_4454935 prefixEnd_4454935 254169215504181420002737 := by
  unfold tailWord_4454935
  simp only [CollatzResearch.WordTrace]
  refine ⟨162484828115538812169358259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108323218743692541446238839 162484828115538812169358259)
  ·
    refine ⟨243727242173308218254037389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162484828115538812169358259 243727242173308218254037389)
    ·
      refine ⟨91397715814990581845264021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 243727242173308218254037389 91397715814990581845264021)
      ·
        refine ⟨4284267928827683523996751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 91397715814990581845264021 4284267928827683523996751)
        ·
          refine ⟨6426401893241525285995127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4284267928827683523996751 6426401893241525285995127)
          ·
            refine ⟨9639602839862287928992691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6426401893241525285995127 9639602839862287928992691)
            ·
              refine ⟨14459404259793431893489037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9639602839862287928992691 14459404259793431893489037)
              ·
                refine ⟨5422276597422536960058389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14459404259793431893489037 5422276597422536960058389)
                ·
                  refine ⟨254169215504181420002737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5422276597422536960058389 254169215504181420002737)
                  ·
                    rfl

theorem cell23_4454935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 3, 6].length) (baseStart_4454935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4454935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4454935 prefixEnd_4454935 := by exact prefixLift 4454935
  have htrace : WordTrace (prefixWord ++ tailWord_4454935) baseStart_4454935 baseEnd_4454935 := by
    simpa [prefixWord, tailWord_4454935, baseEnd_4454935] using wordTrace_append hprefix tailTrace_4454935
  have hstable : (prefixWord ++ tailWord_4454935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4454935).length < 2 ^ (prefixWord ++ tailWord_4454935).sum := by decide
  have hdescent : baseEnd_4454935 < baseStart_4454935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4454935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4454938 : List Nat := [3, 1, 1, 3, 1, 1, 2, 1, 3, 5, 2]
def baseStart_4454938 : Nat := 118140960795 + 4454938 * 2 ^ 59
def prefixEnd_4454938 : Nat := 4983230072969 + 3 ^ 40 * 4454938 * 2
def baseEnd_4454938 : Nat := 2287524479979596268287119

theorem tailTrace_4454938 : CollatzResearch.WordTrace tailWord_4454938 prefixEnd_4454938 2287524479979596268287119 := by
  unfold tailWord_4454938
  simp only [CollatzResearch.WordTrace]
  refine ⟨40621234383631985920429367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108323291689685295787811645 40621234383631985920429367)
  ·
    refine ⟨60931851575447978880644051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40621234383631985920429367 60931851575447978880644051)
    ·
      refine ⟨91397777363171968320966077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60931851575447978880644051 91397777363171968320966077)
      ·
        refine ⟨34274166511189488120362279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91397777363171968320966077 34274166511189488120362279)
        ·
          refine ⟨51411249766784232180543419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34274166511189488120362279 51411249766784232180543419)
          ·
            refine ⟨77116874650176348270815129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51411249766784232180543419 77116874650176348270815129)
            ·
              refine ⟨57837655987632261203111347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77116874650176348270815129 57837655987632261203111347)
              ·
                refine ⟨86756483981448391804667021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57837655987632261203111347 86756483981448391804667021)
                ·
                  refine ⟨32533681493043146926750133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86756483981448391804667021 32533681493043146926750133)
                  ·
                    refine ⟨3050032639972795024382825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32533681493043146926750133 3050032639972795024382825)
                    ·
                      refine ⟨2287524479979596268287119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3050032639972795024382825 2287524479979596268287119)
                      ·
                        rfl

theorem cell23_4454938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 3, 5, 2].length) (baseStart_4454938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4454938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4454938 prefixEnd_4454938 := by exact prefixLift 4454938
  have htrace : WordTrace (prefixWord ++ tailWord_4454938) baseStart_4454938 baseEnd_4454938 := by
    simpa [prefixWord, tailWord_4454938, baseEnd_4454938] using wordTrace_append hprefix tailTrace_4454938
  have hstable : (prefixWord ++ tailWord_4454938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4454938).length < 2 ^ (prefixWord ++ tailWord_4454938).sum := by decide
  have hdescent : baseEnd_4454938 < baseStart_4454938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4454938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4454961 : List Nat := [1, 2, 2, 3, 1, 1, 3, 1, 3, 6]
def baseStart_4454961 : Nat := 118140960795 + 4454961 * 2 ^ 59
def prefixEnd_4454961 : Nat := 4983230072969 + 3 ^ 40 * 4454961 * 2
def baseEnd_4454961 : Nat := 762512096678216559433171

theorem tailTrace_4454961 : CollatzResearch.WordTrace tailWord_4454961 prefixEnd_4454961 762512096678216559433171 := by
  unfold tailWord_4454961
  simp only [CollatzResearch.WordTrace]
  refine ⟨162485776413444618609804737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108323850942296412406536491 162485776413444618609804737)
  ·
    refine ⟨121864332310083463957353553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162485776413444618609804737 121864332310083463957353553)
    ·
      refine ⟨91398249232562597968015165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121864332310083463957353553 91398249232562597968015165)
      ·
        refine ⟨34274343462210974238005687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91398249232562597968015165 34274343462210974238005687)
        ·
          refine ⟨51411515193316461357008531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34274343462210974238005687 51411515193316461357008531)
          ·
            refine ⟨77117272789974692035512797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51411515193316461357008531 77117272789974692035512797)
            ·
              refine ⟨28918977296240509513317299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77117272789974692035512797 28918977296240509513317299)
              ·
                refine ⟨43378465944360764269975949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28918977296240509513317299 43378465944360764269975949)
                ·
                  refine ⟨16266924729135286601240981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43378465944360764269975949 16266924729135286601240981)
                  ·
                    refine ⟨762512096678216559433171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16266924729135286601240981 762512096678216559433171)
                    ·
                      rfl

theorem cell23_4454961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 6].length) (baseStart_4454961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4454961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4454961 prefixEnd_4454961 := by exact prefixLift 4454961
  have htrace : WordTrace (prefixWord ++ tailWord_4454961) baseStart_4454961 baseEnd_4454961 := by
    simpa [prefixWord, tailWord_4454961, baseEnd_4454961] using wordTrace_append hprefix tailTrace_4454961
  have hstable : (prefixWord ++ tailWord_4454961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4454961).length < 2 ^ (prefixWord ++ tailWord_4454961).sum := by decide
  have hdescent : baseEnd_4454961 < baseStart_4454961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4454961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4454965 : List Nat := [1, 3, 3, 1, 1, 2, 5, 1, 1, 5]
def baseStart_4454965 : Nat := 118140960795 + 4454965 * 2 ^ 59
def prefixEnd_4454965 : Nat := 4983230072969 + 3 ^ 40 * 4454965 * 2
def baseEnd_4454965 : Nat := 762512781319089220883165

theorem tailTrace_4454965 : CollatzResearch.WordTrace tailWord_4454965 prefixEnd_4454965 762512781319089220883165 := by
  unfold tailWord_4454965
  simp only [CollatzResearch.WordTrace]
  refine ⟨162485922305430127292950349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108323948203620084861966899 162485922305430127292950349)
  ·
    refine ⟨60932220864536297734856381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162485922305430127292950349 60932220864536297734856381)
    ·
      refine ⟨22849582824201111650571143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60932220864536297734856381 22849582824201111650571143)
      ·
        refine ⟨34274374236301667475856715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22849582824201111650571143 34274374236301667475856715)
        ·
          refine ⟨51411561354452501213785073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34274374236301667475856715 51411561354452501213785073)
          ·
            refine ⟨38558671015839375910338805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51411561354452501213785073 38558671015839375910338805)
            ·
              refine ⟨3614875407734941491594263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38558671015839375910338805 3614875407734941491594263)
              ·
                refine ⟨5422313111602412237391395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3614875407734941491594263 5422313111602412237391395)
                ·
                  refine ⟨8133469667403618356087093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5422313111602412237391395 8133469667403618356087093)
                  ·
                    refine ⟨762512781319089220883165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8133469667403618356087093 762512781319089220883165)
                    ·
                      rfl

theorem cell23_4454965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_4454965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4454965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4454965 prefixEnd_4454965 := by exact prefixLift 4454965
  have htrace : WordTrace (prefixWord ++ tailWord_4454965) baseStart_4454965 baseEnd_4454965 := by
    simpa [prefixWord, tailWord_4454965, baseEnd_4454965] using wordTrace_append hprefix tailTrace_4454965
  have hstable : (prefixWord ++ tailWord_4454965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4454965).length < 2 ^ (prefixWord ++ tailWord_4454965).sum := by decide
  have hdescent : baseEnd_4454965 < baseStart_4454965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4454965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4454971 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 4, 6, 3]
def baseStart_4454971 : Nat := 118140960795 + 4454971 * 2 ^ 59
def prefixEnd_4454971 : Nat := 4983230072969 + 3 ^ 40 * 4454971 * 2
def baseEnd_4454971 : Nat := 2287541424841194639174467

theorem tailTrace_4454971 : CollatzResearch.WordTrace tailWord_4454971 prefixEnd_4454971 2287541424841194639174467 := by
  unfold tailWord_4454971
  simp only [CollatzResearch.WordTrace]
  refine ⟨162486141143408390317668767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108324094095605593545112511 162486141143408390317668767)
  ·
    refine ⟨243729211715112585476503151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162486141143408390317668767 243729211715112585476503151)
    ·
      refine ⟨365593817572668878214754727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243729211715112585476503151 365593817572668878214754727)
      ·
        refine ⟨548390726359003317322132091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 365593817572668878214754727 548390726359003317322132091)
        ·
          refine ⟨822586089538504975983198137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 548390726359003317322132091 822586089538504975983198137)
          ·
            refine ⟨616939567153878731987398603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 822586089538504975983198137 616939567153878731987398603)
            ·
              refine ⟨925409350730818097981097905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 616939567153878731987398603 925409350730818097981097905)
              ·
                refine ⟨694057013048113573485823429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 925409350730818097981097905 694057013048113573485823429)
                ·
                  refine ⟨130135689946521295028591893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 694057013048113573485823429 130135689946521295028591893)
                  ·
                    refine ⟨6100110466243185704465245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 130135689946521295028591893 6100110466243185704465245)
                    ·
                      refine ⟨2287541424841194639174467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6100110466243185704465245 2287541424841194639174467)
                      ·
                        rfl

theorem cell23_4454971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 6, 3].length) (baseStart_4454971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4454971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4454971 prefixEnd_4454971 := by exact prefixLift 4454971
  have htrace : WordTrace (prefixWord ++ tailWord_4454971) baseStart_4454971 baseEnd_4454971 := by
    simpa [prefixWord, tailWord_4454971, baseEnd_4454971] using wordTrace_append hprefix tailTrace_4454971
  have hstable : (prefixWord ++ tailWord_4454971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4454971).length < 2 ^ (prefixWord ++ tailWord_4454971).sum := by decide
  have hdescent : baseEnd_4454971 < baseStart_4454971 := by decide
  rcases family_descends (prefixWord ++ tailWord_4454971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4454988 : List Nat := [2, 2, 1, 3, 1, 2, 1, 1, 5, 2, 3]
def baseStart_4454988 : Nat := 118140960795 + 4454988 * 2 ^ 59
def prefixEnd_4454988 : Nat := 4983230072969 + 3 ^ 40 * 4454988 * 2
def baseEnd_4454988 : Nat := 2287550154012321072661889

theorem tailTrace_4454988 : CollatzResearch.WordTrace tailWord_4454988 prefixEnd_4454988 2287550154012321072661889 := by
  unfold tailWord_4454988
  simp only [CollatzResearch.WordTrace]
  refine ⟨81243380592173401110518809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108324507456231201480691745 81243380592173401110518809)
  ·
    refine ⟨60932535444130050832889107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81243380592173401110518809 60932535444130050832889107)
    ·
      refine ⟨91398803166195076249333661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60932535444130050832889107 91398803166195076249333661)
      ·
        refine ⟨34274551187323153593500123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91398803166195076249333661 34274551187323153593500123)
        ·
          refine ⟨51411826780984730390250185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34274551187323153593500123 51411826780984730390250185)
          ·
            refine ⟨38558870085738547792687639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51411826780984730390250185 38558870085738547792687639)
            ·
              refine ⟨57838305128607821689031459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38558870085738547792687639 57838305128607821689031459)
              ·
                refine ⟨86757457692911732533547189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57838305128607821689031459 86757457692911732533547189)
                ·
                  refine ⟨8133511658710474925020049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 86757457692911732533547189 8133511658710474925020049)
                  ·
                    refine ⟨6100133744032856193765037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8133511658710474925020049 6100133744032856193765037)
                    ·
                      refine ⟨2287550154012321072661889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6100133744032856193765037 2287550154012321072661889)
                      ·
                        rfl

theorem cell23_4454988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_4454988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4454988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4454988 prefixEnd_4454988 := by exact prefixLift 4454988
  have htrace : WordTrace (prefixWord ++ tailWord_4454988) baseStart_4454988 baseEnd_4454988 := by
    simpa [prefixWord, tailWord_4454988, baseEnd_4454988] using wordTrace_append hprefix tailTrace_4454988
  have hstable : (prefixWord ++ tailWord_4454988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4454988).length < 2 ^ (prefixWord ++ tailWord_4454988).sum := by decide
  have hdescent : baseEnd_4454988 < baseStart_4454988 := by decide
  rcases family_descends (prefixWord ++ tailWord_4454988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4454991 : List Nat := [1, 1, 2, 1, 1, 2, 7, 8]
def baseStart_4454991 : Nat := 118140960795 + 4454991 * 2 ^ 59
def prefixEnd_4454991 : Nat := 4983230072969 + 3 ^ 40 * 4454991 * 2
def baseEnd_4454991 : Nat := 84724136831640168923125

theorem tailTrace_4454991 : CollatzResearch.WordTrace tailWord_4454991 prefixEnd_4454991 84724136831640168923125 := by
  unfold tailWord_4454991
  simp only [CollatzResearch.WordTrace]
  refine ⟨162486870603335933733396827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108324580402223955822264551 162486870603335933733396827)
  ·
    refine ⟨243730305905003900600095241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162486870603335933733396827 243730305905003900600095241)
    ·
      refine ⟨182797729428752925450071431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243730305905003900600095241 182797729428752925450071431)
      ·
        refine ⟨274196594143129388175107147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182797729428752925450071431 274196594143129388175107147)
        ·
          refine ⟨411294891214694082262660721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 274196594143129388175107147 411294891214694082262660721)
          ·
            refine ⟨308471168411020561696995541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 411294891214694082262660721 308471168411020561696995541)
            ·
              refine ⟨7229793009633294414773333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 308471168411020561696995541 7229793009633294414773333)
              ·
                refine ⟨84724136831640168923125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7229793009633294414773333 84724136831640168923125)
                ·
                  rfl

theorem cell23_4454991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 8].length) (baseStart_4454991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4454991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4454991 prefixEnd_4454991 := by exact prefixLift 4454991
  have htrace : WordTrace (prefixWord ++ tailWord_4454991) baseStart_4454991 baseEnd_4454991 := by
    simpa [prefixWord, tailWord_4454991, baseEnd_4454991] using wordTrace_append hprefix tailTrace_4454991
  have hstable : (prefixWord ++ tailWord_4454991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4454991).length < 2 ^ (prefixWord ++ tailWord_4454991).sum := by decide
  have hdescent : baseEnd_4454991 < baseStart_4454991 := by decide
  rcases family_descends (prefixWord ++ tailWord_4454991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4455006 : List Nat := [4, 4, 1, 2, 1, 1, 1, 1, 1, 5, 2]
def baseStart_4455006 : Nat := 118140960795 + 4455006 * 2 ^ 59
def prefixEnd_4455006 : Nat := 4983230072969 + 3 ^ 40 * 4455006 * 2
def baseEnd_4455006 : Nat := 2287559396664102002236807

theorem tailTrace_4455006 : CollatzResearch.WordTrace tailWord_4455006 prefixEnd_4455006 2287559396664102002236807 := by
  unfold tailWord_4455006
  simp only [CollatzResearch.WordTrace]
  refine ⟨20310927212285198911899109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108324945132187727530128581 20310927212285198911899109)
  ·
    refine ⟨3808298852303474795981083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20310927212285198911899109 3808298852303474795981083)
    ·
      refine ⟨5712448278455212193971625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3808298852303474795981083 5712448278455212193971625)
      ·
        refine ⟨4284336208841409145478719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5712448278455212193971625 4284336208841409145478719)
        ·
          refine ⟨6426504313262113718218079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4284336208841409145478719 6426504313262113718218079)
          ·
            refine ⟨9639756469893170577327119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6426504313262113718218079 9639756469893170577327119)
            ·
              refine ⟨14459634704839755865990679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9639756469893170577327119 14459634704839755865990679)
              ·
                refine ⟨21689452057259633798986019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14459634704839755865990679 21689452057259633798986019)
                ·
                  refine ⟨32534178085889450698479029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21689452057259633798986019 32534178085889450698479029)
                  ·
                    refine ⟨3050079195552136002982409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32534178085889450698479029 3050079195552136002982409)
                    ·
                      refine ⟨2287559396664102002236807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3050079195552136002982409 2287559396664102002236807)
                      ·
                        rfl

theorem cell23_4455006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_4455006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4455006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4455006 prefixEnd_4455006 := by exact prefixLift 4455006
  have htrace : WordTrace (prefixWord ++ tailWord_4455006) baseStart_4455006 baseEnd_4455006 := by
    simpa [prefixWord, tailWord_4455006, baseEnd_4455006] using wordTrace_append hprefix tailTrace_4455006
  have hstable : (prefixWord ++ tailWord_4455006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4455006).length < 2 ^ (prefixWord ++ tailWord_4455006).sum := by decide
  have hdescent : baseEnd_4455006 < baseStart_4455006 := by decide
  rcases family_descends (prefixWord ++ tailWord_4455006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4455022 : List Nat := [4, 1, 2, 2, 2, 2, 1, 3, 1, 2, 3]
def baseStart_4455022 : Nat := 118140960795 + 4455022 * 2 ^ 59
def prefixEnd_4455022 : Nat := 4983230072969 + 3 ^ 40 * 4455022 * 2
def baseEnd_4455022 : Nat := 2287567612354573939636733

theorem tailTrace_4455022 : CollatzResearch.WordTrace tailWord_4455022 prefixEnd_4455022 2287567612354573939636733 := by
  unfold tailWord_4455022
  simp only [CollatzResearch.WordTrace]
  refine ⟨20311000158277953253471915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108325334177482417351850213 20311000158277953253471915)
  ·
    refine ⟨30466500237416929880207873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20311000158277953253471915 30466500237416929880207873)
    ·
      refine ⟨22849875178062697410155905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30466500237416929880207873 22849875178062697410155905)
      ·
        refine ⟨17137406383547023057616929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22849875178062697410155905 17137406383547023057616929)
        ·
          refine ⟨12853054787660267293212697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17137406383547023057616929 12853054787660267293212697)
          ·
            refine ⟨9639791090745200469909523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12853054787660267293212697 9639791090745200469909523)
            ·
              refine ⟨14459686636117800704864285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9639791090745200469909523 14459686636117800704864285)
              ·
                refine ⟨5422382488544175264324107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14459686636117800704864285 5422382488544175264324107)
                ·
                  refine ⟨8133573732816262896486161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5422382488544175264324107 8133573732816262896486161)
                  ·
                    refine ⟨6100180299612197172364621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8133573732816262896486161 6100180299612197172364621)
                    ·
                      refine ⟨2287567612354573939636733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6100180299612197172364621 2287567612354573939636733)
                      ·
                        rfl

theorem cell23_4455022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_4455022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4455022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4455022 prefixEnd_4455022 := by exact prefixLift 4455022
  have htrace : WordTrace (prefixWord ++ tailWord_4455022) baseStart_4455022 baseEnd_4455022 := by
    simpa [prefixWord, tailWord_4455022, baseEnd_4455022] using wordTrace_append hprefix tailTrace_4455022
  have hstable : (prefixWord ++ tailWord_4455022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4455022).length < 2 ^ (prefixWord ++ tailWord_4455022).sum := by decide
  have hdescent : baseEnd_4455022 < baseStart_4455022 := by decide
  rcases family_descends (prefixWord ++ tailWord_4455022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4455029 : List Nat := [1, 3, 4, 2, 2, 2, 1, 2, 2, 4]
def baseStart_4455029 : Nat := 118140960795 + 4455029 * 2 ^ 59
def prefixEnd_4455029 : Nat := 4983230072969 + 3 ^ 40 * 4455029 * 2
def baseEnd_4455029 : Nat := 762523735573051804083067

theorem tailTrace_4455029 : CollatzResearch.WordTrace tailWord_4455029 prefixEnd_4455029 762523735573051804083067 := by
  unfold tailWord_4455029
  simp only [CollatzResearch.WordTrace]
  refine ⟨162488256577198266223280141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108325504384798844148853427 162488256577198266223280141)
  ·
    refine ⟨60933096216449349833730053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162488256577198266223280141 60933096216449349833730053)
    ·
      refine ⟨11424955540584253093824385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60933096216449349833730053 11424955540584253093824385)
      ·
        refine ⟨8568716655438189820368289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11424955540584253093824385 8568716655438189820368289)
        ·
          refine ⟨6426537491578642365276217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8568716655438189820368289 6426537491578642365276217)
          ·
            refine ⟨4819903118683981773957163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6426537491578642365276217 4819903118683981773957163)
            ·
              refine ⟨7229854678025972660935745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4819903118683981773957163 7229854678025972660935745)
              ·
                refine ⟨5422391008519479495701809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7229854678025972660935745 5422391008519479495701809)
                ·
                  refine ⟨4066793256389609621776357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5422391008519479495701809 4066793256389609621776357)
                  ·
                    refine ⟨762523735573051804083067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4066793256389609621776357 762523735573051804083067)
                    ·
                      rfl

theorem cell23_4455029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_4455029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4455029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4455029 prefixEnd_4455029 := by exact prefixLift 4455029
  have htrace : WordTrace (prefixWord ++ tailWord_4455029) baseStart_4455029 baseEnd_4455029 := by
    simpa [prefixWord, tailWord_4455029, baseEnd_4455029] using wordTrace_append hprefix tailTrace_4455029
  have hstable : (prefixWord ++ tailWord_4455029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4455029).length < 2 ^ (prefixWord ++ tailWord_4455029).sum := by decide
  have hdescent : baseEnd_4455029 < baseStart_4455029 := by decide
  rcases family_descends (prefixWord ++ tailWord_4455029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4455035 : List Nat := [1, 1, 1, 1, 1, 4, 2, 6, 2, 1, 3]
def baseStart_4455035 : Nat := 118140960795 + 4455035 * 2 ^ 59
def prefixEnd_4455035 : Nat := 4983230072969 + 3 ^ 40 * 4455035 * 2
def baseEnd_4455035 : Nat := 2287574287603082388774173

theorem tailTrace_4455035 : CollatzResearch.WordTrace tailWord_4455035 prefixEnd_4455035 2287574287603082388774173 := by
  unfold tailWord_4455035
  simp only [CollatzResearch.WordTrace]
  refine ⟨162488475415176529247998559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108325650276784352831999039 162488475415176529247998559)
  ·
    refine ⟨243732713122764793871997839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162488475415176529247998559 243732713122764793871997839)
    ·
      refine ⟨365599069684147190807996759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243732713122764793871997839 365599069684147190807996759)
      ·
        refine ⟨548398604526220786211995139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 365599069684147190807996759 548398604526220786211995139)
        ·
          refine ⟨822597906789331179317992709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 548398604526220786211995139 822597906789331179317992709)
          ·
            refine ⟨154237107522999596122123633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 822597906789331179317992709 154237107522999596122123633)
            ·
              refine ⟨115677830642249697091592725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154237107522999596122123633 115677830642249697091592725)
              ·
                refine ⟨5422398311355454551168409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 115677830642249697091592725 5422398311355454551168409)
                ·
                  refine ⟨4066798733516590913376307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5422398311355454551168409 4066798733516590913376307)
                  ·
                    refine ⟨6100198100274886370064461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4066798733516590913376307 6100198100274886370064461)
                    ·
                      refine ⟨2287574287603082388774173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6100198100274886370064461 2287574287603082388774173)
                      ·
                        rfl

theorem cell23_4455035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 6, 2, 1, 3].length) (baseStart_4455035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4455035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4455035 prefixEnd_4455035 := by exact prefixLift 4455035
  have htrace : WordTrace (prefixWord ++ tailWord_4455035) baseStart_4455035 baseEnd_4455035 := by
    simpa [prefixWord, tailWord_4455035, baseEnd_4455035] using wordTrace_append hprefix tailTrace_4455035
  have hstable : (prefixWord ++ tailWord_4455035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4455035).length < 2 ^ (prefixWord ++ tailWord_4455035).sum := by decide
  have hdescent : baseEnd_4455035 < baseStart_4455035 := by decide
  rcases family_descends (prefixWord ++ tailWord_4455035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4455051 : List Nat := [1, 1, 1, 1, 4, 1, 2, 3, 1, 8]
def baseStart_4455051 : Nat := 118140960795 + 4455051 * 2 ^ 59
def prefixEnd_4455051 : Nat := 4983230072969 + 3 ^ 40 * 4455051 * 2
def baseEnd_4455051 : Nat := 762527501097851442058033

theorem tailTrace_4455051 : CollatzResearch.WordTrace tailWord_4455051 prefixEnd_4455051 762527501097851442058033 := by
  unfold tailWord_4455051
  simp only [CollatzResearch.WordTrace]
  refine ⟨162489058983118563980581007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108326039322079042653720671 162489058983118563980581007)
  ·
    refine ⟨243733588474677845970871511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162489058983118563980581007 243733588474677845970871511)
    ·
      refine ⟨365600382712016768956307267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243733588474677845970871511 365600382712016768956307267)
      ·
        refine ⟨548400574068025153434460901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 365600382712016768956307267 548400574068025153434460901)
        ·
          refine ⟨102825107637754716268961419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 548400574068025153434460901 102825107637754716268961419)
          ·
            refine ⟨154237661456632074403442129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102825107637754716268961419 154237661456632074403442129)
            ·
              refine ⟨115678246092474055802581597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154237661456632074403442129 115678246092474055802581597)
              ·
                refine ⟨43379342284677770925968099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115678246092474055802581597 43379342284677770925968099)
                ·
                  refine ⟨65069013427016656388952149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43379342284677770925968099 65069013427016656388952149)
                  ·
                    refine ⟨762527501097851442058033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 65069013427016656388952149 762527501097851442058033)
                    ·
                      rfl

theorem cell23_4455051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 8].length) (baseStart_4455051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4455051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4455051 prefixEnd_4455051 := by exact prefixLift 4455051
  have htrace : WordTrace (prefixWord ++ tailWord_4455051) baseStart_4455051 baseEnd_4455051 := by
    simpa [prefixWord, tailWord_4455051, baseEnd_4455051] using wordTrace_append hprefix tailTrace_4455051
  have hstable : (prefixWord ++ tailWord_4455051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4455051).length < 2 ^ (prefixWord ++ tailWord_4455051).sum := by decide
  have hdescent : baseEnd_4455051 < baseStart_4455051 := by decide
  rcases family_descends (prefixWord ++ tailWord_4455051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4455081 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 11]
def baseStart_4455081 : Nat := 118140960795 + 4455081 * 2 ^ 59
def prefixEnd_4455081 : Nat := 4983230072969 + 3 ^ 40 * 4455081 * 2
def baseEnd_4455081 : Nat := 254177545301465467644329

theorem tailTrace_4455081 : CollatzResearch.WordTrace tailWord_4455081 prefixEnd_4455081 254177545301465467644329 := by
  unfold tailWord_4455081
  simp only [CollatzResearch.WordTrace]
  refine ⟨162490153173009879104173097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108326768782006586069448731 162490153173009879104173097)
  ·
    refine ⟨121867614879757409328129823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162490153173009879104173097 121867614879757409328129823)
    ·
      refine ⟨182801422319636113992194735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121867614879757409328129823 182801422319636113992194735)
      ·
        refine ⟨274202133479454170988292103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182801422319636113992194735 274202133479454170988292103)
        ·
          refine ⟨411303200219181256482438155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 274202133479454170988292103 411303200219181256482438155)
          ·
            refine ⟨616954800328771884723657233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 411303200219181256482438155 616954800328771884723657233)
            ·
              refine ⟨462716100246578913542742925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 616954800328771884723657233 462716100246578913542742925)
              ·
                refine ⟨173518537592467092578528597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 462716100246578913542742925 173518537592467092578528597)
                ·
                  refine ⟨254177545301465467644329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 173518537592467092578528597 254177545301465467644329)
                  ·
                    rfl

theorem cell23_4455081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 11].length) (baseStart_4455081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4455081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4455081 prefixEnd_4455081 := by exact prefixLift 4455081
  have htrace : WordTrace (prefixWord ++ tailWord_4455081) baseStart_4455081 baseEnd_4455081 := by
    simpa [prefixWord, tailWord_4455081, baseEnd_4455081] using wordTrace_append hprefix tailTrace_4455081
  have hstable : (prefixWord ++ tailWord_4455081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4455081).length < 2 ^ (prefixWord ++ tailWord_4455081).sum := by decide
  have hdescent : baseEnd_4455081 < baseStart_4455081 := by decide
  rcases family_descends (prefixWord ++ tailWord_4455081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4455148 : List Nat := [2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 4]
def baseStart_4455148 : Nat := 118140960795 + 4455148 * 2 ^ 59
def prefixEnd_4455148 : Nat := 4983230072969 + 3 ^ 40 * 4455148 * 2
def baseEnd_4455148 : Nat := 2287632310917040446661153

theorem tailTrace_4455148 : CollatzResearch.WordTrace tailWord_4455148 prefixEnd_4455148 2287632310917040446661153 := by
  unfold tailWord_4455148
  simp only [CollatzResearch.WordTrace]
  refine ⟨81246298431883574773431049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108328397909178099697908065 81246298431883574773431049)
  ·
    refine ⟨60934723823912681080073287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81246298431883574773431049 60934723823912681080073287)
    ·
      refine ⟨91402085735869021620109931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60934723823912681080073287 91402085735869021620109931)
      ·
        refine ⟨137103128603803532430164897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91402085735869021620109931 137103128603803532430164897)
        ·
          refine ⟨102827346452852649322623673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137103128603803532430164897 102827346452852649322623673)
          ·
            refine ⟨77120509839639486991967755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102827346452852649322623673 77120509839639486991967755)
            ·
              refine ⟨115680764759459230487951633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77120509839639486991967755 115680764759459230487951633)
              ·
                refine ⟨86760573569594422865963725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115680764759459230487951633 86760573569594422865963725)
                ·
                  refine ⟨32535215088597908574736397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86760573569594422865963725 32535215088597908574736397)
                  ·
                    refine ⟨12200705658224215715526149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32535215088597908574736397 12200705658224215715526149)
                    ·
                      refine ⟨2287632310917040446661153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12200705658224215715526149 2287632310917040446661153)
                      ·
                        rfl

theorem cell23_4455148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 4].length) (baseStart_4455148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4455148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4455148 prefixEnd_4455148 := by exact prefixLift 4455148
  have htrace : WordTrace (prefixWord ++ tailWord_4455148) baseStart_4455148 baseEnd_4455148 := by
    simpa [prefixWord, tailWord_4455148, baseEnd_4455148] using wordTrace_append hprefix tailTrace_4455148
  have hstable : (prefixWord ++ tailWord_4455148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4455148).length < 2 ^ (prefixWord ++ tailWord_4455148).sum := by decide
  have hdescent : baseEnd_4455148 < baseStart_4455148 := by decide
  rcases family_descends (prefixWord ++ tailWord_4455148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4455275 : List Nat := [1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 5]
def baseStart_4455275 : Nat := 118140960795 + 4455275 * 2 ^ 59
def prefixEnd_4455275 : Nat := 4983230072969 + 3 ^ 40 * 4455275 * 2
def baseEnd_4455275 : Nat := 2287697522960161449773069

theorem tailTrace_4455275 : CollatzResearch.WordTrace tailWord_4455275 prefixEnd_4455275 2287697522960161449773069 := by
  unfold tailWord_4455275
  simp only [CollatzResearch.WordTrace]
  refine ⟨162497228934307050236735279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108331485956204700157823519 162497228934307050236735279)
  ·
    refine ⟨243745843401460575355102919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162497228934307050236735279 243745843401460575355102919)
    ·
      refine ⟨365618765102190863032654379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243745843401460575355102919 365618765102190863032654379)
      ·
        refine ⟨548428147653286294548981569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 365618765102190863032654379 548428147653286294548981569)
        ·
          refine ⟨411321110739964720911736177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 548428147653286294548981569 411321110739964720911736177)
          ·
            refine ⟨308490833054973540683802133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 411321110739964720911736177 308490833054973540683802133)
            ·
              refine ⟨14460507799451884719553225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 308490833054973540683802133 14460507799451884719553225)
              ·
                refine ⟨10845380849588913539664919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14460507799451884719553225 10845380849588913539664919)
                ·
                  refine ⟨16268071274383370309497379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10845380849588913539664919 16268071274383370309497379)
                  ·
                    refine ⟨24402106911575055464246069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16268071274383370309497379 24402106911575055464246069)
                    ·
                      refine ⟨2287697522960161449773069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24402106911575055464246069 2287697522960161449773069)
                      ·
                        rfl

theorem cell23_4455275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 5].length) (baseStart_4455275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4455275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4455275 prefixEnd_4455275 := by exact prefixLift 4455275
  have htrace : WordTrace (prefixWord ++ tailWord_4455275) baseStart_4455275 baseEnd_4455275 := by
    simpa [prefixWord, tailWord_4455275, baseEnd_4455275] using wordTrace_append hprefix tailTrace_4455275
  have hstable : (prefixWord ++ tailWord_4455275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4455275).length < 2 ^ (prefixWord ++ tailWord_4455275).sum := by decide
  have hdescent : baseEnd_4455275 < baseStart_4455275 := by decide
  rcases family_descends (prefixWord ++ tailWord_4455275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4455286 : List Nat := [5, 1, 1, 3, 1, 3, 1, 2, 1, 5]
def baseStart_4455286 : Nat := 118140960795 + 4455286 * 2 ^ 59
def prefixEnd_4455286 : Nat := 4983230072969 + 3 ^ 40 * 4455286 * 2
def baseEnd_4455286 : Nat := 762567723749120302245173

theorem tailTrace_4455286 : CollatzResearch.WordTrace tailWord_4455286 prefixEnd_4455286 762567723749120302245173 := by
  unfold tailWord_4455286
  simp only [CollatzResearch.WordTrace]
  refine ⟨10156101883579199944711607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 108331753424844799410257141 10156101883579199944711607)
  ·
    refine ⟨15234152825368799917067411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10156101883579199944711607 15234152825368799917067411)
    ·
      refine ⟨22851229238053199875601117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15234152825368799917067411 22851229238053199875601117)
      ·
        refine ⟨8569210964269949953350419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22851229238053199875601117 8569210964269949953350419)
        ·
          refine ⟨12853816446404924930025629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8569210964269949953350419 12853816446404924930025629)
          ·
            refine ⟨4820181167401846848759611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12853816446404924930025629 4820181167401846848759611)
            ·
              refine ⟨7230271751102770273139417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4820181167401846848759611 7230271751102770273139417)
              ·
                refine ⟨5422703813327077704854563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7230271751102770273139417 5422703813327077704854563)
                ·
                  refine ⟨8134055719990616557281845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5422703813327077704854563 8134055719990616557281845)
                  ·
                    refine ⟨762567723749120302245173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8134055719990616557281845 762567723749120302245173)
                    ·
                      rfl

theorem cell23_4455286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_4455286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4455286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4455286 prefixEnd_4455286 := by exact prefixLift 4455286
  have htrace : WordTrace (prefixWord ++ tailWord_4455286) baseStart_4455286 baseEnd_4455286 := by
    simpa [prefixWord, tailWord_4455286, baseEnd_4455286] using wordTrace_append hprefix tailTrace_4455286
  have hstable : (prefixWord ++ tailWord_4455286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4455286).length < 2 ^ (prefixWord ++ tailWord_4455286).sum := by decide
  have hdescent : baseEnd_4455286 < baseStart_4455286 := by decide
  rcases family_descends (prefixWord ++ tailWord_4455286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4455289 : List Nat := [1, 2, 1, 3, 2, 5, 1, 2, 1, 1, 4]
def baseStart_4455289 : Nat := 118140960795 + 4455289 * 2 ^ 59
def prefixEnd_4455289 : Nat := 4983230072969 + 3 ^ 40 * 4455289 * 2
def baseEnd_4455289 : Nat := 2287704711689324394998005

theorem tailTrace_4455289 : CollatzResearch.WordTrace tailWord_4455289 prefixEnd_4455289 2287704711689324394998005 := by
  unfold tailWord_4455289
  simp only [CollatzResearch.WordTrace]
  refine ⟨162497739556256330627744921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108331826370837553751829947 162497739556256330627744921)
  ·
    refine ⟨121873304667192247970808691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162497739556256330627744921 121873304667192247970808691)
    ·
      refine ⟨182809957000788371956213037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121873304667192247970808691 182809957000788371956213037)
      ·
        refine ⟨68553733875295639483579889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 182809957000788371956213037 68553733875295639483579889)
        ·
          refine ⟨51415300406471729612684917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68553733875295639483579889 51415300406471729612684917)
          ·
            refine ⟨4820184413106724651189211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51415300406471729612684917 4820184413106724651189211)
            ·
              refine ⟨7230276619660086976783817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4820184413106724651189211 7230276619660086976783817)
              ·
                refine ⟨5422707464745065232587863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7230276619660086976783817 5422707464745065232587863)
                ·
                  refine ⟨8134061197117597848881795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5422707464745065232587863 8134061197117597848881795)
                  ·
                    refine ⟨12201091795676396773322693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8134061197117597848881795 12201091795676396773322693)
                    ·
                      refine ⟨2287704711689324394998005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12201091795676396773322693 2287704711689324394998005)
                      ·
                        rfl

theorem cell23_4455289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 2, 1, 1, 4].length) (baseStart_4455289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4455289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4455289 prefixEnd_4455289 := by exact prefixLift 4455289
  have htrace : WordTrace (prefixWord ++ tailWord_4455289) baseStart_4455289 baseEnd_4455289 := by
    simpa [prefixWord, tailWord_4455289, baseEnd_4455289] using wordTrace_append hprefix tailTrace_4455289
  have hstable : (prefixWord ++ tailWord_4455289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4455289).length < 2 ^ (prefixWord ++ tailWord_4455289).sum := by decide
  have hdescent : baseEnd_4455289 < baseStart_4455289 := by decide
  rcases family_descends (prefixWord ++ tailWord_4455289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4455306 : List Nat := [3, 1, 2, 4, 1, 2, 3, 1, 1, 1, 4]
def baseStart_4455306 : Nat := 118140960795 + 4455306 * 2 ^ 59
def prefixEnd_4455306 : Nat := 4983230072969 + 3 ^ 40 * 4455306 * 2
def baseEnd_4455306 : Nat := 2287713440860450828485427

theorem tailTrace_4455306 : CollatzResearch.WordTrace tailWord_4455306 prefixEnd_4455306 2287713440860450828485427 := by
  unfold tailWord_4455306
  simp only [CollatzResearch.WordTrace]
  refine ⟨40624589899298685632778443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108332239731463161687409181 40624589899298685632778443)
  ·
    refine ⟨60936884848948028449167665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40624589899298685632778443 60936884848948028449167665)
    ·
      refine ⟨45702663636711021336875749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60936884848948028449167665 45702663636711021336875749)
      ·
        refine ⟨8569249431883316500664203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45702663636711021336875749 8569249431883316500664203)
        ·
          refine ⟨12853874147824974750996305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8569249431883316500664203 12853874147824974750996305)
          ·
            refine ⟨9640405610868731063247229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12853874147824974750996305 9640405610868731063247229)
            ·
              refine ⟨3615152104075774148717711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9640405610868731063247229 3615152104075774148717711)
              ·
                refine ⟨5422728156113661223076567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3615152104075774148717711 5422728156113661223076567)
                ·
                  refine ⟨8134092234170491834614851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5422728156113661223076567 8134092234170491834614851)
                  ·
                    refine ⟨12201138351255737751922277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8134092234170491834614851 12201138351255737751922277)
                    ·
                      refine ⟨2287713440860450828485427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12201138351255737751922277 2287713440860450828485427)
                      ·
                        rfl

theorem cell23_4455306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_4455306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4455306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4455306 prefixEnd_4455306 := by exact prefixLift 4455306
  have htrace : WordTrace (prefixWord ++ tailWord_4455306) baseStart_4455306 baseEnd_4455306 := by
    simpa [prefixWord, tailWord_4455306, baseEnd_4455306] using wordTrace_append hprefix tailTrace_4455306
  have hstable : (prefixWord ++ tailWord_4455306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4455306).length < 2 ^ (prefixWord ++ tailWord_4455306).sum := by decide
  have hdescent : baseEnd_4455306 < baseStart_4455306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4455306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4455325 : List Nat := [1, 4, 2, 1, 2, 1, 1, 1, 1, 9]
def baseStart_4455325 : Nat := 118140960795 + 4455325 * 2 ^ 59
def prefixEnd_4455325 : Nat := 4983230072969 + 3 ^ 40 * 4455325 * 2
def baseEnd_4455325 : Nat := 762574398997628751382613

theorem tailTrace_4455325 : CollatzResearch.WordTrace tailWord_4455325 prefixEnd_4455325 762574398997628751382613 := by
  unfold tailWord_4455325
  simp only [CollatzResearch.WordTrace]
  refine ⟨162499052584125908776055429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108332701722750605850703619 162499052584125908776055429)
  ·
    refine ⟨30468572359523607895510393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 162499052584125908776055429 30468572359523607895510393)
    ·
      refine ⟨22851429269642705921632795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30468572359523607895510393 22851429269642705921632795)
      ·
        refine ⟨34277143904464058882449193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22851429269642705921632795 34277143904464058882449193)
        ·
          refine ⟨25707857928348044161836895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34277143904464058882449193 25707857928348044161836895)
          ·
            refine ⟨38561786892522066242755343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25707857928348044161836895 38561786892522066242755343)
            ·
              refine ⟨57842680338783099364133015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38561786892522066242755343 57842680338783099364133015)
              ·
                refine ⟨86764020508174649046199523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57842680338783099364133015 86764020508174649046199523)
                ·
                  refine ⟨130146030762261973569299285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86764020508174649046199523 130146030762261973569299285)
                  ·
                    refine ⟨762574398997628751382613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 130146030762261973569299285 762574398997628751382613)
                    ·
                      rfl

theorem cell23_4455325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_4455325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4455325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4455325 prefixEnd_4455325 := by exact prefixLift 4455325
  have htrace : WordTrace (prefixWord ++ tailWord_4455325) baseStart_4455325 baseEnd_4455325 := by
    simpa [prefixWord, tailWord_4455325, baseEnd_4455325] using wordTrace_append hprefix tailTrace_4455325
  have hstable : (prefixWord ++ tailWord_4455325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4455325).length < 2 ^ (prefixWord ++ tailWord_4455325).sum := by decide
  have hdescent : baseEnd_4455325 < baseStart_4455325 := by decide
  rcases family_descends (prefixWord ++ tailWord_4455325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4455349 : List Nat := [1, 3, 3, 2, 1, 1, 1, 3, 3, 3, 2]
def baseStart_4455349 : Nat := 118140960795 + 4455349 * 2 ^ 59
def prefixEnd_4455349 : Nat := 4983230072969 + 3 ^ 40 * 4455349 * 2
def baseEnd_4455349 : Nat := 2287735520528594160247729

theorem tailTrace_4455349 : CollatzResearch.WordTrace tailWord_4455349 prefixEnd_4455349 2287735520528594160247729 := by
  unfold tailWord_4455349
  simp only [CollatzResearch.WordTrace]
  refine ⟨162499927936038960874929101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108333285290692640583286067 162499927936038960874929101)
  ·
    refine ⟨60937472976014610328098413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162499927936038960874929101 60937472976014610328098413)
    ·
      refine ⟨22851552366005478873036905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60937472976014610328098413 22851552366005478873036905)
      ·
        refine ⟨17138664274504109154777679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22851552366005478873036905 17138664274504109154777679)
        ·
          refine ⟨25707996411756163732166519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17138664274504109154777679 25707996411756163732166519)
          ·
            refine ⟨38561994617634245598249779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25707996411756163732166519 38561994617634245598249779)
            ·
              refine ⟨57842991926451368397374669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38561994617634245598249779 57842991926451368397374669)
              ·
                refine ⟨21691121972419263149015501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57842991926451368397374669 21691121972419263149015501)
                ·
                  refine ⟨8134170739657223680880813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21691121972419263149015501 8134170739657223680880813)
                  ·
                    refine ⟨3050314027371458880330305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8134170739657223680880813 3050314027371458880330305)
                    ·
                      refine ⟨2287735520528594160247729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3050314027371458880330305 2287735520528594160247729)
                      ·
                        rfl

theorem cell23_4455349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_4455349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4455349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4455349 prefixEnd_4455349 := by exact prefixLift 4455349
  have htrace : WordTrace (prefixWord ++ tailWord_4455349) baseStart_4455349 baseEnd_4455349 := by
    simpa [prefixWord, tailWord_4455349, baseEnd_4455349] using wordTrace_append hprefix tailTrace_4455349
  have hstable : (prefixWord ++ tailWord_4455349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4455349).length < 2 ^ (prefixWord ++ tailWord_4455349).sum := by decide
  have hdescent : baseEnd_4455349 < baseStart_4455349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4455349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4455365 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 6, 1, 5]
def baseStart_4455365 : Nat := 118140960795 + 4455365 * 2 ^ 59
def prefixEnd_4455365 : Nat := 4983230072969 + 3 ^ 40 * 4455365 * 2
def baseEnd_4455365 : Nat := 2287743736219066097647655

theorem tailTrace_4455365 : CollatzResearch.WordTrace tailWord_4455365 prefixEnd_4455365 2287743736219066097647655 := by
  unfold tailWord_4455365
  simp only [CollatzResearch.WordTrace]
  refine ⟨162500511503980995607511549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108333674335987330405007699 162500511503980995607511549)
  ·
    refine ⟨60937691813992873352816831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162500511503980995607511549 60937691813992873352816831)
    ·
      refine ⟨91406537720989310029225247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60937691813992873352816831 91406537720989310029225247)
      ·
        refine ⟨137109806581483965043837871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91406537720989310029225247 137109806581483965043837871)
        ·
          refine ⟨205664709872225947565756807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137109806581483965043837871 205664709872225947565756807)
          ·
            refine ⟨308497064808338921348635211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205664709872225947565756807 308497064808338921348635211)
            ·
              refine ⟨462745597212508382022952817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 308497064808338921348635211 462745597212508382022952817)
              ·
                refine ⟨347059197909381286517214613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 462745597212508382022952817 347059197909381286517214613)
                ·
                  refine ⟨16268399902002247805494435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 347059197909381286517214613 16268399902002247805494435)
                  ·
                    refine ⟨24402599853003371708241653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16268399902002247805494435 24402599853003371708241653)
                    ·
                      refine ⟨2287743736219066097647655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24402599853003371708241653 2287743736219066097647655)
                      ·
                        rfl

theorem cell23_4455365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 1, 5].length) (baseStart_4455365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4455365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4455365 prefixEnd_4455365 := by exact prefixLift 4455365
  have htrace : WordTrace (prefixWord ++ tailWord_4455365) baseStart_4455365 baseEnd_4455365 := by
    simpa [prefixWord, tailWord_4455365, baseEnd_4455365] using wordTrace_append hprefix tailTrace_4455365
  have hstable : (prefixWord ++ tailWord_4455365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4455365).length < 2 ^ (prefixWord ++ tailWord_4455365).sum := by decide
  have hdescent : baseEnd_4455365 < baseStart_4455365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4455365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4455402 : List Nat := [3, 1, 3, 1, 2, 2, 2, 2, 7]
def baseStart_4455402 : Nat := 118140960795 + 4455402 * 2 ^ 59
def prefixEnd_4455402 : Nat := 4983230072969 + 3 ^ 40 * 4455402 * 2
def baseEnd_4455402 : Nat := 254195859444809161431665

theorem tailTrace_4455402 : CollatzResearch.WordTrace tailWord_4455402 prefixEnd_4455402 254195859444809161431665 := by
  unfold tailWord_4455402
  simp only [CollatzResearch.WordTrace]
  refine ⟨40625465251211737731652115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108334574003231300617738973 40625465251211737731652115)
  ·
    refine ⟨60938197876817606597478173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40625465251211737731652115 60938197876817606597478173)
    ·
      refine ⟨22851824203806602474054315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60938197876817606597478173 22851824203806602474054315)
      ·
        refine ⟨34277736305709903711081473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22851824203806602474054315 34277736305709903711081473)
        ·
          refine ⟨25708302229282427783311105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34277736305709903711081473 25708302229282427783311105)
          ·
            refine ⟨19281226671961820837483329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25708302229282427783311105 19281226671961820837483329)
            ·
              refine ⟨14460920003971365628112497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19281226671961820837483329 14460920003971365628112497)
              ·
                refine ⟨10845690002978524221084373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14460920003971365628112497 10845690002978524221084373)
                ·
                  refine ⟨254195859444809161431665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10845690002978524221084373 254195859444809161431665)
                  ·
                    rfl

theorem cell23_4455402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 7].length) (baseStart_4455402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4455402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4455402 prefixEnd_4455402 := by exact prefixLift 4455402
  have htrace : WordTrace (prefixWord ++ tailWord_4455402) baseStart_4455402 baseEnd_4455402 := by
    simpa [prefixWord, tailWord_4455402, baseEnd_4455402] using wordTrace_append hprefix tailTrace_4455402
  have hstable : (prefixWord ++ tailWord_4455402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4455402).length < 2 ^ (prefixWord ++ tailWord_4455402).sum := by decide
  have hdescent : baseEnd_4455402 < baseStart_4455402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4455402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4455432 : List Nat := [2, 1, 3, 2, 1, 3, 1, 1, 4, 5]
def baseStart_4455432 : Nat := 118140960795 + 4455432 * 2 ^ 59
def prefixEnd_4455432 : Nat := 4983230072969 + 3 ^ 40 * 4455432 * 2
def baseEnd_4455432 : Nat := 762592713140972445169949

theorem tailTrace_4455432 : CollatzResearch.WordTrace tailWord_4455432 prefixEnd_4455432 762592713140972445169949 := by
  unfold tailWord_4455432
  simp only [CollatzResearch.WordTrace]
  refine ⟨81251477597369133025100275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108335303463158844033467033 81251477597369133025100275)
  ·
    refine ⟨121877216396053699537650413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81251477597369133025100275 121877216396053699537650413)
    ·
      refine ⟨45703956148520137326618905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121877216396053699537650413 45703956148520137326618905)
      ·
        refine ⟨34277967111390102994964179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45703956148520137326618905 34277967111390102994964179)
        ·
          refine ⟨51416950667085154492446269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34277967111390102994964179 51416950667085154492446269)
          ·
            refine ⟨19281356500156932934667351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51416950667085154492446269 19281356500156932934667351)
            ·
              refine ⟨28922034750235399402001027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19281356500156932934667351 28922034750235399402001027)
              ·
                refine ⟨43383052125353099103001541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28922034750235399402001027 43383052125353099103001541)
                ·
                  refine ⟨8134322273503706081812789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43383052125353099103001541 8134322273503706081812789)
                  ·
                    refine ⟨762592713140972445169949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8134322273503706081812789 762592713140972445169949)
                    ·
                      rfl

theorem cell23_4455432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 4, 5].length) (baseStart_4455432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4455432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4455432 prefixEnd_4455432 := by exact prefixLift 4455432
  have htrace : WordTrace (prefixWord ++ tailWord_4455432) baseStart_4455432 baseEnd_4455432 := by
    simpa [prefixWord, tailWord_4455432, baseEnd_4455432] using wordTrace_append hprefix tailTrace_4455432
  have hstable : (prefixWord ++ tailWord_4455432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4455432).length < 2 ^ (prefixWord ++ tailWord_4455432).sum := by decide
  have hdescent : baseEnd_4455432 < baseStart_4455432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4455432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4455436 : List Nat := [2, 2, 1, 2, 3, 3, 3, 2, 5]
def baseStart_4455436 : Nat := 118140960795 + 4455436 * 2 ^ 59
def prefixEnd_4455436 : Nat := 4983230072969 + 3 ^ 40 * 4455436 * 2
def baseEnd_4455436 : Nat := 254197799260615035539981

theorem tailTrace_4455436 : CollatzResearch.WordTrace tailWord_4455436 prefixEnd_4455436 254197799260615035539981 := by
  unfold tailWord_4455436
  simp only [CollatzResearch.WordTrace]
  refine ⟨81251550543361887366673081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108335400724482516488897441 81251550543361887366673081)
  ·
    refine ⟨60938662907521415525004811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81251550543361887366673081 60938662907521415525004811)
    ·
      refine ⟨91407994361282123287507217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60938662907521415525004811 91407994361282123287507217)
      ·
        refine ⟨68555995770961592465630413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91407994361282123287507217 68555995770961592465630413)
        ·
          refine ⟨25708498414110597174611405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68555995770961592465630413 25708498414110597174611405)
          ·
            refine ⟨9640686905291473940479277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25708498414110597174611405 9640686905291473940479277)
            ·
              refine ⟨3615257589484302727679729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9640686905291473940479277 3615257589484302727679729)
              ·
                refine ⟨2711443192113227045759797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3615257589484302727679729 2711443192113227045759797)
                ·
                  refine ⟨254197799260615035539981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2711443192113227045759797 254197799260615035539981)
                  ·
                    rfl

theorem cell23_4455436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 2, 5].length) (baseStart_4455436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4455436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4455436 prefixEnd_4455436 := by exact prefixLift 4455436
  have htrace : WordTrace (prefixWord ++ tailWord_4455436) baseStart_4455436 baseEnd_4455436 := by
    simpa [prefixWord, tailWord_4455436, baseEnd_4455436] using wordTrace_append hprefix tailTrace_4455436
  have hstable : (prefixWord ++ tailWord_4455436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4455436).length < 2 ^ (prefixWord ++ tailWord_4455436).sum := by decide
  have hdescent : baseEnd_4455436 < baseStart_4455436 := by decide
  rcases family_descends (prefixWord ++ tailWord_4455436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4455466 : List Nat := [3, 1, 4, 1, 3, 1, 2, 1, 2, 5]
def baseStart_4455466 : Nat := 118140960795 + 4455466 * 2 ^ 59
def prefixEnd_4455466 : Nat := 4983230072969 + 3 ^ 40 * 4455466 * 2
def baseEnd_4455466 : Nat := 762598532588390067494897

theorem tailTrace_4455466 : CollatzResearch.WordTrace tailWord_4455466 prefixEnd_4455466 762598532588390067494897 := by
  unfold tailWord_4455466
  simp only [CollatzResearch.WordTrace]
  refine ⟨40626048819153772464234563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108336130184410059904625501 40626048819153772464234563)
  ·
    refine ⟨60939073228730658696351845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40626048819153772464234563 60939073228730658696351845)
    ·
      refine ⟨11426076230386998505565971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60939073228730658696351845 11426076230386998505565971)
      ·
        refine ⟨17139114345580497758348957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11426076230386998505565971 17139114345580497758348957)
        ·
          refine ⟨6427167879592686659380859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17139114345580497758348957 6427167879592686659380859)
          ·
            refine ⟨9640751819389029989071289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6427167879592686659380859 9640751819389029989071289)
            ·
              refine ⟨7230563864541772491803467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9640751819389029989071289 7230563864541772491803467)
              ·
                refine ⟨10845845796812658737705201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7230563864541772491803467 10845845796812658737705201)
                ·
                  refine ⟨8134384347609494053278901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10845845796812658737705201 8134384347609494053278901)
                  ·
                    refine ⟨762598532588390067494897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8134384347609494053278901 762598532588390067494897)
                    ·
                      rfl

theorem cell23_4455466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_4455466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4455466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4455466 prefixEnd_4455466 := by exact prefixLift 4455466
  have htrace : WordTrace (prefixWord ++ tailWord_4455466) baseStart_4455466 baseEnd_4455466 := by
    simpa [prefixWord, tailWord_4455466, baseEnd_4455466] using wordTrace_append hprefix tailTrace_4455466
  have hstable : (prefixWord ++ tailWord_4455466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4455466).length < 2 ^ (prefixWord ++ tailWord_4455466).sum := by decide
  have hdescent : baseEnd_4455466 < baseStart_4455466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4455466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4455486 : List Nat := [4, 2, 1, 3, 1, 1, 2, 2, 2, 1, 4]
def baseStart_4455486 : Nat := 118140960795 + 4455486 * 2 ^ 59
def prefixEnd_4455486 : Nat := 4983230072969 + 3 ^ 40 * 4455486 * 2
def baseEnd_4455486 : Nat := 2287805867378260124234599

theorem tailTrace_4455486 : CollatzResearch.WordTrace tailWord_4455486 prefixEnd_4455486 2287805867378260124234599 := by
  unfold tailWord_4455486
  simp only [CollatzResearch.WordTrace]
  refine ⟨20313115592067829159083289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108336616491028422181777541 20313115592067829159083289)
  ·
    refine ⟨15234836694050871869312467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20313115592067829159083289 15234836694050871869312467)
    ·
      refine ⟨22852255041076307803968701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15234836694050871869312467 22852255041076307803968701)
      ·
        refine ⟨8569595640403615426488263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22852255041076307803968701 8569595640403615426488263)
        ·
          refine ⟨12854393460605423139732395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8569595640403615426488263 12854393460605423139732395)
          ·
            refine ⟨19281590190908134709598593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12854393460605423139732395 19281590190908134709598593)
            ·
              refine ⟨14461192643181101032198945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19281590190908134709598593 14461192643181101032198945)
              ·
                refine ⟨10845894482385825774149209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14461192643181101032198945 10845894482385825774149209)
                ·
                  refine ⟨8134420861789369330611907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10845894482385825774149209 8134420861789369330611907)
                  ·
                    refine ⟨12201631292684053995917861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8134420861789369330611907 12201631292684053995917861)
                    ·
                      refine ⟨2287805867378260124234599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12201631292684053995917861 2287805867378260124234599)
                      ·
                        rfl

theorem cell23_4455486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_4455486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4455486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4455486 prefixEnd_4455486 := by exact prefixLift 4455486
  have htrace : WordTrace (prefixWord ++ tailWord_4455486) baseStart_4455486 baseEnd_4455486 := by
    simpa [prefixWord, tailWord_4455486, baseEnd_4455486] using wordTrace_append hprefix tailTrace_4455486
  have hstable : (prefixWord ++ tailWord_4455486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4455486).length < 2 ^ (prefixWord ++ tailWord_4455486).sum := by decide
  have hdescent : baseEnd_4455486 < baseStart_4455486 := by decide
  rcases family_descends (prefixWord ++ tailWord_4455486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4455496 : List Nat := [2, 1, 3, 1, 1, 1, 5, 4, 1, 4]
def baseStart_4455496 : Nat := 118140960795 + 4455496 * 2 ^ 59
def prefixEnd_4455496 : Nat := 4983230072969 + 3 ^ 40 * 4455496 * 2
def baseEnd_4455496 : Nat := 762603667394935028369851

theorem tailTrace_4455496 : CollatzResearch.WordTrace tailWord_4455496 prefixEnd_4455496 762603667394935028369851 := by
  unfold tailWord_4455496
  simp only [CollatzResearch.WordTrace]
  refine ⟨81252644733253202490265171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108336859644337603320353561 81252644733253202490265171)
  ·
    refine ⟨121878967099879803735397757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81252644733253202490265171 121878967099879803735397757)
    ·
      refine ⟨45704612662454926400774159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121878967099879803735397757 45704612662454926400774159)
      ·
        refine ⟨68556918993682389601161239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45704612662454926400774159 68556918993682389601161239)
        ·
          refine ⟨102835378490523584401741859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68556918993682389601161239 102835378490523584401741859)
          ·
            refine ⟨154253067735785376602612789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102835378490523584401741859 154253067735785376602612789)
            ·
              refine ⟨14461225100229879056494949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 154253067735785376602612789 14461225100229879056494949)
              ·
                refine ⟨2711479706293102323092803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14461225100229879056494949 2711479706293102323092803)
                ·
                  refine ⟨4067219559439653484639205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2711479706293102323092803 4067219559439653484639205)
                  ·
                    refine ⟨762603667394935028369851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4067219559439653484639205 762603667394935028369851)
                    ·
                      rfl

theorem cell23_4455496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 4, 1, 4].length) (baseStart_4455496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4455496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4455496 prefixEnd_4455496 := by exact prefixLift 4455496
  have htrace : WordTrace (prefixWord ++ tailWord_4455496) baseStart_4455496 baseEnd_4455496 := by
    simpa [prefixWord, tailWord_4455496, baseEnd_4455496] using wordTrace_append hprefix tailTrace_4455496
  have hstable : (prefixWord ++ tailWord_4455496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4455496).length < 2 ^ (prefixWord ++ tailWord_4455496).sum := by decide
  have hdescent : baseEnd_4455496 < baseStart_4455496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4455496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4455552 : List Nat := [2, 1, 1, 2, 1, 3, 2, 2, 3, 6]
def baseStart_4455552 : Nat := 118140960795 + 4455552 * 2 ^ 59
def prefixEnd_4455552 : Nat := 4983230072969 + 3 ^ 40 * 4455552 * 2
def baseEnd_4455552 : Nat := 762613252367152288669765

theorem tailTrace_4455552 : CollatzResearch.WordTrace tailWord_4455552 prefixEnd_4455552 762613252367152288669765 := by
  unfold tailWord_4455552
  simp only [CollatzResearch.WordTrace]
  refine ⟨81253665977151763272284455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108338221302869017696379273 81253665977151763272284455)
  ·
    refine ⟨121880498965727644908426683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81253665977151763272284455 121880498965727644908426683)
    ·
      refine ⟨182820748448591467362640025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121880498965727644908426683 182820748448591467362640025)
      ·
        refine ⟨137115561336443600521980019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182820748448591467362640025 137115561336443600521980019)
        ·
          refine ⟨205673342004665400782970029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137115561336443600521980019 205673342004665400782970029)
          ·
            refine ⟨77127503251749525293613761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 205673342004665400782970029 77127503251749525293613761)
            ·
              refine ⟨57845627438812143970210321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77127503251749525293613761 57845627438812143970210321)
              ·
                refine ⟨43384220579109107977657741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57845627438812143970210321 43384220579109107977657741)
                ·
                  refine ⟨16269082717165915491621653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43384220579109107977657741 16269082717165915491621653)
                  ·
                    refine ⟨762613252367152288669765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16269082717165915491621653 762613252367152288669765)
                    ·
                      rfl

theorem cell23_4455552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 3, 6].length) (baseStart_4455552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4455552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4455552 prefixEnd_4455552 := by exact prefixLift 4455552
  have htrace : WordTrace (prefixWord ++ tailWord_4455552) baseStart_4455552 baseEnd_4455552 := by
    simpa [prefixWord, tailWord_4455552, baseEnd_4455552] using wordTrace_append hprefix tailTrace_4455552
  have hstable : (prefixWord ++ tailWord_4455552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4455552).length < 2 ^ (prefixWord ++ tailWord_4455552).sum := by decide
  have hdescent : baseEnd_4455552 < baseStart_4455552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4455552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4455553 : List Nat := [1, 2, 4, 2, 2, 2, 2, 1, 3, 1, 3]
def baseStart_4455553 : Nat := 118140960795 + 4455553 * 2 ^ 59
def prefixEnd_4455553 : Nat := 4983230072969 + 3 ^ 40 * 4455553 * 2
def baseEnd_4455553 : Nat := 2287840270582111362096791

theorem tailTrace_4455553 : CollatzResearch.WordTrace tailWord_4455553 prefixEnd_4455553 2287840270582111362096791 := by
  unfold tailWord_4455553
  simp only [CollatzResearch.WordTrace]
  refine ⟨162507368427299903715355313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108338245618199935810236875 162507368427299903715355313)
  ·
    refine ⟨121880526320474927786516485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162507368427299903715355313 121880526320474927786516485)
    ·
      refine ⟨22852598685089048959971841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121880526320474927786516485 22852598685089048959971841)
      ·
        refine ⟨17139449013816786719978881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22852598685089048959971841 17139449013816786719978881)
        ·
          refine ⟨12854586760362590039984161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17139449013816786719978881 12854586760362590039984161)
          ·
            refine ⟨9640940070271942529988121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12854586760362590039984161 9640940070271942529988121)
            ·
              refine ⟨7230705052703956897491091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9640940070271942529988121 7230705052703956897491091)
              ·
                refine ⟨10846057579055935346236637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7230705052703956897491091 10846057579055935346236637)
                ·
                  refine ⟨4067271592145975754838739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10846057579055935346236637 4067271592145975754838739)
                  ·
                    refine ⟨6100907388218963632258109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4067271592145975754838739 6100907388218963632258109)
                    ·
                      refine ⟨2287840270582111362096791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6100907388218963632258109 2287840270582111362096791)
                      ·
                        rfl

theorem cell23_4455553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_4455553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4455553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4455553 prefixEnd_4455553 := by exact prefixLift 4455553
  have htrace : WordTrace (prefixWord ++ tailWord_4455553) baseStart_4455553 baseEnd_4455553 := by
    simpa [prefixWord, tailWord_4455553, baseEnd_4455553] using wordTrace_append hprefix tailTrace_4455553
  have hstable : (prefixWord ++ tailWord_4455553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4455553).length < 2 ^ (prefixWord ++ tailWord_4455553).sum := by decide
  have hdescent : baseEnd_4455553 < baseStart_4455553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4455553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4455576 : List Nat := [2, 1, 2, 4, 2, 1, 1, 4, 1, 1, 4]
def baseStart_4455576 : Nat := 118140960795 + 4455576 * 2 ^ 59
def prefixEnd_4455576 : Nat := 4983230072969 + 3 ^ 40 * 4455576 * 2
def baseEnd_4455576 : Nat := 2287852080637164772109185

theorem tailTrace_4455576 : CollatzResearch.WordTrace tailWord_4455576 prefixEnd_4455576 2287852080637164772109185 := by
  unfold tailWord_4455576
  simp only [CollatzResearch.WordTrace]
  refine ⟨81254103653108289321721291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108338804870811052428961721 81254103653108289321721291)
  ·
    refine ⟨121881155479662433982581937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81254103653108289321721291 121881155479662433982581937)
    ·
      refine ⟨91410866609746825486936453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121881155479662433982581937 91410866609746825486936453)
      ·
        refine ⟨17139537489327529778800585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91410866609746825486936453 17139537489327529778800585)
        ·
          refine ⟨12854653116995647334100439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17139537489327529778800585 12854653116995647334100439)
          ·
            refine ⟨19281979675493471001150659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12854653116995647334100439 19281979675493471001150659)
            ·
              refine ⟨28922969513240206501725989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19281979675493471001150659 28922969513240206501725989)
              ·
                refine ⟨5423056783732538719073623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28922969513240206501725989 5423056783732538719073623)
                ·
                  refine ⟨8134585175598808078610435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5423056783732538719073623 8134585175598808078610435)
                  ·
                    refine ⟨12201877763398212117915653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8134585175598808078610435 12201877763398212117915653)
                    ·
                      refine ⟨2287852080637164772109185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12201877763398212117915653 2287852080637164772109185)
                      ·
                        rfl

theorem cell23_4455576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_4455576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4455576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4455576 prefixEnd_4455576 := by exact prefixLift 4455576
  have htrace : WordTrace (prefixWord ++ tailWord_4455576) baseStart_4455576 baseEnd_4455576 := by
    simpa [prefixWord, tailWord_4455576, baseEnd_4455576] using wordTrace_append hprefix tailTrace_4455576
  have hstable : (prefixWord ++ tailWord_4455576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4455576).length < 2 ^ (prefixWord ++ tailWord_4455576).sum := by decide
  have hdescent : baseEnd_4455576 < baseStart_4455576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4455576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4455630 : List Nat := [4, 1, 1, 1, 5, 2, 1, 2, 1, 2, 3]
def baseStart_4455630 : Nat := 118140960795 + 4455630 * 2 ^ 59
def prefixEnd_4455630 : Nat := 4983230072969 + 3 ^ 40 * 4455630 * 2
def baseEnd_4455630 : Nat := 2287879808592507560833937

theorem tailTrace_4455630 : CollatzResearch.WordTrace tailWord_4455630 prefixEnd_4455630 2287879808592507560833937 := by
  unfold tailWord_4455630
  simp only [CollatzResearch.WordTrace]
  refine ⟨20313772106002618233238543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108340117898680630577272229 20313772106002618233238543)
  ·
    refine ⟨30470658159003927349857815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20313772106002618233238543 30470658159003927349857815)
    ·
      refine ⟨45705987238505891024786723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30470658159003927349857815 45705987238505891024786723)
      ·
        refine ⟨68558980857758836537180085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45705987238505891024786723 68558980857758836537180085)
        ·
          refine ⟨6427404455414890925360633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68558980857758836537180085 6427404455414890925360633)
          ·
            refine ⟨4820553341561168194020475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6427404455414890925360633 4820553341561168194020475)
            ·
              refine ⟨7230830012341752291030713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4820553341561168194020475 7230830012341752291030713)
              ·
                refine ⟨5423122509256314218273035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7230830012341752291030713 5423122509256314218273035)
                ·
                  refine ⟨8134683763884471327409553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5423122509256314218273035 8134683763884471327409553)
                  ·
                    refine ⟨6101012822913353495557165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8134683763884471327409553 6101012822913353495557165)
                    ·
                      refine ⟨2287879808592507560833937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6101012822913353495557165 2287879808592507560833937)
                      ·
                        rfl

theorem cell23_4455630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 2, 1, 2, 3].length) (baseStart_4455630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4455630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4455630 prefixEnd_4455630 := by exact prefixLift 4455630
  have htrace : WordTrace (prefixWord ++ tailWord_4455630) baseStart_4455630 baseEnd_4455630 := by
    simpa [prefixWord, tailWord_4455630, baseEnd_4455630] using wordTrace_append hprefix tailTrace_4455630
  have hstable : (prefixWord ++ tailWord_4455630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4455630).length < 2 ^ (prefixWord ++ tailWord_4455630).sum := by decide
  have hdescent : baseEnd_4455630 < baseStart_4455630 := by decide
  rcases family_descends (prefixWord ++ tailWord_4455630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4455676 : List Nat := [2, 2, 2, 1, 5, 1, 1, 1, 2, 6]
def baseStart_4455676 : Nat := 118140960795 + 4455676 * 2 ^ 59
def prefixEnd_4455676 : Nat := 4983230072969 + 3 ^ 40 * 4455676 * 2
def baseEnd_4455676 : Nat := 762634476234204793619575

theorem tailTrace_4455676 : CollatzResearch.WordTrace tailWord_4455676 prefixEnd_4455676 762634476234204793619575 := by
  unfold tailWord_4455676
  simp only [CollatzResearch.WordTrace]
  refine ⟨81255927302927147861041441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108341236403902863814721921 81255927302927147861041441)
  ·
    refine ⟨60941945477195360895781081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81255927302927147861041441 60941945477195360895781081)
    ·
      refine ⟨45706459107896520671835811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60941945477195360895781081 45706459107896520671835811)
      ·
        refine ⟨68559688661844781007753717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45706459107896520671835811 68559688661844781007753717)
        ·
          refine ⟨6427470812047948219476911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68559688661844781007753717 6427470812047948219476911)
          ·
            refine ⟨9641206218071922329215367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6427470812047948219476911 9641206218071922329215367)
            ·
              refine ⟨14461809327107883493823051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9641206218071922329215367 14461809327107883493823051)
              ·
                refine ⟨21692713990661825240734577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14461809327107883493823051 21692713990661825240734577)
                ·
                  refine ⟨16269535492996368930550933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21692713990661825240734577 16269535492996368930550933)
                  ·
                    refine ⟨762634476234204793619575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16269535492996368930550933 762634476234204793619575)
                    ·
                      rfl

theorem cell23_4455676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 2, 6].length) (baseStart_4455676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4455676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4455676 prefixEnd_4455676 := by exact prefixLift 4455676
  have htrace : WordTrace (prefixWord ++ tailWord_4455676) baseStart_4455676 baseEnd_4455676 := by
    simpa [prefixWord, tailWord_4455676, baseEnd_4455676] using wordTrace_append hprefix tailTrace_4455676
  have hstable : (prefixWord ++ tailWord_4455676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4455676).length < 2 ^ (prefixWord ++ tailWord_4455676).sum := by decide
  have hdescent : baseEnd_4455676 < baseStart_4455676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4455676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4455679 : List Nat := [1, 1, 2, 2, 1, 5, 1, 1, 1, 4, 4]
def baseStart_4455679 : Nat := 118140960795 + 4455679 * 2 ^ 59
def prefixEnd_4455679 : Nat := 4983230072969 + 3 ^ 40 * 4455679 * 2
def baseEnd_4455679 : Nat := 2287904969144577869121211

theorem tailTrace_4455679 : CollatzResearch.WordTrace tailWord_4455679 prefixEnd_4455679 2287904969144577869121211 := by
  unfold tailWord_4455679
  simp only [CollatzResearch.WordTrace]
  refine ⟨162511964024843427234442091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108341309349895618156294727 162511964024843427234442091)
  ·
    refine ⟨243767946037265140851663137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162511964024843427234442091 243767946037265140851663137)
    ·
      refine ⟨182825959527948855638747353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243767946037265140851663137 182825959527948855638747353)
      ·
        refine ⟨137119469645961641729060515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182825959527948855638747353 137119469645961641729060515)
        ·
          refine ⟨205679204468942462593590773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137119469645961641729060515 205679204468942462593590773)
          ·
            refine ⟨19282425418963355868149135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 205679204468942462593590773 19282425418963355868149135)
            ·
              refine ⟨28923638128445033802223703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19282425418963355868149135 28923638128445033802223703)
              ·
                refine ⟨43385457192667550703335555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28923638128445033802223703 43385457192667550703335555)
                ·
                  refine ⟨65078185789001326055003333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43385457192667550703335555 65078185789001326055003333)
                  ·
                    refine ⟨12202159835437748635313125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 65078185789001326055003333 12202159835437748635313125)
                    ·
                      refine ⟨2287904969144577869121211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12202159835437748635313125 2287904969144577869121211)
                      ·
                        rfl

theorem cell23_4455679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 4, 4].length) (baseStart_4455679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4455679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4455679 prefixEnd_4455679 := by exact prefixLift 4455679
  have htrace : WordTrace (prefixWord ++ tailWord_4455679) baseStart_4455679 baseEnd_4455679 := by
    simpa [prefixWord, tailWord_4455679, baseEnd_4455679] using wordTrace_append hprefix tailTrace_4455679
  have hstable : (prefixWord ++ tailWord_4455679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4455679).length < 2 ^ (prefixWord ++ tailWord_4455679).sum := by decide
  have hdescent : baseEnd_4455679 < baseStart_4455679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4455679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4455683 : List Nat := [1, 1, 1, 3, 2, 5, 2, 1, 1, 4, 2]
def baseStart_4455683 : Nat := 118140960795 + 4455683 * 2 ^ 59
def prefixEnd_4455683 : Nat := 4983230072969 + 3 ^ 40 * 4455683 * 2
def baseEnd_4455683 : Nat := 2287907023067195853471193

theorem tailTrace_4455683 : CollatzResearch.WordTrace tailWord_4455683 prefixEnd_4455683 2287907023067195853471193 := by
  unfold tailWord_4455683
  simp only [CollatzResearch.WordTrace]
  refine ⟨162512109916828935917587703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108341406611219290611725135 162512109916828935917587703)
  ·
    refine ⟨243768164875243403876381555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162512109916828935917587703 243768164875243403876381555)
    ·
      refine ⟨365652247312865105814572333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243768164875243403876381555 365652247312865105814572333)
      ·
        refine ⟨137119592742324414680464625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 365652247312865105814572333 137119592742324414680464625)
        ·
          refine ⟨102839694556743311010348469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137119592742324414680464625 102839694556743311010348469)
          ·
            refine ⟨9641221364694685407220169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 102839694556743311010348469 9641221364694685407220169)
            ·
              refine ⟨7230916023521014055415127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9641221364694685407220169 7230916023521014055415127)
              ·
                refine ⟨10846374035281521083122691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7230916023521014055415127 10846374035281521083122691)
                ·
                  refine ⟨16269561052922281624684037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10846374035281521083122691 16269561052922281624684037)
                  ·
                    refine ⟨3050542697422927804628257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16269561052922281624684037 3050542697422927804628257)
                    ·
                      refine ⟨2287907023067195853471193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3050542697422927804628257 2287907023067195853471193)
                      ·
                        rfl

theorem cell23_4455683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 4, 2].length) (baseStart_4455683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4455683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4455683 prefixEnd_4455683 := by exact prefixLift 4455683
  have htrace : WordTrace (prefixWord ++ tailWord_4455683) baseStart_4455683 baseEnd_4455683 := by
    simpa [prefixWord, tailWord_4455683, baseEnd_4455683] using wordTrace_append hprefix tailTrace_4455683
  have hstable : (prefixWord ++ tailWord_4455683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4455683).length < 2 ^ (prefixWord ++ tailWord_4455683).sum := by decide
  have hdescent : baseEnd_4455683 < baseStart_4455683 := by decide
  rcases family_descends (prefixWord ++ tailWord_4455683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4455689 : List Nat := [1, 2, 1, 1, 3, 3, 3, 2, 7]
def baseStart_4455689 : Nat := 118140960795 + 4455689 * 2 ^ 59
def prefixEnd_4455689 : Nat := 4983230072969 + 3 ^ 40 * 4455689 * 2
def baseEnd_4455689 : Nat := 254212233772346981110685

theorem tailTrace_4455689 : CollatzResearch.WordTrace tailWord_4455689 prefixEnd_4455689 254212233772346981110685 := by
  unfold tailWord_4455689
  simp only [CollatzResearch.WordTrace]
  refine ⟨162512328754807198942306121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108341552503204799294870747 162512328754807198942306121)
  ·
    refine ⟨121884246566105399206729591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162512328754807198942306121 121884246566105399206729591)
    ·
      refine ⟨182826369849158098810094387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121884246566105399206729591 182826369849158098810094387)
      ·
        refine ⟨274239554773737148215141581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182826369849158098810094387 274239554773737148215141581)
        ·
          refine ⟨102839833040151430580678093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 274239554773737148215141581 102839833040151430580678093)
          ·
            refine ⟨38564937390056786467754285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102839833040151430580678093 38564937390056786467754285)
            ·
              refine ⟨14461851521271294925407857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38564937390056786467754285 14461851521271294925407857)
              ·
                refine ⟨10846388640953471194055893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14461851521271294925407857 10846388640953471194055893)
                ·
                  refine ⟨254212233772346981110685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10846388640953471194055893 254212233772346981110685)
                  ·
                    rfl

theorem cell23_4455689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 7].length) (baseStart_4455689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4455689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4455689 prefixEnd_4455689 := by exact prefixLift 4455689
  have htrace : WordTrace (prefixWord ++ tailWord_4455689) baseStart_4455689 baseEnd_4455689 := by
    simpa [prefixWord, tailWord_4455689, baseEnd_4455689] using wordTrace_append hprefix tailTrace_4455689
  have hstable : (prefixWord ++ tailWord_4455689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4455689).length < 2 ^ (prefixWord ++ tailWord_4455689).sum := by decide
  have hdescent : baseEnd_4455689 < baseStart_4455689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4455689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4455716 : List Nat := [2, 3, 1, 3, 1, 1, 1, 1, 4, 3, 3]
def baseStart_4455716 : Nat := 118140960795 + 4455716 * 2 ^ 59
def prefixEnd_4455716 : Nat := 4983230072969 + 3 ^ 40 * 4455716 * 2
def baseEnd_4455716 : Nat := 2287923967928794224358541

theorem tailTrace_4455716 : CollatzResearch.WordTrace tailWord_4455716 prefixEnd_4455716 2287923967928794224358541 := by
  unfold tailWord_4455716
  simp only [CollatzResearch.WordTrace]
  refine ⟨81256656762854691276769501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108342209017139588369026001 81256656762854691276769501)
  ·
    refine ⟨30471246286070509228788563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81256656762854691276769501 30471246286070509228788563)
    ·
      refine ⟨45706869429105763843182845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30471246286070509228788563 45706869429105763843182845)
      ·
        refine ⟨17140076035914661441193567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45706869429105763843182845 17140076035914661441193567)
        ·
          refine ⟨25710114053871992161790351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17140076035914661441193567 25710114053871992161790351)
          ·
            refine ⟨38565171080807988242685527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25710114053871992161790351 38565171080807988242685527)
            ·
              refine ⟨57847756621211982364028291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38565171080807988242685527 57847756621211982364028291)
              ·
                refine ⟨86771634931817973546042437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57847756621211982364028291 86771634931817973546042437)
                ·
                  refine ⟨16269681549715870039882957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 86771634931817973546042437 16269681549715870039882957)
                  ·
                    refine ⟨6101130581143451264956109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16269681549715870039882957 6101130581143451264956109)
                    ·
                      refine ⟨2287923967928794224358541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6101130581143451264956109 2287923967928794224358541)
                      ·
                        rfl

theorem cell23_4455716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_4455716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4455716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4455716 prefixEnd_4455716 := by exact prefixLift 4455716
  have htrace : WordTrace (prefixWord ++ tailWord_4455716) baseStart_4455716 baseEnd_4455716 := by
    simpa [prefixWord, tailWord_4455716, baseEnd_4455716] using wordTrace_append hprefix tailTrace_4455716
  have hstable : (prefixWord ++ tailWord_4455716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4455716).length < 2 ^ (prefixWord ++ tailWord_4455716).sum := by decide
  have hdescent : baseEnd_4455716 < baseStart_4455716 := by decide
  rcases family_descends (prefixWord ++ tailWord_4455716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4455717 : List Nat := [1, 3, 1, 2, 4, 3, 1, 2, 2, 2, 2]
def baseStart_4455717 : Nat := 118140960795 + 4455717 * 2 ^ 59
def prefixEnd_4455717 : Nat := 4983230072969 + 3 ^ 40 * 4455717 * 2
def baseEnd_4455717 : Nat := 2287924481409448720446037

theorem tailTrace_4455717 : CollatzResearch.WordTrace tailWord_4455717 prefixEnd_4455717 2287924481409448720446037 := by
  unfold tailWord_4455717
  simp only [CollatzResearch.WordTrace]
  refine ⟨162513349998705759724325405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108342233332470506482883603 162513349998705759724325405)
  ·
    refine ⟨60942506249514659896622027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162513349998705759724325405 60942506249514659896622027)
    ·
      refine ⟨91413759374271989844933041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60942506249514659896622027 91413759374271989844933041)
      ·
        refine ⟨68560319530703992383699781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91413759374271989844933041 68560319530703992383699781)
        ·
          refine ⟨12855059912006998571943709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68560319530703992383699781 12855059912006998571943709)
          ·
            refine ⟨4820647467002624464478891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12855059912006998571943709 4820647467002624464478891)
            ·
              refine ⟨7230971200503936696718337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4820647467002624464478891 7230971200503936696718337)
              ·
                refine ⟨5423228400377952522538753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7230971200503936696718337 5423228400377952522538753)
                ·
                  refine ⟨4067421300283464391904065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5423228400377952522538753 4067421300283464391904065)
                  ·
                    refine ⟨3050565975212598293928049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4067421300283464391904065 3050565975212598293928049)
                    ·
                      refine ⟨2287924481409448720446037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3050565975212598293928049 2287924481409448720446037)
                      ·
                        rfl

theorem cell23_4455717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 2, 2, 2, 2].length) (baseStart_4455717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4455717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4455717 prefixEnd_4455717 := by exact prefixLift 4455717
  have htrace : WordTrace (prefixWord ++ tailWord_4455717) baseStart_4455717 baseEnd_4455717 := by
    simpa [prefixWord, tailWord_4455717, baseEnd_4455717] using wordTrace_append hprefix tailTrace_4455717
  have hstable : (prefixWord ++ tailWord_4455717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4455717).length < 2 ^ (prefixWord ++ tailWord_4455717).sum := by decide
  have hdescent : baseEnd_4455717 < baseStart_4455717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4455717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4455734 : List Nat := [5, 1, 2, 3, 1, 2, 1, 1, 1, 4, 2]
def baseStart_4455734 : Nat := 118140960795 + 4455734 * 2 ^ 59
def prefixEnd_4455734 : Nat := 4983230072969 + 3 ^ 40 * 4455734 * 2
def baseEnd_4455734 : Nat := 2287933210580575153933459

theorem tailTrace_4455734 : CollatzResearch.WordTrace tailWord_4455734 prefixEnd_4455734 2287933210580575153933459 := by
  unfold tailWord_4455734
  simp only [CollatzResearch.WordTrace]
  refine ⟨10157123127477760726730891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 108342646693096114418462837 10157123127477760726730891)
  ·
    refine ⟨15235684691216641090096337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10157123127477760726730891 15235684691216641090096337)
    ·
      refine ⟨11426763518412480817572253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15235684691216641090096337 11426763518412480817572253)
      ·
        refine ⟨4285036319404680306589595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11426763518412480817572253 4285036319404680306589595)
        ·
          refine ⟨6427554479107020459884393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4285036319404680306589595 6427554479107020459884393)
          ·
            refine ⟨4820665859330265344913295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6427554479107020459884393 4820665859330265344913295)
            ·
              refine ⟨7230998788995398017369943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4820665859330265344913295 7230998788995398017369943)
              ·
                refine ⟨10846498183493097026054915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7230998788995398017369943 10846498183493097026054915)
                ·
                  refine ⟨16269747275239645539082373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10846498183493097026054915 16269747275239645539082373)
                  ·
                    refine ⟨3050577614107433538577945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16269747275239645539082373 3050577614107433538577945)
                    ·
                      refine ⟨2287933210580575153933459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3050577614107433538577945 2287933210580575153933459)
                      ·
                        rfl

theorem cell23_4455734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_4455734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4455734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4455734 prefixEnd_4455734 := by exact prefixLift 4455734
  have htrace : WordTrace (prefixWord ++ tailWord_4455734) baseStart_4455734 baseEnd_4455734 := by
    simpa [prefixWord, tailWord_4455734, baseEnd_4455734] using wordTrace_append hprefix tailTrace_4455734
  have hstable : (prefixWord ++ tailWord_4455734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4455734).length < 2 ^ (prefixWord ++ tailWord_4455734).sum := by decide
  have hdescent : baseEnd_4455734 < baseStart_4455734 := by decide
  rcases family_descends (prefixWord ++ tailWord_4455734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4455756 : List Nat := [2, 2, 1, 3, 2, 2, 2, 1, 1, 3, 4]
def baseStart_4455756 : Nat := 118140960795 + 4455756 * 2 ^ 59
def prefixEnd_4455756 : Nat := 4983230072969 + 3 ^ 40 * 4455756 * 2
def baseEnd_4455756 : Nat := 2287944507154974067858357

theorem tailTrace_4455756 : CollatzResearch.WordTrace tailWord_4455756 prefixEnd_4455756 2287944507154974067858357 := by
  unfold tailWord_4455756
  simp only [CollatzResearch.WordTrace]
  refine ⟨81257386222782234692497561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108343181630376312923330081 81257386222782234692497561)
  ·
    refine ⟨60943039667086676019373171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81257386222782234692497561 60943039667086676019373171)
    ·
      refine ⟨91414559500630014029059757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60943039667086676019373171 91414559500630014029059757)
      ·
        refine ⟨34280459812736255260897409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91414559500630014029059757 34280459812736255260897409)
        ·
          refine ⟨25710344859552191445673057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34280459812736255260897409 25710344859552191445673057)
          ·
            refine ⟨19282758644664143584254793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25710344859552191445673057 19282758644664143584254793)
            ·
              refine ⟨14462068983498107688191095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19282758644664143584254793 14462068983498107688191095)
              ·
                refine ⟨21693103475247161532286643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14462068983498107688191095 21693103475247161532286643)
                ·
                  refine ⟨32539655212870742298429965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21693103475247161532286643 32539655212870742298429965)
                  ·
                    refine ⟨12202370704826528361911237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32539655212870742298429965 12202370704826528361911237)
                    ·
                      refine ⟨2287944507154974067858357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12202370704826528361911237 2287944507154974067858357)
                      ·
                        rfl

theorem cell23_4455756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_4455756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4455756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4455756 prefixEnd_4455756 := by exact prefixLift 4455756
  have htrace : WordTrace (prefixWord ++ tailWord_4455756) baseStart_4455756 baseEnd_4455756 := by
    simpa [prefixWord, tailWord_4455756, baseEnd_4455756] using wordTrace_append hprefix tailTrace_4455756
  have hstable : (prefixWord ++ tailWord_4455756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4455756).length < 2 ^ (prefixWord ++ tailWord_4455756).sum := by decide
  have hdescent : baseEnd_4455756 < baseStart_4455756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4455756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4455769 : List Nat := [1, 2, 1, 2, 2, 2, 2, 1, 1, 3, 6]
def baseStart_4455769 : Nat := 118140960795 + 4455769 * 2 ^ 59
def prefixEnd_4455769 : Nat := 4983230072969 + 3 ^ 40 * 4455769 * 2
def baseEnd_4455769 : Nat := 2287951182403482516995797

theorem tailTrace_4455769 : CollatzResearch.WordTrace tailWord_4455769 prefixEnd_4455769 2287951182403482516995797 := by
  unfold tailWord_4455769
  simp only [CollatzResearch.WordTrace]
  refine ⟨162515246594517372605218361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108343497729678248403478907 162515246594517372605218361)
  ·
    refine ⟨121886434945888029453913771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162515246594517372605218361 121886434945888029453913771)
    ·
      refine ⟨182829652418832044180870657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121886434945888029453913771 182829652418832044180870657)
      ·
        refine ⟨137122239314124033135652993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182829652418832044180870657 137122239314124033135652993)
        ·
          refine ⟨102841679485593024851739745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137122239314124033135652993 102841679485593024851739745)
          ·
            refine ⟨77131259614194768638804809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102841679485593024851739745 77131259614194768638804809)
            ·
              refine ⟨57848444710646076479103607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77131259614194768638804809 57848444710646076479103607)
              ·
                refine ⟨86772667065969114718655411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57848444710646076479103607 86772667065969114718655411)
                ·
                  refine ⟨130159000598953672077983117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86772667065969114718655411 130159000598953672077983117)
                  ·
                    refine ⟨48809625224607627029243669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 130159000598953672077983117 48809625224607627029243669)
                    ·
                      refine ⟨2287951182403482516995797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48809625224607627029243669 2287951182403482516995797)
                      ·
                        rfl

theorem cell23_4455769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 3, 6].length) (baseStart_4455769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4455769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4455769 prefixEnd_4455769 := by exact prefixLift 4455769
  have htrace : WordTrace (prefixWord ++ tailWord_4455769) baseStart_4455769 baseEnd_4455769 := by
    simpa [prefixWord, tailWord_4455769, baseEnd_4455769] using wordTrace_append hprefix tailTrace_4455769
  have hstable : (prefixWord ++ tailWord_4455769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4455769).length < 2 ^ (prefixWord ++ tailWord_4455769).sum := by decide
  have hdescent : baseEnd_4455769 < baseStart_4455769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4455769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4455863 : List Nat := [1, 1, 3, 1, 3, 2, 2, 4, 1, 1, 4]
def baseStart_4455863 : Nat := 118140960795 + 4455863 * 2 ^ 59
def prefixEnd_4455863 : Nat := 4983230072969 + 3 ^ 40 * 4455863 * 2
def baseEnd_4455863 : Nat := 2287999449585005149220365

theorem tailTrace_4455863 : CollatzResearch.WordTrace tailWord_4455863 prefixEnd_4455863 2287999449585005149220365 := by
  unfold tailWord_4455863
  simp only [CollatzResearch.WordTrace]
  refine ⟨162518675056176826659140243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108345783370784551106093495 162518675056176826659140243)
  ·
    refine ⟨243778012584265239988710365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162518675056176826659140243 243778012584265239988710365)
    ·
      refine ⟨91416754719099464995766387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 243778012584265239988710365 91416754719099464995766387)
      ·
        refine ⟨137125132078649197493649581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91416754719099464995766387 137125132078649197493649581)
        ·
          refine ⟨51421924529493449060118593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137125132078649197493649581 51421924529493449060118593)
          ·
            refine ⟨38566443397120086795088945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51421924529493449060118593 38566443397120086795088945)
            ·
              refine ⟨28924832547840065096316709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38566443397120086795088945 28924832547840065096316709)
              ·
                refine ⟨5423406102720012205559383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28924832547840065096316709 5423406102720012205559383)
                ·
                  refine ⟨8135109154080018308339075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5423406102720012205559383 8135109154080018308339075)
                  ·
                    refine ⟨12202663731120027462508613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8135109154080018308339075 12202663731120027462508613)
                    ·
                      refine ⟨2287999449585005149220365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12202663731120027462508613 2287999449585005149220365)
                      ·
                        rfl

theorem cell23_4455863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 4, 1, 1, 4].length) (baseStart_4455863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4455863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4455863 prefixEnd_4455863 := by exact prefixLift 4455863
  have htrace : WordTrace (prefixWord ++ tailWord_4455863) baseStart_4455863 baseEnd_4455863 := by
    simpa [prefixWord, tailWord_4455863, baseEnd_4455863] using wordTrace_append hprefix tailTrace_4455863
  have hstable : (prefixWord ++ tailWord_4455863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4455863).length < 2 ^ (prefixWord ++ tailWord_4455863).sum := by decide
  have hdescent : baseEnd_4455863 < baseStart_4455863 := by decide
  rcases family_descends (prefixWord ++ tailWord_4455863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4455880 : List Nat := [2, 1, 3, 1, 3, 1, 1, 2, 5, 2, 2]
def baseStart_4455880 : Nat := 118140960795 + 4455880 * 2 ^ 59
def prefixEnd_4455880 : Nat := 4983230072969 + 3 ^ 40 * 4455880 * 2
def baseEnd_4455880 : Nat := 2288008178756131582707787

theorem tailTrace_4455880 : CollatzResearch.WordTrace tailWord_4455880 prefixEnd_4455880 2288008178756131582707787 := by
  unfold tailWord_4455880
  simp only [CollatzResearch.WordTrace]
  refine ⟨81259647548557619281254547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108346196731410159041672729 81259647548557619281254547)
  ·
    refine ⟨121889471322836428921881821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81259647548557619281254547 121889471322836428921881821)
    ·
      refine ⟨45708551746063660845705683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121889471322836428921881821 45708551746063660845705683)
      ·
        refine ⟨68562827619095491268558525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45708551746063660845705683 68562827619095491268558525)
        ·
          refine ⟨25711060357160809225709447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68562827619095491268558525 25711060357160809225709447)
          ·
            refine ⟨38566590535741213838564171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25711060357160809225709447 38566590535741213838564171)
            ·
              refine ⟨57849885803611820757846257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38566590535741213838564171 57849885803611820757846257)
              ·
                refine ⟨43387414352708865568384693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57849885803611820757846257 43387414352708865568384693)
                ·
                  refine ⟨4067570095566456147036065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43387414352708865568384693 4067570095566456147036065)
                  ·
                    refine ⟨3050677571674842110277049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4067570095566456147036065 3050677571674842110277049)
                    ·
                      refine ⟨2288008178756131582707787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3050677571674842110277049 2288008178756131582707787)
                      ·
                        rfl

theorem cell23_4455880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 5, 2, 2].length) (baseStart_4455880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4455880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4455880 prefixEnd_4455880 := by exact prefixLift 4455880
  have htrace : WordTrace (prefixWord ++ tailWord_4455880) baseStart_4455880 baseEnd_4455880 := by
    simpa [prefixWord, tailWord_4455880, baseEnd_4455880] using wordTrace_append hprefix tailTrace_4455880
  have hstable : (prefixWord ++ tailWord_4455880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4455880).length < 2 ^ (prefixWord ++ tailWord_4455880).sum := by decide
  have hdescent : baseEnd_4455880 < baseStart_4455880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4455880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4455897 : List Nat := [1, 2, 1, 2, 4, 3, 2, 1, 3, 2, 2]
def baseStart_4455897 : Nat := 118140960795 + 4455897 * 2 ^ 59
def prefixEnd_4455897 : Nat := 4983230072969 + 3 ^ 40 * 4455897 * 2
def baseEnd_4455897 : Nat := 2288016907927258016195209

theorem tailTrace_4455897 : CollatzResearch.WordTrace tailWord_4455897 prefixEnd_4455897 2288016907927258016195209 := by
  unfold tailWord_4455897
  simp only [CollatzResearch.WordTrace]
  refine ⟨162519915138053650465877945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108346610092035766977251963 162519915138053650465877945)
  ·
    refine ⟨121889936353540237849408459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162519915138053650465877945 121889936353540237849408459)
    ·
      refine ⟨182834904530310356774112689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121889936353540237849408459 182834904530310356774112689)
      ·
        refine ⟨137126178397732767580584517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182834904530310356774112689 137126178397732767580584517)
        ·
          refine ⟨25711158449574893921359597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 137126178397732767580584517 25711158449574893921359597)
          ·
            refine ⟨9641684418590585220509849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25711158449574893921359597 9641684418590585220509849)
            ·
              refine ⟨7231263313942938915382387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9641684418590585220509849 7231263313942938915382387)
              ·
                refine ⟨10846894970914408373073581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7231263313942938915382387 10846894970914408373073581)
                ·
                  refine ⟨4067585614092903139902593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10846894970914408373073581 4067585614092903139902593)
                  ·
                    refine ⟨3050689210569677354926945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4067585614092903139902593 3050689210569677354926945)
                    ·
                      refine ⟨2288016907927258016195209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3050689210569677354926945 2288016907927258016195209)
                      ·
                        rfl

theorem cell23_4455897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 3, 2, 2].length) (baseStart_4455897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4455897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4455897 prefixEnd_4455897 := by exact prefixLift 4455897
  have htrace : WordTrace (prefixWord ++ tailWord_4455897) baseStart_4455897 baseEnd_4455897 := by
    simpa [prefixWord, tailWord_4455897, baseEnd_4455897] using wordTrace_append hprefix tailTrace_4455897
  have hstable : (prefixWord ++ tailWord_4455897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4455897).length < 2 ^ (prefixWord ++ tailWord_4455897).sum := by decide
  have hdescent : baseEnd_4455897 < baseStart_4455897 := by decide
  rcases family_descends (prefixWord ++ tailWord_4455897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4455907 : List Nat := [1, 1, 1, 6, 2, 2, 3, 1, 2, 4]
def baseStart_4455907 : Nat := 118140960795 + 4455907 * 2 ^ 59
def prefixEnd_4455907 : Nat := 4983230072969 + 3 ^ 40 * 4455907 * 2
def baseEnd_4455907 : Nat := 762674014244600992356721

theorem tailTrace_4455907 : CollatzResearch.WordTrace tailWord_4455907 prefixEnd_4455907 762674014244600992356721 := by
  unfold tailWord_4455907
  simp only [CollatzResearch.WordTrace]
  refine ⟨162520279868017422173741975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108346853245344948115827983 162520279868017422173741975)
  ·
    refine ⟨243780419802026133260612963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162520279868017422173741975 243780419802026133260612963)
    ·
      refine ⟨365670629703039199890919445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243780419802026133260612963 365670629703039199890919445)
      ·
        refine ⟨17140810767329962494886849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 365670629703039199890919445 17140810767329962494886849)
        ·
          refine ⟨12855608075497471871165137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17140810767329962494886849 12855608075497471871165137)
          ·
            refine ⟨9641706056623103903373853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12855608075497471871165137 9641706056623103903373853)
            ·
              refine ⟨3615639771233663963765195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9641706056623103903373853 3615639771233663963765195)
              ·
                refine ⟨5423459656850495945647793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3615639771233663963765195 5423459656850495945647793)
                ·
                  refine ⟨4067594742637871959235845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5423459656850495945647793 4067594742637871959235845)
                  ·
                    refine ⟨762674014244600992356721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4067594742637871959235845 762674014244600992356721)
                    ·
                      rfl

theorem cell23_4455907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 1, 2, 4].length) (baseStart_4455907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4455907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4455907 prefixEnd_4455907 := by exact prefixLift 4455907
  have htrace : WordTrace (prefixWord ++ tailWord_4455907) baseStart_4455907 baseEnd_4455907 := by
    simpa [prefixWord, tailWord_4455907, baseEnd_4455907] using wordTrace_append hprefix tailTrace_4455907
  have hstable : (prefixWord ++ tailWord_4455907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4455907).length < 2 ^ (prefixWord ++ tailWord_4455907).sum := by decide
  have hdescent : baseEnd_4455907 < baseStart_4455907 := by decide
  rcases family_descends (prefixWord ++ tailWord_4455907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4456010 : List Nat := [3, 1, 2, 1, 1, 3, 3, 4, 5]
def baseStart_4456010 : Nat := 118140960795 + 4456010 * 2 ^ 59
def prefixEnd_4456010 : Nat := 4983230072969 + 3 ^ 40 * 4456010 * 2
def baseEnd_4456010 : Nat := 254230547915690674898021

theorem tailTrace_4456010 : CollatzResearch.WordTrace tailWord_4456010 prefixEnd_4456010 254230547915690674898021 := by
  unfold tailWord_4456010
  simp only [CollatzResearch.WordTrace]
  refine ⟨40631009146661067691185371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108349357724429513843160989 40631009146661067691185371)
  ·
    refine ⟨60946513719991601536778057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40631009146661067691185371 60946513719991601536778057)
    ·
      refine ⟨45709885289993701152583543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60946513719991601536778057 45709885289993701152583543)
      ·
        refine ⟨68564827934990551728875315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45709885289993701152583543 68564827934990551728875315)
        ·
          refine ⟨102847241902485827593312973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68564827934990551728875315 102847241902485827593312973)
          ·
            refine ⟨38567715713432185347492365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102847241902485827593312973 38567715713432185347492365)
            ·
              refine ⟨14462893392537069505309637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38567715713432185347492365 14462893392537069505309637)
              ·
                refine ⟨2711792511100700532245557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14462893392537069505309637 2711792511100700532245557)
                ·
                  refine ⟨254230547915690674898021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2711792511100700532245557 254230547915690674898021)
                  ·
                    rfl

theorem cell23_4456010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 4, 5].length) (baseStart_4456010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4456010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4456010 prefixEnd_4456010 := by exact prefixLift 4456010
  have htrace : WordTrace (prefixWord ++ tailWord_4456010) baseStart_4456010 baseEnd_4456010 := by
    simpa [prefixWord, tailWord_4456010, baseEnd_4456010] using wordTrace_append hprefix tailTrace_4456010
  have hstable : (prefixWord ++ tailWord_4456010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4456010).length < 2 ^ (prefixWord ++ tailWord_4456010).sum := by decide
  have hdescent : baseEnd_4456010 < baseStart_4456010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4456010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4456020 : List Nat := [2, 4, 1, 1, 1, 2, 3, 1, 2, 3, 3]
def baseStart_4456020 : Nat := 118140960795 + 4456020 * 2 ^ 59
def prefixEnd_4456020 : Nat := 4983230072969 + 3 ^ 40 * 4456020 * 2
def baseEnd_4456020 : Nat := 2288080066047761034957143

theorem tailTrace_4456020 : CollatzResearch.WordTrace tailWord_4456020 prefixEnd_4456020 2288080066047761034957143 := by
  unfold tailWord_4456020
  simp only [CollatzResearch.WordTrace]
  refine ⟨81262200658304021236302757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108349600877738694981737009 81262200658304021236302757)
  ·
    refine ⟨15236662623432003981806767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81262200658304021236302757 15236662623432003981806767)
    ·
      refine ⟨22854993935148005972710151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15236662623432003981806767 22854993935148005972710151)
      ·
        refine ⟨34282490902722008959065227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22854993935148005972710151 34282490902722008959065227)
        ·
          refine ⟨51423736354083013438597841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34282490902722008959065227 51423736354083013438597841)
          ·
            refine ⟨38567802265562260078948381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51423736354083013438597841 38567802265562260078948381)
            ·
              refine ⟨14462925849585847529605643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38567802265562260078948381 14462925849585847529605643)
              ·
                refine ⟨21694388774378771294408465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14462925849585847529605643 21694388774378771294408465)
                ·
                  refine ⟨16270791580784078470806349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21694388774378771294408465 16270791580784078470806349)
                  ·
                    refine ⟨6101546842794029426552381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16270791580784078470806349 6101546842794029426552381)
                    ·
                      refine ⟨2288080066047761034957143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6101546842794029426552381 2288080066047761034957143)
                      ·
                        rfl

theorem cell23_4456020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_4456020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4456020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4456020 prefixEnd_4456020 := by exact prefixLift 4456020
  have htrace : WordTrace (prefixWord ++ tailWord_4456020) baseStart_4456020 baseEnd_4456020 := by
    simpa [prefixWord, tailWord_4456020, baseEnd_4456020] using wordTrace_append hprefix tailTrace_4456020
  have hstable : (prefixWord ++ tailWord_4456020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4456020).length < 2 ^ (prefixWord ++ tailWord_4456020).sum := by decide
  have hdescent : baseEnd_4456020 < baseStart_4456020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4456020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4456040 : List Nat := [2, 1, 4, 3, 1, 2, 1, 1, 1, 7]
def baseStart_4456040 : Nat := 118140960795 + 4456040 * 2 ^ 59
def prefixEnd_4456040 : Nat := 4983230072969 + 3 ^ 40 * 4456040 * 2
def baseEnd_4456040 : Nat := 762696778553616985569017

theorem tailTrace_4456040 : CollatzResearch.WordTrace tailWord_4456040 prefixEnd_4456040 762696778553616985569017 := by
  unfold tailWord_4456040
  simp only [CollatzResearch.WordTrace]
  refine ⟨81262565388267792944166787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108350087184357057258889049 81262565388267792944166787)
  ·
    refine ⟨121893848082401689416250181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81262565388267792944166787 121893848082401689416250181)
    ·
      refine ⟨22855096515450316765546909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121893848082401689416250181 22855096515450316765546909)
      ·
        refine ⟨8570661193293868787080091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22855096515450316765546909 8570661193293868787080091)
        ·
          refine ⟨12855991789940803180620137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8570661193293868787080091 12855991789940803180620137)
          ·
            refine ⟨9641993842455602385465103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12855991789940803180620137 9641993842455602385465103)
            ·
              refine ⟨14462990763683403578197655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9641993842455602385465103 14462990763683403578197655)
              ·
                refine ⟨21694486145525105367296483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14462990763683403578197655 21694486145525105367296483)
                ·
                  refine ⟨32541729218287658050944725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21694486145525105367296483 32541729218287658050944725)
                  ·
                    refine ⟨762696778553616985569017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32541729218287658050944725 762696778553616985569017)
                    ·
                      rfl

theorem cell23_4456040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_4456040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4456040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4456040 prefixEnd_4456040 := by exact prefixLift 4456040
  have htrace : WordTrace (prefixWord ++ tailWord_4456040) baseStart_4456040 baseEnd_4456040 := by
    simpa [prefixWord, tailWord_4456040, baseEnd_4456040] using wordTrace_append hprefix tailTrace_4456040
  have hstable : (prefixWord ++ tailWord_4456040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4456040).length < 2 ^ (prefixWord ++ tailWord_4456040).sum := by decide
  have hdescent : baseEnd_4456040 < baseStart_4456040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4456040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4456143 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 5, 6]
def baseStart_4456143 : Nat := 118140960795 + 4456143 * 2 ^ 59
def prefixEnd_4456143 : Nat := 4983230072969 + 3 ^ 40 * 4456143 * 2
def baseEnd_4456143 : Nat := 762714408056088017906359

theorem tailTrace_4456143 : CollatzResearch.WordTrace tailWord_4456143 prefixEnd_4456143 762714408056088017906359 := by
  unfold tailWord_4456143
  simp only [CollatzResearch.WordTrace]
  refine ⟨162528887495162434479333083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108352591663441622986222055 162528887495162434479333083)
  ·
    refine ⟨243793331242743651718999625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162528887495162434479333083 243793331242743651718999625)
    ·
      refine ⟨182844998432057738789249719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243793331242743651718999625 182844998432057738789249719)
      ·
        refine ⟨274267497648086608183874579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182844998432057738789249719 274267497648086608183874579)
        ·
          refine ⟨411401246472129912275811869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 274267497648086608183874579 411401246472129912275811869)
          ·
            refine ⟨154275467427048717103429451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 411401246472129912275811869 154275467427048717103429451)
            ·
              refine ⟨231413201140573075655144177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154275467427048717103429451 231413201140573075655144177)
              ·
                refine ⟨173559900855429806741358133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 231413201140573075655144177 173559900855429806741358133)
                ·
                  refine ⟨16271240705196544382002325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 173559900855429806741358133 16271240705196544382002325)
                  ·
                    refine ⟨762714408056088017906359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16271240705196544382002325 762714408056088017906359)
                    ·
                      rfl

theorem cell23_4456143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 6].length) (baseStart_4456143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4456143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4456143 prefixEnd_4456143 := by exact prefixLift 4456143
  have htrace : WordTrace (prefixWord ++ tailWord_4456143) baseStart_4456143 baseEnd_4456143 := by
    simpa [prefixWord, tailWord_4456143, baseEnd_4456143] using wordTrace_append hprefix tailTrace_4456143
  have hstable : (prefixWord ++ tailWord_4456143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4456143).length < 2 ^ (prefixWord ++ tailWord_4456143).sum := by decide
  have hdescent : baseEnd_4456143 < baseStart_4456143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4456143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4456154 : List Nat := [3, 1, 1, 2, 2, 4, 2, 1, 2, 3, 2]
def baseStart_4456154 : Nat := 118140960795 + 4456154 * 2 ^ 59
def prefixEnd_4456154 : Nat := 4983230072969 + 3 ^ 40 * 4456154 * 2
def baseEnd_4456154 : Nat := 2288148872455463510681527

theorem tailTrace_4456154 : CollatzResearch.WordTrace tailWord_4456154 prefixEnd_4456154 2288148872455463510681527 := by
  unfold tailWord_4456154
  simp only [CollatzResearch.WordTrace]
  refine ⟨40632322174530645839495879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108352859132081722238655677 40632322174530645839495879)
  ·
    refine ⟨60948483261795968759243819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40632322174530645839495879 60948483261795968759243819)
    ·
      refine ⟨91422724892693953138865729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60948483261795968759243819 91422724892693953138865729)
      ·
        refine ⟨68567043669520464854149297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91422724892693953138865729 68567043669520464854149297)
        ·
          refine ⟨51425282752140348640611973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68567043669520464854149297 51425282752140348640611973)
          ·
            refine ⟨9642240516026315370114745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51425282752140348640611973 9642240516026315370114745)
            ·
              refine ⟨7231680387019736527586059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9642240516026315370114745 7231680387019736527586059)
              ·
                refine ⟨10847520580529604791379089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7231680387019736527586059 10847520580529604791379089)
                ·
                  refine ⟨8135640435397203593534317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10847520580529604791379089 8135640435397203593534317)
                  ·
                    refine ⟨3050865163273951347575369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8135640435397203593534317 3050865163273951347575369)
                    ·
                      refine ⟨2288148872455463510681527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3050865163273951347575369 2288148872455463510681527)
                      ·
                        rfl

theorem cell23_4456154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 2, 3, 2].length) (baseStart_4456154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4456154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4456154 prefixEnd_4456154 := by exact prefixLift 4456154
  have htrace : WordTrace (prefixWord ++ tailWord_4456154) baseStart_4456154 baseEnd_4456154 := by
    simpa [prefixWord, tailWord_4456154, baseEnd_4456154] using wordTrace_append hprefix tailTrace_4456154
  have hstable : (prefixWord ++ tailWord_4456154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4456154).length < 2 ^ (prefixWord ++ tailWord_4456154).sum := by decide
  have hdescent : baseEnd_4456154 < baseStart_4456154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4456154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4456160 : List Nat := [2, 1, 1, 3, 1, 2, 2, 1, 6, 4]
def baseStart_4456160 : Nat := 118140960795 + 4456160 * 2 ^ 59
def prefixEnd_4456160 : Nat := 4983230072969 + 3 ^ 40 * 4456160 * 2
def baseEnd_4456160 : Nat := 762717317779796829068833

theorem tailTrace_4456160 : CollatzResearch.WordTrace tailWord_4456160 prefixEnd_4456160 762717317779796829068833 := by
  unfold tailWord_4456160
  simp only [CollatzResearch.WordTrace]
  refine ⟨81264753768050423191350967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108353005024067230921801289 81264753768050423191350967)
  ·
    refine ⟨121897130652075634787026451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81264753768050423191350967 121897130652075634787026451)
    ·
      refine ⟨182845695978113452180539677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121897130652075634787026451 182845695978113452180539677)
      ·
        refine ⟨68567135991792544567702379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 182845695978113452180539677 68567135991792544567702379)
        ·
          refine ⟨102850703987688816851553569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68567135991792544567702379 102850703987688816851553569)
          ·
            refine ⟨77138027990766612638665177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102850703987688816851553569 77138027990766612638665177)
            ·
              refine ⟨57853520993074959478998883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77138027990766612638665177 57853520993074959478998883)
              ·
                refine ⟨86780281489612439218498325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57853520993074959478998883 86780281489612439218498325)
                ·
                  refine ⟨4067825694825583088367109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 86780281489612439218498325 4067825694825583088367109)
                  ·
                    refine ⟨762717317779796829068833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4067825694825583088367109 762717317779796829068833)
                    ·
                      rfl

theorem cell23_4456160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 6, 4].length) (baseStart_4456160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4456160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4456160 prefixEnd_4456160 := by exact prefixLift 4456160
  have htrace : WordTrace (prefixWord ++ tailWord_4456160) baseStart_4456160 baseEnd_4456160 := by
    simpa [prefixWord, tailWord_4456160, baseEnd_4456160] using wordTrace_append hprefix tailTrace_4456160
  have hstable : (prefixWord ++ tailWord_4456160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4456160).length < 2 ^ (prefixWord ++ tailWord_4456160).sum := by decide
  have hdescent : baseEnd_4456160 < baseStart_4456160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4456160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4456177 : List Nat := [1, 2, 2, 2, 2, 3, 1, 4, 2, 4]
def baseStart_4456177 : Nat := 118140960795 + 4456177 * 2 ^ 59
def prefixEnd_4456177 : Nat := 4983230072969 + 3 ^ 40 * 4456177 * 2
def baseEnd_4456177 : Nat := 762720227503505640231307

theorem tailTrace_4456177 : CollatzResearch.WordTrace tailWord_4456177 prefixEnd_4456177 762720227503505640231307 := by
  unfold tailWord_4456177
  simp only [CollatzResearch.WordTrace]
  refine ⟨162530127577039258286070785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108353418384692838857380523 162530127577039258286070785)
  ·
    refine ⟨121897595682779443714553089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162530127577039258286070785 121897595682779443714553089)
    ·
      refine ⟨91423196762084582785914817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121897595682779443714553089 91423196762084582785914817)
      ·
        refine ⟨68567397571563437089436113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91423196762084582785914817 68567397571563437089436113)
        ·
          refine ⟨51425548178672577817077085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68567397571563437089436113 51425548178672577817077085)
          ·
            refine ⟨19284580567002216681403907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51425548178672577817077085 19284580567002216681403907)
            ·
              refine ⟨28926870850503325022105861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19284580567002216681403907 28926870850503325022105861)
              ·
                refine ⟨5423788284469373441644849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28926870850503325022105861 5423788284469373441644849)
                ·
                  refine ⟨4067841213352030081233637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5423788284469373441644849 4067841213352030081233637)
                  ·
                    refine ⟨762720227503505640231307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4067841213352030081233637 762720227503505640231307)
                    ·
                      rfl

theorem cell23_4456177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 4, 2, 4].length) (baseStart_4456177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4456177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4456177 prefixEnd_4456177 := by exact prefixLift 4456177
  have htrace : WordTrace (prefixWord ++ tailWord_4456177) baseStart_4456177 baseEnd_4456177 := by
    simpa [prefixWord, tailWord_4456177, baseEnd_4456177] using wordTrace_append hprefix tailTrace_4456177
  have hstable : (prefixWord ++ tailWord_4456177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4456177).length < 2 ^ (prefixWord ++ tailWord_4456177).sum := by decide
  have hdescent : baseEnd_4456177 < baseStart_4456177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4456177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4456194 : List Nat := [3, 4, 1, 1, 1, 1, 1, 5, 2, 4]
def baseStart_4456194 : Nat := 118140960795 + 4456194 * 2 ^ 59
def prefixEnd_4456194 : Nat := 4983230072969 + 3 ^ 40 * 4456194 * 2
def baseEnd_4456194 : Nat := 762723137227214451393781

theorem tailTrace_4456194 : CollatzResearch.WordTrace tailWord_4456194 prefixEnd_4456194 762723137227214451393781 := by
  unfold tailWord_4456194
  simp only [CollatzResearch.WordTrace]
  refine ⟨40632686904494417547359909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108353831745318446792959757 40632686904494417547359909)
  ·
    refine ⟨7618628794592703290129983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40632686904494417547359909 7618628794592703290129983)
    ·
      refine ⟨11427943191889054935194975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7618628794592703290129983 11427943191889054935194975)
      ·
        refine ⟨17141914787833582402792463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11427943191889054935194975 17141914787833582402792463)
        ·
          refine ⟨25712872181750373604188695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17141914787833582402792463 25712872181750373604188695)
          ·
            refine ⟨38569308272625560406283043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25712872181750373604188695 38569308272625560406283043)
            ·
              refine ⟨57853962408938340609424565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38569308272625560406283043 57853962408938340609424565)
              ·
                refine ⟨5423808975837969432133553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57853962408938340609424565 5423808975837969432133553)
                ·
                  refine ⟨4067856731878477074100165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5423808975837969432133553 4067856731878477074100165)
                  ·
                    refine ⟨762723137227214451393781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4067856731878477074100165 762723137227214451393781)
                    ·
                      rfl

theorem cell23_4456194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_4456194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4456194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4456194 prefixEnd_4456194 := by exact prefixLift 4456194
  have htrace : WordTrace (prefixWord ++ tailWord_4456194) baseStart_4456194 baseEnd_4456194 := by
    simpa [prefixWord, tailWord_4456194, baseEnd_4456194] using wordTrace_append hprefix tailTrace_4456194
  have hstable : (prefixWord ++ tailWord_4456194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4456194).length < 2 ^ (prefixWord ++ tailWord_4456194).sum := by decide
  have hdescent : baseEnd_4456194 < baseStart_4456194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4456194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4456205 : List Nat := [1, 7, 2, 1, 1, 1, 1, 1, 1, 5, 2]
def baseStart_4456205 : Nat := 118140960795 + 4456205 * 2 ^ 59
def prefixEnd_4456205 : Nat := 4983230072969 + 3 ^ 40 * 4456205 * 2
def baseEnd_4456205 : Nat := 2288175059968842811143793

theorem tailTrace_4456205 : CollatzResearch.WordTrace tailWord_4456205 prefixEnd_4456205 2288175059968842811143793 := by
  unfold tailWord_4456205
  simp only [CollatzResearch.WordTrace]
  refine ⟨162531148820937819068090069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108354099213958546045393379 162531148820937819068090069)
  ·
    refine ⟨3809323800490730134408361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 162531148820937819068090069 3809323800490730134408361)
    ·
      refine ⟨2856992850368047600806271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3809323800490730134408361 2856992850368047600806271)
      ·
        refine ⟨4285489275552071401209407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2856992850368047600806271 4285489275552071401209407)
        ·
          refine ⟨6428233913328107101814111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4285489275552071401209407 6428233913328107101814111)
          ·
            refine ⟨9642350869992160652721167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6428233913328107101814111 9642350869992160652721167)
            ·
              refine ⟨14463526304988240979081751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9642350869992160652721167 14463526304988240979081751)
              ·
                refine ⟨21695289457482361468622627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14463526304988240979081751 21695289457482361468622627)
                ·
                  refine ⟨32542934186223542202933941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21695289457482361468622627 32542934186223542202933941)
                  ·
                    refine ⟨3050900079958457081525057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32542934186223542202933941 3050900079958457081525057)
                    ·
                      refine ⟨2288175059968842811143793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3050900079958457081525057 2288175059968842811143793)
                      ·
                        rfl

theorem cell23_4456205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_4456205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4456205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4456205 prefixEnd_4456205 := by exact prefixLift 4456205
  have htrace : WordTrace (prefixWord ++ tailWord_4456205) baseStart_4456205 baseEnd_4456205 := by
    simpa [prefixWord, tailWord_4456205, baseEnd_4456205] using wordTrace_append hprefix tailTrace_4456205
  have hstable : (prefixWord ++ tailWord_4456205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4456205).length < 2 ^ (prefixWord ++ tailWord_4456205).sum := by decide
  have hdescent : baseEnd_4456205 < baseStart_4456205 := by decide
  rcases family_descends (prefixWord ++ tailWord_4456205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4456212 : List Nat := [2, 4, 4, 1, 1, 1, 2, 3, 1, 1, 3]
def baseStart_4456212 : Nat := 118140960795 + 4456212 * 2 ^ 59
def prefixEnd_4456212 : Nat := 4983230072969 + 3 ^ 40 * 4456212 * 2
def baseEnd_4456212 : Nat := 2288178654333424283756261

theorem tailTrace_4456212 : CollatzResearch.WordTrace tailWord_4456212 prefixEnd_4456212 2288178654333424283756261 := by
  unfold tailWord_4456212
  simp only [CollatzResearch.WordTrace]
  refine ⟨81265702065956229631797445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108354269421274972842396593 81265702065956229631797445)
  ·
    refine ⟨15237319137366793055962021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81265702065956229631797445 15237319137366793055962021)
    ·
      refine ⟨2856997338256273697992879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15237319137366793055962021 2856997338256273697992879)
      ·
        refine ⟨4285496007384410546989319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2856997338256273697992879 4285496007384410546989319)
        ·
          refine ⟨6428244011076615820483979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4285496007384410546989319 6428244011076615820483979)
          ·
            refine ⟨9642366016614923730725969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6428244011076615820483979 9642366016614923730725969)
            ·
              refine ⟨7231774512461192798044477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9642366016614923730725969 7231774512461192798044477)
              ·
                refine ⟨2711915442172947299266679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7231774512461192798044477 2711915442172947299266679)
                ·
                  refine ⟨4067873163259420948900019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2711915442172947299266679 4067873163259420948900019)
                  ·
                    refine ⟨6101809744889131423350029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4067873163259420948900019 6101809744889131423350029)
                    ·
                      refine ⟨2288178654333424283756261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6101809744889131423350029 2288178654333424283756261)
                      ·
                        rfl

theorem cell23_4456212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_4456212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4456212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4456212 prefixEnd_4456212 := by exact prefixLift 4456212
  have htrace : WordTrace (prefixWord ++ tailWord_4456212) baseStart_4456212 baseEnd_4456212 := by
    simpa [prefixWord, tailWord_4456212, baseEnd_4456212] using wordTrace_append hprefix tailTrace_4456212
  have hstable : (prefixWord ++ tailWord_4456212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4456212).length < 2 ^ (prefixWord ++ tailWord_4456212).sum := by decide
  have hdescent : baseEnd_4456212 < baseStart_4456212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4456212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4456218 : List Nat := [3, 1, 1, 3, 2, 3, 2, 3, 1, 2, 2]
def baseStart_4456218 : Nat := 118140960795 + 4456218 * 2 ^ 59
def prefixEnd_4456218 : Nat := 4983230072969 + 3 ^ 40 * 4456218 * 2
def baseEnd_4456218 : Nat := 2288181735217351260281233

theorem tailTrace_4456218 : CollatzResearch.WordTrace tailWord_4456218 prefixEnd_4456218 2288181735217351260281233 := by
  unfold tailWord_4456218
  simp only [CollatzResearch.WordTrace]
  refine ⟨40632905742472680572078327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108354415313260481525542205 40632905742472680572078327)
  ·
    refine ⟨60949358613709020858117491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40632905742472680572078327 60949358613709020858117491)
    ·
      refine ⟨91424037920563531287176237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60949358613709020858117491 91424037920563531287176237)
      ·
        refine ⟨34284014220211324232691089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91424037920563531287176237 34284014220211324232691089)
        ·
          refine ⟨25713010665158493174518317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34284014220211324232691089 25713010665158493174518317)
          ·
            refine ⟨9642378999434434940444369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25713010665158493174518317 9642378999434434940444369)
            ·
              refine ⟨7231784249575826205333277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9642378999434434940444369 7231784249575826205333277)
              ·
                refine ⟨2711919093590934826999979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7231784249575826205333277 2711919093590934826999979)
                ·
                  refine ⟨4067878640386402240499969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2711919093590934826999979 4067878640386402240499969)
                  ·
                    refine ⟨3050908980289801680374977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4067878640386402240499969 3050908980289801680374977)
                    ·
                      refine ⟨2288181735217351260281233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3050908980289801680374977 2288181735217351260281233)
                      ·
                        rfl

theorem cell23_4456218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 3, 1, 2, 2].length) (baseStart_4456218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4456218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4456218 prefixEnd_4456218 := by exact prefixLift 4456218
  have htrace : WordTrace (prefixWord ++ tailWord_4456218) baseStart_4456218 baseEnd_4456218 := by
    simpa [prefixWord, tailWord_4456218, baseEnd_4456218] using wordTrace_append hprefix tailTrace_4456218
  have hstable : (prefixWord ++ tailWord_4456218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4456218).length < 2 ^ (prefixWord ++ tailWord_4456218).sum := by decide
  have hdescent : baseEnd_4456218 < baseStart_4456218 := by decide
  rcases family_descends (prefixWord ++ tailWord_4456218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4456277 : List Nat := [1, 3, 2, 2, 2, 3, 1, 1, 2, 1, 5]
def baseStart_4456277 : Nat := 118140960795 + 4456277 * 2 ^ 59
def prefixEnd_4456277 : Nat := 4983230072969 + 3 ^ 40 * 4456277 * 2
def baseEnd_4456277 : Nat := 2288212030575966529443461

theorem tailTrace_4456277 : CollatzResearch.WordTrace tailWord_4456277 prefixEnd_4456277 2288212030575966529443461 := by
  unfold tailWord_4456277
  simp only [CollatzResearch.WordTrace]
  refine ⟨162533774876676975364711085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108355849917784650243140723 162533774876676975364711085)
  ·
    refine ⟨60950165578753865761766657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162533774876676975364711085 60950165578753865761766657)
    ·
      refine ⟨45712624184065399321324993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60950165578753865761766657 45712624184065399321324993)
      ·
        refine ⟨34284468138049049490993745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45712624184065399321324993 34284468138049049490993745)
        ·
          refine ⟨25713351103536787118245309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34284468138049049490993745 25713351103536787118245309)
          ·
            refine ⟨9642506663826295169341991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25713351103536787118245309 9642506663826295169341991)
            ·
              refine ⟨14463759995739442754012987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9642506663826295169341991 14463759995739442754012987)
              ·
                refine ⟨21695639993609164131019481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14463759995739442754012987 21695639993609164131019481)
                ·
                  refine ⟨16271729995206873098264611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21695639993609164131019481 16271729995206873098264611)
                  ·
                    refine ⟨24407594992810309647396917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16271729995206873098264611 24407594992810309647396917)
                    ·
                      refine ⟨2288212030575966529443461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24407594992810309647396917 2288212030575966529443461)
                      ·
                        rfl

theorem cell23_4456277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_4456277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4456277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4456277 prefixEnd_4456277 := by exact prefixLift 4456277
  have htrace : WordTrace (prefixWord ++ tailWord_4456277) baseStart_4456277 baseEnd_4456277 := by
    simpa [prefixWord, tailWord_4456277, baseEnd_4456277] using wordTrace_append hprefix tailTrace_4456277
  have hstable : (prefixWord ++ tailWord_4456277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4456277).length < 2 ^ (prefixWord ++ tailWord_4456277).sum := by decide
  have hdescent : baseEnd_4456277 < baseStart_4456277 := by decide
  rcases family_descends (prefixWord ++ tailWord_4456277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4456297 : List Nat := [1, 2, 1, 1, 1, 3, 1, 8, 5]
def baseStart_4456297 : Nat := 118140960795 + 4456297 * 2 ^ 59
def prefixEnd_4456297 : Nat := 4983230072969 + 3 ^ 40 * 4456297 * 2
def baseEnd_4456297 : Nat := 254246922243228494577041

theorem tailTrace_4456297 : CollatzResearch.WordTrace tailWord_4456297 prefixEnd_4456297 254246922243228494577041 := by
  unfold tailWord_4456297
  simp only [CollatzResearch.WordTrace]
  refine ⟨162534504336604518780439145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108356336224403012520292763 162534504336604518780439145)
  ·
    refine ⟨121900878252453389085329359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162534504336604518780439145 121900878252453389085329359)
    ·
      refine ⟨182851317378680083627994039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121900878252453389085329359 182851317378680083627994039)
      ·
        refine ⟨274276976068020125441991059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182851317378680083627994039 274276976068020125441991059)
        ·
          refine ⟨411415464102030188162986589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 274276976068020125441991059 411415464102030188162986589)
          ·
            refine ⟨154280799038261320561119971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 411415464102030188162986589 154280799038261320561119971)
            ·
              refine ⟨231421198557391980841679957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154280799038261320561119971 231421198557391980841679957)
              ·
                refine ⟨2711967170594437275488437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 231421198557391980841679957 2711967170594437275488437)
                ·
                  refine ⟨254246922243228494577041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2711967170594437275488437 254246922243228494577041)
                  ·
                    rfl

theorem cell23_4456297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 8, 5].length) (baseStart_4456297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4456297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4456297 prefixEnd_4456297 := by exact prefixLift 4456297
  have htrace : WordTrace (prefixWord ++ tailWord_4456297) baseStart_4456297 baseEnd_4456297 := by
    simpa [prefixWord, tailWord_4456297, baseEnd_4456297] using wordTrace_append hprefix tailTrace_4456297
  have hstable : (prefixWord ++ tailWord_4456297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4456297).length < 2 ^ (prefixWord ++ tailWord_4456297).sum := by decide
  have hdescent : baseEnd_4456297 < baseStart_4456297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4456297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4456320 : List Nat := [2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 7]
def baseStart_4456320 : Nat := 118140960795 + 4456320 * 2 ^ 59
def prefixEnd_4456320 : Nat := 4983230072969 + 3 ^ 40 * 4456320 * 2
def baseEnd_4456320 : Nat := 2288234110244109861205763

theorem tailTrace_4456320 : CollatzResearch.WordTrace tailWord_4456320 prefixEnd_4456320 2288234110244109861205763 := by
  unfold tailWord_4456320
  simp only [CollatzResearch.WordTrace]
  refine ⟨81267671607760596854263207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108356895477014129139017609 81267671607760596854263207)
  ·
    refine ⟨121901507411640895281394811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81267671607760596854263207 121901507411640895281394811)
    ·
      refine ⟨182852261117461342922092217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121901507411640895281394811 182852261117461342922092217)
      ·
        refine ⟨137139195838096007191569163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182852261117461342922092217 137139195838096007191569163)
        ·
          refine ⟨205708793757144010787353745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137139195838096007191569163 205708793757144010787353745)
          ·
            refine ⟨154281595317858008090515309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 205708793757144010787353745 154281595317858008090515309)
            ·
              refine ⟨57855598244196753033943241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 154281595317858008090515309 57855598244196753033943241)
              ·
                refine ⟨43391698683147564775457431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57855598244196753033943241 43391698683147564775457431)
                ·
                  refine ⟨65087548024721347163186147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43391698683147564775457431 65087548024721347163186147)
                  ·
                    refine ⟨97631322037082020744779221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 65087548024721347163186147 97631322037082020744779221)
                    ·
                      refine ⟨2288234110244109861205763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 97631322037082020744779221 2288234110244109861205763)
                      ·
                        rfl

theorem cell23_4456320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 7].length) (baseStart_4456320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4456320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4456320 prefixEnd_4456320 := by exact prefixLift 4456320
  have htrace : WordTrace (prefixWord ++ tailWord_4456320) baseStart_4456320 baseEnd_4456320 := by
    simpa [prefixWord, tailWord_4456320, baseEnd_4456320] using wordTrace_append hprefix tailTrace_4456320
  have hstable : (prefixWord ++ tailWord_4456320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4456320).length < 2 ^ (prefixWord ++ tailWord_4456320).sum := by decide
  have hdescent : baseEnd_4456320 < baseStart_4456320 := by decide
  rcases family_descends (prefixWord ++ tailWord_4456320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4456348 : List Nat := [2, 2, 3, 3, 1, 3, 2, 2, 5]
def baseStart_4456348 : Nat := 118140960795 + 4456348 * 2 ^ 59
def prefixEnd_4456348 : Nat := 4983230072969 + 3 ^ 40 * 4456348 * 2
def baseEnd_4456348 : Nat := 254249831966937305739515

theorem tailTrace_4456348 : CollatzResearch.WordTrace tailWord_4456348 prefixEnd_4456348 254249831966937305739515 := by
  unfold tailWord_4456348
  simp only [CollatzResearch.WordTrace]
  refine ⟨81268182229709877245272849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108357576306279836327030465 81268182229709877245272849)
  ·
    refine ⟨60951136672282407933954637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81268182229709877245272849 60951136672282407933954637)
    ·
      refine ⟨22856676252105902975232989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60951136672282407933954637 22856676252105902975232989)
      ·
        refine ⟨8571253594539713615712371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22856676252105902975232989 8571253594539713615712371)
        ·
          refine ⟨12856880391809570423568557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8571253594539713615712371 12856880391809570423568557)
          ·
            refine ⟨4821330146928588908838209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12856880391809570423568557 4821330146928588908838209)
            ·
              refine ⟨3615997610196441681628657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4821330146928588908838209 3615997610196441681628657)
              ·
                refine ⟨2711998207647331261221493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3615997610196441681628657 2711998207647331261221493)
                ·
                  refine ⟨254249831966937305739515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2711998207647331261221493 254249831966937305739515)
                  ·
                    rfl

theorem cell23_4456348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 2, 5].length) (baseStart_4456348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4456348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4456348 prefixEnd_4456348 := by exact prefixLift 4456348
  have htrace : WordTrace (prefixWord ++ tailWord_4456348) baseStart_4456348 baseEnd_4456348 := by
    simpa [prefixWord, tailWord_4456348, baseEnd_4456348] using wordTrace_append hprefix tailTrace_4456348
  have hstable : (prefixWord ++ tailWord_4456348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4456348).length < 2 ^ (prefixWord ++ tailWord_4456348).sum := by decide
  have hdescent : baseEnd_4456348 < baseStart_4456348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4456348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4456357 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 7, 4]
def baseStart_4456357 : Nat := 118140960795 + 4456357 * 2 ^ 59
def prefixEnd_4456357 : Nat := 4983230072969 + 3 ^ 40 * 4456357 * 2
def baseEnd_4456357 : Nat := 762751036342775405481031

theorem tailTrace_4456357 : CollatzResearch.WordTrace tailWord_4456357 prefixEnd_4456357 762751036342775405481031 := by
  unfold tailWord_4456357
  simp only [CollatzResearch.WordTrace]
  refine ⟨162536692716387149027623325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108357795144258099351748883 162536692716387149027623325)
  ·
    refine ⟨60951259768645180885358747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162536692716387149027623325 60951259768645180885358747)
    ·
      refine ⟨91426889652967771328038121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60951259768645180885358747 91426889652967771328038121)
      ·
        refine ⟨68570167239725828496028591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91426889652967771328038121 68570167239725828496028591)
        ·
          refine ⟨102855250859588742744042887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68570167239725828496028591 102855250859588742744042887)
          ·
            refine ⟨154282876289383114116064331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102855250859588742744042887 154282876289383114116064331)
            ·
              refine ⟨231424314434074671174096497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154282876289383114116064331 231424314434074671174096497)
              ·
                refine ⟨173568235825556003380572373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 231424314434074671174096497 173568235825556003380572373)
                ·
                  refine ⟨4068005527161468829232165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 173568235825556003380572373 4068005527161468829232165)
                  ·
                    refine ⟨762751036342775405481031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4068005527161468829232165 762751036342775405481031)
                    ·
                      rfl

theorem cell23_4456357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 7, 4].length) (baseStart_4456357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4456357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4456357 prefixEnd_4456357 := by exact prefixLift 4456357
  have htrace : WordTrace (prefixWord ++ tailWord_4456357) baseStart_4456357 baseEnd_4456357 := by
    simpa [prefixWord, tailWord_4456357, baseEnd_4456357] using wordTrace_append hprefix tailTrace_4456357
  have hstable : (prefixWord ++ tailWord_4456357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4456357).length < 2 ^ (prefixWord ++ tailWord_4456357).sum := by decide
  have hdescent : baseEnd_4456357 < baseStart_4456357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4456357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4456367 : List Nat := [1, 1, 2, 1, 2, 2, 4, 2, 1, 4, 3]
def baseStart_4456367 : Nat := 118140960795 + 4456367 * 2 ^ 59
def prefixEnd_4456367 : Nat := 4983230072969 + 3 ^ 40 * 4456367 * 2
def baseEnd_4456367 : Nat := 2288258243834871177318047

theorem tailTrace_4456367 : CollatzResearch.WordTrace tailWord_4456367 prefixEnd_4456367 2288258243834871177318047 := by
  unfold tailWord_4456367
  simp only [CollatzResearch.WordTrace]
  refine ⟨162537057446350920735487355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108358038297567280490324903 162537057446350920735487355)
  ·
    refine ⟨243805586169526381103231033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162537057446350920735487355 243805586169526381103231033)
    ·
      refine ⟨182854189627144785827423275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243805586169526381103231033 182854189627144785827423275)
      ·
        refine ⟨274281284440717178741134913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182854189627144785827423275 274281284440717178741134913)
        ·
          refine ⟨205710963330537884055851185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 274281284440717178741134913 205710963330537884055851185)
          ·
            refine ⟨154283222497903413041888389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 205710963330537884055851185 154283222497903413041888389)
            ·
              refine ⟨28928104218356889945354073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 154283222497903413041888389 28928104218356889945354073)
              ·
                refine ⟨21696078163767667459015555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28928104218356889945354073 21696078163767667459015555)
                ·
                  refine ⟨32544117245651501188523333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21696078163767667459015555 32544117245651501188523333)
                  ·
                    refine ⟨6102021983559656472848125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32544117245651501188523333 6102021983559656472848125)
                    ·
                      refine ⟨2288258243834871177318047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6102021983559656472848125 2288258243834871177318047)
                      ·
                        rfl

theorem cell23_4456367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 4, 3].length) (baseStart_4456367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4456367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4456367 prefixEnd_4456367 := by exact prefixLift 4456367
  have htrace : WordTrace (prefixWord ++ tailWord_4456367) baseStart_4456367 baseEnd_4456367 := by
    simpa [prefixWord, tailWord_4456367, baseEnd_4456367] using wordTrace_append hprefix tailTrace_4456367
  have hstable : (prefixWord ++ tailWord_4456367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4456367).length < 2 ^ (prefixWord ++ tailWord_4456367).sum := by decide
  have hdescent : baseEnd_4456367 < baseStart_4456367 := by decide
  rcases family_descends (prefixWord ++ tailWord_4456367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4456381 : List Nat := [1, 4, 1, 2, 3, 3, 1, 1, 2, 1, 4]
def baseStart_4456381 : Nat := 118140960795 + 4456381 * 2 ^ 59
def prefixEnd_4456381 : Nat := 4983230072969 + 3 ^ 40 * 4456381 * 2
def baseEnd_4456381 : Nat := 2288265432564034122542983

theorem tailTrace_4456381 : CollatzResearch.WordTrace tailWord_4456381 prefixEnd_4456381 2288265432564034122542983 := by
  unfold tailWord_4456381
  simp only [CollatzResearch.WordTrace]
  refine ⟨162537568068300201126496997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108358378712200134084331331 162537568068300201126496997)
  ·
    refine ⟨30475794012806287711218187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 162537568068300201126496997 30475794012806287711218187)
    ·
      refine ⟨45713691019209431566827281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30475794012806287711218187 45713691019209431566827281)
      ·
        refine ⟨34285268264407073675120461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45713691019209431566827281 34285268264407073675120461)
        ·
          refine ⟨12856975599152652628170173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34285268264407073675120461 12856975599152652628170173)
          ·
            refine ⟨4821365849682244735563815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12856975599152652628170173 4821365849682244735563815)
            ·
              refine ⟨7232048774523367103345723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4821365849682244735563815 7232048774523367103345723)
              ·
                refine ⟨10848073161785050655018585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7232048774523367103345723 10848073161785050655018585)
                ·
                  refine ⟨8136054871338787991263939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10848073161785050655018585 8136054871338787991263939)
                  ·
                    refine ⟨12204082307008181986895909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8136054871338787991263939 12204082307008181986895909)
                    ·
                      refine ⟨2288265432564034122542983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12204082307008181986895909 2288265432564034122542983)
                      ·
                        rfl

theorem cell23_4456381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_4456381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4456381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4456381 prefixEnd_4456381 := by exact prefixLift 4456381
  have htrace : WordTrace (prefixWord ++ tailWord_4456381) baseStart_4456381 baseEnd_4456381 := by
    simpa [prefixWord, tailWord_4456381, baseEnd_4456381] using wordTrace_append hprefix tailTrace_4456381
  have hstable : (prefixWord ++ tailWord_4456381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4456381).length < 2 ^ (prefixWord ++ tailWord_4456381).sum := by decide
  have hdescent : baseEnd_4456381 < baseStart_4456381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4456381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4456417 : List Nat := [1, 2, 3, 1, 2, 1, 2, 1, 5, 5]
def baseStart_4456417 : Nat := 118140960795 + 4456417 * 2 ^ 59
def prefixEnd_4456417 : Nat := 4983230072969 + 3 ^ 40 * 4456417 * 2
def baseEnd_4456417 : Nat := 762761305955865327230939

theorem tailTrace_4456417 : CollatzResearch.WordTrace tailWord_4456417 prefixEnd_4456417 762761305955865327230939 := by
  unfold tailWord_4456417
  simp only [CollatzResearch.WordTrace]
  refine ⟨162538881096169779274807505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108359254064113186183205003 162538881096169779274807505)
  ·
    refine ⟨121904160822127334456105629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162538881096169779274807505 121904160822127334456105629)
    ·
      refine ⟨45714060308297750421039611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121904160822127334456105629 45714060308297750421039611)
      ·
        refine ⟨68571090462446625631559417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45714060308297750421039611 68571090462446625631559417)
        ·
          refine ⟨51428317846834969223669563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68571090462446625631559417 51428317846834969223669563)
          ·
            refine ⟨77142476770252453835504345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51428317846834969223669563 77142476770252453835504345)
            ·
              refine ⟨57856857577689340376628259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77142476770252453835504345 57856857577689340376628259)
              ·
                refine ⟨86785286366534010564942389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57856857577689340376628259 86785286366534010564942389)
                ·
                  refine ⟨8136120596862563490463349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 86785286366534010564942389 8136120596862563490463349)
                  ·
                    refine ⟨762761305955865327230939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8136120596862563490463349 762761305955865327230939)
                    ·
                      rfl

theorem cell23_4456417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 5, 5].length) (baseStart_4456417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4456417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4456417 prefixEnd_4456417 := by exact prefixLift 4456417
  have htrace : WordTrace (prefixWord ++ tailWord_4456417) baseStart_4456417 baseEnd_4456417 := by
    simpa [prefixWord, tailWord_4456417, baseEnd_4456417] using wordTrace_append hprefix tailTrace_4456417
  have hstable : (prefixWord ++ tailWord_4456417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4456417).length < 2 ^ (prefixWord ++ tailWord_4456417).sum := by decide
  have hdescent : baseEnd_4456417 < baseStart_4456417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4456417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4456447 : List Nat := [1, 1, 2, 2, 1, 2, 1, 6, 1, 6]
def baseStart_4456447 : Nat := 118140960795 + 4456447 * 2 ^ 59
def prefixEnd_4456447 : Nat := 4983230072969 + 3 ^ 40 * 4456447 * 2
def baseEnd_4456447 : Nat := 762766440762410288105893

theorem tailTrace_4456447 : CollatzResearch.WordTrace tailWord_4456447 prefixEnd_4456447 762766440762410288105893 := by
  unfold tailWord_4456447
  simp only [CollatzResearch.WordTrace]
  refine ⟨162539975286061094398399595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108359983524040729598933063 162539975286061094398399595)
  ·
    refine ⟨243809962929091641597599393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162539975286061094398399595 243809962929091641597599393)
    ·
      refine ⟨182857472196818731198199545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243809962929091641597599393 182857472196818731198199545)
      ·
        refine ⟨137143104147614048398649659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182857472196818731198199545 137143104147614048398649659)
        ·
          refine ⟨205714656221421072597974489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137143104147614048398649659 205714656221421072597974489)
          ·
            refine ⟨154285992166065804448480867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 205714656221421072597974489 154285992166065804448480867)
            ·
              refine ⟨231428988249098706672721301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154285992166065804448480867 231428988249098706672721301)
              ·
                refine ⟨10848233824176501875283811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 231428988249098706672721301 10848233824176501875283811)
                ·
                  refine ⟨16272350736264752812925717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10848233824176501875283811 16272350736264752812925717)
                  ·
                    refine ⟨762766440762410288105893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16272350736264752812925717 762766440762410288105893)
                    ·
                      rfl

theorem cell23_4456447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 6].length) (baseStart_4456447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4456447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4456447 prefixEnd_4456447 := by exact prefixLift 4456447
  have htrace : WordTrace (prefixWord ++ tailWord_4456447) baseStart_4456447 baseEnd_4456447 := by
    simpa [prefixWord, tailWord_4456447, baseEnd_4456447] using wordTrace_append hprefix tailTrace_4456447
  have hstable : (prefixWord ++ tailWord_4456447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4456447).length < 2 ^ (prefixWord ++ tailWord_4456447).sum := by decide
  have hdescent : baseEnd_4456447 < baseStart_4456447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4456447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4456458 : List Nat := [3, 1, 2, 2, 4, 1, 1, 2, 2, 3, 2]
def baseStart_4456458 : Nat := 118140960795 + 4456458 * 2 ^ 59
def prefixEnd_4456458 : Nat := 4983230072969 + 3 ^ 40 * 4456458 * 2
def baseEnd_4456458 : Nat := 2288304970574430321280129

theorem tailTrace_4456458 : CollatzResearch.WordTrace tailWord_4456458 prefixEnd_4456458 2288304970574430321280129 := by
  unfold tailWord_4456458
  simp only [CollatzResearch.WordTrace]
  refine ⟨40635094122255310819262507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108360250992680828851366685 40635094122255310819262507)
  ·
    refine ⟨60952641183382966228893761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40635094122255310819262507 60952641183382966228893761)
    ·
      refine ⟨45714480887537224671670321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60952641183382966228893761 45714480887537224671670321)
      ·
        refine ⟨34285860665652918503752741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45714480887537224671670321 34285860665652918503752741)
        ·
          refine ⟨6428598874809922219453639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34285860665652918503752741 6428598874809922219453639)
          ·
            refine ⟨9642898312214883329180459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6428598874809922219453639 9642898312214883329180459)
            ·
              refine ⟨14464347468322324993770689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9642898312214883329180459 14464347468322324993770689)
              ·
                refine ⟨10848260601241743745328017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14464347468322324993770689 10848260601241743745328017)
                ·
                  refine ⟨8136195450931307808996013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10848260601241743745328017 8136195450931307808996013)
                  ·
                    refine ⟨3051073294099240428373505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8136195450931307808996013 3051073294099240428373505)
                    ·
                      refine ⟨2288304970574430321280129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3051073294099240428373505 2288304970574430321280129)
                      ·
                        rfl

theorem cell23_4456458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 2, 3, 2].length) (baseStart_4456458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4456458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4456458 prefixEnd_4456458 := by exact prefixLift 4456458
  have htrace : WordTrace (prefixWord ++ tailWord_4456458) baseStart_4456458 baseEnd_4456458 := by
    simpa [prefixWord, tailWord_4456458, baseEnd_4456458] using wordTrace_append hprefix tailTrace_4456458
  have hstable : (prefixWord ++ tailWord_4456458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4456458).length < 2 ^ (prefixWord ++ tailWord_4456458).sum := by decide
  have hdescent : baseEnd_4456458 < baseStart_4456458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4456458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4456467 : List Nat := [1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 6]
def baseStart_4456467 : Nat := 118140960795 + 4456467 * 2 ^ 59
def prefixEnd_4456467 : Nat := 4983230072969 + 3 ^ 40 * 4456467 * 2
def baseEnd_4456467 : Nat := 2288309591900320786067587

theorem tailTrace_4456467 : CollatzResearch.WordTrace tailWord_4456467 prefixEnd_4456467 2288309591900320786067587 := by
  unfold tailWord_4456467
  simp only [CollatzResearch.WordTrace]
  refine ⟨162540704745988637814127655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108360469830659091876085103 162540704745988637814127655)
  ·
    refine ⟨243811057118982956721191483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162540704745988637814127655 243811057118982956721191483)
    ·
      refine ⟨365716585678474435081787225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243811057118982956721191483 365716585678474435081787225)
      ·
        refine ⟨274287439258855826311340419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 365716585678474435081787225 274287439258855826311340419)
        ·
          refine ⟨411431158888283739467010629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 274287439258855826311340419 411431158888283739467010629)
          ·
            refine ⟨77143342291553201150064493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 411431158888283739467010629 77143342291553201150064493)
            ·
              refine ⟨28928753359332450431274185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77143342291553201150064493 28928753359332450431274185)
              ·
                refine ⟨21696565019499337823455639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28928753359332450431274185 21696565019499337823455639)
                ·
                  refine ⟨32544847529249006735183459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21696565019499337823455639 32544847529249006735183459)
                  ·
                    refine ⟨48817271293873510102775189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32544847529249006735183459 48817271293873510102775189)
                    ·
                      refine ⟨2288309591900320786067587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48817271293873510102775189 2288309591900320786067587)
                      ·
                        rfl

theorem cell23_4456467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 6].length) (baseStart_4456467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4456467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4456467 prefixEnd_4456467 := by exact prefixLift 4456467
  have htrace : WordTrace (prefixWord ++ tailWord_4456467) baseStart_4456467 baseEnd_4456467 := by
    simpa [prefixWord, tailWord_4456467, baseEnd_4456467] using wordTrace_append hprefix tailTrace_4456467
  have hstable : (prefixWord ++ tailWord_4456467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4456467).length < 2 ^ (prefixWord ++ tailWord_4456467).sum := by decide
  have hdescent : baseEnd_4456467 < baseStart_4456467 := by decide
  rcases family_descends (prefixWord ++ tailWord_4456467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4456474 : List Nat := [3, 1, 1, 3, 1, 3, 2, 2, 1, 1, 5]
def baseStart_4456474 : Nat := 118140960795 + 4456474 * 2 ^ 59
def prefixEnd_4456474 : Nat := 4983230072969 + 3 ^ 40 * 4456474 * 2
def baseEnd_4456474 : Nat := 2288313186264902258680055

theorem tailTrace_4456474 : CollatzResearch.WordTrace tailWord_4456474 prefixEnd_4456474 2288313186264902258680055 := by
  unfold tailWord_4456474
  simp only [CollatzResearch.WordTrace]
  refine ⟨40635240014240819502408119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108360640037975518673088317 40635240014240819502408119)
  ·
    refine ⟨60952860021361229253612179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40635240014240819502408119 60952860021361229253612179)
    ·
      refine ⟨91429290032041843880418269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60952860021361229253612179 91429290032041843880418269)
      ·
        refine ⟨34285983762015691455156851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91429290032041843880418269 34285983762015691455156851)
        ·
          refine ⟨51428975643023537182735277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34285983762015691455156851 51428975643023537182735277)
          ·
            refine ⟨19285865866133826443525729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51428975643023537182735277 19285865866133826443525729)
            ·
              refine ⟨14464399399600369832644297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19285865866133826443525729 14464399399600369832644297)
              ·
                refine ⟨10848299549700277374483223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14464399399600369832644297 10848299549700277374483223)
                ·
                  refine ⟨16272449324550416061724835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10848299549700277374483223 16272449324550416061724835)
                  ·
                    refine ⟨24408673986825624092587253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16272449324550416061724835 24408673986825624092587253)
                    ·
                      refine ⟨2288313186264902258680055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24408673986825624092587253 2288313186264902258680055)
                      ·
                        rfl

theorem cell23_4456474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_4456474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4456474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4456474 prefixEnd_4456474 := by exact prefixLift 4456474
  have htrace : WordTrace (prefixWord ++ tailWord_4456474) baseStart_4456474 baseEnd_4456474 := by
    simpa [prefixWord, tailWord_4456474, baseEnd_4456474] using wordTrace_append hprefix tailTrace_4456474
  have hstable : (prefixWord ++ tailWord_4456474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4456474).length < 2 ^ (prefixWord ++ tailWord_4456474).sum := by decide
  have hdescent : baseEnd_4456474 < baseStart_4456474 := by decide
  rcases family_descends (prefixWord ++ tailWord_4456474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4456488 : List Nat := [2, 1, 5, 3, 1, 1, 1, 1, 3, 1, 4]
def baseStart_4456488 : Nat := 118140960795 + 4456488 * 2 ^ 59
def prefixEnd_4456488 : Nat := 4983230072969 + 3 ^ 40 * 4456488 * 2
def baseEnd_4456488 : Nat := 2288320374994065203904991

theorem tailTrace_4456488 : CollatzResearch.WordTrace tailWord_4456488 prefixEnd_4456488 2288320374994065203904991 := by
  unfold tailWord_4456488
  simp only [CollatzResearch.WordTrace]
  refine ⟨81270735339456279200321059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108360980452608372267094745 81270735339456279200321059)
  ·
    refine ⟨121906103009184418800481589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81270735339456279200321059 121906103009184418800481589)
    ·
      refine ⟨11428697157111039262545149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 121906103009184418800481589 11428697157111039262545149)
      ·
        refine ⟨4285761433916639723454431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11428697157111039262545149 4285761433916639723454431)
        ·
          refine ⟨6428642150874959585181647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4285761433916639723454431 6428642150874959585181647)
          ·
            refine ⟨9642963226312439377772471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6428642150874959585181647 9642963226312439377772471)
            ·
              refine ⟨14464444839468659066658707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9642963226312439377772471 14464444839468659066658707)
              ·
                refine ⟨21696667259202988599988061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14464444839468659066658707 21696667259202988599988061)
                ·
                  refine ⟨8136250222201120724995523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21696667259202988599988061 8136250222201120724995523)
                  ·
                    refine ⟨12204375333301681087493285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8136250222201120724995523 12204375333301681087493285)
                    ·
                      refine ⟨2288320374994065203904991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12204375333301681087493285 2288320374994065203904991)
                      ·
                        rfl

theorem cell23_4456488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_4456488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4456488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4456488 prefixEnd_4456488 := by exact prefixLift 4456488
  have htrace : WordTrace (prefixWord ++ tailWord_4456488) baseStart_4456488 baseEnd_4456488 := by
    simpa [prefixWord, tailWord_4456488, baseEnd_4456488] using wordTrace_append hprefix tailTrace_4456488
  have hstable : (prefixWord ++ tailWord_4456488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4456488).length < 2 ^ (prefixWord ++ tailWord_4456488).sum := by decide
  have hdescent : baseEnd_4456488 < baseStart_4456488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4456488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4456494 : List Nat := [4, 1, 3, 1, 1, 2, 2, 9]
def baseStart_4456494 : Nat := 118140960795 + 4456494 * 2 ^ 59
def prefixEnd_4456494 : Nat := 4983230072969 + 3 ^ 40 * 4456494 * 2
def baseEnd_4456494 : Nat := 84752720588073784460369

theorem tailTrace_4456494 : CollatzResearch.WordTrace tailWord_4456494 prefixEnd_4456494 84752720588073784460369 := by
  unfold tailWord_4456494
  simp only [CollatzResearch.WordTrace]
  refine ⟨20317711189611352678170067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108361126344593880950240357 20317711189611352678170067)
  ·
    refine ⟨30476566784417029017255101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20317711189611352678170067 30476566784417029017255101)
    ·
      refine ⟨11428712544156385881470663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30476566784417029017255101 11428712544156385881470663)
      ·
        refine ⟨17143068816234578822205995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11428712544156385881470663 17143068816234578822205995)
        ·
          refine ⟨25714603224351868233308993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17143068816234578822205995 25714603224351868233308993)
          ·
            refine ⟨19285952418263901174981745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25714603224351868233308993 19285952418263901174981745)
            ·
              refine ⟨14464464313697925881236309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19285952418263901174981745 14464464313697925881236309)
              ·
                refine ⟨84752720588073784460369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14464464313697925881236309 84752720588073784460369)
                ·
                  rfl

theorem cell23_4456494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 9].length) (baseStart_4456494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4456494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4456494 prefixEnd_4456494 := by exact prefixLift 4456494
  have htrace : WordTrace (prefixWord ++ tailWord_4456494) baseStart_4456494 baseEnd_4456494 := by
    simpa [prefixWord, tailWord_4456494, baseEnd_4456494] using wordTrace_append hprefix tailTrace_4456494
  have hstable : (prefixWord ++ tailWord_4456494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4456494).length < 2 ^ (prefixWord ++ tailWord_4456494).sum := by decide
  have hdescent : baseEnd_4456494 < baseStart_4456494 := by decide
  rcases family_descends (prefixWord ++ tailWord_4456494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4456508 : List Nat := [2, 2, 2, 2, 2, 1, 5, 1, 1, 2, 3]
def baseStart_4456508 : Nat := 118140960795 + 4456508 * 2 ^ 59
def prefixEnd_4456508 : Nat := 4983230072969 + 3 ^ 40 * 4456508 * 2
def baseEnd_4456508 : Nat := 2288330644607155125654899

theorem tailTrace_4456508 : CollatzResearch.WordTrace tailWord_4456508 prefixEnd_4456508 2288330644607155125654899 := by
  unfold tailWord_4456508
  simp only [CollatzResearch.WordTrace]
  refine ⟨81271100069420050908185089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108361466759226734544246785 81271100069420050908185089)
  ·
    refine ⟨60953325052065038181138817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81271100069420050908185089 60953325052065038181138817)
    ·
      refine ⟨45714993789048778635854113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60953325052065038181138817 45714993789048778635854113)
      ·
        refine ⟨34286245341786583976890585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45714993789048778635854113 34286245341786583976890585)
        ·
          refine ⟨25714684006339937982667939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34286245341786583976890585 25714684006339937982667939)
          ·
            refine ⟨38572026009509906974001909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25714684006339937982667939 38572026009509906974001909)
            ·
              refine ⟨3616127438391553778812679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38572026009509906974001909 3616127438391553778812679)
              ·
                refine ⟨5424191157587330668219019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3616127438391553778812679 5424191157587330668219019)
                ·
                  refine ⟨8136286736380996002328529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5424191157587330668219019 8136286736380996002328529)
                  ·
                    refine ⟨6102215052285747001746397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8136286736380996002328529 6102215052285747001746397)
                    ·
                      refine ⟨2288330644607155125654899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6102215052285747001746397 2288330644607155125654899)
                      ·
                        rfl

theorem cell23_4456508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 1, 1, 2, 3].length) (baseStart_4456508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4456508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4456508 prefixEnd_4456508 := by exact prefixLift 4456508
  have htrace : WordTrace (prefixWord ++ tailWord_4456508) baseStart_4456508 baseEnd_4456508 := by
    simpa [prefixWord, tailWord_4456508, baseEnd_4456508] using wordTrace_append hprefix tailTrace_4456508
  have hstable : (prefixWord ++ tailWord_4456508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4456508).length < 2 ^ (prefixWord ++ tailWord_4456508).sum := by decide
  have hdescent : baseEnd_4456508 < baseStart_4456508 := by decide
  rcases family_descends (prefixWord ++ tailWord_4456508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4456561 : List Nat := [1, 2, 2, 2, 1, 1, 3, 4, 1, 4, 2]
def baseStart_4456561 : Nat := 118140960795 + 4456561 * 2 ^ 59
def prefixEnd_4456561 : Nat := 4983230072969 + 3 ^ 40 * 4456561 * 2
def baseEnd_4456561 : Nat := 2288357859081843418292155

theorem tailTrace_4456561 : CollatzResearch.WordTrace tailWord_4456561 prefixEnd_4456561 2288357859081843418292155 := by
  unfold tailWord_4456561
  simp only [CollatzResearch.WordTrace]
  refine ⟨162544133207648091868049537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108362755471765394578699691 162544133207648091868049537)
  ·
    refine ⟨121908099905736068901037153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162544133207648091868049537 121908099905736068901037153)
    ·
      refine ⟨91431074929302051675777865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121908099905736068901037153 91431074929302051675777865)
      ·
        refine ⟨68573306196976538756833399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91431074929302051675777865 68573306196976538756833399)
        ·
          refine ⟨102859959295464808135250099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68573306196976538756833399 102859959295464808135250099)
          ·
            refine ⟨154289938943197212202875149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102859959295464808135250099 154289938943197212202875149)
            ·
              refine ⟨57858727103698954576078181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 154289938943197212202875149 57858727103698954576078181)
              ·
                refine ⟨10848511331943553983014659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57858727103698954576078181 10848511331943553983014659)
                ·
                  refine ⟨16272766997915330974521989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10848511331943553983014659 16272766997915330974521989)
                  ·
                    refine ⟨3051143812109124557722873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16272766997915330974521989 3051143812109124557722873)
                    ·
                      refine ⟨2288357859081843418292155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3051143812109124557722873 2288357859081843418292155)
                      ·
                        rfl

theorem cell23_4456561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 4, 2].length) (baseStart_4456561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4456561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4456561 prefixEnd_4456561 := by exact prefixLift 4456561
  have htrace : WordTrace (prefixWord ++ tailWord_4456561) baseStart_4456561 baseEnd_4456561 := by
    simpa [prefixWord, tailWord_4456561, baseEnd_4456561] using wordTrace_append hprefix tailTrace_4456561
  have hstable : (prefixWord ++ tailWord_4456561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4456561).length < 2 ^ (prefixWord ++ tailWord_4456561).sum := by decide
  have hdescent : baseEnd_4456561 < baseStart_4456561 := by decide
  rcases family_descends (prefixWord ++ tailWord_4456561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4456631 : List Nat := [1, 1, 3, 1, 4, 3, 1, 2, 2, 5]
def baseStart_4456631 : Nat := 118140960795 + 4456631 * 2 ^ 59
def prefixEnd_4456631 : Nat := 4983230072969 + 3 ^ 40 * 4456631 * 2
def baseEnd_4456631 : Nat := 762797934242552714805611

theorem tailTrace_4456631 : CollatzResearch.WordTrace tailWord_4456631 prefixEnd_4456631 762797934242552714805611 := by
  unfold tailWord_4456631
  simp only [CollatzResearch.WordTrace]
  refine ⟨162546686317394493823097747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108364457544929662548731831 162546686317394493823097747)
  ·
    refine ⟨243820029476091740734646621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162546686317394493823097747 243820029476091740734646621)
    ·
      refine ⟨91432511053534402775492483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 243820029476091740734646621 91432511053534402775492483)
      ·
        refine ⟨137148766580301604163238725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91432511053534402775492483 137148766580301604163238725)
        ·
          refine ⟨25715393733806550780607261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 137148766580301604163238725 25715393733806550780607261)
          ·
            refine ⟨9643272650177456542727723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25715393733806550780607261 9643272650177456542727723)
            ·
              refine ⟨14464908975266184814091585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9643272650177456542727723 14464908975266184814091585)
              ·
                refine ⟨10848681731449638610568689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14464908975266184814091585 10848681731449638610568689)
                ·
                  refine ⟨8136511298587228957926517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10848681731449638610568689 8136511298587228957926517)
                  ·
                    refine ⟨762797934242552714805611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8136511298587228957926517 762797934242552714805611)
                    ·
                      rfl

theorem cell23_4456631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 2, 5].length) (baseStart_4456631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4456631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4456631 prefixEnd_4456631 := by exact prefixLift 4456631
  have htrace : WordTrace (prefixWord ++ tailWord_4456631) baseStart_4456631 baseEnd_4456631 := by
    simpa [prefixWord, tailWord_4456631, baseEnd_4456631] using wordTrace_append hprefix tailTrace_4456631
  have hstable : (prefixWord ++ tailWord_4456631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4456631).length < 2 ^ (prefixWord ++ tailWord_4456631).sum := by decide
  have hdescent : baseEnd_4456631 < baseStart_4456631 := by decide
  rcases family_descends (prefixWord ++ tailWord_4456631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4456651 : List Nat := [1, 1, 1, 1, 3, 2, 4, 1, 1, 6, 2]
def baseStart_4456651 : Nat := 118140960795 + 4456651 * 2 ^ 59
def prefixEnd_4456651 : Nat := 4983230072969 + 3 ^ 40 * 4456651 * 2
def baseEnd_4456651 : Nat := 2288404072340748066166741

theorem tailTrace_4456651 : CollatzResearch.WordTrace tailWord_4456651 prefixEnd_4456651 2288404072340748066166741 := by
  unfold tailWord_4456651
  simp only [CollatzResearch.WordTrace]
  refine ⟨162547415777322037238825807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108364943851548024825883871 162547415777322037238825807)
  ·
    refine ⟨243821123665983055858238711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162547415777322037238825807 243821123665983055858238711)
    ·
      refine ⟨365731685498974583787358067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243821123665983055858238711 365731685498974583787358067)
      ·
        refine ⟨548597528248461875681037101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 365731685498974583787358067 548597528248461875681037101)
        ·
          refine ⟨205724073093173203380388913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 548597528248461875681037101 205724073093173203380388913)
          ·
            refine ⟨154293054819879902535291685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 205724073093173203380388913 154293054819879902535291685)
            ·
              refine ⟨28929947778727481725367191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 154293054819879902535291685 28929947778727481725367191)
              ·
                refine ⟨43394921668091222588050787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28929947778727481725367191 43394921668091222588050787)
                ·
                  refine ⟨65092382502136833882076181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43394921668091222588050787 65092382502136833882076181)
                  ·
                    refine ⟨3051205429787664088222321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 65092382502136833882076181 3051205429787664088222321)
                    ·
                      refine ⟨2288404072340748066166741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3051205429787664088222321 2288404072340748066166741)
                      ·
                        rfl

theorem cell23_4456651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 6, 2].length) (baseStart_4456651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4456651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4456651 prefixEnd_4456651 := by exact prefixLift 4456651
  have htrace : WordTrace (prefixWord ++ tailWord_4456651) baseStart_4456651 baseEnd_4456651 := by
    simpa [prefixWord, tailWord_4456651, baseEnd_4456651] using wordTrace_append hprefix tailTrace_4456651
  have hstable : (prefixWord ++ tailWord_4456651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4456651).length < 2 ^ (prefixWord ++ tailWord_4456651).sum := by decide
  have hdescent : baseEnd_4456651 < baseStart_4456651 := by decide
  rcases family_descends (prefixWord ++ tailWord_4456651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4456691 : List Nat := [1, 1, 1, 2, 2, 4, 4, 2, 6]
def baseStart_4456691 : Nat := 118140960795 + 4456691 * 2 ^ 59
def prefixEnd_4456691 : Nat := 4983230072969 + 3 ^ 40 * 4456691 * 2
def baseEnd_4456691 : Nat := 254269401285214212185173

theorem tailTrace_4456691 : CollatzResearch.WordTrace tailWord_4456691 prefixEnd_4456691 254269401285214212185173 := by
  unfold tailWord_4456691
  simp only [CollatzResearch.WordTrace]
  refine ⟨162548874697177124070281927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108365916464784749380187951 162548874697177124070281927)
  ·
    refine ⟨243823312045765686105422891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162548874697177124070281927 243823312045765686105422891)
    ·
      refine ⟨365734968068648529158134337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243823312045765686105422891 365734968068648529158134337)
      ·
        refine ⟨274301226051486396868600753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 365734968068648529158134337 274301226051486396868600753)
        ·
          refine ⟨205725919538614797651450565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 274301226051486396868600753 205725919538614797651450565)
          ·
            refine ⟨38573609913490274559646981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 205725919538614797651450565 38573609913490274559646981)
            ·
              refine ⟨7232551858779426479933809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38573609913490274559646981 7232551858779426479933809)
              ·
                refine ⟨5424413894084569859950357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7232551858779426479933809 5424413894084569859950357)
                ·
                  refine ⟨254269401285214212185173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5424413894084569859950357 254269401285214212185173)
                  ·
                    rfl

theorem cell23_4456691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 2, 6].length) (baseStart_4456691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4456691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4456691 prefixEnd_4456691 := by exact prefixLift 4456691
  have htrace : WordTrace (prefixWord ++ tailWord_4456691) baseStart_4456691 baseEnd_4456691 := by
    simpa [prefixWord, tailWord_4456691, baseEnd_4456691] using wordTrace_append hprefix tailTrace_4456691
  have hstable : (prefixWord ++ tailWord_4456691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4456691).length < 2 ^ (prefixWord ++ tailWord_4456691).sum := by decide
  have hdescent : baseEnd_4456691 < baseStart_4456691 := by decide
  rcases family_descends (prefixWord ++ tailWord_4456691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4456721 : List Nat := [1, 2, 2, 1, 1, 5, 2, 1, 3, 5]
def baseStart_4456721 : Nat := 118140960795 + 4456721 * 2 ^ 59
def prefixEnd_4456721 : Nat := 4983230072969 + 3 ^ 40 * 4456721 * 2
def baseEnd_4456721 : Nat := 762813338662187597430473

theorem tailTrace_4456721 : CollatzResearch.WordTrace tailWord_4456721 prefixEnd_4456721 762813338662187597430473 := by
  unfold tailWord_4456721
  simp only [CollatzResearch.WordTrace]
  refine ⟨162549968887068439193874017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108366645924712292795916011 162549968887068439193874017)
  ·
    refine ⟨121912476665301329395405513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162549968887068439193874017 121912476665301329395405513)
    ·
      refine ⟨91434357498975997046554135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121912476665301329395405513 91434357498975997046554135)
      ·
        refine ⟨137151536248463995569831203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91434357498975997046554135 137151536248463995569831203)
        ·
          refine ⟨205727304372695993354746805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137151536248463995569831203 205727304372695993354746805)
          ·
            refine ⟨19286934784940249377007513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 205727304372695993354746805 19286934784940249377007513)
            ·
              refine ⟨14465201088705187032755635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19286934784940249377007513 14465201088705187032755635)
              ·
                refine ⟨21697801633057780549133453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14465201088705187032755635 21697801633057780549133453)
                ·
                  refine ⟨8136675612396667705925045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21697801633057780549133453 8136675612396667705925045)
                  ·
                    refine ⟨762813338662187597430473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8136675612396667705925045 762813338662187597430473)
                    ·
                      rfl

theorem cell23_4456721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 5].length) (baseStart_4456721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4456721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4456721 prefixEnd_4456721 := by exact prefixLift 4456721
  have htrace : WordTrace (prefixWord ++ tailWord_4456721) baseStart_4456721 baseEnd_4456721 := by
    simpa [prefixWord, tailWord_4456721, baseEnd_4456721] using wordTrace_append hprefix tailTrace_4456721
  have hstable : (prefixWord ++ tailWord_4456721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4456721).length < 2 ^ (prefixWord ++ tailWord_4456721).sum := by decide
  have hdescent : baseEnd_4456721 < baseStart_4456721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4456721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4456728 : List Nat := [2, 1, 2, 3, 1, 2, 3, 1, 1, 5, 2]
def baseStart_4456728 : Nat := 118140960795 + 4456728 * 2 ^ 59
def prefixEnd_4456728 : Nat := 4983230072969 + 3 ^ 40 * 4456728 * 2
def baseEnd_4456728 : Nat := 2288443610351144264903887

theorem tailTrace_4456728 : CollatzResearch.WordTrace tailWord_4456728 prefixEnd_4456728 2288443610351144264903887 := by
  unfold tailWord_4456728
  simp only [CollatzResearch.WordTrace]
  refine ⟨81275112099021539694689419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108366816132028719592919225 81275112099021539694689419)
  ·
    refine ⟨121912668148532309542034129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81275112099021539694689419 121912668148532309542034129)
    ·
      refine ⟨91434501111399232156525597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121912668148532309542034129 91434501111399232156525597)
      ·
        refine ⟨34287937916774712058697099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91434501111399232156525597 34287937916774712058697099)
        ·
          refine ⟨51431906875162068088045649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34287937916774712058697099 51431906875162068088045649)
          ·
            refine ⟨38573930156371551066034237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51431906875162068088045649 38573930156371551066034237)
            ·
              refine ⟨14465223808639331649762839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38573930156371551066034237 14465223808639331649762839)
              ·
                refine ⟨21697835712958997474644259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14465223808639331649762839 21697835712958997474644259)
                ·
                  refine ⟨32546753569438496211966389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21697835712958997474644259 32546753569438496211966389)
                  ·
                    refine ⟨3051258147134859019871849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32546753569438496211966389 3051258147134859019871849)
                    ·
                      refine ⟨2288443610351144264903887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3051258147134859019871849 2288443610351144264903887)
                      ·
                        rfl

theorem cell23_4456728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 1, 5, 2].length) (baseStart_4456728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4456728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4456728 prefixEnd_4456728 := by exact prefixLift 4456728
  have htrace : WordTrace (prefixWord ++ tailWord_4456728) baseStart_4456728 baseEnd_4456728 := by
    simpa [prefixWord, tailWord_4456728, baseEnd_4456728] using wordTrace_append hprefix tailTrace_4456728
  have hstable : (prefixWord ++ tailWord_4456728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4456728).length < 2 ^ (prefixWord ++ tailWord_4456728).sum := by decide
  have hdescent : baseEnd_4456728 < baseStart_4456728 := by decide
  rcases family_descends (prefixWord ++ tailWord_4456728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4456772 : List Nat := [2, 3, 4, 1, 2, 1, 2, 2, 1, 5]
def baseStart_4456772 : Nat := 118140960795 + 4456772 * 2 ^ 59
def prefixEnd_4456772 : Nat := 4983230072969 + 3 ^ 40 * 4456772 * 2
def baseEnd_4456772 : Nat := 762822067833314030917895

theorem tailTrace_4456772 : CollatzResearch.WordTrace tailWord_4456772 prefixEnd_4456772 762822067833314030917895 := by
  unfold tailWord_4456772
  simp only [CollatzResearch.WordTrace]
  refine ⟨81275914504941837451990285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108367886006589116602653713 81275914504941837451990285)
  ·
    refine ⟨30478467939353189044496357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81275914504941837451990285 30478467939353189044496357)
    ·
      refine ⟨5714712738628722945843067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30478467939353189044496357 5714712738628722945843067)
      ·
        refine ⟨8572069107943084418764601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5714712738628722945843067 8572069107943084418764601)
        ·
          refine ⟨6429051830957313314073451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8572069107943084418764601 6429051830957313314073451)
          ·
            refine ⟨9643577746435969971110177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6429051830957313314073451 9643577746435969971110177)
            ·
              refine ⟨7232683309826977478332633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9643577746435969971110177 7232683309826977478332633)
              ·
                refine ⟨5424512482370233108749475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7232683309826977478332633 5424512482370233108749475)
                ·
                  refine ⟨8136768723555349663124213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5424512482370233108749475 8136768723555349663124213)
                  ·
                    refine ⟨762822067833314030917895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8136768723555349663124213 762822067833314030917895)
                    ·
                      rfl

theorem cell23_4456772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_4456772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4456772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4456772 prefixEnd_4456772 := by exact prefixLift 4456772
  have htrace : WordTrace (prefixWord ++ tailWord_4456772) baseStart_4456772 baseEnd_4456772 := by
    simpa [prefixWord, tailWord_4456772, baseEnd_4456772] using wordTrace_append hprefix tailTrace_4456772
  have hstable : (prefixWord ++ tailWord_4456772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4456772).length < 2 ^ (prefixWord ++ tailWord_4456772).sum := by decide
  have hdescent : baseEnd_4456772 < baseStart_4456772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4456772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4456775 : List Nat := [1, 1, 4, 1, 2, 2, 1, 4, 3, 2, 2]
def baseStart_4456775 : Nat := 118140960795 + 4456775 * 2 ^ 59
def prefixEnd_4456775 : Nat := 4983230072969 + 3 ^ 40 * 4456775 * 2
def baseEnd_4456775 : Nat := 2288467743941905581016171

theorem tailTrace_4456775 : CollatzResearch.WordTrace tailWord_4456775 prefixEnd_4456775 2288467743941905581016171 := by
  unfold tailWord_4456775
  simp only [CollatzResearch.WordTrace]
  refine ⟨162551938428872806416339779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108367958952581870944226519 162551938428872806416339779)
  ·
    refine ⟨243827907643309209624509669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162551938428872806416339779 243827907643309209624509669)
    ·
      refine ⟨45717732683120476804595563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 243827907643309209624509669 45717732683120476804595563)
      ·
        refine ⟨68576599024680715206893345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45717732683120476804595563 68576599024680715206893345)
        ·
          refine ⟨51432449268510536405170009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68576599024680715206893345 51432449268510536405170009)
          ·
            refine ⟨38574336951382902303877507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51432449268510536405170009 38574336951382902303877507)
            ·
              refine ⟨57861505427074353455816261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38574336951382902303877507 57861505427074353455816261)
              ·
                refine ⟨10849032267576441272965549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57861505427074353455816261 10849032267576441272965549)
                ·
                  refine ⟨4068387100341165477362081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10849032267576441272965549 4068387100341165477362081)
                  ·
                    refine ⟨3051290325255874108021561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4068387100341165477362081 3051290325255874108021561)
                    ·
                      refine ⟨2288467743941905581016171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3051290325255874108021561 2288467743941905581016171)
                      ·
                        rfl

theorem cell23_4456775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 3, 2, 2].length) (baseStart_4456775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4456775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4456775 prefixEnd_4456775 := by exact prefixLift 4456775
  have htrace : WordTrace (prefixWord ++ tailWord_4456775) baseStart_4456775 baseEnd_4456775 := by
    simpa [prefixWord, tailWord_4456775, baseEnd_4456775] using wordTrace_append hprefix tailTrace_4456775
  have hstable : (prefixWord ++ tailWord_4456775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4456775).length < 2 ^ (prefixWord ++ tailWord_4456775).sum := by decide
  have hdescent : baseEnd_4456775 < baseStart_4456775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4456775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4456792 : List Nat := [2, 1, 2, 2, 1, 1, 2, 7, 1, 2, 2]
def baseStart_4456792 : Nat := 118140960795 + 4456792 * 2 ^ 59
def prefixEnd_4456792 : Nat := 4983230072969 + 3 ^ 40 * 4456792 * 2
def baseEnd_4456792 : Nat := 2288476473113032014503593

theorem tailTrace_4456792 : CollatzResearch.WordTrace tailWord_4456792 prefixEnd_4456792 2288476473113032014503593 := by
  unfold tailWord_4456792
  simp only [CollatzResearch.WordTrace]
  refine ⟨81276279234905609159854315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108368372313207478879805753 81276279234905609159854315)
  ·
    refine ⟨121914418852358413739781473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81276279234905609159854315 121914418852358413739781473)
    ·
      refine ⟨91435814139268810304836105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121914418852358413739781473 91435814139268810304836105)
      ·
        refine ⟨68576860604451607728627079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91435814139268810304836105 68576860604451607728627079)
        ·
          refine ⟨102865290906677411592940619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68576860604451607728627079 102865290906677411592940619)
          ·
            refine ⟨154297936360016117389410929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102865290906677411592940619 154297936360016117389410929)
            ·
              refine ⟨115723452270012088042058197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154297936360016117389410929 115723452270012088042058197)
              ·
                refine ⟨2712268412578408313485739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 115723452270012088042058197 2712268412578408313485739)
                ·
                  refine ⟨4068402618867612470228609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2712268412578408313485739 4068402618867612470228609)
                  ·
                    refine ⟨3051301964150709352671457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4068402618867612470228609 3051301964150709352671457)
                    ·
                      refine ⟨2288476473113032014503593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3051301964150709352671457 2288476473113032014503593)
                      ·
                        rfl

theorem cell23_4456792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 7, 1, 2, 2].length) (baseStart_4456792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4456792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4456792 prefixEnd_4456792 := by exact prefixLift 4456792
  have htrace : WordTrace (prefixWord ++ tailWord_4456792) baseStart_4456792 baseEnd_4456792 := by
    simpa [prefixWord, tailWord_4456792, baseEnd_4456792] using wordTrace_append hprefix tailTrace_4456792
  have hstable : (prefixWord ++ tailWord_4456792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4456792).length < 2 ^ (prefixWord ++ tailWord_4456792).sum := by decide
  have hdescent : baseEnd_4456792 < baseStart_4456792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4456792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4456809 : List Nat := [1, 2, 1, 1, 1, 3, 7, 2, 1, 2, 2]
def baseStart_4456809 : Nat := 118140960795 + 4456809 * 2 ^ 59
def prefixEnd_4456809 : Nat := 4983230072969 + 3 ^ 40 * 4456809 * 2
def baseEnd_4456809 : Nat := 2288485202284158447991015

theorem tailTrace_4456809 : CollatzResearch.WordTrace tailWord_4456809 prefixEnd_4456809 2288485202284158447991015 := by
  unfold tailWord_4456809
  simp only [CollatzResearch.WordTrace]
  refine ⟨162553178510749630223077481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108368785673833086815384987 162553178510749630223077481)
  ·
    refine ⟨121914883883062222667308111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162553178510749630223077481 121914883883062222667308111)
    ·
      refine ⟨182872325824593334000962167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121914883883062222667308111 182872325824593334000962167)
      ·
        refine ⟨274308488736890001001443251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182872325824593334000962167 274308488736890001001443251)
        ·
          refine ⟨411462733105335001502164877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 274308488736890001001443251 411462733105335001502164877)
          ·
            refine ⟨154298524914500625563311829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 411462733105335001502164877 154298524914500625563311829)
            ·
              refine ⟨3616371677683608411640121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 154298524914500625563311829 3616371677683608411640121)
              ·
                refine ⟨2712278758262706308730091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3616371677683608411640121 2712278758262706308730091)
                ·
                  refine ⟨4068418137394059463095137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2712278758262706308730091 4068418137394059463095137)
                  ·
                    refine ⟨3051313603045544597321353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4068418137394059463095137 3051313603045544597321353)
                    ·
                      refine ⟨2288485202284158447991015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3051313603045544597321353 2288485202284158447991015)
                      ·
                        rfl

theorem cell23_4456809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 2, 1, 2, 2].length) (baseStart_4456809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4456809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4456809 prefixEnd_4456809 := by exact prefixLift 4456809
  have htrace : WordTrace (prefixWord ++ tailWord_4456809) baseStart_4456809 baseEnd_4456809 := by
    simpa [prefixWord, tailWord_4456809, baseEnd_4456809] using wordTrace_append hprefix tailTrace_4456809
  have hstable : (prefixWord ++ tailWord_4456809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4456809).length < 2 ^ (prefixWord ++ tailWord_4456809).sum := by decide
  have hdescent : baseEnd_4456809 < baseStart_4456809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4456809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4456831 : List Nat := [1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 4]
def baseStart_4456831 : Nat := 118140960795 + 4456831 * 2 ^ 59
def prefixEnd_4456831 : Nat := 4983230072969 + 3 ^ 40 * 4456831 * 2
def baseEnd_4456831 : Nat := 2288496498858557361915913

theorem tailTrace_4456831 : CollatzResearch.WordTrace tailWord_4456831 prefixEnd_4456831 2288496498858557361915913 := by
  unfold tailWord_4456831
  simp only [CollatzResearch.WordTrace]
  refine ⟨162553980916669927980378347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108369320611113285320252231 162553980916669927980378347)
  ·
    refine ⟨243830971375004891970567521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162553980916669927980378347 243830971375004891970567521)
    ·
      refine ⟨182873228531253668977925641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243830971375004891970567521 182873228531253668977925641)
      ·
        refine ⟨137154921398440251733444231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182873228531253668977925641 137154921398440251733444231)
        ·
          refine ⟨205732382097660377600166347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137154921398440251733444231 205732382097660377600166347)
          ·
            refine ⟨308598573146490566400249521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205732382097660377600166347 308598573146490566400249521)
            ·
              refine ⟨231448929859867924800187141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 308598573146490566400249521 231448929859867924800187141)
              ·
                refine ⟨43396674348725235900035089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 231448929859867924800187141 43396674348725235900035089)
                ·
                  refine ⟨32547505761543926925026317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43396674348725235900035089 32547505761543926925026317)
                  ·
                    refine ⟨12205314660578972596884869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32547505761543926925026317 12205314660578972596884869)
                    ·
                      refine ⟨2288496498858557361915913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12205314660578972596884869 2288496498858557361915913)
                      ·
                        rfl

theorem cell23_4456831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 4].length) (baseStart_4456831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4456831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4456831 prefixEnd_4456831 := by exact prefixLift 4456831
  have htrace : WordTrace (prefixWord ++ tailWord_4456831) baseStart_4456831 baseEnd_4456831 := by
    simpa [prefixWord, tailWord_4456831, baseEnd_4456831] using wordTrace_append hprefix tailTrace_4456831
  have hstable : (prefixWord ++ tailWord_4456831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4456831).length < 2 ^ (prefixWord ++ tailWord_4456831).sum := by decide
  have hdescent : baseEnd_4456831 < baseStart_4456831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4456831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4456842 : List Nat := [3, 1, 2, 5, 1, 1, 1, 2, 1, 3, 3]
def baseStart_4456842 : Nat := 118140960795 + 4456842 * 2 ^ 59
def prefixEnd_4456842 : Nat := 4983230072969 + 3 ^ 40 * 4456842 * 2
def baseEnd_4456842 : Nat := 2288502147145756818878363

theorem tailTrace_4456842 : CollatzResearch.WordTrace tailWord_4456842 prefixEnd_4456842 2288502147145756818878363 := by
  unfold tailWord_4456842
  simp only [CollatzResearch.WordTrace]
  refine ⟨40638595529907519214757195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108369588079753384572685853 40638595529907519214757195)
  ·
    refine ⟨60957893294861278822135793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40638595529907519214757195 60957893294861278822135793)
    ·
      refine ⟨45718419971145959116601845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60957893294861278822135793 45718419971145959116601845)
      ·
        refine ⟨4286101872294933667181423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45718419971145959116601845 4286101872294933667181423)
        ·
          refine ⟨6429152808442400500772135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4286101872294933667181423 6429152808442400500772135)
          ·
            refine ⟨9643729212663600751158203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6429152808442400500772135 9643729212663600751158203)
            ·
              refine ⟨14465593818995401126737305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9643729212663600751158203 14465593818995401126737305)
              ·
                refine ⟨10849195364246550845052979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14465593818995401126737305 10849195364246550845052979)
                ·
                  refine ⟨16273793046369826267579469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10849195364246550845052979 16273793046369826267579469)
                  ·
                    refine ⟨6102672392388684850342301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16273793046369826267579469 6102672392388684850342301)
                    ·
                      refine ⟨2288502147145756818878363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6102672392388684850342301 2288502147145756818878363)
                      ·
                        rfl

theorem cell23_4456842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_4456842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4456842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4456842 prefixEnd_4456842 := by exact prefixLift 4456842
  have htrace : WordTrace (prefixWord ++ tailWord_4456842) baseStart_4456842 baseEnd_4456842 := by
    simpa [prefixWord, tailWord_4456842, baseEnd_4456842] using wordTrace_append hprefix tailTrace_4456842
  have hstable : (prefixWord ++ tailWord_4456842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4456842).length < 2 ^ (prefixWord ++ tailWord_4456842).sum := by decide
  have hdescent : baseEnd_4456842 < baseStart_4456842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4456842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4456868 : List Nat := [2, 3, 1, 2, 1, 1, 3, 1, 2, 4, 3]
def baseStart_4456868 : Nat := 118140960795 + 4456868 * 2 ^ 59
def prefixEnd_4456868 : Nat := 4983230072969 + 3 ^ 40 * 4456868 * 2
def baseEnd_4456868 : Nat := 2288515497642773717153243

theorem tailTrace_4456868 : CollatzResearch.WordTrace tailWord_4456868 prefixEnd_4456868 2288515497642773717153243 := by
  unfold tailWord_4456868
  simp only [CollatzResearch.WordTrace]
  refine ⟨81277665208767941649737629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108370220278357255532983505 81277665208767941649737629)
  ·
    refine ⟨30479124453287978118651611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81277665208767941649737629 30479124453287978118651611)
    ·
      refine ⟨45718686679931967177977417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30479124453287978118651611 45718686679931967177977417)
      ·
        refine ⟨34289015009948975383483063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45718686679931967177977417 34289015009948975383483063)
        ·
          refine ⟨51433522514923463075224595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34289015009948975383483063 51433522514923463075224595)
          ·
            refine ⟨77150283772385194612836893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51433522514923463075224595 77150283772385194612836893)
            ·
              refine ⟨28931356414644447979813835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77150283772385194612836893 28931356414644447979813835)
              ·
                refine ⟨43397034621966671969720753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28931356414644447979813835 43397034621966671969720753)
                ·
                  refine ⟨32547775966475003977290565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43397034621966671969720753 32547775966475003977290565)
                  ·
                    refine ⟨6102707993714063245741981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32547775966475003977290565 6102707993714063245741981)
                    ·
                      refine ⟨2288515497642773717153243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6102707993714063245741981 2288515497642773717153243)
                      ·
                        rfl

theorem cell23_4456868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_4456868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4456868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4456868 prefixEnd_4456868 := by exact prefixLift 4456868
  have htrace : WordTrace (prefixWord ++ tailWord_4456868) baseStart_4456868 baseEnd_4456868 := by
    simpa [prefixWord, tailWord_4456868, baseEnd_4456868] using wordTrace_append hprefix tailTrace_4456868
  have hstable : (prefixWord ++ tailWord_4456868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4456868).length < 2 ^ (prefixWord ++ tailWord_4456868).sum := by decide
  have hdescent : baseEnd_4456868 < baseStart_4456868 := by decide
  rcases family_descends (prefixWord ++ tailWord_4456868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4456882 : List Nat := [3, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2]
def baseStart_4456882 : Nat := 118140960795 + 4456882 * 2 ^ 59
def prefixEnd_4456882 : Nat := 4983230072969 + 3 ^ 40 * 4456882 * 2
def baseEnd_4456882 : Nat := 2288522686371936662378179

theorem tailTrace_4456882 : CollatzResearch.WordTrace tailWord_4456882 prefixEnd_4456882 2288522686371936662378179 := by
  unfold tailWord_4456882
  simp only [CollatzResearch.WordTrace]
  refine ⟨40638960259871290922621225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108370560692990109126989933 40638960259871290922621225)
  ·
    refine ⟨30479220194903468191965919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40638960259871290922621225 30479220194903468191965919)
    ·
      refine ⟨45718830292355202287948879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30479220194903468191965919 45718830292355202287948879)
      ·
        refine ⟨68578245438532803431923319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45718830292355202287948879 68578245438532803431923319)
        ·
          refine ⟨102867368157799205147884979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68578245438532803431923319 102867368157799205147884979)
          ·
            refine ⟨154301052236698807721827469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102867368157799205147884979 154301052236698807721827469)
            ·
              refine ⟨57862894588762052895685301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 154301052236698807721827469 57862894588762052895685301)
              ·
                refine ⟨5424646367696442458970497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57862894588762052895685301 5424646367696442458970497)
                ·
                  refine ⟨4068484775772331844227873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5424646367696442458970497 4068484775772331844227873)
                  ·
                    refine ⟨3051363581829248883170905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4068484775772331844227873 3051363581829248883170905)
                    ·
                      refine ⟨2288522686371936662378179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3051363581829248883170905 2288522686371936662378179)
                      ·
                        rfl

theorem cell23_4456882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2].length) (baseStart_4456882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4456882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4456882 prefixEnd_4456882 := by exact prefixLift 4456882
  have htrace : WordTrace (prefixWord ++ tailWord_4456882) baseStart_4456882 baseEnd_4456882 := by
    simpa [prefixWord, tailWord_4456882, baseEnd_4456882] using wordTrace_append hprefix tailTrace_4456882
  have hstable : (prefixWord ++ tailWord_4456882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4456882).length < 2 ^ (prefixWord ++ tailWord_4456882).sum := by decide
  have hdescent : baseEnd_4456882 < baseStart_4456882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4456882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4456916 : List Nat := [2, 4, 1, 2, 2, 3, 1, 2, 2, 2, 2]
def baseStart_4456916 : Nat := 118140960795 + 4456916 * 2 ^ 59
def prefixEnd_4456916 : Nat := 4983230072969 + 3 ^ 40 * 4456916 * 2
def baseEnd_4456916 : Nat := 2288540144714189529353023

theorem tailTrace_4456916 : CollatzResearch.WordTrace tailWord_4456916 prefixEnd_4456916 2288540144714189529353023 := by
  unfold tailWord_4456916
  simp only [CollatzResearch.WordTrace]
  refine ⟨81278540560680993748611301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108371387414241324998148401 81278540560680993748611301)
  ·
    refine ⟨15239726355127686327864619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81278540560680993748611301 15239726355127686327864619)
    ·
      refine ⟨22859589532691529491796929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15239726355127686327864619 22859589532691529491796929)
      ·
        refine ⟨17144692149518647118847697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22859589532691529491796929 17144692149518647118847697)
        ·
          refine ⟨12858519112138985339135773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17144692149518647118847697 12858519112138985339135773)
          ·
            refine ⟨4821944667052119502175915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12858519112138985339135773 4821944667052119502175915)
            ·
              refine ⟨7232917000578179253263873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4821944667052119502175915 7232917000578179253263873)
              ·
                refine ⟨5424687750433634439947905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7232917000578179253263873 5424687750433634439947905)
                ·
                  refine ⟨4068515812825225829960929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5424687750433634439947905 4068515812825225829960929)
                  ·
                    refine ⟨3051386859618919372470697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4068515812825225829960929 3051386859618919372470697)
                    ·
                      refine ⟨2288540144714189529353023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3051386859618919372470697 2288540144714189529353023)
                      ·
                        rfl

theorem cell23_4456916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_4456916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4456916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4456916 prefixEnd_4456916 := by exact prefixLift 4456916
  have htrace : WordTrace (prefixWord ++ tailWord_4456916) baseStart_4456916 baseEnd_4456916 := by
    simpa [prefixWord, tailWord_4456916, baseEnd_4456916] using wordTrace_append hprefix tailTrace_4456916
  have hstable : (prefixWord ++ tailWord_4456916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4456916).length < 2 ^ (prefixWord ++ tailWord_4456916).sum := by decide
  have hdescent : baseEnd_4456916 < baseStart_4456916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4456916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4456995 : List Nat := [1, 1, 1, 4, 4, 2, 1, 3, 6]
def baseStart_4456995 : Nat := 118140960795 + 4456995 * 2 ^ 59
def prefixEnd_4456995 : Nat := 4983230072969 + 3 ^ 40 * 4456995 * 2
def baseEnd_4456995 : Nat := 254286745520654968918351

theorem tailTrace_4456995 : CollatzResearch.WordTrace tailWord_4456995 prefixEnd_4456995 254286745520654968918351 := by
  unfold tailWord_4456995
  simp only [CollatzResearch.WordTrace]
  refine ⟨162559962488075783989348439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108373308325383855992898959 162559962488075783989348439)
  ·
    refine ⟨243839943732113675984022659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162559962488075783989348439 243839943732113675984022659)
    ·
      refine ⟨365759915598170513976033989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243839943732113675984022659 365759915598170513976033989)
      ·
        refine ⟨68579984174656971370506373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 365759915598170513976033989 68579984174656971370506373)
        ·
          refine ⟨12858747032748182131969945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68579984174656971370506373 12858747032748182131969945)
          ·
            refine ⟨9644060274561136598977459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12858747032748182131969945 9644060274561136598977459)
            ·
              refine ⟨14466090411841704898466189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9644060274561136598977459 14466090411841704898466189)
              ·
                refine ⟨5424783904440639336924821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14466090411841704898466189 5424783904440639336924821)
                ·
                  refine ⟨254286745520654968918351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5424783904440639336924821 254286745520654968918351)
                  ·
                    rfl

theorem cell23_4456995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 3, 6].length) (baseStart_4456995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4456995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4456995 prefixEnd_4456995 := by exact prefixLift 4456995
  have htrace : WordTrace (prefixWord ++ tailWord_4456995) baseStart_4456995 baseEnd_4456995 := by
    simpa [prefixWord, tailWord_4456995, baseEnd_4456995] using wordTrace_append hprefix tailTrace_4456995
  have hstable : (prefixWord ++ tailWord_4456995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4456995).length < 2 ^ (prefixWord ++ tailWord_4456995).sum := by decide
  have hdescent : baseEnd_4456995 < baseStart_4456995 := by decide
  rcases family_descends (prefixWord ++ tailWord_4456995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4457045 : List Nat := [1, 3, 2, 2, 1, 1, 3, 2, 3, 1, 4]
def baseStart_4457045 : Nat := 118140960795 + 4457045 * 2 ^ 59
def prefixEnd_4457045 : Nat := 4983230072969 + 3 ^ 40 * 4457045 * 2
def baseEnd_4457045 : Nat := 2288606383718619524639929

theorem tailTrace_4457045 : CollatzResearch.WordTrace tailWord_4457045 prefixEnd_4457045 2288606383718619524639929 := by
  unfold tailWord_4457045
  simp only [CollatzResearch.WordTrace]
  refine ⟨162561786137894642528668589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108374524091929761685779059 162561786137894642528668589)
  ·
    refine ⟨60960669801710490948250721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162561786137894642528668589 60960669801710490948250721)
    ·
      refine ⟨45720502351282868211188041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60960669801710490948250721 45720502351282868211188041)
      ·
        refine ⟨34290376763462151158391031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45720502351282868211188041 34290376763462151158391031)
        ·
          refine ⟨51435565145193226737586547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34290376763462151158391031 51435565145193226737586547)
          ·
            refine ⟨77153347717789840106379821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51435565145193226737586547 77153347717789840106379821)
            ·
              refine ⟨28932505394171190039892433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77153347717789840106379821 28932505394171190039892433)
              ·
                refine ⟨21699379045628392529919325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28932505394171190039892433 21699379045628392529919325)
                ·
                  refine ⟨8137267142110647198719747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21699379045628392529919325 8137267142110647198719747)
                  ·
                    refine ⟨12205900713165970798079621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8137267142110647198719747 12205900713165970798079621)
                    ·
                      refine ⟨2288606383718619524639929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12205900713165970798079621 2288606383718619524639929)
                      ·
                        rfl

theorem cell23_4457045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_4457045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4457045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4457045 prefixEnd_4457045 := by exact prefixLift 4457045
  have htrace : WordTrace (prefixWord ++ tailWord_4457045) baseStart_4457045 baseEnd_4457045 := by
    simpa [prefixWord, tailWord_4457045, baseEnd_4457045] using wordTrace_append hprefix tailTrace_4457045
  have hstable : (prefixWord ++ tailWord_4457045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4457045).length < 2 ^ (prefixWord ++ tailWord_4457045).sum := by decide
  have hdescent : baseEnd_4457045 < baseStart_4457045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4457045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4457068 : List Nat := [2, 2, 1, 1, 3, 1, 2, 11]
def baseStart_4457068 : Nat := 118140960795 + 4457068 * 2 ^ 59
def prefixEnd_4457068 : Nat := 4983230072969 + 3 ^ 40 * 4457068 * 2
def baseEnd_4457068 : Nat := 84763636806432330913049

theorem tailTrace_4457068 : CollatzResearch.WordTrace tailWord_4457068 prefixEnd_4457068 84763636806432330913049 := by
  unfold tailWord_4457068
  simp only [CollatzResearch.WordTrace]
  refine ⟨81281312508405658728377929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108375083344540878304503905 81281312508405658728377929)
  ·
    refine ⟨60960984381304244046283447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81281312508405658728377929 60960984381304244046283447)
    ·
      refine ⟨91441476571956366069425171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60960984381304244046283447 91441476571956366069425171)
      ·
        refine ⟨137162214857934549104137757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91441476571956366069425171 137162214857934549104137757)
        ·
          refine ⟨51435830571725455914051659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137162214857934549104137757 51435830571725455914051659)
          ·
            refine ⟨77153745857588183871077489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51435830571725455914051659 77153745857588183871077489)
            ·
              refine ⟨57865309393191137903308117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77153745857588183871077489 57865309393191137903308117)
              ·
                refine ⟨84763636806432330913049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 57865309393191137903308117 84763636806432330913049)
                ·
                  rfl

theorem cell23_4457068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 11].length) (baseStart_4457068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4457068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4457068 prefixEnd_4457068 := by exact prefixLift 4457068
  have htrace : WordTrace (prefixWord ++ tailWord_4457068) baseStart_4457068 baseEnd_4457068 := by
    simpa [prefixWord, tailWord_4457068, baseEnd_4457068] using wordTrace_append hprefix tailTrace_4457068
  have hstable : (prefixWord ++ tailWord_4457068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4457068).length < 2 ^ (prefixWord ++ tailWord_4457068).sum := by decide
  have hdescent : baseEnd_4457068 < baseStart_4457068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4457068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4457085 : List Nat := [1, 4, 1, 1, 5, 1, 10]
def baseStart_4457085 : Nat := 118140960795 + 4457085 * 2 ^ 59
def prefixEnd_4457085 : Nat := 4983230072969 + 3 ^ 40 * 4457085 * 2
def baseEnd_4457085 : Nat := 28254653369688881088145

theorem tailTrace_4457085 : CollatzResearch.WordTrace tailWord_4457085 prefixEnd_4457085 28254653369688881088145 := by
  unfold tailWord_4457085
  simp only [CollatzResearch.WordTrace]
  refine ⟨162563245057749729360124709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108375496705166486240083139 162563245057749729360124709)
  ·
    refine ⟨30480608448328074255023383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 162563245057749729360124709 30480608448328074255023383)
    ·
      refine ⟨45720912672492111382535075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30480608448328074255023383 45720912672492111382535075)
      ·
        refine ⟨68581369008738167073802613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45720912672492111382535075 68581369008738167073802613)
        ·
          refine ⟨6429503344569203163168995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68581369008738167073802613 6429503344569203163168995)
          ·
            refine ⟨9644255016853804744753493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6429503344569203163168995 9644255016853804744753493)
            ·
              refine ⟨28254653369688881088145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9644255016853804744753493 28254653369688881088145)
              ·
                rfl

theorem cell23_4457085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 10].length) (baseStart_4457085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4457085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4457085 prefixEnd_4457085 := by exact prefixLift 4457085
  have htrace : WordTrace (prefixWord ++ tailWord_4457085) baseStart_4457085 baseEnd_4457085 := by
    simpa [prefixWord, tailWord_4457085, baseEnd_4457085] using wordTrace_append hprefix tailTrace_4457085
  have hstable : (prefixWord ++ tailWord_4457085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4457085).length < 2 ^ (prefixWord ++ tailWord_4457085).sum := by decide
  have hdescent : baseEnd_4457085 < baseStart_4457085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4457085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4457090 : List Nat := [3, 4, 3, 1, 1, 1, 2, 1, 3, 1, 3]
def baseStart_4457090 : Nat := 118140960795 + 4457090 * 2 ^ 59
def prefixEnd_4457090 : Nat := 4983230072969 + 3 ^ 40 * 4457090 * 2
def baseEnd_4457090 : Nat := 2288629490348071848577223

theorem tailTrace_4457090 : CollatzResearch.WordTrace tailWord_4457090 prefixEnd_4457090 2288629490348071848577223 := by
  unfold tailWord_4457090
  simp only [CollatzResearch.WordTrace]
  refine ⟨40640856855682903803514181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108375618281821076809371149 40640856855682903803514181)
  ·
    refine ⟨7620160660440544463158909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40640856855682903803514181 7620160660440544463158909)
    ·
      refine ⟨2857560247665204173684591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7620160660440544463158909 2857560247665204173684591)
      ·
        refine ⟨4286340371497806260526887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2857560247665204173684591 4286340371497806260526887)
        ·
          refine ⟨6429510557246709390790331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4286340371497806260526887 6429510557246709390790331)
          ·
            refine ⟨9644265835870064086185497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6429510557246709390790331 9644265835870064086185497)
            ·
              refine ⟨7233199376902548064639123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9644265835870064086185497 7233199376902548064639123)
              ·
                refine ⟨10849799065353822096958685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7233199376902548064639123 10849799065353822096958685)
                ·
                  refine ⟨4068674649507683286359507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10849799065353822096958685 4068674649507683286359507)
                  ·
                    refine ⟨6103011974261524929539261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4068674649507683286359507 6103011974261524929539261)
                    ·
                      refine ⟨2288629490348071848577223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6103011974261524929539261 2288629490348071848577223)
                      ·
                        rfl

theorem cell23_4457090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_4457090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4457090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4457090 prefixEnd_4457090 := by exact prefixLift 4457090
  have htrace : WordTrace (prefixWord ++ tailWord_4457090) baseStart_4457090 baseEnd_4457090 := by
    simpa [prefixWord, tailWord_4457090, baseEnd_4457090] using wordTrace_append hprefix tailTrace_4457090
  have hstable : (prefixWord ++ tailWord_4457090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4457090).length < 2 ^ (prefixWord ++ tailWord_4457090).sum := by decide
  have hdescent : baseEnd_4457090 < baseStart_4457090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4457090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4457106 : List Nat := [3, 2, 3, 1, 2, 2, 3, 1, 2, 4]
def baseStart_4457106 : Nat := 118140960795 + 4457106 * 2 ^ 59
def prefixEnd_4457106 : Nat := 4983230072969 + 3 ^ 40 * 4457106 * 2
def baseEnd_4457106 : Nat := 762879235346181261992383

theorem tailTrace_4457106 : CollatzResearch.WordTrace tailWord_4457106 prefixEnd_4457106 762879235346181261992383 := by
  unfold tailWord_4457106
  simp only [CollatzResearch.WordTrace]
  refine ⟨40641002747668412486659793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108376007327115766631092781 40641002747668412486659793)
  ·
    refine ⟨30480752060751309364994845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40641002747668412486659793 30480752060751309364994845)
    ·
      refine ⟨11430282022781741011873067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30480752060751309364994845 11430282022781741011873067)
      ·
        refine ⟨17145423034172611517809601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11430282022781741011873067 17145423034172611517809601)
        ·
          refine ⟨12859067275629458638357201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17145423034172611517809601 12859067275629458638357201)
          ·
            refine ⟨9644300456722093978767901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12859067275629458638357201 9644300456722093978767901)
            ·
              refine ⟨3616612671270785242037963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9644300456722093978767901 3616612671270785242037963)
              ·
                refine ⟨5424919006906177863056945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3616612671270785242037963 5424919006906177863056945)
                ·
                  refine ⟨4068689255179633397292709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5424919006906177863056945 4068689255179633397292709)
                  ·
                    refine ⟨762879235346181261992383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4068689255179633397292709 762879235346181261992383)
                    ·
                      rfl

theorem cell23_4457106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_4457106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4457106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4457106 prefixEnd_4457106 := by exact prefixLift 4457106
  have htrace : WordTrace (prefixWord ++ tailWord_4457106) baseStart_4457106 baseEnd_4457106 := by
    simpa [prefixWord, tailWord_4457106, baseEnd_4457106] using wordTrace_append hprefix tailTrace_4457106
  have hstable : (prefixWord ++ tailWord_4457106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4457106).length < 2 ^ (prefixWord ++ tailWord_4457106).sum := by decide
  have hdescent : baseEnd_4457106 < baseStart_4457106 := by decide
  rcases family_descends (prefixWord ++ tailWord_4457106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4457139 : List Nat := [1, 1, 1, 2, 3, 4, 2, 3, 1, 3, 2]
def baseStart_4457139 : Nat := 118140960795 + 4457139 * 2 ^ 59
def prefixEnd_4457139 : Nat := 4983230072969 + 3 ^ 40 * 4457139 * 2
def baseEnd_4457139 : Nat := 2288654650900142156864497

theorem tailTrace_4457139 : CollatzResearch.WordTrace tailWord_4457139 prefixEnd_4457139 2288654650900142156864497 := by
  unfold tailWord_4457139
  simp only [CollatzResearch.WordTrace]
  refine ⟨162565214599554096582590471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108376809733036064388393647 162565214599554096582590471)
  ·
    refine ⟨243847821899331144873885707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162565214599554096582590471 243847821899331144873885707)
    ·
      refine ⟨365771732848996717310828561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243847821899331144873885707 365771732848996717310828561)
      ·
        refine ⟨274328799636747537983121421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 365771732848996717310828561 274328799636747537983121421)
        ·
          refine ⟨102873299863780326743670533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 274328799636747537983121421 102873299863780326743670533)
          ·
            refine ⟨19288743724458811264438225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102873299863780326743670533 19288743724458811264438225)
            ·
              refine ⟨14466557793344108448328669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19288743724458811264438225 14466557793344108448328669)
              ·
                refine ⟨5424959172504040668123251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14466557793344108448328669 5424959172504040668123251)
                ·
                  refine ⟨8137438758756061002184877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5424959172504040668123251 8137438758756061002184877)
                  ·
                    refine ⟨3051539534533522875819329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8137438758756061002184877 3051539534533522875819329)
                    ·
                      refine ⟨2288654650900142156864497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3051539534533522875819329 2288654650900142156864497)
                      ·
                        rfl

theorem cell23_4457139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 3, 1, 3, 2].length) (baseStart_4457139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4457139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4457139 prefixEnd_4457139 := by exact prefixLift 4457139
  have htrace : WordTrace (prefixWord ++ tailWord_4457139) baseStart_4457139 baseEnd_4457139 := by
    simpa [prefixWord, tailWord_4457139, baseEnd_4457139] using wordTrace_append hprefix tailTrace_4457139
  have hstable : (prefixWord ++ tailWord_4457139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4457139).length < 2 ^ (prefixWord ++ tailWord_4457139).sum := by decide
  have hdescent : baseEnd_4457139 < baseStart_4457139 := by decide
  rcases family_descends (prefixWord ++ tailWord_4457139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4457242 : List Nat := [3, 1, 1, 3, 2, 1, 3, 1, 1, 3, 4]
def baseStart_4457242 : Nat := 118140960795 + 4457242 * 2 ^ 59
def prefixEnd_4457242 : Nat := 4983230072969 + 3 ^ 40 * 4457242 * 2
def baseEnd_4457242 : Nat := 2288707539407555253876523

theorem tailTrace_4457242 : CollatzResearch.WordTrace tailWord_4457242 prefixEnd_4457242 2288707539407555253876523 := by
  unfold tailWord_4457242
  simp only [CollatzResearch.WordTrace]
  refine ⟨40642242829545236293397495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108379314212120630115726653 40642242829545236293397495)
  ·
    refine ⟨60963364244317854440096243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40642242829545236293397495 60963364244317854440096243)
    ·
      refine ⟨91445046366476781660144365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60963364244317854440096243 91445046366476781660144365)
      ·
        refine ⟨34291892387428793122554137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91445046366476781660144365 34291892387428793122554137)
        ·
          refine ⟨25718919290571594841915603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34291892387428793122554137 25718919290571594841915603)
          ·
            refine ⟨38578378935857392262873405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25718919290571594841915603 38578378935857392262873405)
            ·
              refine ⟨14466892100946522098577527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38578378935857392262873405 14466892100946522098577527)
              ·
                refine ⟨21700338151419783147866291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14466892100946522098577527 21700338151419783147866291)
                ·
                  refine ⟨32550507227129674721799437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21700338151419783147866291 32550507227129674721799437)
                  ·
                    refine ⟨12206440210173628020674789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32550507227129674721799437 12206440210173628020674789)
                    ·
                      refine ⟨2288707539407555253876523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12206440210173628020674789 2288707539407555253876523)
                      ·
                        rfl

theorem cell23_4457242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_4457242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4457242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4457242 prefixEnd_4457242 := by exact prefixLift 4457242
  have htrace : WordTrace (prefixWord ++ tailWord_4457242) baseStart_4457242 baseEnd_4457242 := by
    simpa [prefixWord, tailWord_4457242, baseEnd_4457242] using wordTrace_append hprefix tailTrace_4457242
  have hstable : (prefixWord ++ tailWord_4457242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4457242).length < 2 ^ (prefixWord ++ tailWord_4457242).sum := by decide
  have hdescent : baseEnd_4457242 < baseStart_4457242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4457242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4457269 : List Nat := [1, 3, 3, 1, 3, 1, 1, 3, 3, 4]
def baseStart_4457269 : Nat := 118140960795 + 4457269 * 2 ^ 59
def prefixEnd_4457269 : Nat := 4983230072969 + 3 ^ 40 * 4457269 * 2
def baseEnd_4457269 : Nat := 762907134461742216079633

theorem tailTrace_4457269 : CollatzResearch.WordTrace tailWord_4457269 prefixEnd_4457269 762907134461742216079633 := by
  unfold tailWord_4457269
  simp only [CollatzResearch.WordTrace]
  refine ⟨162569956089083128784822861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108379970726055419189881907 162569956089083128784822861)
  ·
    refine ⟨60963733533406173294308573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162569956089083128784822861 60963733533406173294308573)
    ·
      refine ⟨22861400075027314985365715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60963733533406173294308573 22861400075027314985365715)
      ·
        refine ⟨34292100112540972478048573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22861400075027314985365715 34292100112540972478048573)
        ·
          refine ⟨12859537542202864679268215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34292100112540972478048573 12859537542202864679268215)
          ·
            refine ⟨19289306313304297018902323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12859537542202864679268215 19289306313304297018902323)
            ·
              refine ⟨28933959469956445528353485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19289306313304297018902323 28933959469956445528353485)
              ·
                refine ⟨10850234801233667073132557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28933959469956445528353485 10850234801233667073132557)
                ·
                  refine ⟨4068838050462625152424709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10850234801233667073132557 4068838050462625152424709)
                  ·
                    refine ⟨762907134461742216079633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4068838050462625152424709 762907134461742216079633)
                    ·
                      rfl

theorem cell23_4457269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_4457269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4457269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4457269 prefixEnd_4457269 := by exact prefixLift 4457269
  have htrace : WordTrace (prefixWord ++ tailWord_4457269) baseStart_4457269 baseEnd_4457269 := by
    simpa [prefixWord, tailWord_4457269, baseEnd_4457269] using wordTrace_append hprefix tailTrace_4457269
  have hstable : (prefixWord ++ tailWord_4457269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4457269).length < 2 ^ (prefixWord ++ tailWord_4457269).sum := by decide
  have hdescent : baseEnd_4457269 < baseStart_4457269 := by decide
  rcases family_descends (prefixWord ++ tailWord_4457269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4457295 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 4, 9]
def baseStart_4457295 : Nat := 118140960795 + 4457295 * 2 ^ 59
def prefixEnd_4457295 : Nat := 4983230072969 + 3 ^ 40 * 4457295 * 2
def baseEnd_4457295 : Nat := 762911584627414515504593

theorem tailTrace_4457295 : CollatzResearch.WordTrace tailWord_4457295 prefixEnd_4457295 762911584627414515504593 := by
  unfold tailWord_4457295
  simp only [CollatzResearch.WordTrace]
  refine ⟨162570904386988935225269339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108380602924659290150179559 162570904386988935225269339)
  ·
    refine ⟨243856356580483402837904009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162570904386988935225269339 243856356580483402837904009)
    ·
      refine ⟨182892267435362552128428007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243856356580483402837904009 182892267435362552128428007)
      ·
        refine ⟨274338401153043828192642011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182892267435362552128428007 274338401153043828192642011)
        ·
          refine ⟨411507601729565742288963017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 274338401153043828192642011 411507601729565742288963017)
          ·
            refine ⟨308630701297174306716722263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 411507601729565742288963017 308630701297174306716722263)
            ·
              refine ⟨462946051945761460075083395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 308630701297174306716722263 462946051945761460075083395)
              ·
                refine ⟨694419077918642190112625093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 462946051945761460075083395 694419077918642190112625093)
                ·
                  refine ⟨130203577109745410646117205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 694419077918642190112625093 130203577109745410646117205)
                  ·
                    refine ⟨762911584627414515504593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 130203577109745410646117205 762911584627414515504593)
                    ·
                      rfl

theorem cell23_4457295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 9].length) (baseStart_4457295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4457295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4457295 prefixEnd_4457295 := by exact prefixLift 4457295
  have htrace : WordTrace (prefixWord ++ tailWord_4457295) baseStart_4457295 baseEnd_4457295 := by
    simpa [prefixWord, tailWord_4457295, baseEnd_4457295] using wordTrace_append hprefix tailTrace_4457295
  have hstable : (prefixWord ++ tailWord_4457295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4457295).length < 2 ^ (prefixWord ++ tailWord_4457295).sum := by decide
  have hdescent : baseEnd_4457295 < baseStart_4457295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4457295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4457303 : List Nat := [1, 1, 3, 2, 4, 3, 1, 3, 1, 4]
def baseStart_4457303 : Nat := 118140960795 + 4457303 * 2 ^ 59
def prefixEnd_4457303 : Nat := 4983230072969 + 3 ^ 40 * 4457303 * 2
def baseEnd_4457303 : Nat := 762912953909159838404581

theorem tailTrace_4457303 : CollatzResearch.WordTrace tailWord_4457303 prefixEnd_4457303 762912953909159838404581 := by
  unfold tailWord_4457303
  simp only [CollatzResearch.WordTrace]
  refine ⟨162571196170959952591560563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108380797447306635061040375 162571196170959952591560563)
  ·
    refine ⟨243856794256439928887340845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162571196170959952591560563 243856794256439928887340845)
    ·
      refine ⟨91446297846164973332752817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 243856794256439928887340845 91446297846164973332752817)
      ·
        refine ⟨68584723384623729999564613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91446297846164973332752817 68584723384623729999564613)
        ·
          refine ⟨12859635634616949374918365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68584723384623729999564613 12859635634616949374918365)
          ·
            refine ⟨4822363362981356015594387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12859635634616949374918365 4822363362981356015594387)
            ·
              refine ⟨7233545044472034023391581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4822363362981356015594387 7233545044472034023391581)
              ·
                refine ⟨2712579391677012758771843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7233545044472034023391581 2712579391677012758771843)
                ·
                  refine ⟨4068869087515519138157765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2712579391677012758771843 4068869087515519138157765)
                  ·
                    refine ⟨762912953909159838404581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4068869087515519138157765 762912953909159838404581)
                    ·
                      rfl

theorem cell23_4457303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 3, 1, 4].length) (baseStart_4457303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4457303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4457303 prefixEnd_4457303 := by exact prefixLift 4457303
  have htrace : WordTrace (prefixWord ++ tailWord_4457303) baseStart_4457303 baseEnd_4457303 := by
    simpa [prefixWord, tailWord_4457303, baseEnd_4457303] using wordTrace_append hprefix tailTrace_4457303
  have hstable : (prefixWord ++ tailWord_4457303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4457303).length < 2 ^ (prefixWord ++ tailWord_4457303).sum := by decide
  have hdescent : baseEnd_4457303 < baseStart_4457303 := by decide
  rcases family_descends (prefixWord ++ tailWord_4457303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4457349 : List Nat := [1, 3, 1, 1, 3, 4, 1, 1, 3, 1, 4]
def baseStart_4457349 : Nat := 118140960795 + 4457349 * 2 ^ 59
def prefixEnd_4457349 : Nat := 4983230072969 + 3 ^ 40 * 4457349 * 2
def baseEnd_4457349 : Nat := 2288762481837586335238531

theorem tailTrace_4457349 : CollatzResearch.WordTrace tailWord_4457349 prefixEnd_4457349 2288762481837586335238531 := by
  unfold tailWord_4457349
  simp only [CollatzResearch.WordTrace]
  refine ⟨162572873928793302447735101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108381915952528868298490067 162572873928793302447735101)
  ·
    refine ⟨60964827723297488417900663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162572873928793302447735101 60964827723297488417900663)
    ·
      refine ⟨91447241584946232626850995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60964827723297488417900663 91447241584946232626850995)
      ·
        refine ⟨137170862377419348940276493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91447241584946232626850995 137170862377419348940276493)
        ·
          refine ⟨51439073391532255852603685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137170862377419348940276493 51439073391532255852603685)
          ·
            refine ⟨9644826260912297972363191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51439073391532255852603685 9644826260912297972363191)
            ·
              refine ⟨14467239391368446958544787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9644826260912297972363191 14467239391368446958544787)
              ·
                refine ⟨21700859087052670437817181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14467239391368446958544787 21700859087052670437817181)
                ·
                  refine ⟨8137822157644751414181443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21700859087052670437817181 8137822157644751414181443)
                  ·
                    refine ⟨12206733236467127121272165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8137822157644751414181443 12206733236467127121272165)
                    ·
                      refine ⟨2288762481837586335238531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12206733236467127121272165 2288762481837586335238531)
                      ·
                        rfl

theorem cell23_4457349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 3, 1, 4].length) (baseStart_4457349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4457349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4457349 prefixEnd_4457349 := by exact prefixLift 4457349
  have htrace : WordTrace (prefixWord ++ tailWord_4457349) baseStart_4457349 baseEnd_4457349 := by
    simpa [prefixWord, tailWord_4457349, baseEnd_4457349] using wordTrace_append hprefix tailTrace_4457349
  have hstable : (prefixWord ++ tailWord_4457349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4457349).length < 2 ^ (prefixWord ++ tailWord_4457349).sum := by decide
  have hdescent : baseEnd_4457349 < baseStart_4457349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4457349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4457372 : List Nat := [2, 2, 3, 3, 13]
def baseStart_4457372 : Nat := 118140960795 + 4457372 * 2 ^ 59
def prefixEnd_4457372 : Nat := 4983230072969 + 3 ^ 40 * 4457372 * 2
def baseEnd_4457372 : Nat := 3139608082157256166325

theorem tailTrace_4457372 : CollatzResearch.WordTrace tailWord_4457372 prefixEnd_4457372 3139608082157256166325 := by
  unfold tailWord_4457372
  simp only [CollatzResearch.WordTrace]
  refine ⟨81286856403854988687911185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108382475205139984917214913 81286856403854988687911185)
  ·
    refine ⟨60965142302891241515933389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81286856403854988687911185 60965142302891241515933389)
    ·
      refine ⟨22861928363584215568475021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60965142302891241515933389 22861928363584215568475021)
      ·
        refine ⟨8573223136344080838178133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22861928363584215568475021 8573223136344080838178133)
        ·
          refine ⟨3139608082157256166325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 8573223136344080838178133 3139608082157256166325)
          ·
            rfl

theorem cell23_4457372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 13].length) (baseStart_4457372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4457372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4457372 prefixEnd_4457372 := by exact prefixLift 4457372
  have htrace : WordTrace (prefixWord ++ tailWord_4457372) baseStart_4457372 baseEnd_4457372 := by
    simpa [prefixWord, tailWord_4457372, baseEnd_4457372] using wordTrace_append hprefix tailTrace_4457372
  have hstable : (prefixWord ++ tailWord_4457372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4457372).length < 2 ^ (prefixWord ++ tailWord_4457372).sum := by decide
  have hdescent : baseEnd_4457372 < baseStart_4457372 := by decide
  rcases family_descends (prefixWord ++ tailWord_4457372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4457377 : List Nat := [1, 2, 3, 4, 1, 3, 2, 2, 1, 1, 3]
def baseStart_4457377 : Nat := 118140960795 + 4457377 * 2 ^ 59
def prefixEnd_4457377 : Nat := 4983230072969 + 3 ^ 40 * 4457377 * 2
def baseEnd_4457377 : Nat := 2288776859295912225688403

theorem tailTrace_4457377 : CollatzResearch.WordTrace tailWord_4457377 prefixEnd_4457377 2288776859295912225688403 := by
  unfold tailWord_4457377
  simp only [CollatzResearch.WordTrace]
  refine ⟨162573895172691863229754385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108382596781794575486502923 162573895172691863229754385)
  ·
    refine ⟨121930421379518897422315789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162573895172691863229754385 121930421379518897422315789)
    ·
      refine ⟨45723908017319586533368421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121930421379518897422315789 45723908017319586533368421)
      ·
        refine ⟨8573232753247422475006579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45723908017319586533368421 8573232753247422475006579)
        ·
          refine ⟨12859849129871133712509869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8573232753247422475006579 12859849129871133712509869)
          ·
            refine ⟨4822443423701675142191201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12859849129871133712509869 4822443423701675142191201)
            ·
              refine ⟨3616832567776256356643401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4822443423701675142191201 3616832567776256356643401)
              ·
                refine ⟨2712624425832192267482551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3616832567776256356643401 2712624425832192267482551)
                ·
                  refine ⟨4068936638748288401223827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2712624425832192267482551 4068936638748288401223827)
                  ·
                    refine ⟨6103404958122432601835741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4068936638748288401223827 6103404958122432601835741)
                    ·
                      refine ⟨2288776859295912225688403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6103404958122432601835741 2288776859295912225688403)
                      ·
                        rfl

theorem cell23_4457377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_4457377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4457377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4457377 prefixEnd_4457377 := by exact prefixLift 4457377
  have htrace : WordTrace (prefixWord ++ tailWord_4457377) baseStart_4457377 baseEnd_4457377 := by
    simpa [prefixWord, tailWord_4457377, baseEnd_4457377] using wordTrace_append hprefix tailTrace_4457377
  have hstable : (prefixWord ++ tailWord_4457377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4457377).length < 2 ^ (prefixWord ++ tailWord_4457377).sum := by decide
  have hdescent : baseEnd_4457377 < baseStart_4457377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4457377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4457399 : List Nat := [1, 1, 3, 1, 3, 1, 3, 3, 1, 3, 3]
def baseStart_4457399 : Nat := 118140960795 + 4457399 * 2 ^ 59
def prefixEnd_4457399 : Nat := 4983230072969 + 3 ^ 40 * 4457399 * 2
def baseEnd_4457399 : Nat := 2288788155870311139613301

theorem tailTrace_4457399 : CollatzResearch.WordTrace tailWord_4457399 prefixEnd_4457399 2288788155870311139613301 := by
  unfold tailWord_4457399
  simp only [CollatzResearch.WordTrace]
  refine ⟨162574697578612160987055251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108383131719074773991370167 162574697578612160987055251)
  ·
    refine ⟨243862046367918241480582877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162574697578612160987055251 243862046367918241480582877)
    ·
      refine ⟨91448267387969340555218579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 243862046367918241480582877 91448267387969340555218579)
      ·
        refine ⟨137172401081954010832827869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91448267387969340555218579 137172401081954010832827869)
        ·
          refine ⟨51439650405732754062310451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137172401081954010832827869 51439650405732754062310451)
          ·
            refine ⟨77159475608599131093465677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51439650405732754062310451 77159475608599131093465677)
            ·
              refine ⟨28934803353224674160049629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77159475608599131093465677 28934803353224674160049629)
              ·
                refine ⟨10850551257459252810018611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28934803353224674160049629 10850551257459252810018611)
                ·
                  refine ⟨16275826886188879215027917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10850551257459252810018611 16275826886188879215027917)
                  ·
                    refine ⟨6103435082320829705635469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16275826886188879215027917 6103435082320829705635469)
                    ·
                      refine ⟨2288788155870311139613301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6103435082320829705635469 2288788155870311139613301)
                      ·
                        rfl

theorem cell23_4457399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 3, 3].length) (baseStart_4457399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4457399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4457399 prefixEnd_4457399 := by exact prefixLift 4457399
  have htrace : WordTrace (prefixWord ++ tailWord_4457399) baseStart_4457399 baseEnd_4457399 := by
    simpa [prefixWord, tailWord_4457399, baseEnd_4457399] using wordTrace_append hprefix tailTrace_4457399
  have hstable : (prefixWord ++ tailWord_4457399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4457399).length < 2 ^ (prefixWord ++ tailWord_4457399).sum := by decide
  have hdescent : baseEnd_4457399 < baseStart_4457399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4457399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4457402 : List Nat := [3, 1, 1, 1, 2, 1, 3, 2, 2, 7]
def baseStart_4457402 : Nat := 118140960795 + 4457402 * 2 ^ 59
def prefixEnd_4457402 : Nat := 4983230072969 + 3 ^ 40 * 4457402 * 2
def baseEnd_4457402 : Nat := 762929898770758209291929

theorem tailTrace_4457402 : CollatzResearch.WordTrace tailWord_4457402 prefixEnd_4457402 762929898770758209291929 := by
  unfold tailWord_4457402
  simp only [CollatzResearch.WordTrace]
  refine ⟨40643701749400323124853615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108383204665067528332942973 40643701749400323124853615)
  ·
    refine ⟨60965552624100484687280423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40643701749400323124853615 60965552624100484687280423)
    ·
      refine ⟨91448328936150727030920635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60965552624100484687280423 91448328936150727030920635)
      ·
        refine ⟨137172493404226090546380953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91448328936150727030920635 137172493404226090546380953)
        ·
          refine ⟨102879370053169567909785715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137172493404226090546380953 102879370053169567909785715)
          ·
            refine ⟨154319055079754351864678573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102879370053169567909785715 154319055079754351864678573)
            ·
              refine ⟨57869645654907881949254465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 154319055079754351864678573 57869645654907881949254465)
              ·
                refine ⟨43402234241180911461940849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57869645654907881949254465 43402234241180911461940849)
                ·
                  refine ⟨32551675680885683596455637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43402234241180911461940849 32551675680885683596455637)
                  ·
                    refine ⟨762929898770758209291929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32551675680885683596455637 762929898770758209291929)
                    ·
                      rfl

theorem cell23_4457402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 2, 7].length) (baseStart_4457402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4457402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4457402 prefixEnd_4457402 := by exact prefixLift 4457402
  have htrace : WordTrace (prefixWord ++ tailWord_4457402) baseStart_4457402 baseEnd_4457402 := by
    simpa [prefixWord, tailWord_4457402, baseEnd_4457402] using wordTrace_append hprefix tailTrace_4457402
  have hstable : (prefixWord ++ tailWord_4457402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4457402).length < 2 ^ (prefixWord ++ tailWord_4457402).sum := by decide
  have hdescent : baseEnd_4457402 < baseStart_4457402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4457402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4457433 : List Nat := [1, 2, 1, 2, 5, 1, 3, 2, 2, 1, 3]
def baseStart_4457433 : Nat := 118140960795 + 4457433 * 2 ^ 59
def prefixEnd_4457433 : Nat := 4983230072969 + 3 ^ 40 * 4457433 * 2
def baseEnd_4457433 : Nat := 2288805614212564006588145

theorem tailTrace_4457433 : CollatzResearch.WordTrace tailWord_4457433 prefixEnd_4457433 2288805614212564006588145 := by
  unfold tailWord_4457433
  simp only [CollatzResearch.WordTrace]
  refine ⟨162575937660488984793792953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108383958440325989862528635 162575937660488984793792953)
  ·
    refine ⟨121931953245366738595344715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162575937660488984793792953 121931953245366738595344715)
    ·
      refine ⟨182897929868050107893017073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121931953245366738595344715 182897929868050107893017073)
      ·
        refine ⟨137173447401037580919762805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182897929868050107893017073 137173447401037580919762805)
        ·
          refine ⟨12860010693847273211227763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 137173447401037580919762805 12860010693847273211227763)
          ·
            refine ⟨19290016040770909816841645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12860010693847273211227763 19290016040770909816841645)
            ·
              refine ⟨7233756015289091181315617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19290016040770909816841645 7233756015289091181315617)
              ·
                refine ⟨5425317011466818385986713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7233756015289091181315617 5425317011466818385986713)
                ·
                  refine ⟨4068987758600113789490035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5425317011466818385986713 4068987758600113789490035)
                  ·
                    refine ⟨6103481637900170684235053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4068987758600113789490035 6103481637900170684235053)
                    ·
                      refine ⟨2288805614212564006588145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6103481637900170684235053 2288805614212564006588145)
                      ·
                        rfl

theorem cell23_4457433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 2, 2, 1, 3].length) (baseStart_4457433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4457433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4457433 prefixEnd_4457433 := by exact prefixLift 4457433
  have htrace : WordTrace (prefixWord ++ tailWord_4457433) baseStart_4457433 baseEnd_4457433 := by
    simpa [prefixWord, tailWord_4457433, baseEnd_4457433] using wordTrace_append hprefix tailTrace_4457433
  have hstable : (prefixWord ++ tailWord_4457433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4457433).length < 2 ^ (prefixWord ++ tailWord_4457433).sum := by decide
  have hdescent : baseEnd_4457433 < baseStart_4457433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4457433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4457450 : List Nat := [3, 1, 3, 1, 2, 3, 3, 1, 2, 1, 3]
def baseStart_4457450 : Nat := 118140960795 + 4457450 * 2 ^ 59
def prefixEnd_4457450 : Nat := 4983230072969 + 3 ^ 40 * 4457450 * 2
def baseEnd_4457450 : Nat := 2288814343383690440075567

theorem tailTrace_4457450 : CollatzResearch.WordTrace tailWord_4457450 prefixEnd_4457450 2288814343383690440075567 := by
  unfold tailWord_4457450
  simp only [CollatzResearch.WordTrace]
  refine ⟨40644139425356849174290451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108384371800951597798107869 40644139425356849174290451)
  ·
    refine ⟨60966209138035273761435677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40644139425356849174290451 60966209138035273761435677)
    ·
      refine ⟨22862328426763227660538379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60966209138035273761435677 22862328426763227660538379)
      ·
        refine ⟨34293492640144841490807569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22862328426763227660538379 34293492640144841490807569)
        ·
          refine ⟨25720119480108631118105677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34293492640144841490807569 25720119480108631118105677)
          ·
            refine ⟨9645044805040736669289629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25720119480108631118105677 9645044805040736669289629)
            ·
              refine ⟨3616891801890276250983611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9645044805040736669289629 3616891801890276250983611)
              ·
                refine ⟨5425337702835414376475417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3616891801890276250983611 5425337702835414376475417)
                ·
                  refine ⟨4069003277126560782356563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5425337702835414376475417 4069003277126560782356563)
                  ·
                    refine ⟨6103504915689841173534845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4069003277126560782356563 6103504915689841173534845)
                    ·
                      refine ⟨2288814343383690440075567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6103504915689841173534845 2288814343383690440075567)
                      ·
                        rfl

theorem cell23_4457450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 1, 2, 1, 3].length) (baseStart_4457450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4457450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4457450 prefixEnd_4457450 := by exact prefixLift 4457450
  have htrace : WordTrace (prefixWord ++ tailWord_4457450) baseStart_4457450 baseEnd_4457450 := by
    simpa [prefixWord, tailWord_4457450, baseEnd_4457450] using wordTrace_append hprefix tailTrace_4457450
  have hstable : (prefixWord ++ tailWord_4457450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4457450).length < 2 ^ (prefixWord ++ tailWord_4457450).sum := by decide
  have hdescent : baseEnd_4457450 < baseStart_4457450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4457450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4457473 : List Nat := [1, 2, 4, 1, 2, 2, 1, 2, 4, 2, 2]
def baseStart_4457473 : Nat := 118140960795 + 4457473 * 2 ^ 59
def prefixEnd_4457473 : Nat := 4983230072969 + 3 ^ 40 * 4457473 * 2
def baseEnd_4457473 : Nat := 2288826153438743850087961

theorem tailTrace_4457473 : CollatzResearch.WordTrace tailWord_4457473 prefixEnd_4457473 2288826153438743850087961 := by
  unfold tailWord_4457473
  simp only [CollatzResearch.WordTrace]
  refine ⟨162577396580344071625249073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108384931053562714416832715 162577396580344071625249073)
  ·
    refine ⟨121933047435258053718936805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162577396580344071625249073 121933047435258053718936805)
    ·
      refine ⟨22862446394110885072300651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121933047435258053718936805 22862446394110885072300651)
      ·
        refine ⟨34293669591166327608450977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22862446394110885072300651 34293669591166327608450977)
        ·
          refine ⟨25720252193374745706338233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34293669591166327608450977 25720252193374745706338233)
          ·
            refine ⟨19290189145031059279753675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25720252193374745706338233 19290189145031059279753675)
            ·
              refine ⟨28935283717546588919630513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19290189145031059279753675 28935283717546588919630513)
              ·
                refine ⟨21701462788159941689722885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28935283717546588919630513 21701462788159941689722885)
                ·
                  refine ⟨4069024272779989066823041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21701462788159941689722885 4069024272779989066823041)
                  ·
                    refine ⟨3051768204584991800117281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4069024272779989066823041 3051768204584991800117281)
                    ·
                      refine ⟨2288826153438743850087961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3051768204584991800117281 2288826153438743850087961)
                      ·
                        rfl

theorem cell23_4457473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 4, 2, 2].length) (baseStart_4457473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4457473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4457473 prefixEnd_4457473 := by exact prefixLift 4457473
  have htrace : WordTrace (prefixWord ++ tailWord_4457473) baseStart_4457473 baseEnd_4457473 := by
    simpa [prefixWord, tailWord_4457473, baseEnd_4457473] using wordTrace_append hprefix tailTrace_4457473
  have hstable : (prefixWord ++ tailWord_4457473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4457473).length < 2 ^ (prefixWord ++ tailWord_4457473).sum := by decide
  have hdescent : baseEnd_4457473 < baseStart_4457473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4457473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4457489 : List Nat := [1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 3]
def baseStart_4457489 : Nat := 118140960795 + 4457489 * 2 ^ 59
def prefixEnd_4457489 : Nat := 4983230072969 + 3 ^ 40 * 4457489 * 2
def baseEnd_4457489 : Nat := 2288834369129215787487887

theorem tailTrace_4457489 : CollatzResearch.WordTrace tailWord_4457489 prefixEnd_4457489 2288834369129215787487887 := by
  unfold tailWord_4457489
  simp only [CollatzResearch.WordTrace]
  refine ⟨162577980148286106357831521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108385320098857404238554347 162577980148286106357831521)
  ·
    refine ⟨121933485111214579768373641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162577980148286106357831521 121933485111214579768373641)
    ·
      refine ⟨91450113833410934826280231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121933485111214579768373641 91450113833410934826280231)
      ·
        refine ⟨137175170750116402239420347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91450113833410934826280231 137175170750116402239420347)
        ·
          refine ⟨205762756125174603359130521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137175170750116402239420347 205762756125174603359130521)
          ·
            refine ⟨154322067093880952519347891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 205762756125174603359130521 154322067093880952519347891)
            ·
              refine ⟨231483100640821428779021837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154322067093880952519347891 231483100640821428779021837)
              ·
                refine ⟨86806162740308035792133189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 231483100640821428779021837 86806162740308035792133189)
                ·
                  refine ⟨16276155513807756711024973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 86806162740308035792133189 16276155513807756711024973)
                  ·
                    refine ⟨6103558317677908766634365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16276155513807756711024973 6103558317677908766634365)
                    ·
                      refine ⟨2288834369129215787487887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6103558317677908766634365 2288834369129215787487887)
                      ·
                        rfl

theorem cell23_4457489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 3].length) (baseStart_4457489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4457489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4457489 prefixEnd_4457489 := by exact prefixLift 4457489
  have htrace : WordTrace (prefixWord ++ tailWord_4457489) baseStart_4457489 baseEnd_4457489 := by
    simpa [prefixWord, tailWord_4457489, baseEnd_4457489] using wordTrace_append hprefix tailTrace_4457489
  have hstable : (prefixWord ++ tailWord_4457489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4457489).length < 2 ^ (prefixWord ++ tailWord_4457489).sum := by decide
  have hdescent : baseEnd_4457489 < baseStart_4457489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4457489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4457496 : List Nat := [2, 1, 2, 3, 2, 4, 1, 1, 7]
def baseStart_4457496 : Nat := 118140960795 + 4457496 * 2 ^ 59
def prefixEnd_4457496 : Nat := 4983230072969 + 3 ^ 40 * 4457496 * 2
def baseEnd_4457496 : Nat := 254315329277088584455595

theorem tailTrace_4457496 : CollatzResearch.WordTrace tailWord_4457496 prefixEnd_4457496 254315329277088584455595 := by
  unfold tailWord_4457496
  simp only [CollatzResearch.WordTrace]
  refine ⟨81289117729630373276668171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108385490306173831035557561 81289117729630373276668171)
  ·
    refine ⟨121933676594445559915002257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81289117729630373276668171 121933676594445559915002257)
    ·
      refine ⟨91450257445834169936251693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121933676594445559915002257 91450257445834169936251693)
      ·
        refine ⟨34293846542187813726094385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91450257445834169936251693 34293846542187813726094385)
        ·
          refine ⟨25720384906640860294570789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34293846542187813726094385 25720384906640860294570789)
          ·
            refine ⟨4822572169995161305232023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25720384906640860294570789 4822572169995161305232023)
            ·
              refine ⟨7233858254992741957848035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4822572169995161305232023 7233858254992741957848035)
              ·
                refine ⟨10850787382489112936772053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7233858254992741957848035 10850787382489112936772053)
                ·
                  refine ⟨254315329277088584455595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10850787382489112936772053 254315329277088584455595)
                  ·
                    rfl

theorem cell23_4457496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 7].length) (baseStart_4457496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4457496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4457496 prefixEnd_4457496 := by exact prefixLift 4457496
  have htrace : WordTrace (prefixWord ++ tailWord_4457496) baseStart_4457496 baseEnd_4457496 := by
    simpa [prefixWord, tailWord_4457496, baseEnd_4457496] using wordTrace_append hprefix tailTrace_4457496
  have hstable : (prefixWord ++ tailWord_4457496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4457496).length < 2 ^ (prefixWord ++ tailWord_4457496).sum := by decide
  have hdescent : baseEnd_4457496 < baseStart_4457496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4457496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4457507 : List Nat := [1, 1, 1, 4, 3, 4, 2, 1, 2, 2, 2]
def baseStart_4457507 : Nat := 118140960795 + 4457507 * 2 ^ 59
def prefixEnd_4457507 : Nat := 4983230072969 + 3 ^ 40 * 4457507 * 2
def baseEnd_4457507 : Nat := 2288843611780996717062805

theorem tailTrace_4457507 : CollatzResearch.WordTrace tailWord_4457507 prefixEnd_4457507 2288843611780996717062805 := by
  unfold tailWord_4457507
  simp only [CollatzResearch.WordTrace]
  refine ⟨162578636662220895431986775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108385757774813930287991183 162578636662220895431986775)
  ·
    refine ⟨243867954993331343147980163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162578636662220895431986775 243867954993331343147980163)
    ·
      refine ⟨365801932489997014721970245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243867954993331343147980163 365801932489997014721970245)
      ·
        refine ⟨68587862341874440260369421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 365801932489997014721970245 68587862341874440260369421)
        ·
          refine ⟨25720448378202915097638533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68587862341874440260369421 25720448378202915097638533)
          ·
            refine ⟨4822584070913046580807225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25720448378202915097638533 4822584070913046580807225)
            ·
              refine ⟨3616938053184784935605419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4822584070913046580807225 3616938053184784935605419)
              ·
                refine ⟨5425407079777177403408129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3616938053184784935605419 5425407079777177403408129)
                ·
                  refine ⟨4069055309832883052556097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5425407079777177403408129 4069055309832883052556097)
                  ·
                    refine ⟨3051791482374662289417073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4069055309832883052556097 3051791482374662289417073)
                    ·
                      refine ⟨2288843611780996717062805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3051791482374662289417073 2288843611780996717062805)
                      ·
                        rfl

theorem cell23_4457507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 1, 2, 2, 2].length) (baseStart_4457507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4457507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4457507 prefixEnd_4457507 := by exact prefixLift 4457507
  have htrace : WordTrace (prefixWord ++ tailWord_4457507) baseStart_4457507 baseEnd_4457507 := by
    simpa [prefixWord, tailWord_4457507, baseEnd_4457507] using wordTrace_append hprefix tailTrace_4457507
  have hstable : (prefixWord ++ tailWord_4457507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4457507).length < 2 ^ (prefixWord ++ tailWord_4457507).sum := by decide
  have hdescent : baseEnd_4457507 < baseStart_4457507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4457507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4457509 : List Nat := [1, 3, 1, 2, 2, 2, 1, 2, 4, 5]
def baseStart_4457509 : Nat := 118140960795 + 4457509 * 2 ^ 59
def prefixEnd_4457509 : Nat := 4983230072969 + 3 ^ 40 * 4457509 * 2
def baseEnd_4457509 : Nat := 762948212914101903079265

theorem tailTrace_4457509 : CollatzResearch.WordTrace tailWord_4457509 prefixEnd_4457509 762948212914101903079265 := by
  unfold tailWord_4457509
  simp only [CollatzResearch.WordTrace]
  refine ⟨162578709608213649773559581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108385806405475766515706387 162578709608213649773559581)
  ·
    refine ⟨60967016103080118665084843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162578709608213649773559581 60967016103080118665084843)
    ·
      refine ⟨91450524154620177997627265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60967016103080118665084843 91450524154620177997627265)
      ·
        refine ⟨68587893115965133498220449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91450524154620177997627265 68587893115965133498220449)
        ·
          refine ⟨51440919836973850123665337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68587893115965133498220449 51440919836973850123665337)
          ·
            refine ⟨38580689877730387592749003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51440919836973850123665337 38580689877730387592749003)
            ·
              refine ⟨57871034816595581389123505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38580689877730387592749003 57871034816595581389123505)
              ·
                refine ⟨43403276112446686041842629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57871034816595581389123505 43403276112446686041842629)
                ·
                  refine ⟨8138114271083753632845493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43403276112446686041842629 8138114271083753632845493)
                  ·
                    refine ⟨762948212914101903079265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8138114271083753632845493 762948212914101903079265)
                    ·
                      rfl

theorem cell23_4457509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 4, 5].length) (baseStart_4457509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4457509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4457509 prefixEnd_4457509 := by exact prefixLift 4457509
  have htrace : WordTrace (prefixWord ++ tailWord_4457509) baseStart_4457509 baseEnd_4457509 := by
    simpa [prefixWord, tailWord_4457509, baseEnd_4457509] using wordTrace_append hprefix tailTrace_4457509
  have hstable : (prefixWord ++ tailWord_4457509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4457509).length < 2 ^ (prefixWord ++ tailWord_4457509).sum := by decide
  have hdescent : baseEnd_4457509 < baseStart_4457509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4457509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4457546 : List Nat := [3, 1, 2, 1, 1, 2, 4, 2, 2, 1, 4]
def baseStart_4457546 : Nat := 118140960795 + 4457546 * 2 ^ 59
def prefixEnd_4457546 : Nat := 4983230072969 + 3 ^ 40 * 4457546 * 2
def baseEnd_4457546 : Nat := 2288863637526522064475125

theorem tailTrace_4457546 : CollatzResearch.WordTrace tailWord_4457546 prefixEnd_4457546 2288863637526522064475125 := by
  unfold tailWord_4457546
  simp only [CollatzResearch.WordTrace]
  refine ⟨40645014777269901273164123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108386706072719736728437661 40645014777269901273164123)
  ·
    refine ⟨60967522165904851909746185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40645014777269901273164123 60967522165904851909746185)
    ·
      refine ⟨45725641624428638932309639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60967522165904851909746185 45725641624428638932309639)
      ·
        refine ⟨68588462436642958398464459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45725641624428638932309639 68588462436642958398464459)
        ·
          refine ⟨102882693654964437597696689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68588462436642958398464459 102882693654964437597696689)
          ·
            refine ⟨77162020241223328198272517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102882693654964437597696689 77162020241223328198272517)
            ·
              refine ⟨14467878795229374037176097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77162020241223328198272517 14467878795229374037176097)
              ·
                refine ⟨10850909096422030527882073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14467878795229374037176097 10850909096422030527882073)
                ·
                  refine ⟨8138181822316522895911555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10850909096422030527882073 8138181822316522895911555)
                  ·
                    refine ⟨12207272733474784343867333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8138181822316522895911555 12207272733474784343867333)
                    ·
                      refine ⟨2288863637526522064475125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12207272733474784343867333 2288863637526522064475125)
                      ·
                        rfl

theorem cell23_4457546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_4457546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4457546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4457546 prefixEnd_4457546 := by exact prefixLift 4457546
  have htrace : WordTrace (prefixWord ++ tailWord_4457546) baseStart_4457546 baseEnd_4457546 := by
    simpa [prefixWord, tailWord_4457546, baseEnd_4457546] using wordTrace_append hprefix tailTrace_4457546
  have hstable : (prefixWord ++ tailWord_4457546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4457546).length < 2 ^ (prefixWord ++ tailWord_4457546).sum := by decide
  have hdescent : baseEnd_4457546 < baseStart_4457546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4457546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4457559 : List Nat := [1, 1, 3, 2, 2, 1, 1, 2, 2, 4, 4]
def baseStart_4457559 : Nat := 118140960795 + 4457559 * 2 ^ 59
def prefixEnd_4457559 : Nat := 4983230072969 + 3 ^ 40 * 4457559 * 2
def baseEnd_4457559 : Nat := 2288870312775030513612565

theorem tailTrace_4457559 : CollatzResearch.WordTrace tailWord_4457559 prefixEnd_4457559 2288870312775030513612565 := by
  unfold tailWord_4457559
  simp only [CollatzResearch.WordTrace]
  refine ⟨162580533258032508312879731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108387022172021672208586487 162580533258032508312879731)
  ·
    refine ⟨243870799887048762469319597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162580533258032508312879731 243870799887048762469319597)
    ·
      refine ⟨91451549957643285925994849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 243870799887048762469319597 91451549957643285925994849)
      ·
        refine ⟨68588662468232464444496137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91451549957643285925994849 68588662468232464444496137)
        ·
          refine ⟨51441496851174348333372103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68588662468232464444496137 51441496851174348333372103)
          ·
            refine ⟨77162245276761522500058155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51441496851174348333372103 77162245276761522500058155)
            ·
              refine ⟨115743367915142283750087233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77162245276761522500058155 115743367915142283750087233)
              ·
                refine ⟨86807525936356712812565425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115743367915142283750087233 86807525936356712812565425)
                ·
                  refine ⟨65105644452267534609424069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86807525936356712812565425 65105644452267534609424069)
                  ·
                    refine ⟨12207308334800162739267013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 65105644452267534609424069 12207308334800162739267013)
                    ·
                      refine ⟨2288870312775030513612565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12207308334800162739267013 2288870312775030513612565)
                      ·
                        rfl

theorem cell23_4457559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_4457559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4457559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4457559 prefixEnd_4457559 := by exact prefixLift 4457559
  have htrace : WordTrace (prefixWord ++ tailWord_4457559) baseStart_4457559 baseEnd_4457559 := by
    simpa [prefixWord, tailWord_4457559, baseEnd_4457559] using wordTrace_append hprefix tailTrace_4457559
  have hstable : (prefixWord ++ tailWord_4457559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4457559).length < 2 ^ (prefixWord ++ tailWord_4457559).sum := by decide
  have hdescent : baseEnd_4457559 < baseStart_4457559 := by decide
  rcases family_descends (prefixWord ++ tailWord_4457559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4457623 : List Nat := [1, 1, 3, 3, 3, 1, 1, 2, 1, 5, 2]
def baseStart_4457623 : Nat := 118140960795 + 4457623 * 2 ^ 59
def prefixEnd_4457623 : Nat := 4983230072969 + 3 ^ 40 * 4457623 * 2
def baseEnd_4457623 : Nat := 2288903175536918263212271

theorem tailTrace_4457623 : CollatzResearch.WordTrace tailWord_4457623 prefixEnd_4457623 2288903175536918263212271 := by
  unfold tailWord_4457623
  simp only [CollatzResearch.WordTrace]
  refine ⟨162582867529800647243209523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108388578353200431495473015 162582867529800647243209523)
  ·
    refine ⟨243874301294700970864814285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162582867529800647243209523 243874301294700970864814285)
    ·
      refine ⟨91452862985512864074305357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 243874301294700970864814285 91452862985512864074305357)
      ·
        refine ⟨34294823619567324027864509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91452862985512864074305357 34294823619567324027864509)
        ·
          refine ⟨12860558857337746510449191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34294823619567324027864509 12860558857337746510449191)
          ·
            refine ⟨19290838286006619765673787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12860558857337746510449191 19290838286006619765673787)
            ·
              refine ⟨28936257429009929648510681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19290838286006619765673787 28936257429009929648510681)
              ·
                refine ⟨21702193071757447236383011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28936257429009929648510681 21702193071757447236383011)
                ·
                  refine ⟨32553289607636170854574517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21702193071757447236383011 32553289607636170854574517)
                  ·
                    refine ⟨3051870900715891017616361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32553289607636170854574517 3051870900715891017616361)
                    ·
                      refine ⟨2288903175536918263212271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3051870900715891017616361 2288903175536918263212271)
                      ·
                        rfl

theorem cell23_4457623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 5, 2].length) (baseStart_4457623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4457623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4457623 prefixEnd_4457623 := by exact prefixLift 4457623
  have htrace : WordTrace (prefixWord ++ tailWord_4457623) baseStart_4457623 baseEnd_4457623 := by
    simpa [prefixWord, tailWord_4457623, baseEnd_4457623] using wordTrace_append hprefix tailTrace_4457623
  have hstable : (prefixWord ++ tailWord_4457623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4457623).length < 2 ^ (prefixWord ++ tailWord_4457623).sum := by decide
  have hdescent : baseEnd_4457623 < baseStart_4457623 := by decide
  rcases family_descends (prefixWord ++ tailWord_4457623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4457633 : List Nat := [1, 2, 3, 3, 1, 1, 4, 2, 1, 5]
def baseStart_4457633 : Nat := 118140960795 + 4457633 * 2 ^ 59
def prefixEnd_4457633 : Nat := 4983230072969 + 3 ^ 40 * 4457633 * 2
def baseEnd_4457633 : Nat := 762969436781154408029075

theorem tailTrace_4457633 : CollatzResearch.WordTrace tailWord_4457633 prefixEnd_4457633 762969436781154408029075 := by
  unfold tailWord_4457633
  simp only [CollatzResearch.WordTrace]
  refine ⟨162583232259764418951073553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108388821506509612634049035 162583232259764418951073553)
  ·
    refine ⟨121937424194823314213305165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162583232259764418951073553 121937424194823314213305165)
    ·
      refine ⟨45726534073058742829989437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121937424194823314213305165 45726534073058742829989437)
      ·
        refine ⟨17147450277397028561246039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45726534073058742829989437 17147450277397028561246039)
        ·
          refine ⟨25721175416095542841869059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17147450277397028561246039 25721175416095542841869059)
          ·
            refine ⟨38581763124143314262803589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25721175416095542841869059 38581763124143314262803589)
            ·
              refine ⟨7234080585776871424275673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38581763124143314262803589 7234080585776871424275673)
              ·
                refine ⟨5425560439332653568206755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7234080585776871424275673 5425560439332653568206755)
                ·
                  refine ⟨8138340658998980352310133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5425560439332653568206755 8138340658998980352310133)
                  ·
                    refine ⟨762969436781154408029075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8138340658998980352310133 762969436781154408029075)
                    ·
                      rfl

theorem cell23_4457633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 2, 1, 5].length) (baseStart_4457633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4457633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4457633 prefixEnd_4457633 := by exact prefixLift 4457633
  have htrace : WordTrace (prefixWord ++ tailWord_4457633) baseStart_4457633 baseEnd_4457633 := by
    simpa [prefixWord, tailWord_4457633, baseEnd_4457633] using wordTrace_append hprefix tailTrace_4457633
  have hstable : (prefixWord ++ tailWord_4457633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4457633).length < 2 ^ (prefixWord ++ tailWord_4457633).sum := by decide
  have hdescent : baseEnd_4457633 < baseStart_4457633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4457633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4457664 : List Nat := [2, 1, 1, 2, 6, 1, 3, 2, 1, 1, 3]
def baseStart_4457664 : Nat := 118140960795 + 4457664 * 2 ^ 59
def prefixEnd_4457664 : Nat := 4983230072969 + 3 ^ 40 * 4457664 * 2
def baseEnd_4457664 : Nat := 2288924228243752602799583

theorem tailTrace_4457664 : CollatzResearch.WordTrace tailWord_4457664 prefixEnd_4457664 2288924228243752602799583 := by
  unfold tailWord_4457664
  simp only [CollatzResearch.WordTrace]
  refine ⟨81292181461326055622726023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108389575281768074163634697 81292181461326055622726023)
  ·
    refine ⟨121938272191989083434089035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81292181461326055622726023 121938272191989083434089035)
    ·
      refine ⟨182907408287983625151133553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121938272191989083434089035 182907408287983625151133553)
      ·
        refine ⟨137180556215987718863350165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182907408287983625151133553 137180556215987718863350165)
        ·
          refine ⟨6430338572624424321719539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 137180556215987718863350165 6430338572624424321719539)
          ·
            refine ⟨9645507858936636482579309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6430338572624424321719539 9645507858936636482579309)
            ·
              refine ⟨3617065447101238680967241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9645507858936636482579309 3617065447101238680967241)
              ·
                refine ⟨2712799085325929010725431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3617065447101238680967241 2712799085325929010725431)
                ·
                  refine ⟨4069198627988893516088147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2712799085325929010725431 4069198627988893516088147)
                  ·
                    refine ⟨6103797941983340274132221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4069198627988893516088147 6103797941983340274132221)
                    ·
                      refine ⟨2288924228243752602799583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6103797941983340274132221 2288924228243752602799583)
                      ·
                        rfl

theorem cell23_4457664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 2, 1, 1, 3].length) (baseStart_4457664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4457664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4457664 prefixEnd_4457664 := by exact prefixLift 4457664
  have htrace : WordTrace (prefixWord ++ tailWord_4457664) baseStart_4457664 baseEnd_4457664 := by
    simpa [prefixWord, tailWord_4457664, baseEnd_4457664] using wordTrace_append hprefix tailTrace_4457664
  have hstable : (prefixWord ++ tailWord_4457664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4457664).length < 2 ^ (prefixWord ++ tailWord_4457664).sum := by decide
  have hdescent : baseEnd_4457664 < baseStart_4457664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4457664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4457684 : List Nat := [2, 4, 1, 4, 2, 1, 1, 2, 1, 5]
def baseStart_4457684 : Nat := 118140960795 + 4457684 * 2 ^ 59
def prefixEnd_4457684 : Nat := 4983230072969 + 3 ^ 40 * 4457684 * 2
def baseEnd_4457684 : Nat := 762978165952280841516497

theorem tailTrace_4457684 : CollatzResearch.WordTrace tailWord_4457684 prefixEnd_4457684 762978165952280841516497 := by
  unfold tailWord_4457684
  simp only [CollatzResearch.WordTrace]
  refine ⟨81292546191289827330590053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108390061588386436440786737 81292546191289827330590053)
  ·
    refine ⟨15242352410866842624485635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81292546191289827330590053 15242352410866842624485635)
    ·
      refine ⟨22863528616300263936728453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15242352410866842624485635 22863528616300263936728453)
      ·
        refine ⟨4286911615556299488136585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22863528616300263936728453 4286911615556299488136585)
        ·
          refine ⟨3215183711667224616102439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4286911615556299488136585 3215183711667224616102439)
          ·
            refine ⟨4822775567500836924153659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3215183711667224616102439 4822775567500836924153659)
            ·
              refine ⟨7234163351251255386230489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4822775567500836924153659 7234163351251255386230489)
              ·
                refine ⟨5425622513438441539672867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7234163351251255386230489 5425622513438441539672867)
                ·
                  refine ⟨8138433770157662309509301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5425622513438441539672867 8138433770157662309509301)
                  ·
                    refine ⟨762978165952280841516497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8138433770157662309509301 762978165952280841516497)
                    ·
                      rfl

theorem cell23_4457684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_4457684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4457684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4457684 prefixEnd_4457684 := by exact prefixLift 4457684
  have htrace : WordTrace (prefixWord ++ tailWord_4457684) baseStart_4457684 baseEnd_4457684 := by
    simpa [prefixWord, tailWord_4457684, baseEnd_4457684] using wordTrace_append hprefix tailTrace_4457684
  have hstable : (prefixWord ++ tailWord_4457684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4457684).length < 2 ^ (prefixWord ++ tailWord_4457684).sum := by decide
  have hdescent : baseEnd_4457684 < baseStart_4457684 := by decide
  rcases family_descends (prefixWord ++ tailWord_4457684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4457758 : List Nat := [4, 3, 2, 1, 3, 1, 2, 1, 1, 2, 3]
def baseStart_4457758 : Nat := 118140960795 + 4457758 * 2 ^ 59
def prefixEnd_4457758 : Nat := 4983230072969 + 3 ^ 40 * 4457758 * 2
def baseEnd_4457758 : Nat := 2288972495425275235024151

theorem tailTrace_4457758 : CollatzResearch.WordTrace tailWord_4457758 prefixEnd_4457758 2288972495425275235024151 := by
  unfold tailWord_4457758
  simp only [CollatzResearch.WordTrace]
  refine ⟨20323473923038945662421741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108391860922874376866249285 20323473923038945662421741)
  ·
    refine ⟨7621302721139604623408153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20323473923038945662421741 7621302721139604623408153)
    ·
      refine ⟨5715977040854703467556115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7621302721139604623408153 5715977040854703467556115)
      ·
        refine ⟨8573965561282055201334173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5715977040854703467556115 8573965561282055201334173)
        ·
          refine ⟨3215237085480770700500315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8573965561282055201334173 3215237085480770700500315)
          ·
            refine ⟨4822855628221156050750473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3215237085480770700500315 4822855628221156050750473)
            ·
              refine ⟨3617141721165867038062855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4822855628221156050750473 3617141721165867038062855)
              ·
                refine ⟨5425712581748800557094283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3617141721165867038062855 5425712581748800557094283)
                ·
                  refine ⟨8138568872623200835641425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5425712581748800557094283 8138568872623200835641425)
                  ·
                    refine ⟨6103926654467400626731069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8138568872623200835641425 6103926654467400626731069)
                    ·
                      refine ⟨2288972495425275235024151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6103926654467400626731069 2288972495425275235024151)
                      ·
                        rfl

theorem cell23_4457758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_4457758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4457758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4457758 prefixEnd_4457758 := by exact prefixLift 4457758
  have htrace : WordTrace (prefixWord ++ tailWord_4457758) baseStart_4457758 baseEnd_4457758 := by
    simpa [prefixWord, tailWord_4457758, baseEnd_4457758] using wordTrace_append hprefix tailTrace_4457758
  have hstable : (prefixWord ++ tailWord_4457758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4457758).length < 2 ^ (prefixWord ++ tailWord_4457758).sum := by decide
  have hdescent : baseEnd_4457758 < baseStart_4457758 := by decide
  rcases family_descends (prefixWord ++ tailWord_4457758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4457777 : List Nat := [1, 2, 2, 3, 3, 2, 1, 1, 4, 2, 2]
def baseStart_4457777 : Nat := 118140960795 + 4457777 * 2 ^ 59
def prefixEnd_4457777 : Nat := 4983230072969 + 3 ^ 40 * 4457777 * 2
def baseEnd_4457777 : Nat := 2288982251557710660686563

theorem tailTrace_4457777 : CollatzResearch.WordTrace tailWord_4457777 prefixEnd_4457777 2288982251557710660686563 := by
  unfold tailWord_4457777
  simp only [CollatzResearch.WordTrace]
  refine ⟨162588484371242731544315585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108392322914161821029543723 162588484371242731544315585)
  ·
    refine ⟨121941363278432048658236689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162588484371242731544315585 121941363278432048658236689)
    ·
      refine ⟨91456022458824036493677517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121941363278432048658236689 91456022458824036493677517)
      ·
        refine ⟨34296008422059013685129069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91456022458824036493677517 34296008422059013685129069)
        ·
          refine ⟨12861003158272130131923401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34296008422059013685129069 12861003158272130131923401)
          ·
            refine ⟨9645752368704097598942551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12861003158272130131923401 9645752368704097598942551)
            ·
              refine ⟨14468628553056146398413827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9645752368704097598942551 14468628553056146398413827)
              ·
                refine ⟨21702942829584219597620741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14468628553056146398413827 21702942829584219597620741)
                ·
                  refine ⟨4069301780547041174553889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21702942829584219597620741 4069301780547041174553889)
                  ·
                    refine ⟨3051976335410280880915417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4069301780547041174553889 3051976335410280880915417)
                    ·
                      refine ⟨2288982251557710660686563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3051976335410280880915417 2288982251557710660686563)
                      ·
                        rfl

theorem cell23_4457777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 4, 2, 2].length) (baseStart_4457777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4457777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4457777 prefixEnd_4457777 := by exact prefixLift 4457777
  have htrace : WordTrace (prefixWord ++ tailWord_4457777) baseStart_4457777 baseEnd_4457777 := by
    simpa [prefixWord, tailWord_4457777, baseEnd_4457777] using wordTrace_append hprefix tailTrace_4457777
  have hstable : (prefixWord ++ tailWord_4457777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4457777).length < 2 ^ (prefixWord ++ tailWord_4457777).sum := by decide
  have hdescent : baseEnd_4457777 < baseStart_4457777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4457777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4457798 : List Nat := [6, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2]
def baseStart_4457798 : Nat := 118140960795 + 4457798 * 2 ^ 59
def prefixEnd_4457798 : Nat := 4983230072969 + 3 ^ 40 * 4457798 * 2
def baseEnd_4457798 : Nat := 2288993034651455078523967

theorem tailTrace_4457798 : CollatzResearch.WordTrace tailWord_4457798 prefixEnd_4457798 2288993034651455078523967 := by
  unfold tailWord_4457798
  simp only [CollatzResearch.WordTrace]
  refine ⟨5080914072005207879088439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 108392833536111101420553365 5080914072005207879088439)
  ·
    refine ⟨7621371108007811818632659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5080914072005207879088439 7621371108007811818632659)
    ·
      refine ⟨11432056662011717727948989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7621371108007811818632659 11432056662011717727948989)
      ·
        refine ⟨4287021248254394147980871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11432056662011717727948989 4287021248254394147980871)
        ·
          refine ⟨6430531872381591221971307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4287021248254394147980871 6430531872381591221971307)
          ·
            refine ⟨9645797808572386832956961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6430531872381591221971307 9645797808572386832956961)
            ·
              refine ⟨7234348356429290124717721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9645797808572386832956961 7234348356429290124717721)
              ·
                refine ⟨5425761267321967593538291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7234348356429290124717721 5425761267321967593538291)
                ·
                  refine ⟨8138641900982951390307437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5425761267321967593538291 8138641900982951390307437)
                  ·
                    refine ⟨3051990712868606771365289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8138641900982951390307437 3051990712868606771365289)
                    ·
                      refine ⟨2288993034651455078523967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3051990712868606771365289 2288993034651455078523967)
                      ·
                        rfl

theorem cell23_4457798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_4457798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4457798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4457798 prefixEnd_4457798 := by exact prefixLift 4457798
  have htrace : WordTrace (prefixWord ++ tailWord_4457798) baseStart_4457798 baseEnd_4457798 := by
    simpa [prefixWord, tailWord_4457798, baseEnd_4457798] using wordTrace_append hprefix tailTrace_4457798
  have hstable : (prefixWord ++ tailWord_4457798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4457798).length < 2 ^ (prefixWord ++ tailWord_4457798).sum := by decide
  have hdescent : baseEnd_4457798 < baseStart_4457798 := by decide
  rcases family_descends (prefixWord ++ tailWord_4457798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4457803 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 3, 7, 2]
def baseStart_4457803 : Nat := 118140960795 + 4457803 * 2 ^ 59
def prefixEnd_4457803 : Nat := 4983230072969 + 3 ^ 40 * 4457803 * 2
def baseEnd_4457803 : Nat := 2288995602054727558961443

theorem tailTrace_4457803 : CollatzResearch.WordTrace tailWord_4457803 prefixEnd_4457803 2288995602054727558961443 := by
  unfold tailWord_4457803
  simp only [CollatzResearch.WordTrace]
  refine ⟨162589432669148537984762063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108392955112765691989841375 162589432669148537984762063)
  ·
    refine ⟨243884149003722806977143095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162589432669148537984762063 243884149003722806977143095)
    ·
      refine ⟨365826223505584210465714643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243884149003722806977143095 365826223505584210465714643)
      ·
        refine ⟨548739335258376315698571965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 365826223505584210465714643 548739335258376315698571965)
        ·
          refine ⟨205777250721891118386964487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 548739335258376315698571965 205777250721891118386964487)
          ·
            refine ⟨308665876082836677580446731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205777250721891118386964487 308665876082836677580446731)
            ·
              refine ⟨462998814124255016370670097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 308665876082836677580446731 462998814124255016370670097)
              ·
                refine ⟨347249110593191262278002573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 462998814124255016370670097 347249110593191262278002573)
                ·
                  refine ⟨130218416472446723354250965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 347249110593191262278002573 130218416472446723354250965)
                  ·
                    refine ⟨3051994136072970078615257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 130218416472446723354250965 3051994136072970078615257)
                    ·
                      refine ⟨2288995602054727558961443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3051994136072970078615257 2288995602054727558961443)
                      ·
                        rfl

theorem cell23_4457803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 7, 2].length) (baseStart_4457803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4457803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4457803 prefixEnd_4457803 := by exact prefixLift 4457803
  have htrace : WordTrace (prefixWord ++ tailWord_4457803) baseStart_4457803 baseEnd_4457803 := by
    simpa [prefixWord, tailWord_4457803, baseEnd_4457803] using wordTrace_append hprefix tailTrace_4457803
  have hstable : (prefixWord ++ tailWord_4457803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4457803).length < 2 ^ (prefixWord ++ tailWord_4457803).sum := by decide
  have hdescent : baseEnd_4457803 < baseStart_4457803 := by decide
  rcases family_descends (prefixWord ++ tailWord_4457803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4457813 : List Nat := [1, 3, 2, 2, 3, 1, 2, 1, 1, 7]
def baseStart_4457813 : Nat := 118140960795 + 4457813 * 2 ^ 59
def prefixEnd_4457813 : Nat := 4983230072969 + 3 ^ 40 * 4457813 * 2
def baseEnd_4457813 : Nat := 763000245620424173278799

theorem tailTrace_4457813 : CollatzResearch.WordTrace tailWord_4457813 prefixEnd_4457813 763000245620424173278799 := by
  unfold tailWord_4457813
  simp only [CollatzResearch.WordTrace]
  refine ⟨162589797399112309692626093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108393198266074873128417395 162589797399112309692626093)
  ·
    refine ⟨60971174024667116134734785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162589797399112309692626093 60971174024667116134734785)
    ·
      refine ⟨45728380518500337101051089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60971174024667116134734785 45728380518500337101051089)
      ·
        refine ⟨34296285388875252825788317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45728380518500337101051089 34296285388875252825788317)
        ·
          refine ⟨12861107020828219809670619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34296285388875252825788317 12861107020828219809670619)
          ·
            refine ⟨19291660531242329714505929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12861107020828219809670619 19291660531242329714505929)
            ·
              refine ⟨14468745398431747285879447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19291660531242329714505929 14468745398431747285879447)
              ·
                refine ⟨21703118097647620928819171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14468745398431747285879447 21703118097647620928819171)
                ·
                  refine ⟨32554677146471431393228757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21703118097647620928819171 32554677146471431393228757)
                  ·
                    refine ⟨763000245620424173278799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32554677146471431393228757 763000245620424173278799)
                    ·
                      rfl

theorem cell23_4457813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 7].length) (baseStart_4457813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4457813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4457813 prefixEnd_4457813 := by exact prefixLift 4457813
  have htrace : WordTrace (prefixWord ++ tailWord_4457813) baseStart_4457813 baseEnd_4457813 := by
    simpa [prefixWord, tailWord_4457813, baseEnd_4457813] using wordTrace_append hprefix tailTrace_4457813
  have hstable : (prefixWord ++ tailWord_4457813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4457813).length < 2 ^ (prefixWord ++ tailWord_4457813).sum := by decide
  have hdescent : baseEnd_4457813 < baseStart_4457813 := by decide
  rcases family_descends (prefixWord ++ tailWord_4457813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4457834 : List Nat := [3, 1, 3, 3, 2, 1, 3, 2, 5]
def baseStart_4457834 : Nat := 118140960795 + 4457834 * 2 ^ 59
def prefixEnd_4457834 : Nat := 4983230072969 + 3 ^ 40 * 4457834 * 2
def baseEnd_4457834 : Nat := 254334613328335215297089

theorem tailTrace_4457834 : CollatzResearch.WordTrace tailWord_4457834 prefixEnd_4457834 254334613328335215297089 := by
  unfold tailWord_4457834
  simp only [CollatzResearch.WordTrace]
  refine ⟨40647640833009057569785139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108393708888024153519427037 40647640833009057569785139)
  ·
    refine ⟨60971461249513586354677709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40647640833009057569785139 60971461249513586354677709)
    ·
      refine ⟨22864297968567594883004141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60971461249513586354677709 22864297968567594883004141)
      ·
        refine ⟨8574111738212848081126553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22864297968567594883004141 8574111738212848081126553)
        ·
          refine ⟨6430583803659636060844915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8574111738212848081126553 6430583803659636060844915)
          ·
            refine ⟨9645875705489454091267373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6430583803659636060844915 9645875705489454091267373)
            ·
              refine ⟨3617203389558545284225265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9645875705489454091267373 3617203389558545284225265)
              ·
                refine ⟨2712902542168908963168949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3617203389558545284225265 2712902542168908963168949)
                ·
                  refine ⟨254334613328335215297089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2712902542168908963168949 254334613328335215297089)
                  ·
                    rfl

theorem cell23_4457834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 2, 5].length) (baseStart_4457834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4457834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4457834 prefixEnd_4457834 := by exact prefixLift 4457834
  have htrace : WordTrace (prefixWord ++ tailWord_4457834) baseStart_4457834 baseEnd_4457834 := by
    simpa [prefixWord, tailWord_4457834, baseEnd_4457834] using wordTrace_append hprefix tailTrace_4457834
  have hstable : (prefixWord ++ tailWord_4457834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4457834).length < 2 ^ (prefixWord ++ tailWord_4457834).sum := by decide
  have hdescent : baseEnd_4457834 < baseStart_4457834 := by decide
  rcases family_descends (prefixWord ++ tailWord_4457834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4457890 : List Nat := [3, 3, 1, 2, 1, 2, 1, 4, 6]
def baseStart_4457890 : Nat := 118140960795 + 4457890 * 2 ^ 59
def prefixEnd_4457890 : Nat := 4983230072969 + 3 ^ 40 * 4457890 * 2
def baseEnd_4457890 : Nat := 254337808319074302063727

theorem tailTrace_4457890 : CollatzResearch.WordTrace tailWord_4457890 prefixEnd_4457890 254337808319074302063727 := by
  unfold tailWord_4457890
  simp only [CollatzResearch.WordTrace]
  refine ⟨40648151454958337960794781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108395070546555567895452749 40648151454958337960794781)
  ·
    refine ⟨15243056795609376735298043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40648151454958337960794781 15243056795609376735298043)
    ·
      refine ⟨22864585193414065102947065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15243056795609376735298043 22864585193414065102947065)
      ·
        refine ⟨17148438895060548827210299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22864585193414065102947065 17148438895060548827210299)
        ·
          refine ⟨25722658342590823240815449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17148438895060548827210299 25722658342590823240815449)
          ·
            refine ⟨19291993756943117430611587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25722658342590823240815449 19291993756943117430611587)
            ·
              refine ⟨28937990635414676145917381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19291993756943117430611587 28937990635414676145917381)
              ·
                refine ⟨5425873244140251777359509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28937990635414676145917381 5425873244140251777359509)
                ·
                  refine ⟨254337808319074302063727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5425873244140251777359509 254337808319074302063727)
                  ·
                    rfl

theorem cell23_4457890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 4, 6].length) (baseStart_4457890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4457890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4457890 prefixEnd_4457890 := by exact prefixLift 4457890
  have htrace : WordTrace (prefixWord ++ tailWord_4457890) baseStart_4457890 baseEnd_4457890 := by
    simpa [prefixWord, tailWord_4457890, baseEnd_4457890] using wordTrace_append hprefix tailTrace_4457890
  have hstable : (prefixWord ++ tailWord_4457890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4457890).length < 2 ^ (prefixWord ++ tailWord_4457890).sum := by decide
  have hdescent : baseEnd_4457890 < baseStart_4457890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4457890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4457917 : List Nat := [1, 4, 1, 2, 2, 1, 3, 2, 3, 1, 3]
def baseStart_4457917 : Nat := 118140960795 + 4457917 * 2 ^ 59
def prefixEnd_4457917 : Nat := 4983230072969 + 3 ^ 40 * 4457917 * 2
def baseEnd_4457917 : Nat := 2289054138849340112935919

theorem tailTrace_4457917 : CollatzResearch.WordTrace tailWord_4457917 prefixEnd_4457917 2289054138849340112935919 := by
  unfold tailWord_4457917
  simp only [CollatzResearch.WordTrace]
  refine ⟨162593590590735535454412005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108395727060490356969608003 162593590590735535454412005)
  ·
    refine ⟨30486298235762912897702251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 162593590590735535454412005 30486298235762912897702251)
    ·
      refine ⟨45729447353644369346553377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30486298235762912897702251 45729447353644369346553377)
      ·
        refine ⟨34297085515233277009915033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45729447353644369346553377 34297085515233277009915033)
        ·
          refine ⟨25722814136424957757436275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34297085515233277009915033 25722814136424957757436275)
          ·
            refine ⟨38584221204637436636154413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25722814136424957757436275 38584221204637436636154413)
            ·
              refine ⟨14469082951739038738557905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38584221204637436636154413 14469082951739038738557905)
              ·
                refine ⟨10851812213804279053918429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14469082951739038738557905 10851812213804279053918429)
                ·
                  refine ⟨4069429580176604645219411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10851812213804279053918429 4069429580176604645219411)
                  ·
                    refine ⟨6104144370264906967829117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4069429580176604645219411 6104144370264906967829117)
                    ·
                      refine ⟨2289054138849340112935919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6104144370264906967829117 2289054138849340112935919)
                      ·
                        rfl

theorem cell23_4457917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_4457917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4457917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4457917 prefixEnd_4457917 := by exact prefixLift 4457917
  have htrace : WordTrace (prefixWord ++ tailWord_4457917) baseStart_4457917 baseEnd_4457917 := by
    simpa [prefixWord, tailWord_4457917, baseEnd_4457917] using wordTrace_append hprefix tailTrace_4457917
  have hstable : (prefixWord ++ tailWord_4457917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4457917).length < 2 ^ (prefixWord ++ tailWord_4457917).sum := by decide
  have hdescent : baseEnd_4457917 < baseStart_4457917 := by decide
  rcases family_descends (prefixWord ++ tailWord_4457917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4457934 : List Nat := [4, 1, 1, 1, 2, 1, 3, 5, 1, 1, 3]
def baseStart_4457934 : Nat := 118140960795 + 4457934 * 2 ^ 59
def prefixEnd_4457934 : Nat := 4983230072969 + 3 ^ 40 * 4457934 * 2
def baseEnd_4457934 : Nat := 2289062868020466546423341

theorem tailTrace_4457934 : CollatzResearch.WordTrace tailWord_4457934 prefixEnd_4457934 2289062868020466546423341 := by
  unfold tailWord_4457934
  simp only [CollatzResearch.WordTrace]
  refine ⟨20324276328959243419722607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108396140421115964905187237 20324276328959243419722607)
  ·
    refine ⟨30486414493438865129583911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20324276328959243419722607 30486414493438865129583911)
    ·
      refine ⟨45729621740158297694375867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30486414493438865129583911 45729621740158297694375867)
      ·
        refine ⟨68594432610237446541563801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45729621740158297694375867 68594432610237446541563801)
        ·
          refine ⟨51445824457678084906172851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68594432610237446541563801 51445824457678084906172851)
          ·
            refine ⟨77168736686517127359259277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51445824457678084906172851 77168736686517127359259277)
            ·
              refine ⟨28938276257443922759722229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77168736686517127359259277 28938276257443922759722229)
              ·
                refine ⟨2712963399135367758723959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28938276257443922759722229 2712963399135367758723959)
                ·
                  refine ⟨4069445098703051638085939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2712963399135367758723959 4069445098703051638085939)
                  ·
                    refine ⟨6104167648054577457128909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4069445098703051638085939 6104167648054577457128909)
                    ·
                      refine ⟨2289062868020466546423341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6104167648054577457128909 2289062868020466546423341)
                      ·
                        rfl

theorem cell23_4457934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 5, 1, 1, 3].length) (baseStart_4457934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4457934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4457934 prefixEnd_4457934 := by exact prefixLift 4457934
  have htrace : WordTrace (prefixWord ++ tailWord_4457934) baseStart_4457934 baseEnd_4457934 := by
    simpa [prefixWord, tailWord_4457934, baseEnd_4457934] using wordTrace_append hprefix tailTrace_4457934
  have hstable : (prefixWord ++ tailWord_4457934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4457934).length < 2 ^ (prefixWord ++ tailWord_4457934).sum := by decide
  have hdescent : baseEnd_4457934 < baseStart_4457934 := by decide
  rcases family_descends (prefixWord ++ tailWord_4457934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4457943 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 5]
def baseStart_4457943 : Nat := 118140960795 + 4457943 * 2 ^ 59
def prefixEnd_4457943 : Nat := 4983230072969 + 3 ^ 40 * 4457943 * 2
def baseEnd_4457943 : Nat := 2289067489346357011210799

theorem tailTrace_4457943 : CollatzResearch.WordTrace tailWord_4457943 prefixEnd_4457943 2289067489346357011210799 := by
  unfold tailWord_4457943
  simp only [CollatzResearch.WordTrace]
  refine ⟨162594538888641341894858483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108396359259094227929905655 162594538888641341894858483)
  ·
    refine ⟨243891808332962012842287725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162594538888641341894858483 243891808332962012842287725)
    ·
      refine ⟨91459428124860754815857897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 243891808332962012842287725 91459428124860754815857897)
      ·
        refine ⟨68594571093645566111893423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91459428124860754815857897 68594571093645566111893423)
        ·
          refine ⟨102891856640468349167840135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68594571093645566111893423 102891856640468349167840135)
          ·
            refine ⟨154337784960702523751760203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102891856640468349167840135 154337784960702523751760203)
            ·
              refine ⟨231506677441053785627640305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154337784960702523751760203 231506677441053785627640305)
              ·
                refine ⟨173630008080790339220730229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 231506677441053785627640305 173630008080790339220730229)
                ·
                  refine ⟨16277813257574094301943459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 173630008080790339220730229 16277813257574094301943459)
                  ·
                    refine ⟨24416719886361141452915189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16277813257574094301943459 24416719886361141452915189)
                    ·
                      refine ⟨2289067489346357011210799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24416719886361141452915189 2289067489346357011210799)
                      ·
                        rfl

theorem cell23_4457943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_4457943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4457943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4457943 prefixEnd_4457943 := by exact prefixLift 4457943
  have htrace : WordTrace (prefixWord ++ tailWord_4457943) baseStart_4457943 baseEnd_4457943 := by
    simpa [prefixWord, tailWord_4457943, baseEnd_4457943] using wordTrace_append hprefix tailTrace_4457943
  have hstable : (prefixWord ++ tailWord_4457943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4457943).length < 2 ^ (prefixWord ++ tailWord_4457943).sum := by decide
  have hdescent : baseEnd_4457943 < baseStart_4457943 := by decide
  rcases family_descends (prefixWord ++ tailWord_4457943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4457960 : List Nat := [2, 1, 4, 1, 1, 2, 3, 2, 1, 1, 5]
def baseStart_4457960 : Nat := 118140960795 + 4457960 * 2 ^ 59
def prefixEnd_4457960 : Nat := 4983230072969 + 3 ^ 40 * 4457960 * 2
def baseEnd_4457960 : Nat := 2289076218517483444698221

theorem tailTrace_4457960 : CollatzResearch.WordTrace tailWord_4457960 prefixEnd_4457960 2289076218517483444698221 := by
  unfold tailWord_4457960
  simp only [CollatzResearch.WordTrace]
  refine ⟨81297579464789876899113667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108396772619719835865484889 81297579464789876899113667)
  ·
    refine ⟨121946369197184815348670501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81297579464789876899113667 121946369197184815348670501)
    ·
      refine ⟨22864944224472152877875719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121946369197184815348670501 22864944224472152877875719)
      ·
        refine ⟨34297416336708229316813579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22864944224472152877875719 34297416336708229316813579)
        ·
          refine ⟨51446124505062343975220369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34297416336708229316813579 51446124505062343975220369)
          ·
            refine ⟨38584593378796757981415277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51446124505062343975220369 38584593378796757981415277)
            ·
              refine ⟨14469222517048784243030729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38584593378796757981415277 14469222517048784243030729)
              ·
                refine ⟨10851916887786588182273047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14469222517048784243030729 10851916887786588182273047)
                ·
                  refine ⟨16277875331679882273409571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10851916887786588182273047 16277875331679882273409571)
                  ·
                    refine ⟨24416812997519823410114357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16277875331679882273409571 24416812997519823410114357)
                    ·
                      refine ⟨2289076218517483444698221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24416812997519823410114357 2289076218517483444698221)
                      ·
                        rfl

theorem cell23_4457960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_4457960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4457960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4457960 prefixEnd_4457960 := by exact prefixLift 4457960
  have htrace : WordTrace (prefixWord ++ tailWord_4457960) baseStart_4457960 baseEnd_4457960 := by
    simpa [prefixWord, tailWord_4457960, baseEnd_4457960] using wordTrace_append hprefix tailTrace_4457960
  have hstable : (prefixWord ++ tailWord_4457960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4457960).length < 2 ^ (prefixWord ++ tailWord_4457960).sum := by decide
  have hdescent : baseEnd_4457960 < baseStart_4457960 := by decide
  rcases family_descends (prefixWord ++ tailWord_4457960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4457974 : List Nat := [5, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4]
def baseStart_4457974 : Nat := 118140960795 + 4457974 * 2 ^ 59
def prefixEnd_4457974 : Nat := 4983230072969 + 3 ^ 40 * 4457974 * 2
def baseEnd_4457974 : Nat := 2289083407246646389923157

theorem tailTrace_4457974 : CollatzResearch.WordTrace tailWord_4457974 prefixEnd_4457974 2289083407246646389923157 := by
  unfold tailWord_4457974
  simp only [CollatzResearch.WordTrace]
  refine ⟨10162229346970564636827311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 108397113034352689459491317 10162229346970564636827311)
  ·
    refine ⟨15243344020455846955240967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10162229346970564636827311 15243344020455846955240967)
    ·
      refine ⟨22865016030683770432861451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15243344020455846955240967 22865016030683770432861451)
      ·
        refine ⟨34297524046025655649292177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22865016030683770432861451 34297524046025655649292177)
        ·
          refine ⟨25723143034519241736969133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34297524046025655649292177 25723143034519241736969133)
          ·
            refine ⟨9646178637944715651363425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25723143034519241736969133 9646178637944715651363425)
            ·
              refine ⟨7234633978458536738522569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9646178637944715651363425 7234633978458536738522569)
              ·
                refine ⟨5425975483843902553891927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7234633978458536738522569 5425975483843902553891927)
                ·
                  refine ⟨8138963225765853830837891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5425975483843902553891927 8138963225765853830837891)
                  ·
                    refine ⟨12208444838648780746256837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8138963225765853830837891 12208444838648780746256837)
                    ·
                      refine ⟨2289083407246646389923157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12208444838648780746256837 2289083407246646389923157)
                      ·
                        rfl

theorem cell23_4457974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_4457974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4457974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4457974 prefixEnd_4457974 := by exact prefixLift 4457974
  have htrace : WordTrace (prefixWord ++ tailWord_4457974) baseStart_4457974 baseEnd_4457974 := by
    simpa [prefixWord, tailWord_4457974, baseEnd_4457974] using wordTrace_append hprefix tailTrace_4457974
  have hstable : (prefixWord ++ tailWord_4457974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4457974).length < 2 ^ (prefixWord ++ tailWord_4457974).sum := by decide
  have hdescent : baseEnd_4457974 < baseStart_4457974 := by decide
  rcases family_descends (prefixWord ++ tailWord_4457974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4457980 : List Nat := [2, 2, 2, 1, 2, 1, 6, 7]
def baseStart_4457980 : Nat := 118140960795 + 4457980 * 2 ^ 59
def prefixEnd_4457980 : Nat := 4983230072969 + 3 ^ 40 * 4457980 * 2
def baseEnd_4457980 : Nat := 84780981041873087646227

theorem tailTrace_4457980 : CollatzResearch.WordTrace tailWord_4457980 prefixEnd_4457980 84780981041873087646227 := by
  unfold tailWord_4457980
  simp only [CollatzResearch.WordTrace]
  refine ⟨81297944194753648606977697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108397258926338198142636929 81297944194753648606977697)
  ·
    refine ⟨60973458146065236455233273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81297944194753648606977697 60973458146065236455233273)
    ·
      refine ⟨45730093609548927341424955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60973458146065236455233273 45730093609548927341424955)
      ·
        refine ⟨68595140414323391012137433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45730093609548927341424955 68595140414323391012137433)
        ·
          refine ⟨51446355310742543259103075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68595140414323391012137433 51446355310742543259103075)
          ·
            refine ⟨77169532966113814888654613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51446355310742543259103075 77169532966113814888654613)
            ·
              refine ⟨3617321857786585072905685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 77169532966113814888654613 3617321857786585072905685)
              ·
                refine ⟨84780981041873087646227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3617321857786585072905685 84780981041873087646227)
                ·
                  rfl

theorem cell23_4457980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 7].length) (baseStart_4457980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4457980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4457980 prefixEnd_4457980 := by exact prefixLift 4457980
  have htrace : WordTrace (prefixWord ++ tailWord_4457980) baseStart_4457980 baseEnd_4457980 := by
    simpa [prefixWord, tailWord_4457980, baseEnd_4457980] using wordTrace_append hprefix tailTrace_4457980
  have hstable : (prefixWord ++ tailWord_4457980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4457980).length < 2 ^ (prefixWord ++ tailWord_4457980).sum := by decide
  have hdescent : baseEnd_4457980 < baseStart_4457980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4457980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4458008 : List Nat := [2, 1, 2, 3, 5, 1, 1, 1, 3, 2, 2]
def baseStart_4458008 : Nat := 118140960795 + 4458008 * 2 ^ 59
def prefixEnd_4458008 : Nat := 4983230072969 + 3 ^ 40 * 4458008 * 2
def baseEnd_4458008 : Nat := 2289100865588899256898001

theorem tailTrace_4458008 : CollatzResearch.WordTrace tailWord_4458008 prefixEnd_4458008 2289100865588899256898001 := by
  unfold tailWord_4458008
  simp only [CollatzResearch.WordTrace]
  refine ⟨81298454816702928997987339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108397939755603905330649785 81298454816702928997987339)
  ·
    refine ⟨121947682225054393496981009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81298454816702928997987339 121947682225054393496981009)
    ·
      refine ⟨91460761668790795122735757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121947682225054393496981009 91460761668790795122735757)
      ·
        refine ⟨34297785625796548171025909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91460761668790795122735757 34297785625796548171025909)
        ·
          refine ⟨3215417402418426391033679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34297785625796548171025909 3215417402418426391033679)
          ·
            refine ⟨4823126103627639586550519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3215417402418426391033679 4823126103627639586550519)
            ·
              refine ⟨7234689155441459379825779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4823126103627639586550519 7234689155441459379825779)
              ·
                refine ⟨10852033733162189069738669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7234689155441459379825779 10852033733162189069738669)
                ·
                  refine ⟨4069512649935820901152001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10852033733162189069738669 4069512649935820901152001)
                  ·
                    refine ⟨3052134487451865675864001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4069512649935820901152001 3052134487451865675864001)
                    ·
                      refine ⟨2289100865588899256898001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3052134487451865675864001 2289100865588899256898001)
                      ·
                        rfl

theorem cell23_4458008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 3, 2, 2].length) (baseStart_4458008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4458008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4458008 prefixEnd_4458008 := by exact prefixLift 4458008
  have htrace : WordTrace (prefixWord ++ tailWord_4458008) baseStart_4458008 baseEnd_4458008 := by
    simpa [prefixWord, tailWord_4458008, baseEnd_4458008] using wordTrace_append hprefix tailTrace_4458008
  have hstable : (prefixWord ++ tailWord_4458008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4458008).length < 2 ^ (prefixWord ++ tailWord_4458008).sum := by decide
  have hdescent : baseEnd_4458008 < baseStart_4458008 := by decide
  rcases family_descends (prefixWord ++ tailWord_4458008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4458043 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 10]
def baseStart_4458043 : Nat := 118140960795 + 4458043 * 2 ^ 59
def prefixEnd_4458043 : Nat := 4983230072969 + 3 ^ 40 * 4458043 * 2
def baseEnd_4458043 : Nat := 2289118837411806619960339

theorem tailTrace_4458043 : CollatzResearch.WordTrace tailWord_4458043 prefixEnd_4458043 2289118837411806619960339 := by
  unfold tailWord_4458043
  simp only [CollatzResearch.WordTrace]
  refine ⟨162598186188279058973498783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108398790792186039315665855 162598186188279058973498783)
  ·
    refine ⟨243897279282418588460248175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162598186188279058973498783 243897279282418588460248175)
    ·
      refine ⟨365845918923627882690372263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243897279282418588460248175 365845918923627882690372263)
      ·
        refine ⟨548768878385441824035558395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 365845918923627882690372263 548768878385441824035558395)
        ·
          refine ⟨823153317578162736053337593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 548768878385441824035558395 823153317578162736053337593)
          ·
            refine ⟨617364988183622052040003195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 823153317578162736053337593 617364988183622052040003195)
            ·
              refine ⟨926047482275433078060004793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 617364988183622052040003195 926047482275433078060004793)
              ·
                refine ⟨694535611706574808545003595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 926047482275433078060004793 694535611706574808545003595)
                ·
                  refine ⟨1041803417559862212817505393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 694535611706574808545003595 1041803417559862212817505393)
                  ·
                    refine ⟨781352563169896659613129045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1041803417559862212817505393 781352563169896659613129045)
                    ·
                      refine ⟨2289118837411806619960339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 781352563169896659613129045 2289118837411806619960339)
                      ·
                        rfl

theorem cell23_4458043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 10].length) (baseStart_4458043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4458043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4458043 prefixEnd_4458043 := by exact prefixLift 4458043
  have htrace : WordTrace (prefixWord ++ tailWord_4458043) baseStart_4458043 baseEnd_4458043 := by
    simpa [prefixWord, tailWord_4458043, baseEnd_4458043] using wordTrace_append hprefix tailTrace_4458043
  have hstable : (prefixWord ++ tailWord_4458043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4458043).length < 2 ^ (prefixWord ++ tailWord_4458043).sum := by decide
  have hdescent : baseEnd_4458043 < baseStart_4458043 := by decide
  rcases family_descends (prefixWord ++ tailWord_4458043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4458047 : List Nat := [1, 1, 2, 2, 3, 3, 1, 1, 3, 4, 2]
def baseStart_4458047 : Nat := 118140960795 + 4458047 * 2 ^ 59
def prefixEnd_4458047 : Nat := 4983230072969 + 3 ^ 40 * 4458047 * 2
def baseEnd_4458047 : Nat := 2289120891334424604310321

theorem tailTrace_4458047 : CollatzResearch.WordTrace tailWord_4458047 prefixEnd_4458047 2289120891334424604310321 := by
  unfold tailWord_4458047
  simp only [CollatzResearch.WordTrace]
  refine ⟨162598332080264567656644395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108398888053509711771096263 162598332080264567656644395)
  ·
    refine ⟨243897498120396851484966593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162598332080264567656644395 243897498120396851484966593)
    ·
      refine ⟨182923123590297638613724945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243897498120396851484966593 182923123590297638613724945)
      ·
        refine ⟨137192342692723228960293709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182923123590297638613724945 137192342692723228960293709)
        ·
          refine ⟨51447128509771210860110141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137192342692723228960293709 51447128509771210860110141)
          ·
            refine ⟨19292673191164204072541303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51447128509771210860110141 19292673191164204072541303)
            ·
              refine ⟨28939009786746306108811955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19292673191164204072541303 28939009786746306108811955)
              ·
                refine ⟨43408514680119459163217933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28939009786746306108811955 43408514680119459163217933)
                ·
                  refine ⟨16278193005044797186206725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43408514680119459163217933 16278193005044797186206725)
                  ·
                    refine ⟨3052161188445899472413761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16278193005044797186206725 3052161188445899472413761)
                    ·
                      refine ⟨2289120891334424604310321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3052161188445899472413761 2289120891334424604310321)
                      ·
                        rfl

theorem cell23_4458047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 4, 2].length) (baseStart_4458047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4458047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4458047 prefixEnd_4458047 := by exact prefixLift 4458047
  have htrace : WordTrace (prefixWord ++ tailWord_4458047) baseStart_4458047 baseEnd_4458047 := by
    simpa [prefixWord, tailWord_4458047, baseEnd_4458047] using wordTrace_append hprefix tailTrace_4458047
  have hstable : (prefixWord ++ tailWord_4458047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4458047).length < 2 ^ (prefixWord ++ tailWord_4458047).sum := by decide
  have hdescent : baseEnd_4458047 < baseStart_4458047 := by decide
  rcases family_descends (prefixWord ++ tailWord_4458047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4458137 : List Nat := [1, 2, 1, 2, 1, 2, 2, 3, 1, 6, 2]
def baseStart_4458137 : Nat := 118140960795 + 4458137 * 2 ^ 59
def prefixEnd_4458137 : Nat := 4983230072969 + 3 ^ 40 * 4458137 * 2
def baseEnd_4458137 : Nat := 2289167104593329252184907

theorem tailTrace_4458137 : CollatzResearch.WordTrace tailWord_4458137 prefixEnd_4458137 2289167104593329252184907 := by
  unfold tailWord_4458137
  simp only [CollatzResearch.WordTrace]
  refine ⟨162601614649938513027420665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108401076433292342018280443 162601614649938513027420665)
  ·
    refine ⟨121951210987453884770565499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162601614649938513027420665 121951210987453884770565499)
    ·
      refine ⟨182926816481180827155848249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121951210987453884770565499 182926816481180827155848249)
      ·
        refine ⟨137195112360885620366886187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182926816481180827155848249 137195112360885620366886187)
        ·
          refine ⟨205792668541328430550329281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137195112360885620366886187 205792668541328430550329281)
          ·
            refine ⟨154344501405996322912746961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 205792668541328430550329281 154344501405996322912746961)
            ·
              refine ⟨115758376054497242184560221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154344501405996322912746961 115758376054497242184560221)
              ·
                refine ⟨43409391020436465819210083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115758376054497242184560221 43409391020436465819210083)
                ·
                  refine ⟨65114086530654698728815125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43409391020436465819210083 65114086530654698728815125)
                  ·
                    refine ⟨3052222806124439002913209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 65114086530654698728815125 3052222806124439002913209)
                    ·
                      refine ⟨2289167104593329252184907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3052222806124439002913209 2289167104593329252184907)
                      ·
                        rfl

theorem cell23_4458137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 6, 2].length) (baseStart_4458137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4458137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4458137 prefixEnd_4458137 := by exact prefixLift 4458137
  have htrace : WordTrace (prefixWord ++ tailWord_4458137) baseStart_4458137 baseEnd_4458137 := by
    simpa [prefixWord, tailWord_4458137, baseEnd_4458137] using wordTrace_append hprefix tailTrace_4458137
  have hstable : (prefixWord ++ tailWord_4458137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4458137).length < 2 ^ (prefixWord ++ tailWord_4458137).sum := by decide
  have hdescent : baseEnd_4458137 < baseStart_4458137 := by decide
  rcases family_descends (prefixWord ++ tailWord_4458137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4458147 : List Nat := [1, 1, 1, 4, 1, 1, 3, 4, 3, 4]
def baseStart_4458147 : Nat := 118140960795 + 4458147 * 2 ^ 59
def prefixEnd_4458147 : Nat := 4983230072969 + 3 ^ 40 * 4458147 * 2
def baseEnd_4458147 : Nat := 763057413133291404353287

theorem tailTrace_4458147 : CollatzResearch.WordTrace tailWord_4458147 prefixEnd_4458147 763057413133291404353287 := by
  unfold tailWord_4458147
  simp only [CollatzResearch.WordTrace]
  refine ⟨162601979379902284735284695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108401319586601523156856463 162601979379902284735284695)
  ·
    refine ⟨243902969069853427102927043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162601979379902284735284695 243902969069853427102927043)
    ·
      refine ⟨365854453604780140654390565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243902969069853427102927043 365854453604780140654390565)
      ·
        refine ⟨68597710050896276372698231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 365854453604780140654390565 68597710050896276372698231)
        ·
          refine ⟨102896565076344414559047347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68597710050896276372698231 102896565076344414559047347)
          ·
            refine ⟨154344847614516621838571021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102896565076344414559047347 154344847614516621838571021)
            ·
              refine ⟨57879317855443733189464133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 154344847614516621838571021 57879317855443733189464133)
              ·
                refine ⟨10852372097895699973024525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57879317855443733189464133 10852372097895699973024525)
                ·
                  refine ⟨4069639536710887489884197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10852372097895699973024525 4069639536710887489884197)
                  ·
                    refine ⟨763057413133291404353287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4069639536710887489884197 763057413133291404353287)
                    ·
                      rfl

theorem cell23_4458147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 3, 4].length) (baseStart_4458147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4458147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4458147 prefixEnd_4458147 := by exact prefixLift 4458147
  have htrace : WordTrace (prefixWord ++ tailWord_4458147) baseStart_4458147 baseEnd_4458147 := by
    simpa [prefixWord, tailWord_4458147, baseEnd_4458147] using wordTrace_append hprefix tailTrace_4458147
  have hstable : (prefixWord ++ tailWord_4458147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4458147).length < 2 ^ (prefixWord ++ tailWord_4458147).sum := by decide
  have hdescent : baseEnd_4458147 < baseStart_4458147 := by decide
  rcases family_descends (prefixWord ++ tailWord_4458147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4458160 : List Nat := [2, 1, 1, 1, 2, 1, 5, 2, 8]
def baseStart_4458160 : Nat := 118140960795 + 4458160 * 2 ^ 59
def prefixEnd_4458160 : Nat := 4983230072969 + 3 ^ 40 * 4458160 * 2
def baseEnd_4458160 : Nat := 254353212738709184688589

theorem tailTrace_4458160 : CollatzResearch.WordTrace tailWord_4458160 prefixEnd_4458160 254353212738709184688589 := by
  unfold tailWord_4458160
  simp only [CollatzResearch.WordTrace]
  refine ⟨81301226764427593977753967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108401635685903458637005289 81301226764427593977753967)
  ·
    refine ⟨121951840146641390966630951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81301226764427593977753967 121951840146641390966630951)
    ·
      refine ⟨182927760219962086449946427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121951840146641390966630951 182927760219962086449946427)
      ·
        refine ⟨274391640329943129674919641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182927760219962086449946427 274391640329943129674919641)
        ·
          refine ⟨205793730247457347256189731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 274391640329943129674919641 205793730247457347256189731)
          ·
            refine ⟨308690595371186020884284597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205793730247457347256189731 308690595371186020884284597)
            ·
              refine ⟨28939743316048689457901681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 308690595371186020884284597 28939743316048689457901681)
              ·
                refine ⟨21704807487036517093426261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28939743316048689457901681 21704807487036517093426261)
                ·
                  refine ⟨254353212738709184688589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21704807487036517093426261 254353212738709184688589)
                  ·
                    rfl

theorem cell23_4458160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 8].length) (baseStart_4458160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4458160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4458160 prefixEnd_4458160 := by exact prefixLift 4458160
  have htrace : WordTrace (prefixWord ++ tailWord_4458160) baseStart_4458160 baseEnd_4458160 := by
    simpa [prefixWord, tailWord_4458160, baseEnd_4458160] using wordTrace_append hprefix tailTrace_4458160
  have hstable : (prefixWord ++ tailWord_4458160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4458160).length < 2 ^ (prefixWord ++ tailWord_4458160).sum := by decide
  have hdescent : baseEnd_4458160 < baseStart_4458160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4458160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4458174 : List Nat := [4, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3]
def baseStart_4458174 : Nat := 118140960795 + 4458174 * 2 ^ 59
def prefixEnd_4458174 : Nat := 4983230072969 + 3 ^ 40 * 4458174 * 2
def baseEnd_4458174 : Nat := 2289186103377545607422237

theorem tailTrace_4458174 : CollatzResearch.WordTrace tailWord_4458174 prefixEnd_4458174 2289186103377545607422237 := by
  unfold tailWord_4458174
  simp only [CollatzResearch.WordTrace]
  refine ⟨20325370518850558543314697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108401976100536312231011717 20325370518850558543314697)
  ·
    refine ⟨15244027889137918907486023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20325370518850558543314697 15244027889137918907486023)
    ·
      refine ⟨22866041833706878361229035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15244027889137918907486023 22866041833706878361229035)
      ·
        refine ⟨34299062750560317541843553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22866041833706878361229035 34299062750560317541843553)
        ·
          refine ⟨25724297062920238156382665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34299062750560317541843553 25724297062920238156382665)
          ·
            refine ⟨19293222797190178617286999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25724297062920238156382665 19293222797190178617286999)
            ·
              refine ⟨28939834195785267925930499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19293222797190178617286999 28939834195785267925930499)
              ·
                refine ⟨43409751293677901888895749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28939834195785267925930499 43409751293677901888895749)
                ·
                  refine ⟨8139328367564606604167953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43409751293677901888895749 8139328367564606604167953)
                  ·
                    refine ⟨6104496275673454953125965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8139328367564606604167953 6104496275673454953125965)
                    ·
                      refine ⟨2289186103377545607422237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6104496275673454953125965 2289186103377545607422237)
                      ·
                        rfl

theorem cell23_4458174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_4458174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4458174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4458174 prefixEnd_4458174 := by exact prefixLift 4458174
  have htrace : WordTrace (prefixWord ++ tailWord_4458174) baseStart_4458174 baseEnd_4458174 := by
    simpa [prefixWord, tailWord_4458174, baseEnd_4458174] using wordTrace_append hprefix tailTrace_4458174
  have hstable : (prefixWord ++ tailWord_4458174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4458174).length < 2 ^ (prefixWord ++ tailWord_4458174).sum := by decide
  have hdescent : baseEnd_4458174 < baseStart_4458174 := by decide
  rcases family_descends (prefixWord ++ tailWord_4458174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4458178 : List Nat := [3, 5, 1, 2, 1, 1, 1, 1, 1, 2, 5]
def baseStart_4458178 : Nat := 118140960795 + 4458178 * 2 ^ 59
def prefixEnd_4458178 : Nat := 4983230072969 + 3 ^ 40 * 4458178 * 2
def baseEnd_4458178 : Nat := 2289188157300163591772219

theorem tailTrace_4458178 : CollatzResearch.WordTrace tailWord_4458178 prefixEnd_4458178 2289188157300163591772219 := by
  unfold tailWord_4458178
  simp only [CollatzResearch.WordTrace]
  refine ⟨40650777510697494257415797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108402073361859984686442125 40650777510697494257415797)
  ·
    refine ⟨3811010391627890086632731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40650777510697494257415797 3811010391627890086632731)
    ·
      refine ⟨5716515587441835129949097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3811010391627890086632731 5716515587441835129949097)
      ·
        refine ⟨4287386690581376347461823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5716515587441835129949097 4287386690581376347461823)
        ·
          refine ⟨6431080035872064521192735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4287386690581376347461823 6431080035872064521192735)
          ·
            refine ⟨9646620053808096781789103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6431080035872064521192735 9646620053808096781789103)
            ·
              refine ⟨14469930080712145172683655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9646620053808096781789103 14469930080712145172683655)
              ·
                refine ⟨21704895121068217759025483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14469930080712145172683655 21704895121068217759025483)
                ·
                  refine ⟨32557342681602326638538225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21704895121068217759025483 32557342681602326638538225)
                  ·
                    refine ⟨24418007011201744978903669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32557342681602326638538225 24418007011201744978903669)
                    ·
                      refine ⟨2289188157300163591772219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24418007011201744978903669 2289188157300163591772219)
                      ·
                        rfl

theorem cell23_4458178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_4458178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4458178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4458178 prefixEnd_4458178 := by exact prefixLift 4458178
  have htrace : WordTrace (prefixWord ++ tailWord_4458178) baseStart_4458178 baseEnd_4458178 := by
    simpa [prefixWord, tailWord_4458178, baseEnd_4458178] using wordTrace_append hprefix tailTrace_4458178
  have hstable : (prefixWord ++ tailWord_4458178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4458178).length < 2 ^ (prefixWord ++ tailWord_4458178).sum := by decide
  have hdescent : baseEnd_4458178 < baseStart_4458178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4458178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4458194 : List Nat := [3, 2, 2, 2, 2, 2, 1, 3, 6]
def baseStart_4458194 : Nat := 118140960795 + 4458194 * 2 ^ 59
def prefixEnd_4458194 : Nat := 4983230072969 + 3 ^ 40 * 4458194 * 2
def baseEnd_4458194 : Nat := 254355152554515058796905

theorem tailTrace_4458194 : CollatzResearch.WordTrace tailWord_4458194 prefixEnd_4458194 254355152554515058796905 := by
  unfold tailWord_4458194
  simp only [CollatzResearch.WordTrace]
  refine ⟨40650923402683002940561409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108402462407154674508163757 40650923402683002940561409)
  ·
    refine ⟨30488192552012252205421057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40650923402683002940561409 30488192552012252205421057)
    ·
      refine ⟨22866144414009189154065793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30488192552012252205421057 22866144414009189154065793)
      ·
        refine ⟨17149608310506891865549345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22866144414009189154065793 17149608310506891865549345)
        ·
          refine ⟨12862206232880168899162009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17149608310506891865549345 12862206232880168899162009)
          ·
            refine ⟨9646654674660126674371507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12862206232880168899162009 9646654674660126674371507)
            ·
              refine ⟨14469982011990190011557261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9646654674660126674371507 14469982011990190011557261)
              ·
                refine ⟨5426243254496321254333973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14469982011990190011557261 5426243254496321254333973)
                ·
                  refine ⟨254355152554515058796905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5426243254496321254333973 254355152554515058796905)
                  ·
                    rfl

theorem cell23_4458194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 3, 6].length) (baseStart_4458194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4458194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4458194 prefixEnd_4458194 := by exact prefixLift 4458194
  have htrace : WordTrace (prefixWord ++ tailWord_4458194) baseStart_4458194 baseEnd_4458194 := by
    simpa [prefixWord, tailWord_4458194, baseEnd_4458194] using wordTrace_append hprefix tailTrace_4458194
  have hstable : (prefixWord ++ tailWord_4458194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4458194).length < 2 ^ (prefixWord ++ tailWord_4458194).sum := by decide
  have hdescent : baseEnd_4458194 < baseStart_4458194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4458194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4458207 : List Nat := [1, 1, 2, 3, 2, 2, 3, 1, 3, 5]
def baseStart_4458207 : Nat := 118140960795 + 4458207 * 2 ^ 59
def prefixEnd_4458207 : Nat := 4983230072969 + 3 ^ 40 * 4458207 * 2
def baseEnd_4458207 : Nat := 763067682746381326103195

theorem tailTrace_4458207 : CollatzResearch.WordTrace tailWord_4458207 prefixEnd_4458207 763067682746381326103195 := by
  unfold tailWord_4458207
  simp only [CollatzResearch.WordTrace]
  refine ⟨162604167759684914982468875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108402778506456609988312583 162604167759684914982468875)
  ·
    refine ⟨243906251639527372473703313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162604167759684914982468875 243906251639527372473703313)
    ·
      refine ⟨182929688729645529355277485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243906251639527372473703313 182929688729645529355277485)
      ·
        refine ⟨68598633273617073508229057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 182929688729645529355277485 68598633273617073508229057)
        ·
          refine ⟨51448974955212805131171793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68598633273617073508229057 51448974955212805131171793)
          ·
            refine ⟨38586731216409603848378845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51448974955212805131171793 38586731216409603848378845)
            ·
              refine ⟨14470024206153601443142067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38586731216409603848378845 14470024206153601443142067)
              ·
                refine ⟨21705036309230402164713101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14470024206153601443142067 21705036309230402164713101)
                ·
                  refine ⟨8139388615961400811767413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21705036309230402164713101 8139388615961400811767413)
                  ·
                    refine ⟨763067682746381326103195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8139388615961400811767413 763067682746381326103195)
                    ·
                      rfl

theorem cell23_4458207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 3, 5].length) (baseStart_4458207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4458207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4458207 prefixEnd_4458207 := by exact prefixLift 4458207
  have htrace : WordTrace (prefixWord ++ tailWord_4458207) baseStart_4458207 baseEnd_4458207 := by
    simpa [prefixWord, tailWord_4458207, baseEnd_4458207] using wordTrace_append hprefix tailTrace_4458207
  have hstable : (prefixWord ++ tailWord_4458207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4458207).length < 2 ^ (prefixWord ++ tailWord_4458207).sum := by decide
  have hdescent : baseEnd_4458207 < baseStart_4458207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4458207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4458228 : List Nat := [2, 6, 1, 1, 1, 2, 2, 2, 6]
def baseStart_4458228 : Nat := 118140960795 + 4458228 * 2 ^ 59
def prefixEnd_4458228 : Nat := 4983230072969 + 3 ^ 40 * 4458228 * 2
def baseEnd_4458228 : Nat := 254357092370320932905221

theorem tailTrace_4458228 : CollatzResearch.WordTrace tailWord_4458228 prefixEnd_4458228 254357092370320932905221 := by
  unfold tailWord_4458228
  simp only [CollatzResearch.WordTrace]
  refine ⟨81302466846304417784491669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108403289128405890379322225 81302466846304417784491669)
  ·
    refine ⟨3811053133420519583648047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 81302466846304417784491669 3811053133420519583648047)
    ·
      refine ⟨5716579700130779375472071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3811053133420519583648047 5716579700130779375472071)
      ·
        refine ⟨8574869550196169063208107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5716579700130779375472071 8574869550196169063208107)
        ·
          refine ⟨12862304325294253594812161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8574869550196169063208107 12862304325294253594812161)
          ·
            refine ⟨9646728243970690196109121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12862304325294253594812161 9646728243970690196109121)
            ·
              refine ⟨7235046182978017647081841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9646728243970690196109121 7235046182978017647081841)
              ·
                refine ⟨5426284637233513235311381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7235046182978017647081841 5426284637233513235311381)
                ·
                  refine ⟨254357092370320932905221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5426284637233513235311381 254357092370320932905221)
                  ·
                    rfl

theorem cell23_4458228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_4458228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4458228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4458228 prefixEnd_4458228 := by exact prefixLift 4458228
  have htrace : WordTrace (prefixWord ++ tailWord_4458228) baseStart_4458228 baseEnd_4458228 := by
    simpa [prefixWord, tailWord_4458228, baseEnd_4458228] using wordTrace_append hprefix tailTrace_4458228
  have hstable : (prefixWord ++ tailWord_4458228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4458228).length < 2 ^ (prefixWord ++ tailWord_4458228).sum := by decide
  have hdescent : baseEnd_4458228 < baseStart_4458228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4458228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4458244 : List Nat := [2, 3, 2, 2, 1, 2, 1, 2, 3, 1, 4]
def baseStart_4458244 : Nat := 118140960795 + 4458244 * 2 ^ 59
def prefixEnd_4458244 : Nat := 4983230072969 + 3 ^ 40 * 4458244 * 2
def baseEnd_4458244 : Nat := 2289222047023360333546915

theorem tailTrace_4458244 : CollatzResearch.WordTrace tailWord_4458244 prefixEnd_4458244 2289222047023360333546915 := by
  unfold tailWord_4458244
  simp only [CollatzResearch.WordTrace]
  refine ⟨81302758630275435150782893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108403678173700580201043857 81302758630275435150782893)
  ·
    refine ⟨30488534486353288181543585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81302758630275435150782893 30488534486353288181543585)
    ·
      refine ⟨22866400864764966136157689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30488534486353288181543585 22866400864764966136157689)
      ·
        refine ⟨17149800648573724602118267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22866400864764966136157689 17149800648573724602118267)
        ·
          refine ⟨25724700972860586903177401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17149800648573724602118267 25724700972860586903177401)
          ·
            refine ⟨19293525729645440177383051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25724700972860586903177401 19293525729645440177383051)
            ·
              refine ⟨28940288594468160266074577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19293525729645440177383051 28940288594468160266074577)
              ·
                refine ⟨21705216445851120199555933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28940288594468160266074577 21705216445851120199555933)
                ·
                  refine ⟨8139456167194170074833475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21705216445851120199555933 8139456167194170074833475)
                  ·
                    refine ⟨12209184250791255112250213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8139456167194170074833475 12209184250791255112250213)
                    ·
                      refine ⟨2289222047023360333546915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12209184250791255112250213 2289222047023360333546915)
                      ·
                        rfl

theorem cell23_4458244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_4458244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4458244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4458244 prefixEnd_4458244 := by exact prefixLift 4458244
  have htrace : WordTrace (prefixWord ++ tailWord_4458244) baseStart_4458244 baseEnd_4458244 := by
    simpa [prefixWord, tailWord_4458244, baseEnd_4458244] using wordTrace_append hprefix tailTrace_4458244
  have hstable : (prefixWord ++ tailWord_4458244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4458244).length < 2 ^ (prefixWord ++ tailWord_4458244).sum := by decide
  have hdescent : baseEnd_4458244 < baseStart_4458244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4458244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4458261 : List Nat := [1, 3, 2, 1, 2, 3, 1, 1, 5, 2, 2]
def baseStart_4458261 : Nat := 118140960795 + 4458261 * 2 ^ 59
def prefixEnd_4458261 : Nat := 4983230072969 + 3 ^ 40 * 4458261 * 2
def baseEnd_4458261 : Nat := 2289230776194486767034337

theorem tailTrace_4458261 : CollatzResearch.WordTrace tailWord_4458261 prefixEnd_4458261 2289230776194486767034337 := by
  unfold tailWord_4458261
  simp only [CollatzResearch.WordTrace]
  refine ⟨162606137301489282204934637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108404091534326188136623091 162606137301489282204934637)
  ·
    refine ⟨60977301488058480826850489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162606137301489282204934637 60977301488058480826850489)
    ·
      refine ⟨45732976116043860620137867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60977301488058480826850489 45732976116043860620137867)
      ·
        refine ⟨68599464174065790930206801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45732976116043860620137867 68599464174065790930206801)
        ·
          refine ⟨51449598130549343197655101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68599464174065790930206801 51449598130549343197655101)
          ·
            refine ⟨19293599298956003699120663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51449598130549343197655101 19293599298956003699120663)
            ·
              refine ⟨28940398948434005548680995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19293599298956003699120663 28940398948434005548680995)
              ·
                refine ⟨43410598422651008323021493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28940398948434005548680995 43410598422651008323021493)
                ·
                  refine ⟨4069743602123532030283265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43410598422651008323021493 4069743602123532030283265)
                  ·
                    refine ⟨3052307701592649022712449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4069743602123532030283265 3052307701592649022712449)
                    ·
                      refine ⟨2289230776194486767034337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3052307701592649022712449 2289230776194486767034337)
                      ·
                        rfl

theorem cell23_4458261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 5, 2, 2].length) (baseStart_4458261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4458261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4458261 prefixEnd_4458261 := by exact prefixLift 4458261
  have htrace : WordTrace (prefixWord ++ tailWord_4458261) baseStart_4458261 baseEnd_4458261 := by
    simpa [prefixWord, tailWord_4458261, baseEnd_4458261] using wordTrace_append hprefix tailTrace_4458261
  have hstable : (prefixWord ++ tailWord_4458261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4458261).length < 2 ^ (prefixWord ++ tailWord_4458261).sum := by decide
  have hdescent : baseEnd_4458261 < baseStart_4458261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4458261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4458264 : List Nat := [2, 1, 2, 3, 1, 1, 4, 1, 3, 2, 3]
def baseStart_4458264 : Nat := 118140960795 + 4458264 * 2 ^ 59
def prefixEnd_4458264 : Nat := 4983230072969 + 3 ^ 40 * 4458264 * 2
def baseEnd_4458264 : Nat := 2289232316636450255296823

theorem tailTrace_4458264 : CollatzResearch.WordTrace tailWord_4458264 prefixEnd_4458264 2289232316636450255296823 := by
  unfold tailWord_4458264
  simp only [CollatzResearch.WordTrace]
  refine ⟨81303123360239206858646923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108404164480318942478195897 81303123360239206858646923)
  ·
    refine ⟨121954685040358810287970385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81303123360239206858646923 121954685040358810287970385)
    ·
      refine ⟨91466013780269107715977789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121954685040358810287970385 91466013780269107715977789)
      ·
        refine ⟨34299755167600915393491671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91466013780269107715977789 34299755167600915393491671)
        ·
          refine ⟨51449632751401373090237507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34299755167600915393491671 51449632751401373090237507)
          ·
            refine ⟨77174449127102059635356261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51449632751401373090237507 77174449127102059635356261)
            ·
              refine ⟨14470209211331636181629299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77174449127102059635356261 14470209211331636181629299)
              ·
                refine ⟨21705313816997454272443949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14470209211331636181629299 21705313816997454272443949)
                ·
                  refine ⟨8139492681374045352166481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21705313816997454272443949 8139492681374045352166481)
                  ·
                    refine ⟨6104619511030534014124861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8139492681374045352166481 6104619511030534014124861)
                    ·
                      refine ⟨2289232316636450255296823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6104619511030534014124861 2289232316636450255296823)
                      ·
                        rfl

theorem cell23_4458264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_4458264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4458264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4458264 prefixEnd_4458264 := by exact prefixLift 4458264
  have htrace : WordTrace (prefixWord ++ tailWord_4458264) baseStart_4458264 baseEnd_4458264 := by
    simpa [prefixWord, tailWord_4458264, baseEnd_4458264] using wordTrace_append hprefix tailTrace_4458264
  have hstable : (prefixWord ++ tailWord_4458264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4458264).length < 2 ^ (prefixWord ++ tailWord_4458264).sum := by decide
  have hdescent : baseEnd_4458264 < baseStart_4458264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4458264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4458274 : List Nat := [3, 3, 1, 1, 2, 1, 1, 4, 1, 2, 4]
def baseStart_4458274 : Nat := 118140960795 + 4458274 * 2 ^ 59
def prefixEnd_4458274 : Nat := 4983230072969 + 3 ^ 40 * 4458274 * 2
def baseEnd_4458274 : Nat := 2289237451442995216171777

theorem tailTrace_4458274 : CollatzResearch.WordTrace tailWord_4458274 prefixEnd_4458274 2289237451442995216171777 := by
  unfold tailWord_4458274
  simp only [CollatzResearch.WordTrace]
  refine ⟨40651652862610546356289469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108404407633628123616771917 40651652862610546356289469)
  ·
    refine ⟨15244369823478954883608551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40651652862610546356289469 15244369823478954883608551)
    ·
      refine ⟨22866554735218432325412827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15244369823478954883608551 22866554735218432325412827)
      ·
        refine ⟨34299832102827648488119241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22866554735218432325412827 34299832102827648488119241)
        ·
          refine ⟨25724874077120736366089431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34299832102827648488119241 25724874077120736366089431)
          ·
            refine ⟨38587311115681104549134147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25724874077120736366089431 38587311115681104549134147)
            ·
              refine ⟨57880966673521656823701221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38587311115681104549134147 57880966673521656823701221)
              ·
                refine ⟨10852681251285310654443979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57880966673521656823701221 10852681251285310654443979)
                ·
                  refine ⟨16279021876927965981665969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10852681251285310654443979 16279021876927965981665969)
                  ·
                    refine ⟨12209266407695974486249477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16279021876927965981665969 12209266407695974486249477)
                    ·
                      refine ⟨2289237451442995216171777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12209266407695974486249477 2289237451442995216171777)
                      ·
                        rfl

theorem cell23_4458274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_4458274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4458274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4458274 prefixEnd_4458274 := by exact prefixLift 4458274
  have htrace : WordTrace (prefixWord ++ tailWord_4458274) baseStart_4458274 baseEnd_4458274 := by
    simpa [prefixWord, tailWord_4458274, baseEnd_4458274] using wordTrace_append hprefix tailTrace_4458274
  have hstable : (prefixWord ++ tailWord_4458274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4458274).length < 2 ^ (prefixWord ++ tailWord_4458274).sum := by decide
  have hdescent : baseEnd_4458274 < baseStart_4458274 := by decide
  rcases family_descends (prefixWord ++ tailWord_4458274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4458311 : List Nat := [1, 1, 4, 1, 2, 1, 2, 5, 2, 1, 3]
def baseStart_4458311 : Nat := 118140960795 + 4458311 * 2 ^ 59
def prefixEnd_4458311 : Nat := 4983230072969 + 3 ^ 40 * 4458311 * 2
def baseEnd_4458311 : Nat := 2289256450227211571409107

theorem tailTrace_4458311 : CollatzResearch.WordTrace tailWord_4458311 prefixEnd_4458311 2289256450227211571409107 := by
  unfold tailWord_4458311
  simp only [CollatzResearch.WordTrace]
  refine ⟨162607960951308140744254787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108405307300872093829503191 162607960951308140744254787)
  ·
    refine ⟨243911941426962211116382181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162607960951308140744254787 243911941426962211116382181)
    ·
      refine ⟨45733489017555414584321659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 243911941426962211116382181 45733489017555414584321659)
      ·
        refine ⟨68600233526333121876482489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45733489017555414584321659 68600233526333121876482489)
        ·
          refine ⟨51450175144749841407361867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68600233526333121876482489 51450175144749841407361867)
          ·
            refine ⟨77175262717124762111042801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51450175144749841407361867 77175262717124762111042801)
            ·
              refine ⟨57881447037843571583282101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77175262717124762111042801 57881447037843571583282101)
              ·
                refine ⟨5426385659797834835932697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57881447037843571583282101 5426385659797834835932697)
                ·
                  refine ⟨4069789244848376126949523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5426385659797834835932697 4069789244848376126949523)
                  ·
                    refine ⟨6104683867272564190424285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4069789244848376126949523 6104683867272564190424285)
                    ·
                      refine ⟨2289256450227211571409107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6104683867272564190424285 2289256450227211571409107)
                      ·
                        rfl

theorem cell23_4458311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 5, 2, 1, 3].length) (baseStart_4458311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4458311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4458311 prefixEnd_4458311 := by exact prefixLift 4458311
  have htrace : WordTrace (prefixWord ++ tailWord_4458311) baseStart_4458311 baseEnd_4458311 := by
    simpa [prefixWord, tailWord_4458311, baseEnd_4458311] using wordTrace_append hprefix tailTrace_4458311
  have hstable : (prefixWord ++ tailWord_4458311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4458311).length < 2 ^ (prefixWord ++ tailWord_4458311).sum := by decide
  have hdescent : baseEnd_4458311 < baseStart_4458311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4458311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4458324 : List Nat := [2, 4, 1, 1, 3, 1, 1, 1, 2, 2, 5]
def baseStart_4458324 : Nat := 118140960795 + 4458324 * 2 ^ 59
def prefixEnd_4458324 : Nat := 4983230072969 + 3 ^ 40 * 4458324 * 2
def baseEnd_4458324 : Nat := 2289263125475720020546547

theorem tailTrace_4458324 : CollatzResearch.WordTrace tailWord_4458324 prefixEnd_4458324 2289263125475720020546547 := by
  unfold tailWord_4458324
  simp only [CollatzResearch.WordTrace]
  refine ⟨81304217550130521982239013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108405623400174029309652017 81304217550130521982239013)
  ·
    refine ⟨15244540790649472871669815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81304217550130521982239013 15244540790649472871669815)
    ·
      refine ⟨22866811185974209307504723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15244540790649472871669815 22866811185974209307504723)
      ·
        refine ⟨34300216778961313961257085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22866811185974209307504723 34300216778961313961257085)
        ·
          refine ⟨12862581292110492735471407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34300216778961313961257085 12862581292110492735471407)
          ·
            refine ⟨19293871938165739103207111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12862581292110492735471407 19293871938165739103207111)
            ·
              refine ⟨28940807907248608654810667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19293871938165739103207111 28940807907248608654810667)
              ·
                refine ⟨43411211860872912982216001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28940807907248608654810667 43411211860872912982216001)
                ·
                  refine ⟨32558408895654684736662001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43411211860872912982216001 32558408895654684736662001)
                  ·
                    refine ⟨24418806671741013552496501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32558408895654684736662001 24418806671741013552496501)
                    ·
                      refine ⟨2289263125475720020546547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24418806671741013552496501 2289263125475720020546547)
                      ·
                        rfl

theorem cell23_4458324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_4458324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4458324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4458324 prefixEnd_4458324 := by exact prefixLift 4458324
  have htrace : WordTrace (prefixWord ++ tailWord_4458324) baseStart_4458324 baseEnd_4458324 := by
    simpa [prefixWord, tailWord_4458324, baseEnd_4458324] using wordTrace_append hprefix tailTrace_4458324
  have hstable : (prefixWord ++ tailWord_4458324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4458324).length < 2 ^ (prefixWord ++ tailWord_4458324).sum := by decide
  have hdescent : baseEnd_4458324 < baseStart_4458324 := by decide
  rcases family_descends (prefixWord ++ tailWord_4458324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4458354 : List Nat := [3, 2, 1, 2, 1, 1, 1, 3, 2, 4, 3]
def baseStart_4458354 : Nat := 118140960795 + 4458354 * 2 ^ 59
def prefixEnd_4458354 : Nat := 4983230072969 + 3 ^ 40 * 4458354 * 2
def baseEnd_4458354 : Nat := 2289278529895354903171409

theorem tailTrace_4458354 : CollatzResearch.WordTrace tailWord_4458354 prefixEnd_4458354 2289278529895354903171409 := by
  unfold tailWord_4458354
  simp only [CollatzResearch.WordTrace]
  refine ⟨40652382322538089772017529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108406352860101572725380077 40652382322538089772017529)
  ·
    refine ⟨30489286741903567329013147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40652382322538089772017529 30489286741903567329013147)
    ·
      refine ⟨45733930112855350993519721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30489286741903567329013147 45733930112855350993519721)
      ·
        refine ⟨34300447584641513245139791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45733930112855350993519721 34300447584641513245139791)
        ·
          refine ⟨51450671376962269867709687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34300447584641513245139791 51450671376962269867709687)
          ·
            refine ⟨77176007065443404801564531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51450671376962269867709687 77176007065443404801564531)
            ·
              refine ⟨115764010598165107202346797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77176007065443404801564531 115764010598165107202346797)
              ·
                refine ⟨43411503974311915200880049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115764010598165107202346797 43411503974311915200880049)
                ·
                  refine ⟨32558627980733936400660037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43411503974311915200880049 32558627980733936400660037)
                  ·
                    refine ⟨6104742746387613075123757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32558627980733936400660037 6104742746387613075123757)
                    ·
                      refine ⟨2289278529895354903171409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6104742746387613075123757 2289278529895354903171409)
                      ·
                        rfl

theorem cell23_4458354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_4458354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4458354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4458354 prefixEnd_4458354 := by exact prefixLift 4458354
  have htrace : WordTrace (prefixWord ++ tailWord_4458354) baseStart_4458354 baseEnd_4458354 := by
    simpa [prefixWord, tailWord_4458354, baseEnd_4458354] using wordTrace_append hprefix tailTrace_4458354
  have hstable : (prefixWord ++ tailWord_4458354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4458354).length < 2 ^ (prefixWord ++ tailWord_4458354).sum := by decide
  have hdescent : baseEnd_4458354 < baseStart_4458354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4458354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4458368 : List Nat := [2, 1, 1, 2, 1, 2, 5, 3, 2, 2, 2]
def baseStart_4458368 : Nat := 118140960795 + 4458368 * 2 ^ 59
def prefixEnd_4458368 : Nat := 4983230072969 + 3 ^ 40 * 4458368 * 2
def baseEnd_4458368 : Nat := 2289285718624517848396345

theorem tailTrace_4458368 : CollatzResearch.WordTrace tailWord_4458368 prefixEnd_4458368 2289285718624517848396345 := by
  unfold tailWord_4458368
  simp only [CollatzResearch.WordTrace]
  refine ⟨81305019956050819739539879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108406693274734426319386505 81305019956050819739539879)
  ·
    refine ⟨121957529934076229609309819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81305019956050819739539879 121957529934076229609309819)
    ·
      refine ⟨182936294901114344413964729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121957529934076229609309819 182936294901114344413964729)
      ·
        refine ⟨137202221175835758310473547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182936294901114344413964729 137202221175835758310473547)
        ·
          refine ⟨205803331763753637465710321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137202221175835758310473547 205803331763753637465710321)
          ·
            refine ⟨154352498822815228099282741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 205803331763753637465710321 154352498822815228099282741)
            ·
              refine ⟨14470546764638927634307757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 154352498822815228099282741 14470546764638927634307757)
              ·
                refine ⟨5426455036739597862865409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14470546764638927634307757 5426455036739597862865409)
                ·
                  refine ⟨4069841277554698397149057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5426455036739597862865409 4069841277554698397149057)
                  ·
                    refine ⟨3052380958166023797861793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4069841277554698397149057 3052380958166023797861793)
                    ·
                      refine ⟨2289285718624517848396345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3052380958166023797861793 2289285718624517848396345)
                      ·
                        rfl

theorem cell23_4458368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 3, 2, 2, 2].length) (baseStart_4458368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4458368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4458368 prefixEnd_4458368 := by exact prefixLift 4458368
  have htrace : WordTrace (prefixWord ++ tailWord_4458368) baseStart_4458368 baseEnd_4458368 := by
    simpa [prefixWord, tailWord_4458368, baseEnd_4458368] using wordTrace_append hprefix tailTrace_4458368
  have hstable : (prefixWord ++ tailWord_4458368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4458368).length < 2 ^ (prefixWord ++ tailWord_4458368).sum := by decide
  have hdescent : baseEnd_4458368 < baseStart_4458368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4458368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4458387 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 5, 7]
def baseStart_4458387 : Nat := 118140960795 + 4458387 * 2 ^ 59
def prefixEnd_4458387 : Nat := 4983230072969 + 3 ^ 40 * 4458387 * 2
def baseEnd_4458387 : Nat := 763098491585651091352919

theorem tailTrace_4458387 : CollatzResearch.WordTrace tailWord_4458387 prefixEnd_4458387 763098491585651091352919 := by
  unfold tailWord_4458387
  simp only [CollatzResearch.WordTrace]
  refine ⟨162610732899032805724021415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108407155266021870482680943 162610732899032805724021415)
  ·
    refine ⟨243916099348549208586032123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162610732899032805724021415 243916099348549208586032123)
    ·
      refine ⟨365874149022823812879048185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243916099348549208586032123 365874149022823812879048185)
      ·
        refine ⟨274405611767117859659286139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 365874149022823812879048185 274405611767117859659286139)
        ·
          refine ⟨411608417650676789488929209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 274405611767117859659286139 411608417650676789488929209)
          ·
            refine ⟨308706313238007592116696907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 411608417650676789488929209 308706313238007592116696907)
            ·
              refine ⟨463059469857011388175045361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 308706313238007592116696907 463059469857011388175045361)
              ·
                refine ⟨347294602392758541131284021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 463059469857011388175045361 347294602392758541131284021)
                ·
                  refine ⟨32558868974321113231057877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 347294602392758541131284021 32558868974321113231057877)
                  ·
                    refine ⟨763098491585651091352919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32558868974321113231057877 763098491585651091352919)
                    ·
                      rfl

theorem cell23_4458387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 7].length) (baseStart_4458387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4458387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4458387 prefixEnd_4458387 := by exact prefixLift 4458387
  have htrace : WordTrace (prefixWord ++ tailWord_4458387) baseStart_4458387 baseEnd_4458387 := by
    simpa [prefixWord, tailWord_4458387, baseEnd_4458387] using wordTrace_append hprefix tailTrace_4458387
  have hstable : (prefixWord ++ tailWord_4458387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4458387).length < 2 ^ (prefixWord ++ tailWord_4458387).sum := by decide
  have hdescent : baseEnd_4458387 < baseStart_4458387 := by decide
  rcases family_descends (prefixWord ++ tailWord_4458387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4458402 : List Nat := [3, 3, 1, 2, 3, 1, 2, 2, 2, 2, 2]
def baseStart_4458402 : Nat := 118140960795 + 4458402 * 2 ^ 59
def prefixEnd_4458402 : Nat := 4983230072969 + 3 ^ 40 * 4458402 * 2
def baseEnd_4458402 : Nat := 2289303176966770715371189

theorem tailTrace_4458402 : CollatzResearch.WordTrace tailWord_4458402 prefixEnd_4458402 2289303176966770715371189 := by
  unfold tailWord_4458402
  simp only [CollatzResearch.WordTrace]
  refine ⟨40652819998494615821454365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108407519995985642190544973 40652819998494615821454365)
  ·
    refine ⟨15244807499435480933045387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40652819998494615821454365 15244807499435480933045387)
    ·
      refine ⟨22867211249153221399568081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15244807499435480933045387 22867211249153221399568081)
      ·
        refine ⟨17150408436864916049676061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22867211249153221399568081 17150408436864916049676061)
        ·
          refine ⟨6431403163824343518628523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17150408436864916049676061 6431403163824343518628523)
          ·
            refine ⟨9647104745736515277942785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6431403163824343518628523 9647104745736515277942785)
            ·
              refine ⟨7235328559302386458457089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9647104745736515277942785 7235328559302386458457089)
              ·
                refine ⟨5426496419476789843842817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7235328559302386458457089 5426496419476789843842817)
                ·
                  refine ⟨4069872314607592382882113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5426496419476789843842817 4069872314607592382882113)
                  ·
                    refine ⟨3052404235955694287161585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4069872314607592382882113 3052404235955694287161585)
                    ·
                      refine ⟨2289303176966770715371189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3052404235955694287161585 2289303176966770715371189)
                      ·
                        rfl

theorem cell23_4458402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_4458402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4458402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4458402 prefixEnd_4458402 := by exact prefixLift 4458402
  have htrace : WordTrace (prefixWord ++ tailWord_4458402) baseStart_4458402 baseEnd_4458402 := by
    simpa [prefixWord, tailWord_4458402, baseEnd_4458402] using wordTrace_append hprefix tailTrace_4458402
  have hstable : (prefixWord ++ tailWord_4458402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4458402).length < 2 ^ (prefixWord ++ tailWord_4458402).sum := by decide
  have hdescent : baseEnd_4458402 < baseStart_4458402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4458402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4458424 : List Nat := [2, 1, 2, 1, 2, 3, 2, 2, 1, 3, 4]
def baseStart_4458424 : Nat := 118140960795 + 4458424 * 2 ^ 59
def prefixEnd_4458424 : Nat := 4983230072969 + 3 ^ 40 * 4458424 * 2
def baseEnd_4458424 : Nat := 2289314473541169629296087

theorem tailTrace_4458424 : CollatzResearch.WordTrace tailWord_4458424 prefixEnd_4458424 2289314473541169629296087 := by
  unfold tailWord_4458424
  simp only [CollatzResearch.WordTrace]
  refine ⟨81306041199949380521559163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108408054933265840695412217 81306041199949380521559163)
  ·
    refine ⟨121959061799924070782338745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81306041199949380521559163 121959061799924070782338745)
    ·
      refine ⟨91469296349943053086754059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121959061799924070782338745 91469296349943053086754059)
      ·
        refine ⟨137203944524914579630131089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91469296349943053086754059 137203944524914579630131089)
        ·
          refine ⟨102902958393685934722598317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137203944524914579630131089 102902958393685934722598317)
          ·
            refine ⟨38588609397632225520974369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102902958393685934722598317 38588609397632225520974369)
            ·
              refine ⟨28941457048224169140730777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38588609397632225520974369 28941457048224169140730777)
              ·
                refine ⟨21706092786168126855548083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28941457048224169140730777 21706092786168126855548083)
                ·
                  refine ⟨32559139179252190283322125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21706092786168126855548083 32559139179252190283322125)
                  ·
                    refine ⟨12209677192219571356245797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32559139179252190283322125 12209677192219571356245797)
                    ·
                      refine ⟨2289314473541169629296087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12209677192219571356245797 2289314473541169629296087)
                      ·
                        rfl

theorem cell23_4458424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 1, 3, 4].length) (baseStart_4458424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4458424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4458424 prefixEnd_4458424 := by exact prefixLift 4458424
  have htrace : WordTrace (prefixWord ++ tailWord_4458424) baseStart_4458424 baseEnd_4458424 := by
    simpa [prefixWord, tailWord_4458424, baseEnd_4458424] using wordTrace_append hprefix tailTrace_4458424
  have hstable : (prefixWord ++ tailWord_4458424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4458424).length < 2 ^ (prefixWord ++ tailWord_4458424).sum := by decide
  have hdescent : baseEnd_4458424 < baseStart_4458424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4458424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4458468 : List Nat := [2, 3, 1, 1, 1, 1, 3, 6, 1, 4]
def baseStart_4458468 : Nat := 118140960795 + 4458468 * 2 ^ 59
def prefixEnd_4458468 : Nat := 4983230072969 + 3 ^ 40 * 4458468 * 2
def baseEnd_4458468 : Nat := 763112355563322485715295

theorem tailTrace_4458468 : CollatzResearch.WordTrace tailWord_4458468 prefixEnd_4458468 763112355563322485715295 := by
  unfold tailWord_4458468
  simp only [CollatzResearch.WordTrace]
  refine ⟨81306843605869678278860029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108409124807826237705146705 81306843605869678278860029)
  ·
    refine ⟨30490066352201129354572511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81306843605869678278860029 30490066352201129354572511)
    ·
      refine ⟨45735099528301694031858767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30490066352201129354572511 45735099528301694031858767)
      ·
        refine ⟨68602649292452541047788151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45735099528301694031858767 68602649292452541047788151)
        ·
          refine ⟨102903973938678811571682227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68602649292452541047788151 102903973938678811571682227)
          ·
            refine ⟨154355960908018217357523341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102903973938678811571682227 154355960908018217357523341)
            ·
              refine ⟨57883485340506831509071253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 154355960908018217357523341 57883485340506831509071253)
              ·
                refine ⟨2713288375336257726987715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 57883485340506831509071253 2713288375336257726987715)
                ·
                  refine ⟨4069932563004386590481573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2713288375336257726987715 4069932563004386590481573)
                  ·
                    refine ⟨763112355563322485715295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4069932563004386590481573 763112355563322485715295)
                    ·
                      rfl

theorem cell23_4458468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 6, 1, 4].length) (baseStart_4458468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4458468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4458468 prefixEnd_4458468 := by exact prefixLift 4458468
  have htrace : WordTrace (prefixWord ++ tailWord_4458468) baseStart_4458468 baseEnd_4458468 := by
    simpa [prefixWord, tailWord_4458468, baseEnd_4458468] using wordTrace_append hprefix tailTrace_4458468
  have hstable : (prefixWord ++ tailWord_4458468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4458468).length < 2 ^ (prefixWord ++ tailWord_4458468).sum := by decide
  have hdescent : baseEnd_4458468 < baseStart_4458468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4458468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4458525 : List Nat := [1, 4, 2, 2, 2, 1, 3, 1, 3, 1, 3]
def baseStart_4458525 : Nat := 118140960795 + 4458525 * 2 ^ 59
def prefixEnd_4458525 : Nat := 4983230072969 + 3 ^ 40 * 4458525 * 2
def baseEnd_4458525 : Nat := 2289366335087273734133123

theorem tailTrace_4458525 : CollatzResearch.WordTrace tailWord_4458525 prefixEnd_4458525 2289366335087273734133123 := by
  unfold tailWord_4458525
  simp only [CollatzResearch.WordTrace]
  refine ⟨162615766172532855292545029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108410510781688570195030019 162615766172532855292545029)
  ·
    refine ⟨30490456157349910367352193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 162615766172532855292545029 30490456157349910367352193)
    ·
      refine ⟨22867842118012432775514145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30490456157349910367352193 22867842118012432775514145)
      ·
        refine ⟨17150881588509324581635609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22867842118012432775514145 17150881588509324581635609)
        ·
          refine ⟨12863161191381993436226707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17150881588509324581635609 12863161191381993436226707)
          ·
            refine ⟨19294741787072990154340061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12863161191381993436226707 19294741787072990154340061)
            ·
              refine ⟨7235528170152371307877523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19294741787072990154340061 7235528170152371307877523)
              ·
                refine ⟨10853292255228556961816285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7235528170152371307877523 10853292255228556961816285)
                ·
                  refine ⟨4069984595710708860681107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10853292255228556961816285 4069984595710708860681107)
                  ·
                    refine ⟨6104976893566063291021661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4069984595710708860681107 6104976893566063291021661)
                    ·
                      refine ⟨2289366335087273734133123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6104976893566063291021661 2289366335087273734133123)
                      ·
                        rfl

theorem cell23_4458525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_4458525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4458525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4458525 prefixEnd_4458525 := by exact prefixLift 4458525
  have htrace : WordTrace (prefixWord ++ tailWord_4458525) baseStart_4458525 baseEnd_4458525 := by
    simpa [prefixWord, tailWord_4458525, baseEnd_4458525] using wordTrace_append hprefix tailTrace_4458525
  have hstable : (prefixWord ++ tailWord_4458525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4458525).length < 2 ^ (prefixWord ++ tailWord_4458525).sum := by decide
  have hdescent : baseEnd_4458525 < baseStart_4458525 := by decide
  rcases family_descends (prefixWord ++ tailWord_4458525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4458531 : List Nat := [1, 1, 1, 4, 3, 1, 2, 2, 3, 1, 4]
def baseStart_4458531 : Nat := 118140960795 + 4458531 * 2 ^ 59
def prefixEnd_4458531 : Nat := 4983230072969 + 3 ^ 40 * 4458531 * 2
def baseEnd_4458531 : Nat := 2289369415971200710658095

theorem tailTrace_4458531 : CollatzResearch.WordTrace tailWord_4458531 prefixEnd_4458531 2289369415971200710658095 := by
  unfold tailWord_4458531
  simp only [CollatzResearch.WordTrace]
  refine ⟨162615985010511118317263447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108410656673674078878175631 162615985010511118317263447)
  ·
    refine ⟨243923977515766677475895171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162615985010511118317263447 243923977515766677475895171)
    ·
      refine ⟨365885966273650016213842757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243923977515766677475895171 365885966273650016213842757)
      ·
        refine ⟨68603618676309378040095517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 365885966273650016213842757 68603618676309378040095517)
        ·
          refine ⟨25726357003616016765035819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68603618676309378040095517 25726357003616016765035819)
          ·
            refine ⟨38589535505424025147553729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25726357003616016765035819 38589535505424025147553729)
            ·
              refine ⟨28942151629068018860665297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38589535505424025147553729 28942151629068018860665297)
              ·
                refine ⟨21706613721801014145498973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28942151629068018860665297 21706613721801014145498973)
                ·
                  refine ⟨8139980145675380304562115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21706613721801014145498973 8139980145675380304562115)
                  ·
                    refine ⟨12209970218513070456843173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8139980145675380304562115 12209970218513070456843173)
                    ·
                      refine ⟨2289369415971200710658095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12209970218513070456843173 2289369415971200710658095)
                      ·
                        rfl

theorem cell23_4458531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_4458531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4458531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4458531 prefixEnd_4458531 := by exact prefixLift 4458531
  have htrace : WordTrace (prefixWord ++ tailWord_4458531) baseStart_4458531 baseEnd_4458531 := by
    simpa [prefixWord, tailWord_4458531, baseEnd_4458531] using wordTrace_append hprefix tailTrace_4458531
  have hstable : (prefixWord ++ tailWord_4458531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4458531).length < 2 ^ (prefixWord ++ tailWord_4458531).sum := by decide
  have hdescent : baseEnd_4458531 < baseStart_4458531 := by decide
  rcases family_descends (prefixWord ++ tailWord_4458531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4458532 : List Nat := [2, 3, 1, 4, 3, 1, 2, 1, 6]
def baseStart_4458532 : Nat := 118140960795 + 4458532 * 2 ^ 59
def prefixEnd_4458532 : Nat := 4983230072969 + 3 ^ 40 * 4458532 * 2
def baseEnd_4458532 : Nat := 254374436605761689638399

theorem tailTrace_4458532 : CollatzResearch.WordTrace tailWord_4458532 prefixEnd_4458532 254374436605761689638399 := by
  unfold tailWord_4458532
  simp only [CollatzResearch.WordTrace]
  refine ⟨81308010741753747744024925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108410680989004996992033233 81308010741753747744024925)
  ·
    refine ⟨30490504028157655404009347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81308010741753747744024925 30490504028157655404009347)
    ·
      refine ⟨45735756042236483106014021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30490504028157655404009347 45735756042236483106014021)
      ·
        refine ⟨8575454257919340582377629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45735756042236483106014021 8575454257919340582377629)
        ·
          refine ⟨3215795346719752718391611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8575454257919340582377629 3215795346719752718391611)
          ·
            refine ⟨4823693020079629077587417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3215795346719752718391611 4823693020079629077587417)
            ·
              refine ⟨3617769765059721808190563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4823693020079629077587417 3617769765059721808190563)
              ·
                refine ⟨5426654647589582712285845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3617769765059721808190563 5426654647589582712285845)
                ·
                  refine ⟨254374436605761689638399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5426654647589582712285845 254374436605761689638399)
                  ·
                    rfl

theorem cell23_4458532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 1, 6].length) (baseStart_4458532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4458532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4458532 prefixEnd_4458532 := by exact prefixLift 4458532
  have htrace : WordTrace (prefixWord ++ tailWord_4458532) baseStart_4458532 baseEnd_4458532 := by
    simpa [prefixWord, tailWord_4458532, baseEnd_4458532] using wordTrace_append hprefix tailTrace_4458532
  have hstable : (prefixWord ++ tailWord_4458532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4458532).length < 2 ^ (prefixWord ++ tailWord_4458532).sum := by decide
  have hdescent : baseEnd_4458532 < baseStart_4458532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4458532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4458588 : List Nat := [2, 2, 4, 1, 1, 4, 1, 8]
def baseStart_4458588 : Nat := 118140960795 + 4458588 * 2 ^ 59
def prefixEnd_4458588 : Nat := 4983230072969 + 3 ^ 40 * 4458588 * 2
def baseEnd_4458588 : Nat := 84792543865500258801679

theorem tailTrace_4458588 : CollatzResearch.WordTrace tailWord_4458588 prefixEnd_4458588 84792543865500258801679 := by
  unfold tailWord_4458588
  simp only [CollatzResearch.WordTrace]
  refine ⟨81309031985652308526044209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108412042647536411368058945 81309031985652308526044209)
  ·
    refine ⟨60981773989239231394533157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81309031985652308526044209 60981773989239231394533157)
    ·
      refine ⟨11434082622982355886474967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60981773989239231394533157 11434082622982355886474967)
      ·
        refine ⟨17151123934473533829712451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11434082622982355886474967 17151123934473533829712451)
        ·
          refine ⟨25726685901710300744568677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17151123934473533829712451 25726685901710300744568677)
          ·
            refine ⟨4823753606570681389606627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25726685901710300744568677 4823753606570681389606627)
            ·
              refine ⟨7235630409856022084409941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4823753606570681389606627 7235630409856022084409941)
              ·
                refine ⟨84792543865500258801679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7235630409856022084409941 84792543865500258801679)
                ·
                  rfl

theorem cell23_4458588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 8].length) (baseStart_4458588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4458588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4458588 prefixEnd_4458588 := by exact prefixLift 4458588
  have htrace : WordTrace (prefixWord ++ tailWord_4458588) baseStart_4458588 baseEnd_4458588 := by
    simpa [prefixWord, tailWord_4458588, baseEnd_4458588] using wordTrace_append hprefix tailTrace_4458588
  have hstable : (prefixWord ++ tailWord_4458588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4458588).length < 2 ^ (prefixWord ++ tailWord_4458588).sum := by decide
  have hdescent : baseEnd_4458588 < baseStart_4458588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4458588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4458631 : List Nat := [1, 1, 4, 2, 1, 1, 3, 2, 2, 6]
def baseStart_4458631 : Nat := 118140960795 + 4458631 * 2 ^ 59
def prefixEnd_4458631 : Nat := 4983230072969 + 3 ^ 40 * 4458631 * 2
def baseEnd_4458631 : Nat := 763140254678883439802545

theorem tailTrace_4458631 : CollatzResearch.WordTrace tailWord_4458631 prefixEnd_4458631 763140254678883439802545 := by
  unfold tailWord_4458631
  simp only [CollatzResearch.WordTrace]
  refine ⟨162619632310148835395903747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108413088206765890263935831 162619632310148835395903747)
  ·
    refine ⟨243929448465223253093855621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162619632310148835395903747 243929448465223253093855621)
    ·
      refine ⟨45736771587229359955097929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 243929448465223253093855621 45736771587229359955097929)
      ·
        refine ⟨34302578690422019966323447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45736771587229359955097929 34302578690422019966323447)
        ·
          refine ⟨51453868035633029949485171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34302578690422019966323447 51453868035633029949485171)
          ·
            refine ⟨77180802053449544924227757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51453868035633029949485171 77180802053449544924227757)
            ·
              refine ⟨28942800770043579346585409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77180802053449544924227757 28942800770043579346585409)
              ·
                refine ⟨21707100577532684509939057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28942800770043579346585409 21707100577532684509939057)
                ·
                  refine ⟨16280325433149513382454293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21707100577532684509939057 16280325433149513382454293)
                  ·
                    refine ⟨763140254678883439802545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16280325433149513382454293 763140254678883439802545)
                    ·
                      rfl

theorem cell23_4458631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 6].length) (baseStart_4458631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4458631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4458631 prefixEnd_4458631 := by exact prefixLift 4458631
  have htrace : WordTrace (prefixWord ++ tailWord_4458631) baseStart_4458631 baseEnd_4458631 := by
    simpa [prefixWord, tailWord_4458631, baseEnd_4458631] using wordTrace_append hprefix tailTrace_4458631
  have hstable : (prefixWord ++ tailWord_4458631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4458631).length < 2 ^ (prefixWord ++ tailWord_4458631).sum := by decide
  have hdescent : baseEnd_4458631 < baseStart_4458631 := by decide
  rcases family_descends (prefixWord ++ tailWord_4458631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4458632 : List Nat := [2, 1, 3, 4, 1, 1, 3, 2, 2, 1, 3]
def baseStart_4458632 : Nat := 118140960795 + 4458632 * 2 ^ 59
def prefixEnd_4458632 : Nat := 4983230072969 + 3 ^ 40 * 4458632 * 2
def baseEnd_4458632 : Nat := 2289421277517304815495131

theorem tailTrace_4458632 : CollatzResearch.WordTrace tailWord_4458632 prefixEnd_4458632 2289421277517304815495131 := by
  unfold tailWord_4458632
  simp only [CollatzResearch.WordTrace]
  refine ⟨81309834391572606283345075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108413112522096808377793433 81309834391572606283345075)
  ·
    refine ⟨121964751587358909425017613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81309834391572606283345075 121964751587358909425017613)
    ·
      refine ⟨45736781845259591034381605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121964751587358909425017613 45736781845259591034381605)
      ·
        refine ⟨8575646595986173318946551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45736781845259591034381605 8575646595986173318946551)
        ·
          refine ⟨12863469893979259978419827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8575646595986173318946551 12863469893979259978419827)
          ·
            refine ⟨19295204840968889967629741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12863469893979259978419827 19295204840968889967629741)
            ·
              refine ⟨7235701815363333737861153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19295204840968889967629741 7235701815363333737861153)
              ·
                refine ⟨5426776361522500303395865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7235701815363333737861153 5426776361522500303395865)
                ·
                  refine ⟨4070082271141875227546899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5426776361522500303395865 4070082271141875227546899)
                  ·
                    refine ⟨6105123406712812841320349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4070082271141875227546899 6105123406712812841320349)
                    ·
                      refine ⟨2289421277517304815495131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6105123406712812841320349 2289421277517304815495131)
                      ·
                        rfl

theorem cell23_4458632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_4458632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4458632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4458632 prefixEnd_4458632 := by exact prefixLift 4458632
  have htrace : WordTrace (prefixWord ++ tailWord_4458632) baseStart_4458632 baseEnd_4458632 := by
    simpa [prefixWord, tailWord_4458632, baseEnd_4458632] using wordTrace_append hprefix tailTrace_4458632
  have hstable : (prefixWord ++ tailWord_4458632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4458632).length < 2 ^ (prefixWord ++ tailWord_4458632).sum := by decide
  have hdescent : baseEnd_4458632 < baseStart_4458632 := by decide
  rcases family_descends (prefixWord ++ tailWord_4458632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4458651 : List Nat := [1, 1, 1, 1, 1, 1, 2, 7, 2, 2, 4]
def baseStart_4458651 : Nat := 118140960795 + 4458651 * 2 ^ 59
def prefixEnd_4458651 : Nat := 4983230072969 + 3 ^ 40 * 4458651 * 2
def baseEnd_4458651 : Nat := 2289431033649740241157543

theorem tailTrace_4458651 : CollatzResearch.WordTrace tailWord_4458651 prefixEnd_4458651 2289431033649740241157543 := by
  unfold tailWord_4458651
  simp only [CollatzResearch.WordTrace]
  refine ⟨162620361770076378811631807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108413574513384252541087871 162620361770076378811631807)
  ·
    refine ⟨243930542655114568217447711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162620361770076378811631807 243930542655114568217447711)
    ·
      refine ⟨365895813982671852326171567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243930542655114568217447711 365895813982671852326171567)
      ·
        refine ⟨548843720974007778489257351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 365895813982671852326171567 548843720974007778489257351)
        ·
          refine ⟨823265581461011667733886027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 548843720974007778489257351 823265581461011667733886027)
          ·
            refine ⟨1234898372191517501600829041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 823265581461011667733886027 1234898372191517501600829041)
            ·
              refine ⟨926173779143638126200621781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1234898372191517501600829041 926173779143638126200621781)
              ·
                refine ⟨21707197948679018582827073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 926173779143638126200621781 21707197948679018582827073)
                ·
                  refine ⟨16280398461509263937120305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21707197948679018582827073 16280398461509263937120305)
                  ·
                    refine ⟨12210298846131947952840229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16280398461509263937120305 12210298846131947952840229)
                    ·
                      refine ⟨2289431033649740241157543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12210298846131947952840229 2289431033649740241157543)
                      ·
                        rfl

theorem cell23_4458651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 2, 4].length) (baseStart_4458651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4458651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4458651 prefixEnd_4458651 := by exact prefixLift 4458651
  have htrace : WordTrace (prefixWord ++ tailWord_4458651) baseStart_4458651 baseEnd_4458651 := by
    simpa [prefixWord, tailWord_4458651, baseEnd_4458651] using wordTrace_append hprefix tailTrace_4458651
  have hstable : (prefixWord ++ tailWord_4458651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4458651).length < 2 ^ (prefixWord ++ tailWord_4458651).sum := by decide
  have hdescent : baseEnd_4458651 < baseStart_4458651 := by decide
  rcases family_descends (prefixWord ++ tailWord_4458651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4458661 : List Nat := [1, 3, 1, 2, 1, 3, 1, 4, 7]
def baseStart_4458661 : Nat := 118140960795 + 4458661 * 2 ^ 59
def prefixEnd_4458661 : Nat := 4983230072969 + 3 ^ 40 * 4458661 * 2
def baseEnd_4458661 : Nat := 254381796495142800225833

theorem tailTrace_4458661 : CollatzResearch.WordTrace tailWord_4458661 prefixEnd_4458661 254381796495142800225833 := by
  unfold tailWord_4458661
  simp only [CollatzResearch.WordTrace]
  refine ⟨162620726500040150519495837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108413817666693433679663891 162620726500040150519495837)
  ·
    refine ⟨60982772437515056444810939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162620726500040150519495837 60982772437515056444810939)
    ·
      refine ⟨91474158656272584667216409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60982772437515056444810939 91474158656272584667216409)
      ·
        refine ⟨68605618992204438500412307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91474158656272584667216409 68605618992204438500412307)
        ·
          refine ⟨102908428488306657750618461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68605618992204438500412307 102908428488306657750618461)
          ·
            refine ⟨38590660683114996656481923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102908428488306657750618461 38590660683114996656481923)
            ·
              refine ⟨57885991024672494984722885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38590660683114996656481923 57885991024672494984722885)
              ·
                refine ⟨10853623317126092809635541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57885991024672494984722885 10853623317126092809635541)
                ·
                  refine ⟨254381796495142800225833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10853623317126092809635541 254381796495142800225833)
                  ·
                    rfl

theorem cell23_4458661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 7].length) (baseStart_4458661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4458661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4458661 prefixEnd_4458661 := by exact prefixLift 4458661
  have htrace : WordTrace (prefixWord ++ tailWord_4458661) baseStart_4458661 baseEnd_4458661 := by
    simpa [prefixWord, tailWord_4458661, baseEnd_4458661] using wordTrace_append hprefix tailTrace_4458661
  have hstable : (prefixWord ++ tailWord_4458661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4458661).length < 2 ^ (prefixWord ++ tailWord_4458661).sum := by decide
  have hdescent : baseEnd_4458661 < baseStart_4458661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4458661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4458706 : List Nat := [3, 2, 2, 2, 1, 4, 2, 1, 2, 2, 2]
def baseStart_4458706 : Nat := 118140960795 + 4458706 * 2 ^ 59
def prefixEnd_4458706 : Nat := 4983230072969 + 3 ^ 40 * 4458706 * 2
def baseEnd_4458706 : Nat := 2289459275085737525969791

theorem tailTrace_4458706 : CollatzResearch.WordTrace tailWord_4458706 prefixEnd_4458706 2289459275085737525969791 := by
  unfold tailWord_4458706
  simp only [CollatzResearch.WordTrace]
  refine ⟨40655591946219280801220993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108414911856584748803255981 40655591946219280801220993)
  ·
    refine ⟨30491693959664460600915745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40655591946219280801220993 30491693959664460600915745)
    ·
      refine ⟨22868770469748345450686809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30491693959664460600915745 22868770469748345450686809)
      ·
        refine ⟨17151577852311259088015107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22868770469748345450686809 17151577852311259088015107)
        ·
          refine ⟨25727366778466888632022661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17151577852311259088015107 25727366778466888632022661)
          ·
            refine ⟨4823881270962541618504249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25727366778466888632022661 4823881270962541618504249)
            ·
              refine ⟨3617910953221906213878187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4823881270962541618504249 3617910953221906213878187)
              ·
                refine ⟨5426866429832859320817281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3617910953221906213878187 5426866429832859320817281)
                ·
                  refine ⟨4070149822374644490612961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5426866429832859320817281 4070149822374644490612961)
                  ·
                    refine ⟨3052612366780983367959721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4070149822374644490612961 3052612366780983367959721)
                    ·
                      refine ⟨2289459275085737525969791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3052612366780983367959721 2289459275085737525969791)
                      ·
                        rfl

theorem cell23_4458706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_4458706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4458706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4458706 prefixEnd_4458706 := by exact prefixLift 4458706
  have htrace : WordTrace (prefixWord ++ tailWord_4458706) baseStart_4458706 baseEnd_4458706 := by
    simpa [prefixWord, tailWord_4458706, baseEnd_4458706] using wordTrace_append hprefix tailTrace_4458706
  have hstable : (prefixWord ++ tailWord_4458706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4458706).length < 2 ^ (prefixWord ++ tailWord_4458706).sum := by decide
  have hdescent : baseEnd_4458706 < baseStart_4458706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4458706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4458725 : List Nat := [1, 3, 1, 4, 2, 2, 2, 1, 2, 5]
def baseStart_4458725 : Nat := 118140960795 + 4458725 * 2 ^ 59
def prefixEnd_4458725 : Nat := 4983230072969 + 3 ^ 40 * 4458725 * 2
def baseEnd_4458725 : Nat := 763156343739390983877401

theorem tailTrace_4458725 : CollatzResearch.WordTrace tailWord_4458725 prefixEnd_4458725 763156343739390983877401 := by
  unfold tailWord_4458725
  simp only [CollatzResearch.WordTrace]
  refine ⟨162623060771808289449825629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108415373847872192966550419 162623060771808289449825629)
  ·
    refine ⟨60983647789428108543684611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162623060771808289449825629 60983647789428108543684611)
    ·
      refine ⟨91475471684142162815526917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60983647789428108543684611 91475471684142162815526917)
      ·
        refine ⟨17151650940776655527911297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91475471684142162815526917 17151650940776655527911297)
        ·
          refine ⟨12863738205582491645933473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17151650940776655527911297 12863738205582491645933473)
          ·
            refine ⟨9647803654186868734450105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12863738205582491645933473 9647803654186868734450105)
            ·
              refine ⟨7235852740640151550837579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9647803654186868734450105 7235852740640151550837579)
              ·
                refine ⟨10853779110960227326256369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7235852740640151550837579 10853779110960227326256369)
                ·
                  refine ⟨8140334333220170494692277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10853779110960227326256369 8140334333220170494692277)
                  ·
                    refine ⟨763156343739390983877401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8140334333220170494692277 763156343739390983877401)
                    ·
                      rfl

theorem cell23_4458725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 2, 5].length) (baseStart_4458725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4458725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4458725 prefixEnd_4458725 := by exact prefixLift 4458725
  have htrace : WordTrace (prefixWord ++ tailWord_4458725) baseStart_4458725 baseEnd_4458725 := by
    simpa [prefixWord, tailWord_4458725, baseEnd_4458725] using wordTrace_append hprefix tailTrace_4458725
  have hstable : (prefixWord ++ tailWord_4458725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4458725).length < 2 ^ (prefixWord ++ tailWord_4458725).sum := by decide
  have hdescent : baseEnd_4458725 < baseStart_4458725 := by decide
  rcases family_descends (prefixWord ++ tailWord_4458725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4458789 : List Nat := [1, 3, 1, 2, 5, 1, 2, 3, 1, 4]
def baseStart_4458789 : Nat := 118140960795 + 4458789 * 2 ^ 59
def prefixEnd_4458789 : Nat := 4983230072969 + 3 ^ 40 * 4458789 * 2
def baseEnd_4458789 : Nat := 763167297993353567077303

theorem tailTrace_4458789 : CollatzResearch.WordTrace tailWord_4458789 prefixEnd_4458789 763167297993353567077303 := by
  unfold tailWord_4458789
  simp only [CollatzResearch.WordTrace]
  refine ⟨162625395043576428380155421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108416930029050952253436947 162625395043576428380155421)
  ·
    refine ⟨60984523141341160642558283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162625395043576428380155421 60984523141341160642558283)
    ·
      refine ⟨91476784712011740963837425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60984523141341160642558283 91476784712011740963837425)
      ·
        refine ⟨68607588534008805722878069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91476784712011740963837425 68607588534008805722878069)
        ·
          refine ⟨6431961425063325536519819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68607588534008805722878069 6431961425063325536519819)
          ·
            refine ⟨9647942137594988304779729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6431961425063325536519819 9647942137594988304779729)
            ·
              refine ⟨7235956603196241228584797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9647942137594988304779729 7235956603196241228584797)
              ·
                refine ⟨2713483726198590460719299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7235956603196241228584797 2713483726198590460719299)
                ·
                  refine ⟨4070225589297885691078949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2713483726198590460719299 4070225589297885691078949)
                  ·
                    refine ⟨763167297993353567077303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4070225589297885691078949 763167297993353567077303)
                    ·
                      rfl

theorem cell23_4458789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 3, 1, 4].length) (baseStart_4458789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4458789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4458789 prefixEnd_4458789 := by exact prefixLift 4458789
  have htrace : WordTrace (prefixWord ++ tailWord_4458789) baseStart_4458789 baseEnd_4458789 := by
    simpa [prefixWord, tailWord_4458789, baseEnd_4458789] using wordTrace_append hprefix tailTrace_4458789
  have hstable : (prefixWord ++ tailWord_4458789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4458789).length < 2 ^ (prefixWord ++ tailWord_4458789).sum := by decide
  have hdescent : baseEnd_4458789 < baseStart_4458789 := by decide
  rcases family_descends (prefixWord ++ tailWord_4458789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4458802 : List Nat := [3, 2, 1, 1, 5, 2, 1, 2, 6]
def baseStart_4458802 : Nat := 118140960795 + 4458802 * 2 ^ 59
def prefixEnd_4458802 : Nat := 4983230072969 + 3 ^ 40 * 4458802 * 2
def baseEnd_4458802 : Nat := 254389841025396572263261

theorem tailTrace_4458802 : CollatzResearch.WordTrace tailWord_4458802 prefixEnd_4458802 254389841025396572263261 := by
  unfold tailWord_4458802
  simp only [CollatzResearch.WordTrace]
  refine ⟨40656467298132332900094665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108417246128352887733585773 40656467298132332900094665)
  ·
    refine ⟨30492350473599249675070999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40656467298132332900094665 30492350473599249675070999)
    ·
      refine ⟨45738525710398874512606499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30492350473599249675070999 45738525710398874512606499)
      ·
        refine ⟨68607788565598311768909749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45738525710398874512606499 68607788565598311768909749)
        ·
          refine ⟨6431980178024841728335289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68607788565598311768909749 6431980178024841728335289)
          ·
            refine ⟨4823985133518631296251467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6431980178024841728335289 4823985133518631296251467)
            ·
              refine ⟨7235977700277946944377201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4823985133518631296251467 7235977700277946944377201)
              ·
                refine ⟨5426983275208460208282901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7235977700277946944377201 5426983275208460208282901)
                ·
                  refine ⟨254389841025396572263261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5426983275208460208282901 254389841025396572263261)
                  ·
                    rfl

theorem cell23_4458802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 2, 6].length) (baseStart_4458802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4458802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4458802 prefixEnd_4458802 := by exact prefixLift 4458802
  have htrace : WordTrace (prefixWord ++ tailWord_4458802) baseStart_4458802 baseEnd_4458802 := by
    simpa [prefixWord, tailWord_4458802, baseEnd_4458802] using wordTrace_append hprefix tailTrace_4458802
  have hstable : (prefixWord ++ tailWord_4458802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4458802).length < 2 ^ (prefixWord ++ tailWord_4458802).sum := by decide
  have hdescent : baseEnd_4458802 < baseStart_4458802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4458802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4458812 : List Nat := [2, 2, 2, 2, 1, 2, 4, 1, 3, 1, 3]
def baseStart_4458812 : Nat := 118140960795 + 4458812 * 2 ^ 59
def prefixEnd_4458812 : Nat := 4983230072969 + 3 ^ 40 * 4458812 * 2
def baseEnd_4458812 : Nat := 2289513704035114111244303

theorem tailTrace_4458812 : CollatzResearch.WordTrace tailWord_4458812 prefixEnd_4458812 2289513704035114111244303 := by
  unfold tailWord_4458812
  simp only [CollatzResearch.WordTrace]
  refine ⟨81313116961246551654121345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108417489281662068872161793 81313116961246551654121345)
  ·
    refine ⟨60984837720934913740591009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81313116961246551654121345 60984837720934913740591009)
    ·
      refine ⟨45738628290701185305443257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60984837720934913740591009 45738628290701185305443257)
      ·
        refine ⟨34303971218025888979082443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45738628290701185305443257 34303971218025888979082443)
        ·
          refine ⟨51455956827038833468623665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34303971218025888979082443 51455956827038833468623665)
          ·
            refine ⟨38591967620279125101467749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51455956827038833468623665 38591967620279125101467749)
            ·
              refine ⟨7235993928802335956525203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38591967620279125101467749 7235993928802335956525203)
              ·
                refine ⟨10853990893203503934787805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7235993928802335956525203 10853990893203503934787805)
                ·
                  refine ⟨4070246584951313975545427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10853990893203503934787805 4070246584951313975545427)
                  ·
                    refine ⟨6105369877426970963318141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4070246584951313975545427 6105369877426970963318141)
                    ·
                      refine ⟨2289513704035114111244303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6105369877426970963318141 2289513704035114111244303)
                      ·
                        rfl

theorem cell23_4458812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_4458812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4458812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4458812 prefixEnd_4458812 := by exact prefixLift 4458812
  have htrace : WordTrace (prefixWord ++ tailWord_4458812) baseStart_4458812 baseEnd_4458812 := by
    simpa [prefixWord, tailWord_4458812, baseEnd_4458812] using wordTrace_append hprefix tailTrace_4458812
  have hstable : (prefixWord ++ tailWord_4458812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4458812).length < 2 ^ (prefixWord ++ tailWord_4458812).sum := by decide
  have hdescent : baseEnd_4458812 < baseStart_4458812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4458812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4458855 : List Nat := [1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 5]
def baseStart_4458855 : Nat := 118140960795 + 4458855 * 2 ^ 59
def prefixEnd_4458855 : Nat := 4983230072969 + 3 ^ 40 * 4458855 * 2
def baseEnd_4458855 : Nat := 2289535783703257443006605

theorem tailTrace_4458855 : CollatzResearch.WordTrace tailWord_4458855 prefixEnd_4458855 2289535783703257443006605 := by
  unfold tailWord_4458855
  simp only [CollatzResearch.WordTrace]
  refine ⟨162627802261337321652058019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108418534840891547768038679 162627802261337321652058019)
  ·
    refine ⟨243941703392005982478087029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162627802261337321652058019 243941703392005982478087029)
    ·
      refine ⟨22869534693000560857320659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 243941703392005982478087029 22869534693000560857320659)
      ·
        refine ⟨34304302039500841285980989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22869534693000560857320659 34304302039500841285980989)
        ·
          refine ⟨12864113264812815482242871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34304302039500841285980989 12864113264812815482242871)
          ·
            refine ⟨19296169897219223223364307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12864113264812815482242871 19296169897219223223364307)
            ·
              refine ⟨28944254845828834835046461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19296169897219223223364307 28944254845828834835046461)
              ·
                refine ⟨10854095567185813063142423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28944254845828834835046461 10854095567185813063142423)
                ·
                  refine ⟨16281143350778719594713635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10854095567185813063142423 16281143350778719594713635)
                  ·
                    refine ⟨24421715026168079392070453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16281143350778719594713635 24421715026168079392070453)
                    ·
                      refine ⟨2289535783703257443006605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24421715026168079392070453 2289535783703257443006605)
                      ·
                        rfl

theorem cell23_4458855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_4458855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4458855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4458855 prefixEnd_4458855 := by exact prefixLift 4458855
  have htrace : WordTrace (prefixWord ++ tailWord_4458855) baseStart_4458855 baseEnd_4458855 := by
    simpa [prefixWord, tailWord_4458855, baseEnd_4458855] using wordTrace_append hprefix tailTrace_4458855
  have hstable : (prefixWord ++ tailWord_4458855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4458855).length < 2 ^ (prefixWord ++ tailWord_4458855).sum := by decide
  have hdescent : baseEnd_4458855 < baseStart_4458855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4458855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4458885 : List Nat := [1, 3, 1, 1, 3, 1, 1, 5, 1, 3, 3]
def baseStart_4458885 : Nat := 118140960795 + 4458885 * 2 ^ 59
def prefixEnd_4458885 : Nat := 4983230072969 + 3 ^ 40 * 4458885 * 2
def baseEnd_4458885 : Nat := 2289551188122892325631467

theorem tailTrace_4458885 : CollatzResearch.WordTrace tailWord_4458885 prefixEnd_4458885 2289551188122892325631467 := by
  unfold tailWord_4458885
  simp only [CollatzResearch.WordTrace]
  refine ⟨162628896451228636775650109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108419264300819091183766739 162628896451228636775650109)
  ·
    refine ⟨60985836169210738790868791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162628896451228636775650109 60985836169210738790868791)
    ·
      refine ⟨91478754253816108186303187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60985836169210738790868791 91478754253816108186303187)
      ·
        refine ⟨137218131380724162279454781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91478754253816108186303187 137218131380724162279454781)
        ·
          refine ⟨51456799267771560854795543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137218131380724162279454781 51456799267771560854795543)
          ·
            refine ⟨77185198901657341282193315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51456799267771560854795543 77185198901657341282193315)
            ·
              refine ⟨115777798352486011923289973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77185198901657341282193315 115777798352486011923289973)
              ·
                refine ⟨10854168595545563617808435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 115777798352486011923289973 10854168595545563617808435)
                ·
                  refine ⟨16281252893318345426712653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10854168595545563617808435 16281252893318345426712653)
                  ·
                    refine ⟨6105469834994379535017245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16281252893318345426712653 6105469834994379535017245)
                    ·
                      refine ⟨2289551188122892325631467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6105469834994379535017245 2289551188122892325631467)
                      ·
                        rfl

theorem cell23_4458885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 3, 3].length) (baseStart_4458885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4458885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4458885 prefixEnd_4458885 := by exact prefixLift 4458885
  have htrace : WordTrace (prefixWord ++ tailWord_4458885) baseStart_4458885 baseEnd_4458885 := by
    simpa [prefixWord, tailWord_4458885, baseEnd_4458885] using wordTrace_append hprefix tailTrace_4458885
  have hstable : (prefixWord ++ tailWord_4458885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4458885).length < 2 ^ (prefixWord ++ tailWord_4458885).sum := by decide
  have hdescent : baseEnd_4458885 < baseStart_4458885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4458885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4458889 : List Nat := [1, 2, 1, 1, 6, 3, 1, 2, 1, 2, 3]
def baseStart_4458889 : Nat := 118140960795 + 4458889 * 2 ^ 59
def prefixEnd_4458889 : Nat := 4983230072969 + 3 ^ 40 * 4458889 * 2
def baseEnd_4458889 : Nat := 2289553242045510309981449

theorem tailTrace_4458889 : CollatzResearch.WordTrace tailWord_4458889 prefixEnd_4458889 2289553242045510309981449 := by
  unfold tailWord_4458889
  simp only [CollatzResearch.WordTrace]
  refine ⟨162629042343214145458795721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108419361562142763639197147 162629042343214145458795721)
  ·
    refine ⟨121971781757410609094096791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162629042343214145458795721 121971781757410609094096791)
    ·
      refine ⟨182957672636115913641145187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121971781757410609094096791 182957672636115913641145187)
      ·
        refine ⟨274436508954173870461717781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182957672636115913641145187 274436508954173870461717781)
        ·
          refine ⟨12864211357226900177893021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 274436508954173870461717781 12864211357226900177893021)
          ·
            refine ⟨4824079258960087566709883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12864211357226900177893021 4824079258960087566709883)
            ·
              refine ⟨7236118888440131350064825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4824079258960087566709883 7236118888440131350064825)
              ·
                refine ⟨5427089166330098512548619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7236118888440131350064825 5427089166330098512548619)
                ·
                  refine ⟨8140633749495147768822929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5427089166330098512548619 8140633749495147768822929)
                  ·
                    refine ⟨6105475312121360826617197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8140633749495147768822929 6105475312121360826617197)
                    ·
                      refine ⟨2289553242045510309981449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6105475312121360826617197 2289553242045510309981449)
                      ·
                        rfl

theorem cell23_4458889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 2, 1, 2, 3].length) (baseStart_4458889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4458889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4458889 prefixEnd_4458889 := by exact prefixLift 4458889
  have htrace : WordTrace (prefixWord ++ tailWord_4458889) baseStart_4458889 baseEnd_4458889 := by
    simpa [prefixWord, tailWord_4458889, baseEnd_4458889] using wordTrace_append hprefix tailTrace_4458889
  have hstable : (prefixWord ++ tailWord_4458889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4458889).length < 2 ^ (prefixWord ++ tailWord_4458889).sum := by decide
  have hdescent : baseEnd_4458889 < baseStart_4458889 := by decide
  rcases family_descends (prefixWord ++ tailWord_4458889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
