import V185TrunkScan23Chunk0345

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2046946 : List Nat := [3, 3, 3, 1, 1, 1, 4, 1, 6]
def baseStart_2046946 : Nat := 118140960795 + 2046946 * 2 ^ 59
def prefixEnd_2046946 : Nat := 4983230072969 + 3 ^ 40 * 2046946 * 2
def baseEnd_2046946 : Nat := 116785241310917060895697

theorem tailTrace_2046946 : CollatzResearch.WordTrace tailWord_2046946 prefixEnd_2046946 116785241310917060895697 := by
  unfold tailWord_2046946
  simp only [CollatzResearch.WordTrace]
  refine ⟨18664563510567926847396173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49772169361514471593056461 18664563510567926847396173)
  ·
    refine ⟨6999211316462972567773565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18664563510567926847396173 6999211316462972567773565)
    ·
      refine ⟨2624704243673614712915087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6999211316462972567773565 2624704243673614712915087)
      ·
        refine ⟨3937056365510422069372631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2624704243673614712915087 3937056365510422069372631)
        ·
          refine ⟨5905584548265633104058947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3937056365510422069372631 5905584548265633104058947)
          ·
            refine ⟨8858376822398449656088421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5905584548265633104058947 8858376822398449656088421)
            ·
              refine ⟨1660945654199709310516579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8858376822398449656088421 1660945654199709310516579)
              ·
                refine ⟨2491418481299563965774869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1660945654199709310516579 2491418481299563965774869)
                ·
                  refine ⟨116785241310917060895697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2491418481299563965774869 116785241310917060895697)
                  ·
                    rfl

theorem cell23_2046946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 1, 6].length) (baseStart_2046946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2046946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2046946 prefixEnd_2046946 := by exact prefixLift 2046946
  have htrace : WordTrace (prefixWord ++ tailWord_2046946) baseStart_2046946 baseEnd_2046946 := by
    simpa [prefixWord, tailWord_2046946, baseEnd_2046946] using wordTrace_append hprefix tailTrace_2046946
  have hstable : (prefixWord ++ tailWord_2046946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046946).length < 2 ^ (prefixWord ++ tailWord_2046946).sum := by decide
  have hdescent : baseEnd_2046946 < baseStart_2046946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046959 : List Nat := [1, 1, 2, 1, 4, 5, 1, 2, 1, 5]
def baseStart_2046959 : Nat := 118140960795 + 2046959 * 2 ^ 59
def prefixEnd_2046959 : Nat := 4983230072969 + 3 ^ 40 * 2046959 * 2
def baseEnd_2046959 : Nat := 350357949015587332399571

theorem tailTrace_2046959 : CollatzResearch.WordTrace tailWord_2046959 prefixEnd_2046959 350357949015587332399571 := by
  unfold tailWord_2046959
  simp only [CollatzResearch.WordTrace]
  refine ⟨74658728191224610609807931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49772485460816407073205287 74658728191224610609807931)
  ·
    refine ⟨111988092286836915914711897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74658728191224610609807931 111988092286836915914711897)
    ·
      refine ⟨83991069215127686936033923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111988092286836915914711897 83991069215127686936033923)
      ·
        refine ⟨125986603822691530404050885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83991069215127686936033923 125986603822691530404050885)
        ·
          refine ⟨23622488216754661950759541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125986603822691530404050885 23622488216754661950759541)
          ·
            refine ⟨2214608270320749557883707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23622488216754661950759541 2214608270320749557883707)
            ·
              refine ⟨3321912405481124336825561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2214608270320749557883707 3321912405481124336825561)
              ·
                refine ⟨2491434304110843252619171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3321912405481124336825561 2491434304110843252619171)
                ·
                  refine ⟨3737151456166264878928757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2491434304110843252619171 3737151456166264878928757)
                  ·
                    refine ⟨350357949015587332399571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3737151456166264878928757 350357949015587332399571)
                    ·
                      rfl

theorem cell23_2046959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 2, 1, 5].length) (baseStart_2046959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2046959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2046959 prefixEnd_2046959 := by exact prefixLift 2046959
  have htrace : WordTrace (prefixWord ++ tailWord_2046959) baseStart_2046959 baseEnd_2046959 := by
    simpa [prefixWord, tailWord_2046959, baseEnd_2046959] using wordTrace_append hprefix tailTrace_2046959
  have hstable : (prefixWord ++ tailWord_2046959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046959).length < 2 ^ (prefixWord ++ tailWord_2046959).sum := by decide
  have hdescent : baseEnd_2046959 < baseStart_2046959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046966 : List Nat := [5, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2]
def baseStart_2046966 : Nat := 118140960795 + 2046966 * 2 ^ 59
def prefixEnd_2046966 : Nat := 4983230072969 + 3 ^ 40 * 2046966 * 2
def baseEnd_2046966 : Nat := 1051077441411343469811181

theorem tailTrace_2046966 : CollatzResearch.WordTrace tailWord_2046966 prefixEnd_2046966 1051077441411343469811181 := by
  unfold tailWord_2046966
  simp only [CollatzResearch.WordTrace]
  refine ⟨4666186468887453175332047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49772655668132833870208501 4666186468887453175332047)
  ·
    refine ⟨6999279703331179762998071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4666186468887453175332047 6999279703331179762998071)
    ·
      refine ⟨10498919554996769644497107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6999279703331179762998071 10498919554996769644497107)
      ·
        refine ⟨15748379332495154466745661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10498919554996769644497107 15748379332495154466745661)
        ·
          refine ⟨5905642249685682925029623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15748379332495154466745661 5905642249685682925029623)
          ·
            refine ⟨8858463374528524387544435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5905642249685682925029623 8858463374528524387544435)
            ·
              refine ⟨13287695061792786581316653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8858463374528524387544435 13287695061792786581316653)
              ·
                refine ⟨4982885648172294967993745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13287695061792786581316653 4982885648172294967993745)
                ·
                  refine ⟨3737164236129221225995309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4982885648172294967993745 3737164236129221225995309)
                  ·
                    refine ⟨1401436588548457959748241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3737164236129221225995309 1401436588548457959748241)
                    ·
                      refine ⟨1051077441411343469811181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1401436588548457959748241 1051077441411343469811181)
                      ·
                        rfl

theorem cell23_2046966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2].length) (baseStart_2046966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2046966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2046966 prefixEnd_2046966 := by exact prefixLift 2046966
  have htrace : WordTrace (prefixWord ++ tailWord_2046966) baseStart_2046966 baseEnd_2046966 := by
    simpa [prefixWord, tailWord_2046966, baseEnd_2046966] using wordTrace_append hprefix tailTrace_2046966
  have hstable : (prefixWord ++ tailWord_2046966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046966).length < 2 ^ (prefixWord ++ tailWord_2046966).sum := by decide
  have hdescent : baseEnd_2046966 < baseStart_2046966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046972 : List Nat := [2, 2, 2, 1, 2, 4, 1, 2, 1, 6]
def baseStart_2046972 : Nat := 118140960795 + 2046972 * 2 ^ 59
def prefixEnd_2046972 : Nat := 4983230072969 + 3 ^ 40 * 2046972 * 2
def baseEnd_2046972 : Nat := 350360174098423482112051

theorem tailTrace_2046972 : CollatzResearch.WordTrace tailWord_2046972 prefixEnd_2046972 350360174098423482112051 := by
  unfold tailWord_2046972
  simp only [CollatzResearch.WordTrace]
  refine ⟨37329601170088756915015585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49772801560118342553354113 37329601170088756915015585)
  ·
    refine ⟨27997200877566567686261689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37329601170088756915015585 27997200877566567686261689)
    ·
      refine ⟨20997900658174925764696267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27997200877566567686261689 20997900658174925764696267)
      ·
        refine ⟨31496850987262388647044401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20997900658174925764696267 31496850987262388647044401)
        ·
          refine ⟨23622638240446791485283301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31496850987262388647044401 23622638240446791485283301)
          ·
            refine ⟨4429244670083773403490619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23622638240446791485283301 4429244670083773403490619)
            ·
              refine ⟨6643867005125660105235929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4429244670083773403490619 6643867005125660105235929)
              ·
                refine ⟨4982900253844245078926947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6643867005125660105235929 4982900253844245078926947)
                ·
                  refine ⟨7474350380766367618390421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4982900253844245078926947 7474350380766367618390421)
                  ·
                    refine ⟨350360174098423482112051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7474350380766367618390421 350360174098423482112051)
                    ·
                      rfl

theorem cell23_2046972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 1, 6].length) (baseStart_2046972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2046972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2046972 prefixEnd_2046972 := by exact prefixLift 2046972
  have htrace : WordTrace (prefixWord ++ tailWord_2046972) baseStart_2046972 baseEnd_2046972 := by
    simpa [prefixWord, tailWord_2046972, baseEnd_2046972] using wordTrace_append hprefix tailTrace_2046972
  have hstable : (prefixWord ++ tailWord_2046972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046972).length < 2 ^ (prefixWord ++ tailWord_2046972).sum := by decide
  have hdescent : baseEnd_2046972 < baseStart_2046972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046990 : List Nat := [4, 1, 1, 2, 2, 4, 2, 2, 1, 1, 3]
def baseStart_2046990 : Nat := 118140960795 + 2046990 * 2 ^ 59
def prefixEnd_2046990 : Nat := 4983230072969 + 3 ^ 40 * 2046990 * 2
def baseEnd_2046990 : Nat := 1051089764947051375911071

theorem tailTrace_2046990 : CollatzResearch.WordTrace tailWord_2046990 prefixEnd_2046990 1051089764947051375911071 := by
  unfold tailWord_2046990
  simp only [CollatzResearch.WordTrace]
  refine ⟨9332482356764037863023303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49773239236074868602790949 9332482356764037863023303)
  ·
    refine ⟨13998723535146056794534955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9332482356764037863023303 13998723535146056794534955)
    ·
      refine ⟨20998085302719085191802433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13998723535146056794534955 20998085302719085191802433)
      ·
        refine ⟨15748563977039313893851825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20998085302719085191802433 15748563977039313893851825)
        ·
          refine ⟨11811422982779485420388869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15748563977039313893851825 11811422982779485420388869)
          ·
            refine ⟨2214641809271153516322913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11811422982779485420388869 2214641809271153516322913)
            ·
              refine ⟨1660981356953365137242185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2214641809271153516322913 1660981356953365137242185)
              ·
                refine ⟨1245736017715023852931639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1660981356953365137242185 1245736017715023852931639)
                ·
                  refine ⟨1868604026572535779397459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1245736017715023852931639 1868604026572535779397459)
                  ·
                    refine ⟨2802906039858803669096189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1868604026572535779397459 2802906039858803669096189)
                    ·
                      refine ⟨1051089764947051375911071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2802906039858803669096189 1051089764947051375911071)
                      ·
                        rfl

theorem cell23_2046990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 2, 1, 1, 3].length) (baseStart_2046990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2046990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2046990 prefixEnd_2046990 := by exact prefixLift 2046990
  have htrace : WordTrace (prefixWord ++ tailWord_2046990) baseStart_2046990 baseEnd_2046990 := by
    simpa [prefixWord, tailWord_2046990, baseEnd_2046990] using wordTrace_append hprefix tailTrace_2046990
  have hstable : (prefixWord ++ tailWord_2046990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046990).length < 2 ^ (prefixWord ++ tailWord_2046990).sum := by decide
  have hdescent : baseEnd_2046990 < baseStart_2046990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046999 : List Nat := [1, 1, 3, 5, 1, 1, 1, 2, 3, 2, 3]
def baseStart_2046999 : Nat := 118140960795 + 2046999 * 2 ^ 59
def prefixEnd_2046999 : Nat := 4983230072969 + 3 ^ 40 * 2046999 * 2
def baseEnd_2046999 : Nat := 1051094386272941840698529

theorem tailTrace_2046999 : CollatzResearch.WordTrace tailWord_2046999 prefixEnd_2046999 1051094386272941840698529 := by
  unfold tailWord_2046999
  simp only [CollatzResearch.WordTrace]
  refine ⟨74660187111079697441264051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49773458074053131627509367 74660187111079697441264051)
  ·
    refine ⟨111990280666619546161896077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74660187111079697441264051 111990280666619546161896077)
    ·
      refine ⟨41996355249982329810711029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111990280666619546161896077 41996355249982329810711029)
      ·
        refine ⟨3937158304685843419754159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41996355249982329810711029 3937158304685843419754159)
        ·
          refine ⟨5905737457028765129631239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3937158304685843419754159 5905737457028765129631239)
          ·
            refine ⟨8858606185543147694446859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5905737457028765129631239 8858606185543147694446859)
            ·
              refine ⟨13287909278314721541670289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8858606185543147694446859 13287909278314721541670289)
              ·
                refine ⟨9965931958736041156252717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13287909278314721541670289 9965931958736041156252717)
                ·
                  refine ⟨3737224484526015433594769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9965931958736041156252717 3737224484526015433594769)
                  ·
                    refine ⟨2802918363394511575196077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3737224484526015433594769 2802918363394511575196077)
                    ·
                      refine ⟨1051094386272941840698529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2802918363394511575196077 1051094386272941840698529)
                      ·
                        rfl

theorem cell23_2046999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_2046999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2046999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2046999 prefixEnd_2046999 := by exact prefixLift 2046999
  have htrace : WordTrace (prefixWord ++ tailWord_2046999) baseStart_2046999 baseEnd_2046999 := by
    simpa [prefixWord, tailWord_2046999, baseEnd_2046999] using wordTrace_append hprefix tailTrace_2046999
  have hstable : (prefixWord ++ tailWord_2046999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046999).length < 2 ^ (prefixWord ++ tailWord_2046999).sum := by decide
  have hdescent : baseEnd_2046999 < baseStart_2046999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047009 : List Nat := [1, 2, 3, 2, 3, 2, 2, 1, 1, 2, 4]
def baseStart_2047009 : Nat := 118140960795 + 2047009 * 2 ^ 59
def prefixEnd_2047009 : Nat := 4983230072969 + 3 ^ 40 * 2047009 * 2
def baseEnd_2047009 : Nat := 1051099521079486801573483

theorem tailTrace_2047009 : CollatzResearch.WordTrace tailWord_2047009 prefixEnd_2047009 1051099521079486801573483 := by
  unfold tailWord_2047009
  simp only [CollatzResearch.WordTrace]
  refine ⟨74660551841043469149128081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49773701227362312766085387 74660551841043469149128081)
  ·
    refine ⟨55995413880782601861846061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74660551841043469149128081 55995413880782601861846061)
    ·
      refine ⟨20998280205293475698192273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55995413880782601861846061 20998280205293475698192273)
      ·
        refine ⟨15748710153970106773644205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20998280205293475698192273 15748710153970106773644205)
        ·
          refine ⟨5905766307738790040116577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15748710153970106773644205 5905766307738790040116577)
          ·
            refine ⟨4429324730804092530087433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5905766307738790040116577 4429324730804092530087433)
            ·
              refine ⟨3321993548103069397565575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4429324730804092530087433 3321993548103069397565575)
              ·
                refine ⟨4982990322154604096348363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3321993548103069397565575 4982990322154604096348363)
                ·
                  refine ⟨7474485483231906144522545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4982990322154604096348363 7474485483231906144522545)
                  ·
                    refine ⟨5605864112423929608391909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7474485483231906144522545 5605864112423929608391909)
                    ·
                      refine ⟨1051099521079486801573483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5605864112423929608391909 1051099521079486801573483)
                      ·
                        rfl

theorem cell23_2047009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_2047009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2047009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2047009 prefixEnd_2047009 := by exact prefixLift 2047009
  have htrace : WordTrace (prefixWord ++ tailWord_2047009) baseStart_2047009 baseEnd_2047009 := by
    simpa [prefixWord, tailWord_2047009, baseEnd_2047009] using wordTrace_append hprefix tailTrace_2047009
  have hstable : (prefixWord ++ tailWord_2047009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047009).length < 2 ^ (prefixWord ++ tailWord_2047009).sum := by decide
  have hdescent : baseEnd_2047009 < baseStart_2047009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047029 : List Nat := [1, 3, 3, 1, 1, 1, 1, 4, 4, 1, 3]
def baseStart_2047029 : Nat := 118140960795 + 2047029 * 2 ^ 59
def prefixEnd_2047029 : Nat := 4983230072969 + 3 ^ 40 * 2047029 * 2
def baseEnd_2047029 : Nat := 1051109790692576723323391

theorem tailTrace_2047029 : CollatzResearch.WordTrace tailWord_2047029 prefixEnd_2047029 1051109790692576723323391 := by
  unfold tailWord_2047029
  simp only [CollatzResearch.WordTrace]
  refine ⟨74661281300971012564856141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49774187533980675043237427 74661281300971012564856141)
  ·
    refine ⟨27997980487864129711821053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74661281300971012564856141 27997980487864129711821053)
    ·
      refine ⟨10499242682949048641932895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27997980487864129711821053 10499242682949048641932895)
      ·
        refine ⟨15748864024423572962899343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10499242682949048641932895 15748864024423572962899343)
        ·
          refine ⟨23623296036635359444349015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15748864024423572962899343 23623296036635359444349015)
          ·
            refine ⟨35434944054953039166523523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23623296036635359444349015 35434944054953039166523523)
            ·
              refine ⟨53152416082429558749785285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35434944054953039166523523 53152416082429558749785285)
              ·
                refine ⟨9966078015455542265584741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53152416082429558749785285 9966078015455542265584741)
                ·
                  refine ⟨1868639627897914174797139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9966078015455542265584741 1868639627897914174797139)
                  ·
                    refine ⟨2802959441846871262195709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1868639627897914174797139 2802959441846871262195709)
                    ·
                      refine ⟨1051109790692576723323391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2802959441846871262195709 1051109790692576723323391)
                      ·
                        rfl

theorem cell23_2047029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_2047029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2047029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2047029 prefixEnd_2047029 := by exact prefixLift 2047029
  have htrace : WordTrace (prefixWord ++ tailWord_2047029) baseStart_2047029 baseEnd_2047029 := by
    simpa [prefixWord, tailWord_2047029, baseEnd_2047029] using wordTrace_append hprefix tailTrace_2047029
  have hstable : (prefixWord ++ tailWord_2047029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047029).length < 2 ^ (prefixWord ++ tailWord_2047029).sum := by decide
  have hdescent : baseEnd_2047029 < baseStart_2047029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047030 : List Nat := [5, 1, 2, 1, 1, 2, 1, 5, 1, 2, 2]
def baseStart_2047030 : Nat := 118140960795 + 2047030 * 2 ^ 59
def prefixEnd_2047030 : Nat := 4983230072969 + 3 ^ 40 * 2047030 * 2
def baseEnd_2047030 : Nat := 1051110304173231219410887

theorem tailTrace_2047030 : CollatzResearch.WordTrace tailWord_2047030 prefixEnd_2047030 1051110304173231219410887 := by
  unfold tailWord_2047030
  simp only [CollatzResearch.WordTrace]
  refine ⟨4666332360872961858477659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49774211849311593157095029 4666332360872961858477659)
  ·
    refine ⟨6999498541309442787716489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4666332360872961858477659 6999498541309442787716489)
    ·
      refine ⟨5249623905982082090787367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6999498541309442787716489 5249623905982082090787367)
      ·
        refine ⟨7874435858973123136181051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5249623905982082090787367 7874435858973123136181051)
        ·
          refine ⟨11811653788459684704271577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7874435858973123136181051 11811653788459684704271577)
          ·
            refine ⟨8858740341344763528203683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11811653788459684704271577 8858740341344763528203683)
            ·
              refine ⟨13288110512017145292305525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8858740341344763528203683 13288110512017145292305525)
              ·
                refine ⟨1245760360501607371153643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13288110512017145292305525 1245760360501607371153643)
                ·
                  refine ⟨1868640540752411056730465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1245760360501607371153643 1868640540752411056730465)
                  ·
                    refine ⟨1401480405564308292547849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1868640540752411056730465 1401480405564308292547849)
                    ·
                      refine ⟨1051110304173231219410887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1401480405564308292547849 1051110304173231219410887)
                      ·
                        rfl

theorem cell23_2047030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_2047030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2047030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2047030 prefixEnd_2047030 := by exact prefixLift 2047030
  have htrace : WordTrace (prefixWord ++ tailWord_2047030) baseStart_2047030 baseEnd_2047030 := by
    simpa [prefixWord, tailWord_2047030, baseEnd_2047030] using wordTrace_append hprefix tailTrace_2047030
  have hstable : (prefixWord ++ tailWord_2047030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047030).length < 2 ^ (prefixWord ++ tailWord_2047030).sum := by decide
  have hdescent : baseEnd_2047030 < baseStart_2047030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047033 : List Nat := [1, 2, 1, 5, 2, 3, 2, 1, 1, 2, 3]
def baseStart_2047033 : Nat := 118140960795 + 2047033 * 2 ^ 59
def prefixEnd_2047033 : Nat := 4983230072969 + 3 ^ 40 * 2047033 * 2
def baseEnd_2047033 : Nat := 1051111844615194707673373

theorem tailTrace_2047033 : CollatzResearch.WordTrace tailWord_2047033 prefixEnd_2047033 1051111844615194707673373 := by
  unfold tailWord_2047033
  simp only [CollatzResearch.WordTrace]
  refine ⟨74661427192956521248001753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49774284795304347498667835 74661427192956521248001753)
  ·
    refine ⟨55996070394717390936001315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74661427192956521248001753 55996070394717390936001315)
    ·
      refine ⟨83994105592076086404001973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55996070394717390936001315 83994105592076086404001973)
      ·
        refine ⟨7874447399257133100375185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83994105592076086404001973 7874447399257133100375185)
        ·
          refine ⟨5905835549442849825281389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7874447399257133100375185 5905835549442849825281389)
          ·
            refine ⟨2214688331041068684480521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5905835549442849825281389 2214688331041068684480521)
            ·
              refine ⟨1661016248280801513360391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2214688331041068684480521 1661016248280801513360391)
              ·
                refine ⟨2491524372421202270040587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1661016248280801513360391 2491524372421202270040587)
                ·
                  refine ⟨3737286558631803405060881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2491524372421202270040587 3737286558631803405060881)
                  ·
                    refine ⟨2802964918973852553795661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3737286558631803405060881 2802964918973852553795661)
                    ·
                      refine ⟨1051111844615194707673373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2802964918973852553795661 1051111844615194707673373)
                      ·
                        rfl

theorem cell23_2047033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_2047033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2047033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2047033 prefixEnd_2047033 := by exact prefixLift 2047033
  have htrace : WordTrace (prefixWord ++ tailWord_2047033) baseStart_2047033 baseEnd_2047033 := by
    simpa [prefixWord, tailWord_2047033, baseEnd_2047033] using wordTrace_append hprefix tailTrace_2047033
  have hstable : (prefixWord ++ tailWord_2047033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047033).length < 2 ^ (prefixWord ++ tailWord_2047033).sum := by decide
  have hdescent : baseEnd_2047033 < baseStart_2047033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047072 : List Nat := [2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 5]
def baseStart_2047072 : Nat := 118140960795 + 2047072 * 2 ^ 59
def prefixEnd_2047072 : Nat := 4983230072969 + 3 ^ 40 * 2047072 * 2
def baseEnd_2047072 : Nat := 1051131870360720055085693

theorem tailTrace_2047072 : CollatzResearch.WordTrace tailWord_2047072 prefixEnd_2047072 1051131870360720055085693 := by
  unfold tailWord_2047072
  simp only [CollatzResearch.WordTrace]
  refine ⟨37331424819907615454335735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49775233093210153939114313 37331424819907615454335735)
  ·
    refine ⟨55997137229861423181503603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37331424819907615454335735 55997137229861423181503603)
    ·
      refine ⟨83995705844792134772255405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55997137229861423181503603 83995705844792134772255405)
      ·
        refine ⟨31498389691797050539595777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83995705844792134772255405 31498389691797050539595777)
        ·
          refine ⟨23623792268847787904696833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31498389691797050539595777 23623792268847787904696833)
          ·
            refine ⟨17717844201635840928522625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23623792268847787904696833 17717844201635840928522625)
            ·
              refine ⟨13288383151226880696391969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17717844201635840928522625 13288383151226880696391969)
              ·
                refine ⟨9966287363420160522293977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13288383151226880696391969 9966287363420160522293977)
                ·
                  refine ⟨7474715522565120391720483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9966287363420160522293977 7474715522565120391720483)
                  ·
                    refine ⟨11212073283847680587580725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7474715522565120391720483 11212073283847680587580725)
                    ·
                      refine ⟨1051131870360720055085693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11212073283847680587580725 1051131870360720055085693)
                      ·
                        rfl

theorem cell23_2047072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_2047072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2047072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2047072 prefixEnd_2047072 := by exact prefixLift 2047072
  have htrace : WordTrace (prefixWord ++ tailWord_2047072) baseStart_2047072 baseEnd_2047072 := by
    simpa [prefixWord, tailWord_2047072, baseEnd_2047072] using wordTrace_append hprefix tailTrace_2047072
  have hstable : (prefixWord ++ tailWord_2047072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047072).length < 2 ^ (prefixWord ++ tailWord_2047072).sum := by decide
  have hdescent : baseEnd_2047072 < baseStart_2047072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047159 : List Nat := [1, 1, 3, 1, 4, 1, 1, 4, 2, 1, 4]
def baseStart_2047159 : Nat := 118140960795 + 2047159 * 2 ^ 59
def prefixEnd_2047159 : Nat := 4983230072969 + 3 ^ 40 * 2047159 * 2
def baseEnd_2047159 : Nat := 1051176543177661214697793

theorem tailTrace_2047159 : CollatzResearch.WordTrace tailWord_2047159 prefixEnd_2047159 1051176543177661214697793 := by
  unfold tailWord_2047159
  simp only [CollatzResearch.WordTrace]
  refine ⟨74666022790500044767088531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49777348527000029844725687 74666022790500044767088531)
  ·
    refine ⟨111999034185750067150632797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74666022790500044767088531 111999034185750067150632797)
    ·
      refine ⟨41999637819656275181487299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111999034185750067150632797 41999637819656275181487299)
      ·
        refine ⟨62999456729484412772230949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41999637819656275181487299 62999456729484412772230949)
        ·
          refine ⟨11812398136778327394793303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62999456729484412772230949 11812398136778327394793303)
          ·
            refine ⟨17718597205167491092189955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11812398136778327394793303 17718597205167491092189955)
            ·
              refine ⟨26577895807751236638284933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17718597205167491092189955 26577895807751236638284933)
              ·
                refine ⟨4983355463953356869678425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26577895807751236638284933 4983355463953356869678425)
                ·
                  refine ⟨3737516597965017652258819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4983355463953356869678425 3737516597965017652258819)
                  ·
                    refine ⟨5606274896947526478388229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3737516597965017652258819 5606274896947526478388229)
                    ·
                      refine ⟨1051176543177661214697793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5606274896947526478388229 1051176543177661214697793)
                      ·
                        rfl

theorem cell23_2047159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 2, 1, 4].length) (baseStart_2047159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2047159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2047159 prefixEnd_2047159 := by exact prefixLift 2047159
  have htrace : WordTrace (prefixWord ++ tailWord_2047159) baseStart_2047159 baseEnd_2047159 := by
    simpa [prefixWord, tailWord_2047159, baseEnd_2047159] using wordTrace_append hprefix tailTrace_2047159
  have hstable : (prefixWord ++ tailWord_2047159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047159).length < 2 ^ (prefixWord ++ tailWord_2047159).sum := by decide
  have hdescent : baseEnd_2047159 < baseStart_2047159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047162 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 1, 5, 5]
def baseStart_2047162 : Nat := 118140960795 + 2047162 * 2 ^ 59
def prefixEnd_2047162 : Nat := 4983230072969 + 3 ^ 40 * 2047162 * 2
def baseEnd_2047162 : Nat := 1051178083619624702960279

theorem tailTrace_2047162 : CollatzResearch.WordTrace tailWord_2047162 prefixEnd_2047162 1051178083619624702960279 := by
  unfold tailWord_2047162
  simp only [CollatzResearch.WordTrace]
  refine ⟨18666533052372294069861935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49777421472992784186298493 18666533052372294069861935)
  ·
    refine ⟨27999799578558441104792903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18666533052372294069861935 27999799578558441104792903)
    ·
      refine ⟨41999699367837661657189355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27999799578558441104792903 41999699367837661657189355)
      ·
        refine ⟨62999549051756492485784033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41999699367837661657189355 62999549051756492485784033)
        ·
          refine ⟨47249661788817369364338025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62999549051756492485784033 47249661788817369364338025)
          ·
            refine ⟨35437246341613027023253519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47249661788817369364338025 35437246341613027023253519)
            ·
              refine ⟨53155869512419540534880279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35437246341613027023253519 53155869512419540534880279)
              ·
                refine ⟨79733804268629310802320419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53155869512419540534880279 79733804268629310802320419)
                ·
                  refine ⟨119600706402943966203480629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79733804268629310802320419 119600706402943966203480629)
                  ·
                    refine ⟨11212566225275996831576309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 119600706402943966203480629 11212566225275996831576309)
                    ·
                      refine ⟨1051178083619624702960279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11212566225275996831576309 1051178083619624702960279)
                      ·
                        rfl

theorem cell23_2047162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 1, 5, 5].length) (baseStart_2047162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2047162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2047162 prefixEnd_2047162 := by exact prefixLift 2047162
  have htrace : WordTrace (prefixWord ++ tailWord_2047162) baseStart_2047162 baseEnd_2047162 := by
    simpa [prefixWord, tailWord_2047162, baseEnd_2047162] using wordTrace_append hprefix tailTrace_2047162
  have hstable : (prefixWord ++ tailWord_2047162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047162).length < 2 ^ (prefixWord ++ tailWord_2047162).sum := by decide
  have hdescent : baseEnd_2047162 < baseStart_2047162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047170 : List Nat := [3, 5, 1, 1, 2, 1, 1, 1, 2, 3, 3]
def baseStart_2047170 : Nat := 118140960795 + 2047170 * 2 ^ 59
def prefixEnd_2047170 : Nat := 4983230072969 + 3 ^ 40 * 2047170 * 2
def baseEnd_2047170 : Nat := 1051182191464860671660243

theorem tailTrace_2047170 : CollatzResearch.WordTrace tailWord_2047170 prefixEnd_2047170 1051182191464860671660243 := by
  unfold tailWord_2047170
  simp only [CollatzResearch.WordTrace]
  refine ⟨18666605998365048411434741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49777615995640129097159309 18666605998365048411434741)
  ·
    refine ⟨1749994312346723288572007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18666605998365048411434741 1749994312346723288572007)
    ·
      refine ⟨2624991468520084932858011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1749994312346723288572007 2624991468520084932858011)
      ·
        refine ⟨3937487202780127399287017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2624991468520084932858011 3937487202780127399287017)
        ·
          refine ⟨2953115402085095549465263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3937487202780127399287017 2953115402085095549465263)
          ·
            refine ⟨4429673103127643324197895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2953115402085095549465263 4429673103127643324197895)
            ·
              refine ⟨6644509654691464986296843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4429673103127643324197895 6644509654691464986296843)
              ·
                refine ⟨9966764482037197479445265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6644509654691464986296843 9966764482037197479445265)
                ·
                  refine ⟨7475073361527898109583949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9966764482037197479445265 7475073361527898109583949)
                  ·
                    refine ⟨2803152510572961791093981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7475073361527898109583949 2803152510572961791093981)
                    ·
                      refine ⟨1051182191464860671660243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2803152510572961791093981 1051182191464860671660243)
                      ·
                        rfl

theorem cell23_2047170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_2047170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2047170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2047170 prefixEnd_2047170 := by exact prefixLift 2047170
  have htrace : WordTrace (prefixWord ++ tailWord_2047170) baseStart_2047170 baseEnd_2047170 := by
    simpa [prefixWord, tailWord_2047170, baseEnd_2047170] using wordTrace_append hprefix tailTrace_2047170
  have hstable : (prefixWord ++ tailWord_2047170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047170).length < 2 ^ (prefixWord ++ tailWord_2047170).sum := by decide
  have hdescent : baseEnd_2047170 < baseStart_2047170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047186 : List Nat := [3, 2, 2, 2, 1, 1, 3, 2, 3, 4]
def baseStart_2047186 : Nat := 118140960795 + 2047186 * 2 ^ 59
def prefixEnd_2047186 : Nat := 4983230072969 + 3 ^ 40 * 2047186 * 2
def baseEnd_2047186 : Nat := 350396802385110869686723

theorem tailTrace_2047186 : CollatzResearch.WordTrace tailWord_2047186 prefixEnd_2047186 350396802385110869686723 := by
  unfold tailWord_2047186
  simp only [CollatzResearch.WordTrace]
  refine ⟨18666751890350557094580353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49778005040934818918880941 18666751890350557094580353)
  ·
    refine ⟨14000063917762917820935265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18666751890350557094580353 14000063917762917820935265)
    ·
      refine ⟨10500047938322188365701449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14000063917762917820935265 10500047938322188365701449)
      ·
        refine ⟨7875035953741641274276087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10500047938322188365701449 7875035953741641274276087)
        ·
          refine ⟨11812553930612461911414131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7875035953741641274276087 11812553930612461911414131)
          ·
            refine ⟨17718830895918692867121197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11812553930612461911414131 17718830895918692867121197)
            ·
              refine ⟨6644561585969509825170449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17718830895918692867121197 6644561585969509825170449)
              ·
                refine ⟨4983421189477132368877837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6644561585969509825170449 4983421189477132368877837)
                ·
                  refine ⟨1868782946053924638329189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4983421189477132368877837 1868782946053924638329189)
                  ·
                    refine ⟨350396802385110869686723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1868782946053924638329189 350396802385110869686723)
                    ·
                      rfl

theorem cell23_2047186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_2047186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2047186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2047186 prefixEnd_2047186 := by exact prefixLift 2047186
  have htrace : WordTrace (prefixWord ++ tailWord_2047186) baseStart_2047186 baseEnd_2047186 := by
    simpa [prefixWord, tailWord_2047186, baseEnd_2047186] using wordTrace_append hprefix tailTrace_2047186
  have hstable : (prefixWord ++ tailWord_2047186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047186).length < 2 ^ (prefixWord ++ tailWord_2047186).sum := by decide
  have hdescent : baseEnd_2047186 < baseStart_2047186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047190 : List Nat := [5, 2, 1, 2, 2, 2, 1, 1, 2, 5]
def baseStart_2047190 : Nat := 118140960795 + 2047190 * 2 ^ 59
def prefixEnd_2047190 : Nat := 4983230072969 + 3 ^ 40 * 2047190 * 2
def baseEnd_2047190 : Nat := 350397487025983531136717

theorem tailTrace_2047190 : CollatzResearch.WordTrace tailWord_2047190 prefixEnd_2047190 350397487025983531136717 := by
  unfold tailWord_2047190
  simp only [CollatzResearch.WordTrace]
  refine ⟨4666697090836733566341689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49778102302258491374311349 4666697090836733566341689)
  ·
    refine ⟨3500022818127550174756267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4666697090836733566341689 3500022818127550174756267)
    ·
      refine ⟨5250034227191325262134401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3500022818127550174756267 5250034227191325262134401)
      ·
        refine ⟨3937525670393493946600801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5250034227191325262134401 3937525670393493946600801)
        ·
          refine ⟨2953144252795120459950601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3937525670393493946600801 2953144252795120459950601)
          ·
            refine ⟨2214858189596340344962951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2953144252795120459950601 2214858189596340344962951)
            ·
              refine ⟨3322287284394510517444427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2214858189596340344962951 3322287284394510517444427)
              ·
                refine ⟨4983430926591765776166641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3322287284394510517444427 4983430926591765776166641)
                ·
                  refine ⟨3737573194943824332124981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4983430926591765776166641 3737573194943824332124981)
                  ·
                    refine ⟨350397487025983531136717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3737573194943824332124981 350397487025983531136717)
                    ·
                      rfl

theorem cell23_2047190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_2047190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2047190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2047190 prefixEnd_2047190 := by exact prefixLift 2047190
  have htrace : WordTrace (prefixWord ++ tailWord_2047190) baseStart_2047190 baseEnd_2047190 := by
    simpa [prefixWord, tailWord_2047190, baseEnd_2047190] using wordTrace_append hprefix tailTrace_2047190
  have hstable : (prefixWord ++ tailWord_2047190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047190).length < 2 ^ (prefixWord ++ tailWord_2047190).sum := by decide
  have hdescent : baseEnd_2047190 < baseStart_2047190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047246 : List Nat := [4, 1, 1, 2, 1, 3, 1, 4, 1, 5]
def baseStart_2047246 : Nat := 118140960795 + 2047246 * 2 ^ 59
def prefixEnd_2047246 : Nat := 4983230072969 + 3 ^ 40 * 2047246 * 2
def baseEnd_2047246 : Nat := 350407071998200791436631

theorem tailTrace_2047246 : CollatzResearch.WordTrace tailWord_2047246 prefixEnd_2047246 350407071998200791436631 := by
  unfold tailWord_2047246
  simp only [CollatzResearch.WordTrace]
  refine ⟨9333649492648107328188199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49779463960789905750337061 9333649492648107328188199)
  ·
    refine ⟨14000474238972160992282299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9333649492648107328188199 14000474238972160992282299)
    ·
      refine ⟨21000711358458241488423449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14000474238972160992282299 21000711358458241488423449)
      ·
        refine ⟨15750533518843681116317587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21000711358458241488423449 15750533518843681116317587)
        ·
          refine ⟨23625800278265521674476381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15750533518843681116317587 23625800278265521674476381)
          ·
            refine ⟨8859675104349570627928643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23625800278265521674476381 8859675104349570627928643)
            ·
              refine ⟨13289512656524355941892965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8859675104349570627928643 13289512656524355941892965)
              ·
                refine ⟨2491783623098316739104931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13289512656524355941892965 2491783623098316739104931)
                ·
                  refine ⟨3737675434647475108657397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2491783623098316739104931 3737675434647475108657397)
                  ·
                    refine ⟨350407071998200791436631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3737675434647475108657397 350407071998200791436631)
                    ·
                      rfl

theorem cell23_2047246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 4, 1, 5].length) (baseStart_2047246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2047246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2047246 prefixEnd_2047246 := by exact prefixLift 2047246
  have htrace : WordTrace (prefixWord ++ tailWord_2047246) baseStart_2047246 baseEnd_2047246 := by
    simpa [prefixWord, tailWord_2047246, baseEnd_2047246] using wordTrace_append hprefix tailTrace_2047246
  have hstable : (prefixWord ++ tailWord_2047246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047246).length < 2 ^ (prefixWord ++ tailWord_2047246).sum := by decide
  have hdescent : baseEnd_2047246 < baseStart_2047246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047260 : List Nat := [2, 2, 3, 1, 1, 1, 5, 3, 1, 1, 3]
def baseStart_2047260 : Nat := 118140960795 + 2047260 * 2 ^ 59
def prefixEnd_2047260 : Nat := 4983230072969 + 3 ^ 40 * 2047260 * 2
def baseEnd_2047260 : Nat := 1051228404723765319534829

theorem tailTrace_2047260 : CollatzResearch.WordTrace tailWord_2047260 prefixEnd_2047260 1051228404723765319534829 := by
  unfold tailWord_2047260
  simp only [CollatzResearch.WordTrace]
  refine ⟨37334853281567069508257617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49779804375422759344343489 37334853281567069508257617)
  ·
    refine ⟨28001139961175302131193213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37334853281567069508257617 28001139961175302131193213)
    ·
      refine ⟨10500427485440738299197455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28001139961175302131193213 10500427485440738299197455)
      ·
        refine ⟨15750641228161107448796183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10500427485440738299197455 15750641228161107448796183)
        ·
          refine ⟨23625961842241661173194275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15750641228161107448796183 23625961842241661173194275)
          ·
            refine ⟨35438942763362491759791413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23625961842241661173194275 35438942763362491759791413)
            ·
              refine ⟨3322400884065233602480445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35438942763362491759791413 3322400884065233602480445)
              ·
                refine ⟨1245900331524462600930167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3322400884065233602480445 1245900331524462600930167)
                ·
                  refine ⟨1868850497286693901395251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1245900331524462600930167 1868850497286693901395251)
                  ·
                    refine ⟨2803275745930040852092877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1868850497286693901395251 2803275745930040852092877)
                    ·
                      refine ⟨1051228404723765319534829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2803275745930040852092877 1051228404723765319534829)
                      ·
                        rfl

theorem cell23_2047260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 3, 1, 1, 3].length) (baseStart_2047260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2047260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2047260 prefixEnd_2047260 := by exact prefixLift 2047260
  have htrace : WordTrace (prefixWord ++ tailWord_2047260) baseStart_2047260 baseEnd_2047260 := by
    simpa [prefixWord, tailWord_2047260, baseEnd_2047260] using wordTrace_append hprefix tailTrace_2047260
  have hstable : (prefixWord ++ tailWord_2047260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047260).length < 2 ^ (prefixWord ++ tailWord_2047260).sum := by decide
  have hdescent : baseEnd_2047260 < baseStart_2047260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047276 : List Nat := [2, 2, 1, 1, 1, 3, 1, 6, 2, 4]
def baseStart_2047276 : Nat := 118140960795 + 2047276 * 2 ^ 59
def prefixEnd_2047276 : Nat := 4983230072969 + 3 ^ 40 * 2047276 * 2
def baseEnd_2047276 : Nat := 350412206804745752311585

theorem tailTrace_2047276 : CollatzResearch.WordTrace tailWord_2047276 prefixEnd_2047276 350412206804745752311585 := by
  unfold tailWord_2047276
  simp only [CollatzResearch.WordTrace]
  refine ⟨37335145065538086874548841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49780193420717449166065121 37335145065538086874548841)
  ·
    refine ⟨28001358799153565155911631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37335145065538086874548841 28001358799153565155911631)
    ·
      refine ⟨42002038198730347733867447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28001358799153565155911631 42002038198730347733867447)
      ·
        refine ⟨63003057298095521600801171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42002038198730347733867447 63003057298095521600801171)
        ·
          refine ⟨94504585947143282401201757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63003057298095521600801171 94504585947143282401201757)
          ·
            refine ⟨35439219730178730900450659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94504585947143282401201757 35439219730178730900450659)
            ·
              refine ⟨53158829595268096350675989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35439219730178730900450659 53158829595268096350675989)
              ·
                refine ⟨2491820137278192016437937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53158829595268096350675989 2491820137278192016437937)
                ·
                  refine ⟨1868865102958644012328453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2491820137278192016437937 1868865102958644012328453)
                  ·
                    refine ⟨350412206804745752311585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1868865102958644012328453 350412206804745752311585)
                    ·
                      rfl

theorem cell23_2047276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 4].length) (baseStart_2047276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2047276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2047276 prefixEnd_2047276 := by exact prefixLift 2047276
  have htrace : WordTrace (prefixWord ++ tailWord_2047276) baseStart_2047276 baseEnd_2047276 := by
    simpa [prefixWord, tailWord_2047276, baseEnd_2047276] using wordTrace_append hprefix tailTrace_2047276
  have hstable : (prefixWord ++ tailWord_2047276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047276).length < 2 ^ (prefixWord ++ tailWord_2047276).sum := by decide
  have hdescent : baseEnd_2047276 < baseStart_2047276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047277 : List Nat := [1, 5, 3, 1, 1, 3, 1, 1, 3, 1, 3]
def baseStart_2047277 : Nat := 118140960795 + 2047277 * 2 ^ 59
def prefixEnd_2047277 : Nat := 4983230072969 + 3 ^ 40 * 2047277 * 2
def baseEnd_2047277 : Nat := 1051237133894891753022251

theorem tailTrace_2047277 : CollatzResearch.WordTrace tailWord_2047277 prefixEnd_2047277 1051237133894891753022251 := by
  unfold tailWord_2047277
  simp only [CollatzResearch.WordTrace]
  refine ⟨74670326604072550919884085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49780217736048367279922723 74670326604072550919884085)
  ·
    refine ⟨7000343119131801648739133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74670326604072550919884085 7000343119131801648739133)
    ·
      refine ⟨2625128669674425618277175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7000343119131801648739133 2625128669674425618277175)
      ·
        refine ⟨3937693004511638427415763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2625128669674425618277175 3937693004511638427415763)
        ·
          refine ⟨5906539506767457641123645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3937693004511638427415763 5906539506767457641123645)
          ·
            refine ⟨2214952315037796615421367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5906539506767457641123645 2214952315037796615421367)
            ·
              refine ⟨3322428472556694923132051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2214952315037796615421367 3322428472556694923132051)
              ·
                refine ⟨4983642708835042384698077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3322428472556694923132051 4983642708835042384698077)
                ·
                  refine ⟨1868866015813140894261779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4983642708835042384698077 1868866015813140894261779)
                  ·
                    refine ⟨2803299023719711341392669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1868866015813140894261779 2803299023719711341392669)
                    ·
                      refine ⟨1051237133894891753022251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2803299023719711341392669 1051237133894891753022251)
                      ·
                        rfl

theorem cell23_2047277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_2047277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2047277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2047277 prefixEnd_2047277 := by exact prefixLift 2047277
  have htrace : WordTrace (prefixWord ++ tailWord_2047277) baseStart_2047277 baseEnd_2047277 := by
    simpa [prefixWord, tailWord_2047277, baseEnd_2047277] using wordTrace_append hprefix tailTrace_2047277
  have hstable : (prefixWord ++ tailWord_2047277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047277).length < 2 ^ (prefixWord ++ tailWord_2047277).sum := by decide
  have hdescent : baseEnd_2047277 < baseStart_2047277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047300 : List Nat := [2, 3, 4, 1, 1, 1, 3, 2, 1, 1, 4]
def baseStart_2047300 : Nat := 118140960795 + 2047300 * 2 ^ 59
def prefixEnd_2047300 : Nat := 4983230072969 + 3 ^ 40 * 2047300 * 2
def baseEnd_2047300 : Nat := 1051248943949945163034645

theorem tailTrace_2047300 : CollatzResearch.WordTrace tailWord_2047300 prefixEnd_2047300 1051248943949945163034645 := by
  unfold tailWord_2047300
  simp only [CollatzResearch.WordTrace]
  refine ⟨37335582741494612923985677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49780776988659483898647569 37335582741494612923985677)
  ·
    refine ⟨14000843528060479846494629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37335582741494612923985677 14000843528060479846494629)
    ·
      refine ⟨2625158161511339971217743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14000843528060479846494629 2625158161511339971217743)
      ·
        refine ⟨3937737242267009956826615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2625158161511339971217743 3937737242267009956826615)
        ·
          refine ⟨5906605863400514935239923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3937737242267009956826615 5906605863400514935239923)
          ·
            refine ⟨8859908795100772402859885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5906605863400514935239923 8859908795100772402859885)
            ·
              refine ⟨3322465798162789651072457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8859908795100772402859885 3322465798162789651072457)
              ·
                refine ⟨2491849348622092238304343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3322465798162789651072457 2491849348622092238304343)
                ·
                  refine ⟨3737774022933138357456515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2491849348622092238304343 3737774022933138357456515)
                  ·
                    refine ⟨5606661034399707536184773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3737774022933138357456515 5606661034399707536184773)
                    ·
                      refine ⟨1051248943949945163034645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5606661034399707536184773 1051248943949945163034645)
                      ·
                        rfl

theorem cell23_2047300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_2047300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2047300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2047300 prefixEnd_2047300 := by exact prefixLift 2047300
  have htrace : WordTrace (prefixWord ++ tailWord_2047300) baseStart_2047300 baseEnd_2047300 := by
    simpa [prefixWord, tailWord_2047300, baseEnd_2047300] using wordTrace_append hprefix tailTrace_2047300
  have hstable : (prefixWord ++ tailWord_2047300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047300).length < 2 ^ (prefixWord ++ tailWord_2047300).sum := by decide
  have hdescent : baseEnd_2047300 < baseStart_2047300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047303 : List Nat := [1, 1, 4, 1, 2, 3, 3, 2, 1, 2, 3]
def baseStart_2047303 : Nat := 118140960795 + 2047303 * 2 ^ 59
def prefixEnd_2047303 : Nat := 4983230072969 + 3 ^ 40 * 2047303 * 2
def baseEnd_2047303 : Nat := 1051250484391908651297131

theorem tailTrace_2047303 : CollatzResearch.WordTrace tailWord_2047303 prefixEnd_2047303 1051250484391908651297131 := by
  unfold tailWord_2047303
  simp only [CollatzResearch.WordTrace]
  refine ⟨74671274901978357360330563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49780849934652238240220375 74671274901978357360330563)
  ·
    refine ⟨112006912352967536040495845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74671274901978357360330563 112006912352967536040495845)
    ·
      refine ⟨21001296066181413007592971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112006912352967536040495845 21001296066181413007592971)
      ·
        refine ⟨31501944099272119511389457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21001296066181413007592971 31501944099272119511389457)
        ·
          refine ⟨23626458074454089633542093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31501944099272119511389457 23626458074454089633542093)
          ·
            refine ⟨8859921777920283612578285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23626458074454089633542093 8859921777920283612578285)
            ·
              refine ⟨3322470666720106354716857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8859921777920283612578285 3322470666720106354716857)
              ·
                refine ⟨2491853000040079766037643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3322470666720106354716857 2491853000040079766037643)
                ·
                  refine ⟨3737779500060119649056465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2491853000040079766037643 3737779500060119649056465)
                  ·
                    refine ⟨2803334625045089736792349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3737779500060119649056465 2803334625045089736792349)
                    ·
                      refine ⟨1051250484391908651297131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2803334625045089736792349 1051250484391908651297131)
                      ·
                        rfl

theorem cell23_2047303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 2, 1, 2, 3].length) (baseStart_2047303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2047303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2047303 prefixEnd_2047303 := by exact prefixLift 2047303
  have htrace : WordTrace (prefixWord ++ tailWord_2047303) baseStart_2047303 baseEnd_2047303 := by
    simpa [prefixWord, tailWord_2047303, baseEnd_2047303] using wordTrace_append hprefix tailTrace_2047303
  have hstable : (prefixWord ++ tailWord_2047303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047303).length < 2 ^ (prefixWord ++ tailWord_2047303).sum := by decide
  have hdescent : baseEnd_2047303 < baseStart_2047303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047329 : List Nat := [1, 2, 3, 1, 1, 1, 1, 4, 2, 2, 5]
def baseStart_2047329 : Nat := 118140960795 + 2047329 * 2 ^ 59
def prefixEnd_2047329 : Nat := 4983230072969 + 3 ^ 40 * 2047329 * 2
def baseEnd_2047329 : Nat := 1051263834888925549572011

theorem tailTrace_2047329 : CollatzResearch.WordTrace tailWord_2047329 prefixEnd_2047329 1051263834888925549572011 := by
  unfold tailWord_2047329
  simp only [CollatzResearch.WordTrace]
  refine ⟨74672223199884163800777041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49781482133256109200518027 74672223199884163800777041)
  ·
    refine ⟨56004167399913122850582781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74672223199884163800777041 56004167399913122850582781)
    ·
      refine ⟨21001562774967421068968543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56004167399913122850582781 21001562774967421068968543)
      ·
        refine ⟨31502344162451131603452815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21001562774967421068968543 31502344162451131603452815)
        ·
          refine ⟨47253516243676697405179223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31502344162451131603452815 47253516243676697405179223)
          ·
            refine ⟨70880274365515046107768835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47253516243676697405179223 70880274365515046107768835)
            ·
              refine ⟨106320411548272569161653253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70880274365515046107768835 106320411548272569161653253)
              ·
                refine ⟨19935077165301106717809985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106320411548272569161653253 19935077165301106717809985)
                ·
                  refine ⟨14951307873975830038357489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19935077165301106717809985 14951307873975830038357489)
                  ·
                    refine ⟨11213480905481872528768117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14951307873975830038357489 11213480905481872528768117)
                    ·
                      refine ⟨1051263834888925549572011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11213480905481872528768117 1051263834888925549572011)
                      ·
                        rfl

theorem cell23_2047329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_2047329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2047329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2047329 prefixEnd_2047329 := by exact prefixLift 2047329
  have htrace : WordTrace (prefixWord ++ tailWord_2047329) baseStart_2047329 baseEnd_2047329 := by
    simpa [prefixWord, tailWord_2047329, baseEnd_2047329] using wordTrace_append hprefix tailTrace_2047329
  have hstable : (prefixWord ++ tailWord_2047329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047329).length < 2 ^ (prefixWord ++ tailWord_2047329).sum := by decide
  have hdescent : baseEnd_2047329 < baseStart_2047329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047384 : List Nat := [2, 1, 2, 5, 3, 1, 1, 2, 2, 1, 3]
def baseStart_2047384 : Nat := 118140960795 + 2047384 * 2 ^ 59
def prefixEnd_2047384 : Nat := 4983230072969 + 3 ^ 40 * 2047384 * 2
def baseEnd_2047384 : Nat := 1051292076324922834384259

theorem tailTrace_2047384 : CollatzResearch.WordTrace tailWord_2047384 prefixEnd_2047384 1051292076324922834384259 := by
  unfold tailWord_2047384
  simp only [CollatzResearch.WordTrace]
  refine ⟨37337114607342454097014603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49782819476456605462686137 37337114607342454097014603)
  ·
    refine ⟨56005671911013681145521905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37337114607342454097014603 56005671911013681145521905)
    ·
      refine ⟨42004253933260260859141429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56005671911013681145521905 42004253933260260859141429)
      ·
        refine ⟨3937898806243149455544509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42004253933260260859141429 3937898806243149455544509)
        ·
          refine ⟨1476712052341181045829191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3937898806243149455544509 1476712052341181045829191)
          ·
            refine ⟨2215068078511771568743787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1476712052341181045829191 2215068078511771568743787)
            ·
              refine ⟨3322602117767657353115681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2215068078511771568743787 3322602117767657353115681)
              ·
                refine ⟨2491951588325743014836761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3322602117767657353115681 2491951588325743014836761)
                ·
                  refine ⟨1868963691244307261127571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2491951588325743014836761 1868963691244307261127571)
                  ·
                    refine ⟨2803445536866460891691357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1868963691244307261127571 2803445536866460891691357)
                    ·
                      refine ⟨1051292076324922834384259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2803445536866460891691357 1051292076324922834384259)
                      ·
                        rfl

theorem cell23_2047384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_2047384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2047384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2047384 prefixEnd_2047384 := by exact prefixLift 2047384
  have htrace : WordTrace (prefixWord ++ tailWord_2047384) baseStart_2047384 baseEnd_2047384 := by
    simpa [prefixWord, tailWord_2047384, baseEnd_2047384] using wordTrace_append hprefix tailTrace_2047384
  have hstable : (prefixWord ++ tailWord_2047384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047384).length < 2 ^ (prefixWord ++ tailWord_2047384).sum := by decide
  have hdescent : baseEnd_2047384 < baseStart_2047384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047386 : List Nat := [3, 1, 1, 4, 1, 1, 1, 1, 4, 2, 4]
def baseStart_2047386 : Nat := 118140960795 + 2047386 * 2 ^ 59
def prefixEnd_2047386 : Nat := 4983230072969 + 3 ^ 40 * 2047386 * 2
def baseEnd_2047386 : Nat := 1051293103286231826559249

theorem tailTrace_2047386 : CollatzResearch.WordTrace tailWord_2047386 prefixEnd_2047386 1051293103286231826559249 := by
  unfold tailWord_2047386
  simp only [CollatzResearch.WordTrace]
  refine ⟨18668575540169415633900503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49782868107118441690401341 18668575540169415633900503)
  ·
    refine ⟨28002863310254123450850755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18668575540169415633900503 28002863310254123450850755)
    ·
      refine ⟨42004294965381185176276133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28002863310254123450850755 42004294965381185176276133)
      ·
        refine ⟨7875805306008972220551775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42004294965381185176276133 7875805306008972220551775)
        ·
          refine ⟨11813707959013458330827663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7875805306008972220551775 11813707959013458330827663)
          ·
            refine ⟨17720561938520187496241495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11813707959013458330827663 17720561938520187496241495)
            ·
              refine ⟨26580842907780281244362243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17720561938520187496241495 26580842907780281244362243)
              ·
                refine ⟨39871264361670421866543365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26580842907780281244362243 39871264361670421866543365)
                ·
                  refine ⟨7475862067813204099976881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39871264361670421866543365 7475862067813204099976881)
                  ·
                    refine ⟨5606896550859903074982661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7475862067813204099976881 5606896550859903074982661)
                    ·
                      refine ⟨1051293103286231826559249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5606896550859903074982661 1051293103286231826559249)
                      ·
                        rfl

theorem cell23_2047386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_2047386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2047386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2047386 prefixEnd_2047386 := by exact prefixLift 2047386
  have htrace : WordTrace (prefixWord ++ tailWord_2047386) baseStart_2047386 baseEnd_2047386 := by
    simpa [prefixWord, tailWord_2047386, baseEnd_2047386] using wordTrace_append hprefix tailTrace_2047386
  have hstable : (prefixWord ++ tailWord_2047386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047386).length < 2 ^ (prefixWord ++ tailWord_2047386).sum := by decide
  have hdescent : baseEnd_2047386 < baseStart_2047386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047453 : List Nat := [1, 4, 3, 1, 1, 3, 1, 1, 1, 2, 5]
def baseStart_2047453 : Nat := 118140960795 + 2047453 * 2 ^ 59
def prefixEnd_2047453 : Nat := 4983230072969 + 3 ^ 40 * 2047453 * 2
def baseEnd_2047453 : Nat := 1051327506490083064421441

theorem tailTrace_2047453 : CollatzResearch.WordTrace tailWord_2047453 prefixEnd_2047453 1051327506490083064421441 := by
  unfold tailWord_2047453
  simp only [CollatzResearch.WordTrace]
  refine ⟨74676745851434932978291013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49784497234289955318860675 74676745851434932978291013)
  ·
    refine ⟨14001889847144049933429565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74676745851434932978291013 14001889847144049933429565)
    ·
      refine ⟨5250708692679018725036087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14001889847144049933429565 5250708692679018725036087)
      ·
        refine ⟨7876063039018528087554131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5250708692679018725036087 7876063039018528087554131)
        ·
          refine ⟨11814094558527792131331197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7876063039018528087554131 11814094558527792131331197)
          ·
            refine ⟨4430285459447922049249199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11814094558527792131331197 4430285459447922049249199)
            ·
              refine ⟨6645428189171883073873799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4430285459447922049249199 6645428189171883073873799)
              ·
                refine ⟨9968142283757824610810699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6645428189171883073873799 9968142283757824610810699)
                ·
                  refine ⟨14952213425636736916216049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9968142283757824610810699 14952213425636736916216049)
                  ·
                    refine ⟨11214160069227552687162037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14952213425636736916216049 11214160069227552687162037)
                    ·
                      refine ⟨1051327506490083064421441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11214160069227552687162037 1051327506490083064421441)
                      ·
                        rfl

theorem cell23_2047453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_2047453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2047453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2047453 prefixEnd_2047453 := by exact prefixLift 2047453
  have htrace : WordTrace (prefixWord ++ tailWord_2047453) baseStart_2047453 baseEnd_2047453 := by
    simpa [prefixWord, tailWord_2047453, baseEnd_2047453] using wordTrace_append hprefix tailTrace_2047453
  have hstable : (prefixWord ++ tailWord_2047453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047453).length < 2 ^ (prefixWord ++ tailWord_2047453).sum := by decide
  have hdescent : baseEnd_2047453 < baseStart_2047453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047507 : List Nat := [1, 1, 1, 2, 1, 6, 4, 2, 1, 4]
def baseStart_2047507 : Nat := 118140960795 + 2047507 * 2 ^ 59
def prefixEnd_2047507 : Nat := 4983230072969 + 3 ^ 40 * 2047507 * 2
def baseEnd_2047507 : Nat := 350451744815141951048731

theorem tailTrace_2047507 : CollatzResearch.WordTrace tailWord_2047507 prefixEnd_2047507 350451744815141951048731 := by
  unfold tailWord_2047507
  simp only [CollatzResearch.WordTrace]
  refine ⟨74678715393239300200756775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49785810262159533467171183 74678715393239300200756775)
  ·
    refine ⟨112018073089858950301135163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74678715393239300200756775 112018073089858950301135163)
    ·
      refine ⟨168027109634788425451702745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112018073089858950301135163 168027109634788425451702745)
      ·
        refine ⟨126020332226091319088777059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168027109634788425451702745 126020332226091319088777059)
        ·
          refine ⟨189030498339136978633165589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126020332226091319088777059 189030498339136978633165589)
          ·
            refine ⟨8860804609647045873429637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 189030498339136978633165589 8860804609647045873429637)
            ·
              refine ⟨1661400864308821101268057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8860804609647045873429637 1661400864308821101268057)
              ·
                refine ⟨1246050648231615825951043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1661400864308821101268057 1246050648231615825951043)
                ·
                  refine ⟨1869075972347423738926565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1246050648231615825951043 1869075972347423738926565)
                  ·
                    refine ⟨350451744815141951048731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1869075972347423738926565 350451744815141951048731)
                    ·
                      rfl

theorem cell23_2047507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 2, 1, 4].length) (baseStart_2047507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2047507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2047507 prefixEnd_2047507 := by exact prefixLift 2047507
  have htrace : WordTrace (prefixWord ++ tailWord_2047507) baseStart_2047507 baseEnd_2047507 := by
    simpa [prefixWord, tailWord_2047507, baseEnd_2047507] using wordTrace_append hprefix tailTrace_2047507
  have hstable : (prefixWord ++ tailWord_2047507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047507).length < 2 ^ (prefixWord ++ tailWord_2047507).sum := by decide
  have hdescent : baseEnd_2047507 < baseStart_2047507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047576 : List Nat := [2, 1, 2, 2, 1, 2, 1, 12]
def baseStart_2047576 : Nat := 118140960795 + 2047576 * 2 ^ 59
def prefixEnd_2047576 : Nat := 4983230072969 + 3 ^ 40 * 2047576 * 2
def baseEnd_2047576 : Nat := 38940394985577262340125

theorem tailTrace_2047576 : CollatzResearch.WordTrace tailWord_2047576 prefixEnd_2047576 38940394985577262340125 := by
  unfold tailWord_2047576
  simp only [CollatzResearch.WordTrace]
  refine ⟨37340616014994662492509291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49787488019992883323345721 37340616014994662492509291)
  ·
    refine ⟨56010924022491993738763937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37340616014994662492509291 56010924022491993738763937)
    ·
      refine ⟨42008193016868995304072953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56010924022491993738763937 42008193016868995304072953)
      ·
        refine ⟨31506144762651746478054715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42008193016868995304072953 31506144762651746478054715)
        ·
          refine ⟨47259217143977619717082073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31506144762651746478054715 47259217143977619717082073)
          ·
            refine ⟨35444412857983214787811555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47259217143977619717082073 35444412857983214787811555)
            ·
              refine ⟨53166619286974822181717333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35444412857983214787811555 53166619286974822181717333)
              ·
                refine ⟨38940394985577262340125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 53166619286974822181717333 38940394985577262340125)
                ·
                  rfl

theorem cell23_2047576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 12].length) (baseStart_2047576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2047576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2047576 prefixEnd_2047576 := by exact prefixLift 2047576
  have htrace : WordTrace (prefixWord ++ tailWord_2047576) baseStart_2047576 baseEnd_2047576 := by
    simpa [prefixWord, tailWord_2047576, baseEnd_2047576] using wordTrace_append hprefix tailTrace_2047576
  have hstable : (prefixWord ++ tailWord_2047576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047576).length < 2 ^ (prefixWord ++ tailWord_2047576).sum := by decide
  have hdescent : baseEnd_2047576 < baseStart_2047576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047580 : List Nat := [2, 2, 4, 1, 2, 1, 3, 1, 1, 6]
def baseStart_2047580 : Nat := 118140960795 + 2047580 * 2 ^ 59
def prefixEnd_2047580 : Nat := 4983230072969 + 3 ^ 40 * 2047580 * 2
def baseEnd_2047580 : Nat := 350464239511068022511119

theorem tailTrace_2047580 : CollatzResearch.WordTrace tailWord_2047580 prefixEnd_2047580 350464239511068022511119 := by
  unfold tailWord_2047580
  simp only [CollatzResearch.WordTrace]
  refine ⟨37340688960987416834082097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49787585281316555778776129 37340688960987416834082097)
  ·
    refine ⟨28005516720740562625561573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37340688960987416834082097 28005516720740562625561573)
    ·
      refine ⟨5251034385138855492292795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28005516720740562625561573 5251034385138855492292795)
      ·
        refine ⟨7876551577708283238439193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5251034385138855492292795 7876551577708283238439193)
        ·
          refine ⟨5907413683281212428829395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7876551577708283238439193 5907413683281212428829395)
          ·
            refine ⟨8861120524921818643244093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5907413683281212428829395 8861120524921818643244093)
            ·
              refine ⟨3322920196845681991216535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8861120524921818643244093 3322920196845681991216535)
              ·
                refine ⟨4984380295268522986824803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3322920196845681991216535 4984380295268522986824803)
                ·
                  refine ⟨7476570442902784480237205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4984380295268522986824803 7476570442902784480237205)
                  ·
                    refine ⟨350464239511068022511119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7476570442902784480237205 350464239511068022511119)
                    ·
                      rfl

theorem cell23_2047580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_2047580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2047580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2047580 prefixEnd_2047580 := by exact prefixLift 2047580
  have htrace : WordTrace (prefixWord ++ tailWord_2047580) baseStart_2047580 baseEnd_2047580 := by
    simpa [prefixWord, tailWord_2047580, baseEnd_2047580] using wordTrace_append hprefix tailTrace_2047580
  have hstable : (prefixWord ++ tailWord_2047580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047580).length < 2 ^ (prefixWord ++ tailWord_2047580).sum := by decide
  have hdescent : baseEnd_2047580 < baseStart_2047580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047587 : List Nat := [1, 1, 1, 5, 1, 3, 2, 2, 3, 2, 2]
def baseStart_2047587 : Nat := 118140960795 + 2047587 * 2 ^ 59
def prefixEnd_2047587 : Nat := 4983230072969 + 3 ^ 40 * 2047587 * 2
def baseEnd_2047587 : Nat := 1051396312897785540145825

theorem tailTrace_2047587 : CollatzResearch.WordTrace tailWord_2047587 prefixEnd_2047587 1051396312897785540145825 := by
  unfold tailWord_2047587
  simp only [CollatzResearch.WordTrace]
  refine ⟨74681633232949473863669015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49787755488632982575779343 74681633232949473863669015)
  ·
    refine ⟨112022449849424210795503523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74681633232949473863669015 112022449849424210795503523)
    ·
      refine ⟨168033674774136316193255285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112022449849424210795503523 168033674774136316193255285)
      ·
        refine ⟨15753157010075279643117683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 168033674774136316193255285 15753157010075279643117683)
        ·
          refine ⟨23629735515112919464676525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15753157010075279643117683 23629735515112919464676525)
          ·
            refine ⟨8861150818167344799253697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23629735515112919464676525 8861150818167344799253697)
            ·
              refine ⟨6645863113625508599440273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8861150818167344799253697 6645863113625508599440273)
              ·
                refine ⟨4984397335219131449580205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6645863113625508599440273 4984397335219131449580205)
                ·
                  refine ⟨1869149000707174293592577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4984397335219131449580205 1869149000707174293592577)
                  ·
                    refine ⟨1401861750530380720194433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1869149000707174293592577 1401861750530380720194433)
                    ·
                      refine ⟨1051396312897785540145825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1401861750530380720194433 1051396312897785540145825)
                      ·
                        rfl

theorem cell23_2047587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 3, 2, 2].length) (baseStart_2047587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2047587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2047587 prefixEnd_2047587 := by exact prefixLift 2047587
  have htrace : WordTrace (prefixWord ++ tailWord_2047587) baseStart_2047587 baseEnd_2047587 := by
    simpa [prefixWord, tailWord_2047587, baseEnd_2047587] using wordTrace_append hprefix tailTrace_2047587
  have hstable : (prefixWord ++ tailWord_2047587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047587).length < 2 ^ (prefixWord ++ tailWord_2047587).sum := by decide
  have hdescent : baseEnd_2047587 < baseStart_2047587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047593 : List Nat := [1, 2, 1, 1, 1, 4, 6, 7]
def baseStart_2047593 : Nat := 118140960795 + 2047593 * 2 ^ 59
def prefixEnd_2047593 : Nat := 4983230072969 + 3 ^ 40 * 2047593 * 2
def baseEnd_2047593 : Nat := 38940718288211574691511

theorem tailTrace_2047593 : CollatzResearch.WordTrace tailWord_2047593 prefixEnd_2047593 38940718288211574691511 := by
  unfold tailWord_2047593
  simp only [CollatzResearch.WordTrace]
  refine ⟨74681852070927736888387433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49787901380618491258924955 74681852070927736888387433)
  ·
    refine ⟨56011389053195802666290575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74681852070927736888387433 56011389053195802666290575)
    ·
      refine ⟨84017083579793703999435863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56011389053195802666290575 84017083579793703999435863)
      ·
        refine ⟨126025625369690555999153795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84017083579793703999435863 126025625369690555999153795)
        ·
          refine ⟨189038438054535833998730693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126025625369690555999153795 189038438054535833998730693)
          ·
            refine ⟨35444707135225468874762005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189038438054535833998730693 35444707135225468874762005)
            ·
              refine ⟨1661470646963693853504469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35444707135225468874762005 1661470646963693853504469)
              ·
                refine ⟨38940718288211574691511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1661470646963693853504469 38940718288211574691511)
                ·
                  rfl

theorem cell23_2047593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 7].length) (baseStart_2047593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2047593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2047593 prefixEnd_2047593 := by exact prefixLift 2047593
  have htrace : WordTrace (prefixWord ++ tailWord_2047593) baseStart_2047593 baseEnd_2047593 := by
    simpa [prefixWord, tailWord_2047593, baseEnd_2047593] using wordTrace_append hprefix tailTrace_2047593
  have hstable : (prefixWord ++ tailWord_2047593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047593).length < 2 ^ (prefixWord ++ tailWord_2047593).sum := by decide
  have hdescent : baseEnd_2047593 < baseStart_2047593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047598 : List Nat := [4, 1, 2, 2, 4, 1, 1, 3, 1, 1, 3]
def baseStart_2047598 : Nat := 118140960795 + 2047598 * 2 ^ 59
def prefixEnd_2047598 : Nat := 4983230072969 + 3 ^ 40 * 2047598 * 2
def baseEnd_2047598 : Nat := 1051401961184984997108275

theorem tailTrace_2047598 : CollatzResearch.WordTrace tailWord_2047598 prefixEnd_2047598 1051401961184984997108275 := by
  unfold tailWord_2047598
  simp only [CollatzResearch.WordTrace]
  refine ⟨9335254304488702842789931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49788022957273081828212965 9335254304488702842789931)
  ·
    refine ⟨14002881456733054264184897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9335254304488702842789931 14002881456733054264184897)
    ·
      refine ⟨10502161092549790698138673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14002881456733054264184897 10502161092549790698138673)
      ·
        refine ⟨7876620819412343023604005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10502161092549790698138673 7876620819412343023604005)
        ·
          refine ⟨1476866403639814316925751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7876620819412343023604005 1476866403639814316925751)
          ·
            refine ⟨2215299605459721475388627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1476866403639814316925751 2215299605459721475388627)
            ·
              refine ⟨3322949408189582213082941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2215299605459721475388627 3322949408189582213082941)
              ·
                refine ⟨1246106028071093329906103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3322949408189582213082941 1246106028071093329906103)
                ·
                  refine ⟨1869159042106639994859155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1246106028071093329906103 1869159042106639994859155)
                  ·
                    refine ⟨2803738563159959992288733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1869159042106639994859155 2803738563159959992288733)
                    ·
                      refine ⟨1051401961184984997108275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2803738563159959992288733 1051401961184984997108275)
                      ·
                        rfl

theorem cell23_2047598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_2047598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2047598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2047598 prefixEnd_2047598 := by exact prefixLift 2047598
  have htrace : WordTrace (prefixWord ++ tailWord_2047598) baseStart_2047598 baseEnd_2047598 := by
    simpa [prefixWord, tailWord_2047598, baseEnd_2047598] using wordTrace_append hprefix tailTrace_2047598
  have hstable : (prefixWord ++ tailWord_2047598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047598).length < 2 ^ (prefixWord ++ tailWord_2047598).sum := by decide
  have hdescent : baseEnd_2047598 < baseStart_2047598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047621 : List Nat := [1, 3, 1, 1, 4, 1, 5, 2, 1, 2, 2]
def baseStart_2047621 : Nat := 118140960795 + 2047621 * 2 ^ 59
def prefixEnd_2047621 : Nat := 4983230072969 + 3 ^ 40 * 2047621 * 2
def baseEnd_2047621 : Nat := 1051413771240038407120669

theorem tailTrace_2047621 : CollatzResearch.WordTrace tailWord_2047621 prefixEnd_2047621 1051413771240038407120669 := by
  unfold tailWord_2047621
  simp only [CollatzResearch.WordTrace]
  refine ⟨74682873314826297670406717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49788582209884198446937811 74682873314826297670406717)
  ·
    refine ⟨28006077493059861626402519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74682873314826297670406717 28006077493059861626402519)
    ·
      refine ⟨42009116239589792439603779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28006077493059861626402519 42009116239589792439603779)
      ·
        refine ⟨63013674359384688659405669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42009116239589792439603779 63013674359384688659405669)
        ·
          refine ⟨11815063942384629123638563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63013674359384688659405669 11815063942384629123638563)
          ·
            refine ⟨17722595913576943685457845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11815063942384629123638563 17722595913576943685457845)
            ·
              refine ⟨1661493366897838470511673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17722595913576943685457845 1661493366897838470511673)
              ·
                refine ⟨1246120025173378852883755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1661493366897838470511673 1246120025173378852883755)
                ·
                  refine ⟨1869180037760068279325633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1246120025173378852883755 1869180037760068279325633)
                  ·
                    refine ⟨1401885028320051209494225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1869180037760068279325633 1401885028320051209494225)
                    ·
                      refine ⟨1051413771240038407120669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1401885028320051209494225 1051413771240038407120669)
                      ·
                        rfl

theorem cell23_2047621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 2, 1, 2, 2].length) (baseStart_2047621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2047621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2047621 prefixEnd_2047621 := by exact prefixLift 2047621
  have htrace : WordTrace (prefixWord ++ tailWord_2047621) baseStart_2047621 baseEnd_2047621 := by
    simpa [prefixWord, tailWord_2047621, baseEnd_2047621] using wordTrace_append hprefix tailTrace_2047621
  have hstable : (prefixWord ++ tailWord_2047621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047621).length < 2 ^ (prefixWord ++ tailWord_2047621).sum := by decide
  have hdescent : baseEnd_2047621 < baseStart_2047621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047663 : List Nat := [1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 5]
def baseStart_2047663 : Nat := 118140960795 + 2047663 * 2 ^ 59
def prefixEnd_2047663 : Nat := 4983230072969 + 3 ^ 40 * 2047663 * 2
def baseEnd_2047663 : Nat := 1051435337427527242795475

theorem tailTrace_2047663 : CollatzResearch.WordTrace tailWord_2047663 prefixEnd_2047663 1051435337427527242795475 := by
  unfold tailWord_2047663
  simp only [CollatzResearch.WordTrace]
  refine ⟨74684405180674138843435643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49789603453782759228957095 74684405180674138843435643)
  ·
    refine ⟨112026607771011208265153465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74684405180674138843435643 112026607771011208265153465)
    ·
      refine ⟨84019955828258406198865099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112026607771011208265153465 84019955828258406198865099)
      ·
        refine ⟨126029933742387609298297649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84019955828258406198865099 126029933742387609298297649)
        ·
          refine ⟨94522450306790706973723237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126029933742387609298297649 94522450306790706973723237)
          ·
            refine ⟨17722959432523257557573107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94522450306790706973723237 17722959432523257557573107)
            ·
              refine ⟨26584439148784886336359661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17722959432523257557573107 26584439148784886336359661)
              ·
                refine ⟨9969164680794332376134873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26584439148784886336359661 9969164680794332376134873)
                ·
                  refine ⟨7476873510595749282101155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9969164680794332376134873 7476873510595749282101155)
                  ·
                    refine ⟨11215310265893623923151733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7476873510595749282101155 11215310265893623923151733)
                    ·
                      refine ⟨1051435337427527242795475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11215310265893623923151733 1051435337427527242795475)
                      ·
                        rfl

theorem cell23_2047663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 5].length) (baseStart_2047663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2047663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2047663 prefixEnd_2047663 := by exact prefixLift 2047663
  have htrace : WordTrace (prefixWord ++ tailWord_2047663) baseStart_2047663 baseEnd_2047663 := by
    simpa [prefixWord, tailWord_2047663, baseEnd_2047663] using wordTrace_append hprefix tailTrace_2047663
  have hstable : (prefixWord ++ tailWord_2047663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047663).length < 2 ^ (prefixWord ++ tailWord_2047663).sum := by decide
  have hdescent : baseEnd_2047663 < baseStart_2047663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047694 : List Nat := [4, 1, 1, 1, 3, 1, 1, 5, 2, 2, 2]
def baseStart_2047694 : Nat := 118140960795 + 2047694 * 2 ^ 59
def prefixEnd_2047694 : Nat := 4983230072969 + 3 ^ 40 * 2047694 * 2
def baseEnd_2047694 : Nat := 1051451255327816621507833

theorem tailTrace_2047694 : CollatzResearch.WordTrace tailWord_2047694 prefixEnd_2047694 1051451255327816621507833 := by
  unfold tailWord_2047694
  simp only [CollatzResearch.WordTrace]
  refine ⟨9335691980445228892226767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49790357229041220758542757 9335691980445228892226767)
  ·
    refine ⟨14003537970667843338340151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9335691980445228892226767 14003537970667843338340151)
    ·
      refine ⟨21005306956001765007510227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14003537970667843338340151 21005306956001765007510227)
      ·
        refine ⟨31507960434002647511265341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21005306956001765007510227 31507960434002647511265341)
        ·
          refine ⟨11815485162750992816724503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31507960434002647511265341 11815485162750992816724503)
          ·
            refine ⟨17723227744126489225086755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11815485162750992816724503 17723227744126489225086755)
            ·
              refine ⟨26584841616189733837630133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17723227744126489225086755 26584841616189733837630133)
              ·
                refine ⟨2492328901517787547277825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26584841616189733837630133 2492328901517787547277825)
                ·
                  refine ⟨1869246676138340660458369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2492328901517787547277825 1869246676138340660458369)
                  ·
                    refine ⟨1401935007103755495343777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1869246676138340660458369 1401935007103755495343777)
                    ·
                      refine ⟨1051451255327816621507833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1401935007103755495343777 1051451255327816621507833)
                      ·
                        rfl

theorem cell23_2047694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 5, 2, 2, 2].length) (baseStart_2047694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2047694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2047694 prefixEnd_2047694 := by exact prefixLift 2047694
  have htrace : WordTrace (prefixWord ++ tailWord_2047694) baseStart_2047694 baseEnd_2047694 := by
    simpa [prefixWord, tailWord_2047694, baseEnd_2047694] using wordTrace_append hprefix tailTrace_2047694
  have hstable : (prefixWord ++ tailWord_2047694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047694).length < 2 ^ (prefixWord ++ tailWord_2047694).sum := by decide
  have hdescent : baseEnd_2047694 < baseStart_2047694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047700 : List Nat := [2, 4, 1, 3, 1, 1, 1, 1, 9]
def baseStart_2047700 : Nat := 118140960795 + 2047700 * 2 ^ 59
def prefixEnd_2047700 : Nat := 4983230072969 + 3 ^ 40 * 2047700 * 2
def baseEnd_2047700 : Nat := 116828259579082622003645

theorem tailTrace_2047700 : CollatzResearch.WordTrace tailWord_2047700 prefixEnd_2047700 116828259579082622003645 := by
  unfold tailWord_2047700
  simp only [CollatzResearch.WordTrace]
  refine ⟨37342877340770047081266277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49790503121026729441688369 37342877340770047081266277)
  ·
    refine ⟨7001789501394383827737427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37342877340770047081266277 7001789501394383827737427)
    ·
      refine ⟨10502684252091575741606141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7001789501394383827737427 10502684252091575741606141)
      ·
        refine ⟨3938506594534340903102303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10502684252091575741606141 3938506594534340903102303)
        ·
          refine ⟨5907759891801511354653455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3938506594534340903102303 5907759891801511354653455)
          ·
            refine ⟨8861639837702267031980183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5907759891801511354653455 8861639837702267031980183)
            ·
              refine ⟨13292459756553400547970275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8861639837702267031980183 13292459756553400547970275)
              ·
                refine ⟨19938689634830100821955413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13292459756553400547970275 19938689634830100821955413)
                ·
                  refine ⟨116828259579082622003645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 19938689634830100821955413 116828259579082622003645)
                  ·
                    rfl

theorem cell23_2047700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 9].length) (baseStart_2047700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2047700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2047700 prefixEnd_2047700 := by exact prefixLift 2047700
  have htrace : WordTrace (prefixWord ++ tailWord_2047700) baseStart_2047700 baseEnd_2047700 := by
    simpa [prefixWord, tailWord_2047700, baseEnd_2047700] using wordTrace_append hprefix tailTrace_2047700
  have hstable : (prefixWord ++ tailWord_2047700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047700).length < 2 ^ (prefixWord ++ tailWord_2047700).sum := by decide
  have hdescent : baseEnd_2047700 < baseStart_2047700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047717 : List Nat := [1, 3, 1, 4, 1, 1, 4, 3, 5]
def baseStart_2047717 : Nat := 118140960795 + 2047717 * 2 ^ 59
def prefixEnd_2047717 : Nat := 4983230072969 + 3 ^ 40 * 2047717 * 2
def baseEnd_2047717 : Nat := 116829229486985559057803

theorem tailTrace_2047717 : CollatzResearch.WordTrace tailWord_2047717 prefixEnd_2047717 116829229486985559057803 := by
  unfold tailWord_2047717
  simp only [CollatzResearch.WordTrace]
  refine ⟨74686374722478506065901405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49790916481652337377267603 74686374722478506065901405)
  ·
    refine ⟨28007390520929439774713027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74686374722478506065901405 28007390520929439774713027)
    ·
      refine ⟨42011085781394159662069541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28007390520929439774713027 42011085781394159662069541)
      ·
        refine ⟨7877078584011404936638039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42011085781394159662069541 7877078584011404936638039)
        ·
          refine ⟨11815617876017107404957059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7877078584011404936638039 11815617876017107404957059)
          ·
            refine ⟨17723426814025661107435589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11815617876017107404957059 17723426814025661107435589)
            ·
              refine ⟨3323142527629811457644173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17723426814025661107435589 3323142527629811457644173)
              ·
                refine ⟨1246178447861179296616565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3323142527629811457644173 1246178447861179296616565)
                ·
                  refine ⟨116829229486985559057803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1246178447861179296616565 116829229486985559057803)
                  ·
                    rfl

theorem cell23_2047717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 3, 5].length) (baseStart_2047717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2047717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2047717 prefixEnd_2047717 := by exact prefixLift 2047717
  have htrace : WordTrace (prefixWord ++ tailWord_2047717) baseStart_2047717 baseEnd_2047717 := by
    simpa [prefixWord, tailWord_2047717, baseEnd_2047717] using wordTrace_append hprefix tailTrace_2047717
  have hstable : (prefixWord ++ tailWord_2047717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047717).length < 2 ^ (prefixWord ++ tailWord_2047717).sum := by decide
  have hdescent : baseEnd_2047717 < baseStart_2047717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047723 : List Nat := [1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 5]
def baseStart_2047723 : Nat := 118140960795 + 2047723 * 2 ^ 59
def prefixEnd_2047723 : Nat := 4983230072969 + 3 ^ 40 * 2047723 * 2
def baseEnd_2047723 : Nat := 1051466146266797008045199

theorem tailTrace_2047723 : CollatzResearch.WordTrace tailWord_2047723 prefixEnd_2047723 1051466146266797008045199 := by
  unfold tailWord_2047723
  simp only [CollatzResearch.WordTrace]
  refine ⟨74686593560456769090619823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49791062373637846060413215 74686593560456769090619823)
  ·
    refine ⟨112029890340685153635929735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74686593560456769090619823 112029890340685153635929735)
    ·
      refine ⟨168044835511027730453894603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112029890340685153635929735 168044835511027730453894603)
      ·
        refine ⟨252067253266541595680841905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168044835511027730453894603 252067253266541595680841905)
        ·
          refine ⟨189050439949906196760631429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252067253266541595680841905 189050439949906196760631429)
          ·
            refine ⟨35446957490607411892618393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189050439949906196760631429 35446957490607411892618393)
            ·
              refine ⟨26585218117955558919463795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35446957490607411892618393 26585218117955558919463795)
              ·
                refine ⟨39877827176933338379195693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26585218117955558919463795 39877827176933338379195693)
                ·
                  refine ⟨14954185191350001892198385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39877827176933338379195693 14954185191350001892198385)
                  ·
                    refine ⟨11215638893512501419148789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14954185191350001892198385 11215638893512501419148789)
                    ·
                      refine ⟨1051466146266797008045199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11215638893512501419148789 1051466146266797008045199)
                      ·
                        rfl

theorem cell23_2047723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 5].length) (baseStart_2047723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2047723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2047723 prefixEnd_2047723 := by exact prefixLift 2047723
  have htrace : WordTrace (prefixWord ++ tailWord_2047723) baseStart_2047723 baseEnd_2047723 := by
    simpa [prefixWord, tailWord_2047723, baseEnd_2047723] using wordTrace_append hprefix tailTrace_2047723
  have hstable : (prefixWord ++ tailWord_2047723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047723).length < 2 ^ (prefixWord ++ tailWord_2047723).sum := by decide
  have hdescent : baseEnd_2047723 < baseStart_2047723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047730 : List Nat := [3, 2, 1, 3, 1, 1, 2, 1, 4, 5]
def baseStart_2047730 : Nat := 118140960795 + 2047730 * 2 ^ 59
def prefixEnd_2047730 : Nat := 4983230072969 + 3 ^ 40 * 2047730 * 2
def baseEnd_2047730 : Nat := 350489913543792826885889

theorem tailTrace_2047730 : CollatzResearch.WordTrace tailWord_2047730 prefixEnd_2047730 350489913543792826885889 := by
  unfold tailWord_2047730
  simp only [CollatzResearch.WordTrace]
  refine ⟨18671712217857852321531161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49791232580954272857416429 18671712217857852321531161)
  ·
    refine ⟨14003784163393389241148371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18671712217857852321531161 14003784163393389241148371)
    ·
      refine ⟨21005676245090083861722557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14003784163393389241148371 21005676245090083861722557)
      ·
        refine ⟨7877128591908781448145959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21005676245090083861722557 7877128591908781448145959)
        ·
          refine ⟨11815692887863172172218939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7877128591908781448145959 11815692887863172172218939)
          ·
            refine ⟨17723539331794758258328409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11815692887863172172218939 17723539331794758258328409)
            ·
              refine ⟨13292654498846068693746307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17723539331794758258328409 13292654498846068693746307)
              ·
                refine ⟨19938981748269103040619461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13292654498846068693746307 19938981748269103040619461)
                ·
                  refine ⟨3738559077800456820116149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19938981748269103040619461 3738559077800456820116149)
                  ·
                    refine ⟨350489913543792826885889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3738559077800456820116149 350489913543792826885889)
                    ·
                      rfl

theorem cell23_2047730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 4, 5].length) (baseStart_2047730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2047730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2047730 prefixEnd_2047730 := by exact prefixLift 2047730
  have htrace : WordTrace (prefixWord ++ tailWord_2047730) baseStart_2047730 baseEnd_2047730 := by
    simpa [prefixWord, tailWord_2047730, baseEnd_2047730] using wordTrace_append hprefix tailTrace_2047730
  have hstable : (prefixWord ++ tailWord_2047730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047730).length < 2 ^ (prefixWord ++ tailWord_2047730).sum := by decide
  have hdescent : baseEnd_2047730 < baseStart_2047730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047763 : List Nat := [1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 6]
def baseStart_2047763 : Nat := 118140960795 + 2047763 * 2 ^ 59
def prefixEnd_2047763 : Nat := 4983230072969 + 3 ^ 40 * 2047763 * 2
def baseEnd_2047763 : Nat := 1051486685492976851545015

theorem tailTrace_2047763 : CollatzResearch.WordTrace tailWord_2047763 prefixEnd_2047763 1051486685492976851545015 := by
  unfold tailWord_2047763
  simp only [CollatzResearch.WordTrace]
  refine ⟨74688052480311855922075943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49792034986874570614717295 74688052480311855922075943)
  ·
    refine ⟨112032078720467783883113915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74688052480311855922075943 112032078720467783883113915)
    ·
      refine ⟨168048118080701675824670873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112032078720467783883113915 168048118080701675824670873)
      ·
        refine ⟨126036088560526256868503155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168048118080701675824670873 126036088560526256868503155)
        ·
          refine ⟨189054132840789385302754733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126036088560526256868503155 189054132840789385302754733)
          ·
            refine ⟨70895299815296019488533025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189054132840789385302754733 70895299815296019488533025)
            ·
              refine ⟨53171474861472014616399769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70895299815296019488533025 53171474861472014616399769)
              ·
                refine ⟨39878606146104010962299827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53171474861472014616399769 39878606146104010962299827)
                ·
                  refine ⟨59817909219156016443449741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39878606146104010962299827 59817909219156016443449741)
                  ·
                    refine ⟨22431715957183506166293653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59817909219156016443449741 22431715957183506166293653)
                    ·
                      refine ⟨1051486685492976851545015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22431715957183506166293653 1051486685492976851545015)
                      ·
                        rfl

theorem cell23_2047763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 6].length) (baseStart_2047763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2047763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2047763 prefixEnd_2047763 := by exact prefixLift 2047763
  have htrace : WordTrace (prefixWord ++ tailWord_2047763) baseStart_2047763 baseEnd_2047763 := by
    simpa [prefixWord, tailWord_2047763, baseEnd_2047763] using wordTrace_append hprefix tailTrace_2047763
  have hstable : (prefixWord ++ tailWord_2047763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047763).length < 2 ^ (prefixWord ++ tailWord_2047763).sum := by decide
  have hdescent : baseEnd_2047763 < baseStart_2047763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047794 : List Nat := [3, 2, 1, 1, 3, 4, 1, 1, 3, 4]
def baseStart_2047794 : Nat := 118140960795 + 2047794 * 2 ^ 59
def prefixEnd_2047794 : Nat := 4983230072969 + 3 ^ 40 * 2047794 * 2
def baseEnd_2047794 : Nat := 350500867797755410085791

theorem tailTrace_2047794 : CollatzResearch.WordTrace tailWord_2047794 prefixEnd_2047794 350500867797755410085791 := by
  unfold tailWord_2047794
  simp only [CollatzResearch.WordTrace]
  refine ⟨18672295785799887054113609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49792788762133032144302957 18672295785799887054113609)
  ·
    refine ⟨14004221839349915290585207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18672295785799887054113609 14004221839349915290585207)
    ·
      refine ⟨21006332759024872935877811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14004221839349915290585207 21006332759024872935877811)
      ·
        refine ⟨31509499138537309403816717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21006332759024872935877811 31509499138537309403816717)
        ·
          refine ⟨11816062176951491026431269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31509499138537309403816717 11816062176951491026431269)
          ·
            refine ⟨2215511658178404567455863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11816062176951491026431269 2215511658178404567455863)
            ·
              refine ⟨3323267487267606851183795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2215511658178404567455863 3323267487267606851183795)
              ·
                refine ⟨4984901230901410276775693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3323267487267606851183795 4984901230901410276775693)
                ·
                  refine ⟨1869337961588028853790885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4984901230901410276775693 1869337961588028853790885)
                  ·
                    refine ⟨350500867797755410085791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1869337961588028853790885 350500867797755410085791)
                    ·
                      rfl

theorem cell23_2047794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 3, 4].length) (baseStart_2047794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2047794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2047794 prefixEnd_2047794 := by exact prefixLift 2047794
  have htrace : WordTrace (prefixWord ++ tailWord_2047794) baseStart_2047794 baseEnd_2047794 := by
    simpa [prefixWord, tailWord_2047794, baseEnd_2047794] using wordTrace_append hprefix tailTrace_2047794
  have hstable : (prefixWord ++ tailWord_2047794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047794).length < 2 ^ (prefixWord ++ tailWord_2047794).sum := by decide
  have hdescent : baseEnd_2047794 < baseStart_2047794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047807 : List Nat := [1, 1, 2, 2, 6, 1, 1, 3, 6]
def baseStart_2047807 : Nat := 118140960795 + 2047807 * 2 ^ 59
def prefixEnd_2047807 : Nat := 4983230072969 + 3 ^ 40 * 2047807 * 2
def baseEnd_2047807 : Nat := 116834364293530519932757

theorem tailTrace_2047807 : CollatzResearch.WordTrace tailWord_2047807 prefixEnd_2047807 116834364293530519932757 := by
  unfold tailWord_2047807
  simp only [CollatzResearch.WordTrace]
  refine ⟨74689657292152451436677675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49793104861434967624451783 74689657292152451436677675)
  ·
    refine ⟨112034485938228677155016513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74689657292152451436677675 112034485938228677155016513)
    ·
      refine ⟨84025864453671507866262385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112034485938228677155016513 84025864453671507866262385)
      ·
        refine ⟨63019398340253630899696789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84025864453671507866262385 63019398340253630899696789)
        ·
          refine ⟨2954034297199388948423287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 63019398340253630899696789 2954034297199388948423287)
          ·
            refine ⟨4431051445799083422634931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2954034297199388948423287 4431051445799083422634931)
            ·
              refine ⟨6646577168698625133952397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4431051445799083422634931 6646577168698625133952397)
              ·
                refine ⟨2492466438261984425232149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6646577168698625133952397 2492466438261984425232149)
                ·
                  refine ⟨116834364293530519932757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2492466438261984425232149 116834364293530519932757)
                  ·
                    rfl

theorem cell23_2047807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 3, 6].length) (baseStart_2047807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2047807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2047807 prefixEnd_2047807 := by exact prefixLift 2047807
  have htrace : WordTrace (prefixWord ++ tailWord_2047807) baseStart_2047807 baseEnd_2047807 := by
    simpa [prefixWord, tailWord_2047807, baseEnd_2047807] using wordTrace_append hprefix tailTrace_2047807
  have hstable : (prefixWord ++ tailWord_2047807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047807).length < 2 ^ (prefixWord ++ tailWord_2047807).sum := by decide
  have hdescent : baseEnd_2047807 < baseStart_2047807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047817 : List Nat := [1, 2, 1, 1, 2, 4, 2, 1, 5, 1, 3]
def baseStart_2047817 : Nat := 118140960795 + 2047817 * 2 ^ 59
def prefixEnd_2047817 : Nat := 4983230072969 + 3 ^ 40 * 2047817 * 2
def baseEnd_2047817 : Nat := 1051514413448319640269767

theorem tailTrace_2047817 : CollatzResearch.WordTrace tailWord_2047817 prefixEnd_2047817 1051514413448319640269767 := by
  unfold tailWord_2047817
  simp only [CollatzResearch.WordTrace]
  refine ⟨74690022022116223144541705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49793348014744148763027803 74690022022116223144541705)
  ·
    refine ⟨56017516516587167358406279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74690022022116223144541705 56017516516587167358406279)
    ·
      refine ⟨84026274774880751037609419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56017516516587167358406279 84026274774880751037609419)
      ·
        refine ⟨126039412162321126556414129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84026274774880751037609419 126039412162321126556414129)
        ·
          refine ⟨94529559121740844917310597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126039412162321126556414129 94529559121740844917310597)
          ·
            refine ⟨17724292335326408421995737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94529559121740844917310597 17724292335326408421995737)
            ·
              refine ⟨13293219251494806316496803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17724292335326408421995737 13293219251494806316496803)
              ·
                refine ⟨19939828877242209474745205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13293219251494806316496803 19939828877242209474745205)
                ·
                  refine ⟨1869358957241457138257363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19939828877242209474745205 1869358957241457138257363)
                  ·
                    refine ⟨2804038435862185707386045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1869358957241457138257363 2804038435862185707386045)
                    ·
                      refine ⟨1051514413448319640269767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2804038435862185707386045 1051514413448319640269767)
                      ·
                        rfl

theorem cell23_2047817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 5, 1, 3].length) (baseStart_2047817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2047817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2047817 prefixEnd_2047817 := by exact prefixLift 2047817
  have htrace : WordTrace (prefixWord ++ tailWord_2047817) baseStart_2047817 baseEnd_2047817 := by
    simpa [prefixWord, tailWord_2047817, baseEnd_2047817] using wordTrace_append hprefix tailTrace_2047817
  have hstable : (prefixWord ++ tailWord_2047817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047817).length < 2 ^ (prefixWord ++ tailWord_2047817).sum := by decide
  have hdescent : baseEnd_2047817 < baseStart_2047817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047821 : List Nat := [1, 6, 1, 2, 1, 2, 2, 1, 2, 2, 3]
def baseStart_2047821 : Nat := 118140960795 + 2047821 * 2 ^ 59
def prefixEnd_2047821 : Nat := 4983230072969 + 3 ^ 40 * 2047821 * 2
def baseEnd_2047821 : Nat := 1051516467370937624619749

theorem tailTrace_2047821 : CollatzResearch.WordTrace tailWord_2047821 prefixEnd_2047821 1051516467370937624619749 := by
  unfold tailWord_2047821
  simp only [CollatzResearch.WordTrace]
  refine ⟨74690167914101731827687317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49793445276067821218458211 74690167914101731827687317)
  ·
    refine ⟨3501101620973518679422843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 74690167914101731827687317 3501101620973518679422843)
    ·
      refine ⟨5251652431460278019134265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3501101620973518679422843 5251652431460278019134265)
      ·
        refine ⟨3938739323595208514350699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5251652431460278019134265 3938739323595208514350699)
        ·
          refine ⟨5908108985392812771526049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3938739323595208514350699 5908108985392812771526049)
          ·
            refine ⟨4431081739044609578644537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5908108985392812771526049 4431081739044609578644537)
            ·
              refine ⟨3323311304283457183983403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4431081739044609578644537 3323311304283457183983403)
              ·
                refine ⟨4984966956425185775975105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3323311304283457183983403 4984966956425185775975105)
                ·
                  refine ⟨3738725217318889331981329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4984966956425185775975105 3738725217318889331981329)
                  ·
                    refine ⟨2804043912989166998985997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3738725217318889331981329 2804043912989166998985997)
                    ·
                      refine ⟨1051516467370937624619749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2804043912989166998985997 1051516467370937624619749)
                      ·
                        rfl

theorem cell23_2047821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_2047821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2047821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2047821 prefixEnd_2047821 := by exact prefixLift 2047821
  have htrace : WordTrace (prefixWord ++ tailWord_2047821) baseStart_2047821 baseEnd_2047821 := by
    simpa [prefixWord, tailWord_2047821, baseEnd_2047821] using wordTrace_append hprefix tailTrace_2047821
  have hstable : (prefixWord ++ tailWord_2047821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047821).length < 2 ^ (prefixWord ++ tailWord_2047821).sum := by decide
  have hdescent : baseEnd_2047821 < baseStart_2047821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047877 : List Nat := [1, 3, 1, 1, 3, 2, 1, 3, 3, 2, 3]
def baseStart_2047877 : Nat := 118140960795 + 2047877 * 2 ^ 59
def prefixEnd_2047877 : Nat := 4983230072969 + 3 ^ 40 * 2047877 * 2
def baseEnd_2047877 : Nat := 1051545222287589405519491

theorem tailTrace_2047877 : CollatzResearch.WordTrace tailWord_2047877 prefixEnd_2047877 1051545222287589405519491 := by
  unfold tailWord_2047877
  simp only [CollatzResearch.WordTrace]
  refine ⟨74692210401898853391725885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49794806934599235594483923 74692210401898853391725885)
  ·
    refine ⟨28009578900712070021897207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74692210401898853391725885 28009578900712070021897207)
    ·
      refine ⟨42014368351068105032845811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28009578900712070021897207 42014368351068105032845811)
      ·
        refine ⟨63021552526602157549268717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42014368351068105032845811 63021552526602157549268717)
        ·
          refine ⟨23633082197475809080975769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63021552526602157549268717 23633082197475809080975769)
          ·
            refine ⟨17724811648106856810731827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23633082197475809080975769 17724811648106856810731827)
            ·
              refine ⟨26587217472160285216097741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17724811648106856810731827 26587217472160285216097741)
              ·
                refine ⟨9970206552060106956036653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26587217472160285216097741 9970206552060106956036653)
                ·
                  refine ⟨3738827457022540108513745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9970206552060106956036653 3738827457022540108513745)
                  ·
                    refine ⟨2804120592766905081385309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3738827457022540108513745 2804120592766905081385309)
                    ·
                      refine ⟨1051545222287589405519491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2804120592766905081385309 1051545222287589405519491)
                      ·
                        rfl

theorem cell23_2047877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 3, 2, 3].length) (baseStart_2047877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2047877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2047877 prefixEnd_2047877 := by exact prefixLift 2047877
  have htrace : WordTrace (prefixWord ++ tailWord_2047877) baseStart_2047877 baseEnd_2047877 := by
    simpa [prefixWord, tailWord_2047877, baseEnd_2047877] using wordTrace_append hprefix tailTrace_2047877
  have hstable : (prefixWord ++ tailWord_2047877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047877).length < 2 ^ (prefixWord ++ tailWord_2047877).sum := by decide
  have hdescent : baseEnd_2047877 < baseStart_2047877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047901 : List Nat := [1, 4, 2, 1, 2, 4, 1, 2, 2, 4]
def baseStart_2047901 : Nat := 118140960795 + 2047901 * 2 ^ 59
def prefixEnd_2047901 : Nat := 4983230072969 + 3 ^ 40 * 2047901 * 2
def baseEnd_2047901 : Nat := 350519181941099103873127

theorem tailTrace_2047901 : CollatzResearch.WordTrace tailWord_2047901 prefixEnd_2047901 350519181941099103873127 := by
  unfold tailWord_2047901
  simp only [CollatzResearch.WordTrace]
  refine ⟨74693085753811905490599557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49795390502541270327066371 74693085753811905490599557)
  ·
    refine ⟨14004953578839732279487417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74693085753811905490599557 14004953578839732279487417)
    ·
      refine ⟨10503715184129799209615563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14004953578839732279487417 10503715184129799209615563)
      ·
        refine ⟨15755572776194698814423345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10503715184129799209615563 15755572776194698814423345)
        ·
          refine ⟨11816679582146024110817509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15755572776194698814423345 11816679582146024110817509)
          ·
            refine ⟨2215627421652379520778283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11816679582146024110817509 2215627421652379520778283)
            ·
              refine ⟨3323441132478569281167425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2215627421652379520778283 3323441132478569281167425)
              ·
                refine ⟨2492580849358926960875569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3323441132478569281167425 2492580849358926960875569)
                ·
                  refine ⟨1869435637019195220656677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2492580849358926960875569 1869435637019195220656677)
                  ·
                    refine ⟨350519181941099103873127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1869435637019195220656677 350519181941099103873127)
                    ·
                      rfl

theorem cell23_2047901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_2047901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2047901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2047901 prefixEnd_2047901 := by exact prefixLift 2047901
  have htrace : WordTrace (prefixWord ++ tailWord_2047901) baseStart_2047901 baseEnd_2047901 := by
    simpa [prefixWord, tailWord_2047901, baseEnd_2047901] using wordTrace_append hprefix tailTrace_2047901
  have hstable : (prefixWord ++ tailWord_2047901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047901).length < 2 ^ (prefixWord ++ tailWord_2047901).sum := by decide
  have hdescent : baseEnd_2047901 < baseStart_2047901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047908 : List Nat := [2, 3, 1, 2, 1, 3, 2, 4, 1, 2, 2]
def baseStart_2047908 : Nat := 118140960795 + 2047908 * 2 ^ 59
def prefixEnd_2047908 : Nat := 4983230072969 + 3 ^ 40 * 2047908 * 2
def baseEnd_2047908 : Nat := 1051561140187878784231849

theorem tailTrace_2047908 : CollatzResearch.WordTrace tailWord_2047908 prefixEnd_2047908 1051561140187878784231849 := by
  unfold tailWord_2047908
  simp only [CollatzResearch.WordTrace]
  refine ⟨37346670532393272843052189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49795560709857697124069585 37346670532393272843052189)
  ·
    refine ⟨14005001449647477316144571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37346670532393272843052189 14005001449647477316144571)
    ·
      refine ⟨21007502174471215974216857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14005001449647477316144571 21007502174471215974216857)
      ·
        refine ⟨15755626630853411980662643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21007502174471215974216857 15755626630853411980662643)
        ·
          refine ⟨23633439946280117970993965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15755626630853411980662643 23633439946280117970993965)
          ·
            refine ⟨8862539979855044239122737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23633439946280117970993965 8862539979855044239122737)
            ·
              refine ⟨6646904984891283179342053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8862539979855044239122737 6646904984891283179342053)
              ·
                refine ⟨1246294684667115596126635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6646904984891283179342053 1246294684667115596126635)
                ·
                  refine ⟨1869442027000673394189953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1246294684667115596126635 1869442027000673394189953)
                  ·
                    refine ⟨1402081520250505045642465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1869442027000673394189953 1402081520250505045642465)
                    ·
                      refine ⟨1051561140187878784231849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1402081520250505045642465 1051561140187878784231849)
                      ·
                        rfl

theorem cell23_2047908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 4, 1, 2, 2].length) (baseStart_2047908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2047908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2047908 prefixEnd_2047908 := by exact prefixLift 2047908
  have htrace : WordTrace (prefixWord ++ tailWord_2047908) baseStart_2047908 baseEnd_2047908 := by
    simpa [prefixWord, tailWord_2047908, baseEnd_2047908] using wordTrace_append hprefix tailTrace_2047908
  have hstable : (prefixWord ++ tailWord_2047908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047908).length < 2 ^ (prefixWord ++ tailWord_2047908).sum := by decide
  have hdescent : baseEnd_2047908 < baseStart_2047908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047920 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 5]
def baseStart_2047920 : Nat := 118140960795 + 2047920 * 2 ^ 59
def prefixEnd_2047920 : Nat := 4983230072969 + 3 ^ 40 * 2047920 * 2
def baseEnd_2047920 : Nat := 1051567301955732737281793

theorem tailTrace_2047920 : CollatzResearch.WordTrace tailWord_2047920 prefixEnd_2047920 1051567301955732737281793 := by
  unfold tailWord_2047920
  simp only [CollatzResearch.WordTrace]
  refine ⟨37346889370371535867770607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49795852493828714490360809 37346889370371535867770607)
  ·
    refine ⟨56020334055557303801655911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37346889370371535867770607 56020334055557303801655911)
    ·
      refine ⟨84030501083335955702483867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56020334055557303801655911 84030501083335955702483867)
      ·
        refine ⟨126045751625003933553725801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84030501083335955702483867 126045751625003933553725801)
        ·
          refine ⟨94534313718752950165294351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126045751625003933553725801 94534313718752950165294351)
          ·
            refine ⟨141801470578129425247941527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94534313718752950165294351 141801470578129425247941527)
            ·
              refine ⟨212702205867194137871912291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141801470578129425247941527 212702205867194137871912291)
              ·
                refine ⟨319053308800791206807868437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212702205867194137871912291 319053308800791206807868437)
                ·
                  refine ⟨14955623850037087819118833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 319053308800791206807868437 14955623850037087819118833)
                  ·
                    refine ⟨11216717887527815864339125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14955623850037087819118833 11216717887527815864339125)
                    ·
                      refine ⟨1051567301955732737281793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11216717887527815864339125 1051567301955732737281793)
                      ·
                        rfl

theorem cell23_2047920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 5].length) (baseStart_2047920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2047920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2047920 prefixEnd_2047920 := by exact prefixLift 2047920
  have htrace : WordTrace (prefixWord ++ tailWord_2047920) baseStart_2047920 baseEnd_2047920 := by
    simpa [prefixWord, tailWord_2047920, baseEnd_2047920] using wordTrace_append hprefix tailTrace_2047920
  have hstable : (prefixWord ++ tailWord_2047920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047920).length < 2 ^ (prefixWord ++ tailWord_2047920).sum := by decide
  have hdescent : baseEnd_2047920 < baseStart_2047920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047930 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 1, 2, 8]
def baseStart_2047930 : Nat := 118140960795 + 2047930 * 2 ^ 59
def prefixEnd_2047930 : Nat := 4983230072969 + 3 ^ 40 * 2047930 * 2
def baseEnd_2047930 : Nat := 1051572436762277698156747

theorem tailTrace_2047930 : CollatzResearch.WordTrace tailWord_2047930 prefixEnd_2047930 1051572436762277698156747 := by
  unfold tailWord_2047930
  simp only [CollatzResearch.WordTrace]
  refine ⟨18673535867676710860851311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49796095647137895628936829 18673535867676710860851311)
  ·
    refine ⟨28010303801515066291276967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18673535867676710860851311 28010303801515066291276967)
    ·
      refine ⟨42015455702272599436915451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28010303801515066291276967 42015455702272599436915451)
      ·
        refine ⟨63023183553408899155373177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42015455702272599436915451 63023183553408899155373177)
        ·
          refine ⟨47267387665056674366529883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63023183553408899155373177 47267387665056674366529883)
          ·
            refine ⟨70901081497585011549794825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47267387665056674366529883 70901081497585011549794825)
            ·
              refine ⟨53175811123188758662346119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70901081497585011549794825 53175811123188758662346119)
              ·
                refine ⟨79763716684783137993519179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53175811123188758662346119 79763716684783137993519179)
                ·
                  refine ⟨119645575027174706990278769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79763716684783137993519179 119645575027174706990278769)
                  ·
                    refine ⟨89734181270381030242709077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 119645575027174706990278769 89734181270381030242709077)
                    ·
                      refine ⟨1051572436762277698156747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 89734181270381030242709077 1051572436762277698156747)
                      ·
                        rfl

theorem cell23_2047930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 1, 2, 8].length) (baseStart_2047930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2047930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2047930 prefixEnd_2047930 := by exact prefixLift 2047930
  have htrace : WordTrace (prefixWord ++ tailWord_2047930) baseStart_2047930 baseEnd_2047930 := by
    simpa [prefixWord, tailWord_2047930, baseEnd_2047930] using wordTrace_append hprefix tailTrace_2047930
  have hstable : (prefixWord ++ tailWord_2047930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047930).length < 2 ^ (prefixWord ++ tailWord_2047930).sum := by decide
  have hdescent : baseEnd_2047930 < baseStart_2047930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047975 : List Nat := [1, 1, 5, 2, 3, 2, 2, 1, 2, 1, 3]
def baseStart_2047975 : Nat := 118140960795 + 2047975 * 2 ^ 59
def prefixEnd_2047975 : Nat := 4983230072969 + 3 ^ 40 * 2047975 * 2
def baseEnd_2047975 : Nat := 1051595543391730022094041

theorem tailTrace_2047975 : CollatzResearch.WordTrace tailWord_2047975 prefixEnd_2047975 1051595543391730022094041 := by
  unfold tailWord_2047975
  simp only [CollatzResearch.WordTrace]
  refine ⟨74695784755543816128793379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49797189837029210752528919 74695784755543816128793379)
  ·
    refine ⟨112043677133315724193190069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74695784755543816128793379 112043677133315724193190069)
    ·
      refine ⟨10504094731248349143111569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 112043677133315724193190069 10504094731248349143111569)
      ·
        refine ⟨7878071048436261857333677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10504094731248349143111569 7878071048436261857333677)
        ·
          refine ⟨2954276643163598196500129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7878071048436261857333677 2954276643163598196500129)
          ·
            refine ⟨2215707482372698647375097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2954276643163598196500129 2215707482372698647375097)
            ·
              refine ⟨1661780611779523985531323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2215707482372698647375097 1661780611779523985531323)
              ·
                refine ⟨2492670917669285978296985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1661780611779523985531323 2492670917669285978296985)
                ·
                  refine ⟨1869503188251964483722739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2492670917669285978296985 1869503188251964483722739)
                  ·
                    refine ⟨2804254782377946725584109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1869503188251964483722739 2804254782377946725584109)
                    ·
                      refine ⟨1051595543391730022094041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2804254782377946725584109 1051595543391730022094041)
                      ·
                        rfl

theorem cell23_2047975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_2047975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2047975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2047975 prefixEnd_2047975 := by exact prefixLift 2047975
  have htrace : WordTrace (prefixWord ++ tailWord_2047975) baseStart_2047975 baseEnd_2047975 := by
    simpa [prefixWord, tailWord_2047975, baseEnd_2047975] using wordTrace_append hprefix tailTrace_2047975
  have hstable : (prefixWord ++ tailWord_2047975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047975).length < 2 ^ (prefixWord ++ tailWord_2047975).sum := by decide
  have hdescent : baseEnd_2047975 < baseStart_2047975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047985 : List Nat := [1, 2, 2, 2, 6, 1, 1, 2, 1, 3, 2]
def baseStart_2047985 : Nat := 118140960795 + 2047985 * 2 ^ 59
def prefixEnd_2047985 : Nat := 4983230072969 + 3 ^ 40 * 2047985 * 2
def baseEnd_2047985 : Nat := 1051600678198274982968995

theorem tailTrace_2047985 : CollatzResearch.WordTrace tailWord_2047985 prefixEnd_2047985 1051600678198274982968995 := by
  unfold tailWord_2047985
  simp only [CollatzResearch.WordTrace]
  refine ⟨74696149485507587836657409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49797432990338391891104939 74696149485507587836657409)
  ·
    refine ⟨56022112114130690877493057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74696149485507587836657409 56022112114130690877493057)
    ·
      refine ⟨42016584085598018158119793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56022112114130690877493057 42016584085598018158119793)
      ·
        refine ⟨31512438064198513618589845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42016584085598018158119793 31512438064198513618589845)
        ·
          refine ⟨1477145534259305325871399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31512438064198513618589845 1477145534259305325871399)
          ·
            refine ⟨2215718301388957988807099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1477145534259305325871399 2215718301388957988807099)
            ·
              refine ⟨3323577452083436983210649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2215718301388957988807099 3323577452083436983210649)
              ·
                refine ⟨2492683089062577737407987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3323577452083436983210649 2492683089062577737407987)
                ·
                  refine ⟨3739024633593866606111981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2492683089062577737407987 3739024633593866606111981)
                  ·
                    refine ⟨1402134237597699977291993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3739024633593866606111981 1402134237597699977291993)
                    ·
                      refine ⟨1051600678198274982968995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1402134237597699977291993 1051600678198274982968995)
                      ·
                        rfl

theorem cell23_2047985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 2, 1, 3, 2].length) (baseStart_2047985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2047985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2047985 prefixEnd_2047985 := by exact prefixLift 2047985
  have htrace : WordTrace (prefixWord ++ tailWord_2047985) baseStart_2047985 baseEnd_2047985 := by
    simpa [prefixWord, tailWord_2047985, baseEnd_2047985] using wordTrace_append hprefix tailTrace_2047985
  have hstable : (prefixWord ++ tailWord_2047985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047985).length < 2 ^ (prefixWord ++ tailWord_2047985).sum := by decide
  have hdescent : baseEnd_2047985 < baseStart_2047985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047998 : List Nat := [4, 2, 2, 2, 1, 2, 1, 2, 1, 4, 2]
def baseStart_2047998 : Nat := 118140960795 + 2047998 * 2 ^ 59
def prefixEnd_2047998 : Nat := 4983230072969 + 3 ^ 40 * 2047998 * 2
def baseEnd_2047998 : Nat := 1051607353446783432106435

theorem tailTrace_2047998 : CollatzResearch.WordTrace tailWord_2047998 prefixEnd_2047998 1051607353446783432106435 := by
  unfold tailWord_2047998
  simp only [CollatzResearch.WordTrace]
  refine ⟨9337077954307561382110081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49797749089640327371253765 9337077954307561382110081)
  ·
    refine ⟨7002808465730671036582561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9337077954307561382110081 7002808465730671036582561)
    ·
      refine ⟨5252106349298003277436921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7002808465730671036582561 5252106349298003277436921)
      ·
        refine ⟨3939079761973502458077691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5252106349298003277436921 3939079761973502458077691)
        ·
          refine ⟨5908619642960253687116537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3939079761973502458077691 5908619642960253687116537)
          ·
            refine ⟨4431464732220190265337403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5908619642960253687116537 4431464732220190265337403)
            ·
              refine ⟨6647197098330285398006105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4431464732220190265337403 6647197098330285398006105)
              ·
                refine ⟨4985397823747714048504579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6647197098330285398006105 4985397823747714048504579)
                ·
                  refine ⟨7478096735621571072756869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4985397823747714048504579 7478096735621571072756869)
                  ·
                    refine ⟨1402143137929044576141913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7478096735621571072756869 1402143137929044576141913)
                    ·
                      refine ⟨1051607353446783432106435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1402143137929044576141913 1051607353446783432106435)
                      ·
                        rfl

theorem cell23_2047998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_2047998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2047998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2047998 prefixEnd_2047998 := by exact prefixLift 2047998
  have htrace : WordTrace (prefixWord ++ tailWord_2047998) baseStart_2047998 baseEnd_2047998 := by
    simpa [prefixWord, tailWord_2047998, baseEnd_2047998] using wordTrace_append hprefix tailTrace_2047998
  have hstable : (prefixWord ++ tailWord_2047998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047998).length < 2 ^ (prefixWord ++ tailWord_2047998).sum := by decide
  have hdescent : baseEnd_2047998 < baseStart_2047998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048014 : List Nat := [4, 1, 1, 2, 2, 1, 2, 2, 2, 3, 3]
def baseStart_2048014 : Nat := 118140960795 + 2048014 * 2 ^ 59
def prefixEnd_2048014 : Nat := 4983230072969 + 3 ^ 40 * 2048014 * 2
def baseEnd_2048014 : Nat := 1051615569137255369506361

theorem tailTrace_2048014 : CollatzResearch.WordTrace tailWord_2048014 prefixEnd_2048014 1051615569137255369506361 := by
  unfold tailWord_2048014
  simp only [CollatzResearch.WordTrace]
  refine ⟨9337150900300315723682887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49798138134935017192975397 9337150900300315723682887)
  ·
    refine ⟨14005726350450473585524331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9337150900300315723682887 14005726350450473585524331)
    ·
      refine ⟨21008589525675710378286497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14005726350450473585524331 21008589525675710378286497)
      ·
        refine ⟨15756442144256782783714873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21008589525675710378286497 15756442144256782783714873)
        ·
          refine ⟨11817331608192587087786155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15756442144256782783714873 11817331608192587087786155)
          ·
            refine ⟨17725997412288880631679233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11817331608192587087786155 17725997412288880631679233)
            ·
              refine ⟨13294498059216660473759425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17725997412288880631679233 13294498059216660473759425)
              ·
                refine ⟨9970873544412495355319569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13294498059216660473759425 9970873544412495355319569)
                ·
                  refine ⟨7478155158309371516489677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9970873544412495355319569 7478155158309371516489677)
                  ·
                    refine ⟨2804308184366014318683629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7478155158309371516489677 2804308184366014318683629)
                    ·
                      refine ⟨1051615569137255369506361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2804308184366014318683629 1051615569137255369506361)
                      ·
                        rfl

theorem cell23_2048014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_2048014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048014 prefixEnd_2048014 := by exact prefixLift 2048014
  have htrace : WordTrace (prefixWord ++ tailWord_2048014) baseStart_2048014 baseEnd_2048014 := by
    simpa [prefixWord, tailWord_2048014, baseEnd_2048014] using wordTrace_append hprefix tailTrace_2048014
  have hstable : (prefixWord ++ tailWord_2048014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048014).length < 2 ^ (prefixWord ++ tailWord_2048014).sum := by decide
  have hdescent : baseEnd_2048014 < baseStart_2048014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048021 : List Nat := [1, 3, 2, 1, 5, 1, 1, 4, 5]
def baseStart_2048021 : Nat := 118140960795 + 2048021 * 2 ^ 59
def prefixEnd_2048021 : Nat := 4983230072969 + 3 ^ 40 * 2048021 * 2
def baseEnd_2048021 : Nat := 116846573722426315790981

theorem tailTrace_2048021 : CollatzResearch.WordTrace tailWord_2048021 prefixEnd_2048021 116846573722426315790981 := by
  unfold tailWord_2048021
  simp only [CollatzResearch.WordTrace]
  refine ⟨74697462513377165984967917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49798308342251443989978611 74697462513377165984967917)
  ·
    refine ⟨28011548442516437244362969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74697462513377165984967917 28011548442516437244362969)
    ·
      refine ⟨21008661331887327933272227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28011548442516437244362969 21008661331887327933272227)
      ·
        refine ⟨31512991997830991899908341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21008661331887327933272227 31512991997830991899908341)
        ·
          refine ⟨2954342999796655490616407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31512991997830991899908341 2954342999796655490616407)
          ·
            refine ⟨4431514499694983235924611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2954342999796655490616407 4431514499694983235924611)
            ·
              refine ⟨6647271749542474853886917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4431514499694983235924611 6647271749542474853886917)
              ·
                refine ⟨1246363453039214035103797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6647271749542474853886917 1246363453039214035103797)
                ·
                  refine ⟨116846573722426315790981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1246363453039214035103797 116846573722426315790981)
                  ·
                    rfl

theorem cell23_2048021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 4, 5].length) (baseStart_2048021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048021 prefixEnd_2048021 := by exact prefixLift 2048021
  have htrace : WordTrace (prefixWord ++ tailWord_2048021) baseStart_2048021 baseEnd_2048021 := by
    simpa [prefixWord, tailWord_2048021, baseEnd_2048021] using wordTrace_append hprefix tailTrace_2048021
  have hstable : (prefixWord ++ tailWord_2048021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048021).length < 2 ^ (prefixWord ++ tailWord_2048021).sum := by decide
  have hdescent : baseEnd_2048021 < baseStart_2048021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048024 : List Nat := [2, 1, 2, 3, 2, 1, 1, 1, 1, 7, 2]
def baseStart_2048024 : Nat := 118140960795 + 2048024 * 2 ^ 59
def prefixEnd_2048024 : Nat := 4983230072969 + 3 ^ 40 * 2048024 * 2
def baseEnd_2048024 : Nat := 1051620703943800330381315

theorem tailTrace_2048024 : CollatzResearch.WordTrace tailWord_2048024 prefixEnd_2048024 1051620703943800330381315 := by
  unfold tailWord_2048024
  simp only [CollatzResearch.WordTrace]
  refine ⟨37348785966183148748663563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49798381288244198331551417 37348785966183148748663563)
  ·
    refine ⟨56023178949274723122995345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37348785966183148748663563 56023178949274723122995345)
    ·
      refine ⟨42017384211956042342246509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56023178949274723122995345 42017384211956042342246509)
      ·
        refine ⟨15756519079483515878342441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42017384211956042342246509 15756519079483515878342441)
        ·
          refine ⟨11817389309612636908756831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15756519079483515878342441 11817389309612636908756831)
          ·
            refine ⟨17726083964418955363135247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11817389309612636908756831 17726083964418955363135247)
            ·
              refine ⟨26589125946628433044702871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17726083964418955363135247 26589125946628433044702871)
              ·
                refine ⟨39883688919942649567054307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26589125946628433044702871 39883688919942649567054307)
                ·
                  refine ⟨59825533379913974350581461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39883688919942649567054307 59825533379913974350581461)
                  ·
                    refine ⟨1402160938591733773841753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59825533379913974350581461 1402160938591733773841753)
                    ·
                      refine ⟨1051620703943800330381315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1402160938591733773841753 1051620703943800330381315)
                      ·
                        rfl

theorem cell23_2048024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 1, 7, 2].length) (baseStart_2048024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048024 prefixEnd_2048024 := by exact prefixLift 2048024
  have htrace : WordTrace (prefixWord ++ tailWord_2048024) baseStart_2048024 baseEnd_2048024 := by
    simpa [prefixWord, tailWord_2048024, baseEnd_2048024] using wordTrace_append hprefix tailTrace_2048024
  have hstable : (prefixWord ++ tailWord_2048024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048024).length < 2 ^ (prefixWord ++ tailWord_2048024).sum := by decide
  have hdescent : baseEnd_2048024 < baseStart_2048024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048074 : List Nat := [3, 1, 2, 1, 1, 2, 1, 3, 4, 2, 3]
def baseStart_2048074 : Nat := 118140960795 + 2048074 * 2 ^ 59
def prefixEnd_2048074 : Nat := 4983230072969 + 3 ^ 40 * 2048074 * 2
def baseEnd_2048074 : Nat := 1051646377976525134756085

theorem tailTrace_2048074 : CollatzResearch.WordTrace tailWord_2048074 prefixEnd_2048074 1051646377976525134756085 := by
  unfold tailWord_2048074
  simp only [CollatzResearch.WordTrace]
  refine ⟨18674848895546289009161819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49799597054790104024431517 18674848895546289009161819)
  ·
    refine ⟨28012273343319433513742729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18674848895546289009161819 28012273343319433513742729)
    ·
      refine ⟨21009205007489575135307047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28012273343319433513742729 21009205007489575135307047)
      ·
        refine ⟨31513807511234362702960571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21009205007489575135307047 31513807511234362702960571)
        ·
          refine ⟨47270711266851544054440857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31513807511234362702960571 47270711266851544054440857)
          ·
            refine ⟨35453033450138658040830643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47270711266851544054440857 35453033450138658040830643)
            ·
              refine ⟨53179550175207987061245965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35453033450138658040830643 53179550175207987061245965)
              ·
                refine ⟨19942331315702995147967237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53179550175207987061245965 19942331315702995147967237)
                ·
                  refine ⟨3739187121694311590243857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19942331315702995147967237 3739187121694311590243857)
                  ·
                    refine ⟨2804390341270733692682893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3739187121694311590243857 2804390341270733692682893)
                    ·
                      refine ⟨1051646377976525134756085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2804390341270733692682893 1051646377976525134756085)
                      ·
                        rfl

theorem cell23_2048074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 4, 2, 3].length) (baseStart_2048074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048074 prefixEnd_2048074 := by exact prefixLift 2048074
  have htrace : WordTrace (prefixWord ++ tailWord_2048074) baseStart_2048074 baseEnd_2048074 := by
    simpa [prefixWord, tailWord_2048074, baseEnd_2048074] using wordTrace_append hprefix tailTrace_2048074
  have hstable : (prefixWord ++ tailWord_2048074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048074).length < 2 ^ (prefixWord ++ tailWord_2048074).sum := by decide
  have hdescent : baseEnd_2048074 < baseStart_2048074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048097 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 3, 2, 6]
def baseStart_2048097 : Nat := 118140960795 + 2048097 * 2 ^ 59
def prefixEnd_2048097 : Nat := 4983230072969 + 3 ^ 40 * 2048097 * 2
def baseEnd_2048097 : Nat := 1051658188031578544768479

theorem tailTrace_2048097 : CollatzResearch.WordTrace tailWord_2048097 prefixEnd_2048097 1051658188031578544768479 := by
  unfold tailWord_2048097
  simp only [CollatzResearch.WordTrace]
  refine ⟨74700234461101830964734545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49800156307401220643156363 74700234461101830964734545)
  ·
    refine ⟨56025175845826373223550909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74700234461101830964734545 56025175845826373223550909)
    ·
      refine ⟨21009440942184889958831591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56025175845826373223550909 21009440942184889958831591)
      ·
        refine ⟨31514161413277334938247387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21009440942184889958831591 31514161413277334938247387)
        ·
          refine ⟨47271242119916002407371081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31514161413277334938247387 47271242119916002407371081)
          ·
            refine ⟨35453431589937001805528311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47271242119916002407371081 35453431589937001805528311)
            ·
              refine ⟨53180147384905502708292467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35453431589937001805528311 53180147384905502708292467)
              ·
                refine ⟨79770221077358254062438701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53180147384905502708292467 79770221077358254062438701)
                ·
                  refine ⟨29913832904009345273414513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79770221077358254062438701 29913832904009345273414513)
                  ·
                    refine ⟨22435374678007008955060885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29913832904009345273414513 22435374678007008955060885)
                    ·
                      refine ⟨1051658188031578544768479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22435374678007008955060885 1051658188031578544768479)
                      ·
                        rfl

theorem cell23_2048097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_2048097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048097 prefixEnd_2048097 := by exact prefixLift 2048097
  have htrace : WordTrace (prefixWord ++ tailWord_2048097) baseStart_2048097 baseEnd_2048097 := by
    simpa [prefixWord, tailWord_2048097, baseEnd_2048097] using wordTrace_append hprefix tailTrace_2048097
  have hstable : (prefixWord ++ tailWord_2048097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048097).length < 2 ^ (prefixWord ++ tailWord_2048097).sum := by decide
  have hdescent : baseEnd_2048097 < baseStart_2048097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048131 : List Nat := [1, 1, 1, 3, 3, 3, 1, 1, 4, 3, 2]
def baseStart_2048131 : Nat := 118140960795 + 2048131 * 2 ^ 59
def prefixEnd_2048131 : Nat := 4983230072969 + 3 ^ 40 * 2048131 * 2
def baseEnd_2048131 : Nat := 1051675646373831411743323

theorem tailTrace_2048131 : CollatzResearch.WordTrace tailWord_2048131 prefixEnd_2048131 1051675646373831411743323 := by
  unfold tailWord_2048131
  simp only [CollatzResearch.WordTrace]
  refine ⟨74701474542978654771472247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49800983028652436514314831 74701474542978654771472247)
  ·
    refine ⟨112052211814467982157208371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74701474542978654771472247 112052211814467982157208371)
    ·
      refine ⟨168078317721701973235812557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112052211814467982157208371 168078317721701973235812557)
      ·
        refine ⟨63029369145638239963429709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168078317721701973235812557 63029369145638239963429709)
        ·
          refine ⟨23636013429614339986286141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63029369145638239963429709 23636013429614339986286141)
          ·
            refine ⟨8863505036105377494857303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23636013429614339986286141 8863505036105377494857303)
            ·
              refine ⟨13295257554158066242285955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8863505036105377494857303 13295257554158066242285955)
              ·
                refine ⟨19942886331237099363428933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13295257554158066242285955 19942886331237099363428933)
                ·
                  refine ⟨3739291187106956130642925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19942886331237099363428933 3739291187106956130642925)
                  ·
                    refine ⟨1402234195165108548991097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3739291187106956130642925 1402234195165108548991097)
                    ·
                      refine ⟨1051675646373831411743323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1402234195165108548991097 1051675646373831411743323)
                      ·
                        rfl

theorem cell23_2048131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 4, 3, 2].length) (baseStart_2048131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048131 prefixEnd_2048131 := by exact prefixLift 2048131
  have htrace : WordTrace (prefixWord ++ tailWord_2048131) baseStart_2048131 baseEnd_2048131 := by
    simpa [prefixWord, tailWord_2048131, baseEnd_2048131] using wordTrace_append hprefix tailTrace_2048131
  have hstable : (prefixWord ++ tailWord_2048131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048131).length < 2 ^ (prefixWord ++ tailWord_2048131).sum := by decide
  have hdescent : baseEnd_2048131 < baseStart_2048131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048138 : List Nat := [3, 1, 2, 3, 1, 2, 3, 1, 3, 1, 3]
def baseStart_2048138 : Nat := 118140960795 + 2048138 * 2 ^ 59
def prefixEnd_2048138 : Nat := 4983230072969 + 3 ^ 40 * 2048138 * 2
def baseEnd_2048138 : Nat := 1051679240738412884355791

theorem tailTrace_2048138 : CollatzResearch.WordTrace tailWord_2048138 prefixEnd_2048138 1051679240738412884355791 := by
  unfold tailWord_2048138
  simp only [CollatzResearch.WordTrace]
  refine ⟨18675432463488323741744267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49801153235968863311318045 18675432463488323741744267)
  ·
    refine ⟨28013148695232485612616401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18675432463488323741744267 28013148695232485612616401)
    ·
      refine ⟨21009861521424364209462301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28013148695232485612616401 21009861521424364209462301)
      ·
        refine ⟨7878698070534136578548363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21009861521424364209462301 7878698070534136578548363)
        ·
          refine ⟨11818047105801204867822545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7878698070534136578548363 11818047105801204867822545)
          ·
            refine ⟨8863535329350903650866909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11818047105801204867822545 8863535329350903650866909)
            ·
              refine ⟨3323825748506588869075091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8863535329350903650866909 3323825748506588869075091)
              ·
                refine ⟨4985738622759883303612637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3323825748506588869075091 4985738622759883303612637)
                ·
                  refine ⟨1869651983534956238854739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4985738622759883303612637 1869651983534956238854739)
                  ·
                    refine ⟨2804477975302434358282109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1869651983534956238854739 2804477975302434358282109)
                    ·
                      refine ⟨1051679240738412884355791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2804477975302434358282109 1051679240738412884355791)
                      ·
                        rfl

theorem cell23_2048138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_2048138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048138 prefixEnd_2048138 := by exact prefixLift 2048138
  have htrace : WordTrace (prefixWord ++ tailWord_2048138) baseStart_2048138 baseEnd_2048138 := by
    simpa [prefixWord, tailWord_2048138, baseEnd_2048138] using wordTrace_append hprefix tailTrace_2048138
  have hstable : (prefixWord ++ tailWord_2048138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048138).length < 2 ^ (prefixWord ++ tailWord_2048138).sum := by decide
  have hdescent : baseEnd_2048138 < baseStart_2048138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048144 : List Nat := [2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 4]
def baseStart_2048144 : Nat := 118140960795 + 2048144 * 2 ^ 59
def prefixEnd_2048144 : Nat := 4983230072969 + 3 ^ 40 * 2048144 * 2
def baseEnd_2048144 : Nat := 1051682321622339860880763

theorem tailTrace_2048144 : CollatzResearch.WordTrace tailWord_2048144 prefixEnd_2048144 1051682321622339860880763 := by
  unfold tailWord_2048144
  simp only [CollatzResearch.WordTrace]
  refine ⟨37350974345965778995847743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49801299127954371994463657 37350974345965778995847743)
  ·
    refine ⟨56026461518948668493771615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37350974345965778995847743 56026461518948668493771615)
    ·
      refine ⟨84039692278423002740657423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56026461518948668493771615 84039692278423002740657423)
      ·
        refine ⟨126059538417634504110986135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84039692278423002740657423 126059538417634504110986135)
        ·
          refine ⟨189089307626451756166479203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126059538417634504110986135 189089307626451756166479203)
          ·
            refine ⟨283633961439677634249718805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189089307626451756166479203 283633961439677634249718805)
            ·
              refine ⟨13295341942484889105455569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 283633961439677634249718805 13295341942484889105455569)
              ·
                refine ⟨9971506456863666829091677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13295341942484889105455569 9971506456863666829091677)
                ·
                  refine ⟨3739314921323875060909379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9971506456863666829091677 3739314921323875060909379)
                  ·
                    refine ⟨5608972381985812591364069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3739314921323875060909379 5608972381985812591364069)
                    ·
                      refine ⟨1051682321622339860880763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5608972381985812591364069 1051682321622339860880763)
                      ·
                        rfl

theorem cell23_2048144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 4].length) (baseStart_2048144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048144 prefixEnd_2048144 := by exact prefixLift 2048144
  have htrace : WordTrace (prefixWord ++ tailWord_2048144) baseStart_2048144 baseEnd_2048144 := by
    simpa [prefixWord, tailWord_2048144, baseEnd_2048144] using wordTrace_append hprefix tailTrace_2048144
  have hstable : (prefixWord ++ tailWord_2048144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048144).length < 2 ^ (prefixWord ++ tailWord_2048144).sum := by decide
  have hdescent : baseEnd_2048144 < baseStart_2048144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048158 : List Nat := [4, 3, 1, 1, 3, 1, 1, 1, 3, 5]
def baseStart_2048158 : Nat := 118140960795 + 2048158 * 2 ^ 59
def prefixEnd_2048158 : Nat := 4983230072969 + 3 ^ 40 * 2048158 * 2
def baseEnd_2048158 : Nat := 350563170117167602035233

theorem tailTrace_2048158 : CollatzResearch.WordTrace tailWord_2048158 prefixEnd_2048158 350563170117167602035233 := by
  unfold tailWord_2048158
  simp only [CollatzResearch.WordTrace]
  refine ⟨9337807414235104797838141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49801639542587225588470085 9337807414235104797838141)
  ·
    refine ⟨3501677780338164299189303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9337807414235104797838141 3501677780338164299189303)
    ·
      refine ⟨5252516670507246448783955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3501677780338164299189303 5252516670507246448783955)
      ·
        refine ⟨7878775005760869673175933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5252516670507246448783955 7878775005760869673175933)
        ·
          refine ⟨2954540627160326127440975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7878775005760869673175933 2954540627160326127440975)
          ·
            refine ⟨4431810940740489191161463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2954540627160326127440975 4431810940740489191161463)
            ·
              refine ⟨6647716411110733786742195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4431810940740489191161463 6647716411110733786742195)
              ·
                refine ⟨9971574616666100680113293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6647716411110733786742195 9971574616666100680113293)
                ·
                  refine ⟨3739340481249787755042485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9971574616666100680113293 3739340481249787755042485)
                  ·
                    refine ⟨350563170117167602035233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3739340481249787755042485 350563170117167602035233)
                    ·
                      rfl

theorem cell23_2048158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_2048158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048158 prefixEnd_2048158 := by exact prefixLift 2048158
  have htrace : WordTrace (prefixWord ++ tailWord_2048158) baseStart_2048158 baseEnd_2048158 := by
    simpa [prefixWord, tailWord_2048158, baseEnd_2048158] using wordTrace_append hprefix tailTrace_2048158
  have hstable : (prefixWord ++ tailWord_2048158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048158).length < 2 ^ (prefixWord ++ tailWord_2048158).sum := by decide
  have hdescent : baseEnd_2048158 < baseStart_2048158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048161 : List Nat := [1, 2, 3, 3, 1, 3, 1, 1, 3, 1, 4]
def baseStart_2048161 : Nat := 118140960795 + 2048161 * 2 ^ 59
def prefixEnd_2048161 : Nat := 4983230072969 + 3 ^ 40 * 2048161 * 2
def baseEnd_2048161 : Nat := 1051691050793466294368185

theorem tailTrace_2048161 : CollatzResearch.WordTrace tailWord_2048161 prefixEnd_2048161 1051691050793466294368185 := by
  unfold tailWord_2048161
  simp only [CollatzResearch.WordTrace]
  refine ⟨74702568732869969895064337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49801712488579979930042891 74702568732869969895064337)
  ·
    refine ⟨56026926549652477421298253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74702568732869969895064337 56026926549652477421298253)
    ·
      refine ⟨21010097456119679032986845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56026926549652477421298253 21010097456119679032986845)
      ·
        refine ⟨7878786546044879637370067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21010097456119679032986845 7878786546044879637370067)
        ·
          refine ⟨11818179819067319456055101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7878786546044879637370067 11818179819067319456055101)
          ·
            refine ⟨4431817432150244796020663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11818179819067319456055101 4431817432150244796020663)
            ·
              refine ⟨6647726148225367194030995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4431817432150244796020663 6647726148225367194030995)
              ·
                refine ⟨9971589222338050791046493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6647726148225367194030995 9971589222338050791046493)
                ·
                  refine ⟨3739345958376769046642435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9971589222338050791046493 3739345958376769046642435)
                  ·
                    refine ⟨5609018937565153569963653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3739345958376769046642435 5609018937565153569963653)
                    ·
                      refine ⟨1051691050793466294368185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5609018937565153569963653 1051691050793466294368185)
                      ·
                        rfl

theorem cell23_2048161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_2048161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048161 prefixEnd_2048161 := by exact prefixLift 2048161
  have htrace : WordTrace (prefixWord ++ tailWord_2048161) baseStart_2048161 baseEnd_2048161 := by
    simpa [prefixWord, tailWord_2048161, baseEnd_2048161] using wordTrace_append hprefix tailTrace_2048161
  have hstable : (prefixWord ++ tailWord_2048161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048161).length < 2 ^ (prefixWord ++ tailWord_2048161).sum := by decide
  have hdescent : baseEnd_2048161 < baseStart_2048161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048178 : List Nat := [3, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4]
def baseStart_2048178 : Nat := 118140960795 + 2048178 * 2 ^ 59
def prefixEnd_2048178 : Nat := 4983230072969 + 3 ^ 40 * 2048178 * 2
def baseEnd_2048178 : Nat := 1051699779964592727855607

theorem tailTrace_2048178 : CollatzResearch.WordTrace tailWord_2048178 prefixEnd_2048178 1051699779964592727855607 := by
  unfold tailWord_2048178
  simp only [CollatzResearch.WordTrace]
  refine ⟨18675797193452095449608297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49802125849205587865622125 18675797193452095449608297)
  ·
    refine ⟨14006847895089071587206223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18675797193452095449608297 14006847895089071587206223)
    ·
      refine ⟨21010271842633607380809335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14006847895089071587206223 21010271842633607380809335)
      ·
        refine ⟨31515407763950411071214003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21010271842633607380809335 31515407763950411071214003)
        ·
          refine ⟨47273111645925616606821005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31515407763950411071214003 47273111645925616606821005)
          ·
            refine ⟨17727416867222106227557877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47273111645925616606821005 17727416867222106227557877)
            ·
              refine ⟨1661945331302072458833551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17727416867222106227557877 1661945331302072458833551)
              ·
                refine ⟨2492917996953108688250327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1661945331302072458833551 2492917996953108688250327)
                ·
                  refine ⟨3739376995429663032375491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2492917996953108688250327 3739376995429663032375491)
                  ·
                    refine ⟨5609065493144494548563237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3739376995429663032375491 5609065493144494548563237)
                    ·
                      refine ⟨1051699779964592727855607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5609065493144494548563237 1051699779964592727855607)
                      ·
                        rfl

theorem cell23_2048178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4].length) (baseStart_2048178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048178 prefixEnd_2048178 := by exact prefixLift 2048178
  have htrace : WordTrace (prefixWord ++ tailWord_2048178) baseStart_2048178 baseEnd_2048178 := by
    simpa [prefixWord, tailWord_2048178, baseEnd_2048178] using wordTrace_append hprefix tailTrace_2048178
  have hstable : (prefixWord ++ tailWord_2048178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048178).length < 2 ^ (prefixWord ++ tailWord_2048178).sum := by decide
  have hdescent : baseEnd_2048178 < baseStart_2048178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048224 : List Nat := [2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 5]
def baseStart_2048224 : Nat := 118140960795 + 2048224 * 2 ^ 59
def prefixEnd_2048224 : Nat := 4983230072969 + 3 ^ 40 * 2048224 * 2
def baseEnd_2048224 : Nat := 1051723400074699547880395

theorem tailTrace_2048224 : CollatzResearch.WordTrace tailWord_2048224 prefixEnd_2048224 1051723400074699547880395 := by
  unfold tailWord_2048224
  simp only [CollatzResearch.WordTrace]
  refine ⟨37352433265820865827303863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49803244354427821103071817 37352433265820865827303863)
  ·
    refine ⟨56028649898731298740955795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37352433265820865827303863 56028649898731298740955795)
    ·
      refine ⟨84042974848096948111433693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56028649898731298740955795 84042974848096948111433693)
      ·
        refine ⟨31516115568036355541787635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84042974848096948111433693 31516115568036355541787635)
        ·
          refine ⟨47274173352054533312681453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31516115568036355541787635 47274173352054533312681453)
          ·
            refine ⟨17727815007020449992255545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47274173352054533312681453 17727815007020449992255545)
            ·
              refine ⟨13295861255265337494191659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17727815007020449992255545 13295861255265337494191659)
              ·
                refine ⟨19943791882898006241287489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13295861255265337494191659 19943791882898006241287489)
                ·
                  refine ⟨14957843912173504680965617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19943791882898006241287489 14957843912173504680965617)
                  ·
                    refine ⟨11218382934130128510724213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14957843912173504680965617 11218382934130128510724213)
                    ·
                      refine ⟨1051723400074699547880395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11218382934130128510724213 1051723400074699547880395)
                      ·
                        rfl

theorem cell23_2048224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_2048224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048224 prefixEnd_2048224 := by exact prefixLift 2048224
  have htrace : WordTrace (prefixWord ++ tailWord_2048224) baseStart_2048224 baseEnd_2048224 := by
    simpa [prefixWord, tailWord_2048224, baseEnd_2048224] using wordTrace_append hprefix tailTrace_2048224
  have hstable : (prefixWord ++ tailWord_2048224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048224).length < 2 ^ (prefixWord ++ tailWord_2048224).sum := by decide
  have hdescent : baseEnd_2048224 < baseStart_2048224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048226 : List Nat := [3, 3, 4, 1, 2, 1, 2, 1, 1, 5]
def baseStart_2048226 : Nat := 118140960795 + 2048226 * 2 ^ 59
def prefixEnd_2048226 : Nat := 4983230072969 + 3 ^ 40 * 2048226 * 2
def baseEnd_2048226 : Nat := 350574809012002846685129

theorem tailTrace_2048226 : CollatzResearch.WordTrace tailWord_2048226 prefixEnd_2048226 350574809012002846685129 := by
  unfold tailWord_2048226
  simp only [CollatzResearch.WordTrace]
  refine ⟨18676234869408621499045133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49803292985089657330787021 18676234869408621499045133)
  ·
    refine ⟨7003588076028233062141925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18676234869408621499045133 7003588076028233062141925)
    ·
      refine ⟨1313172764255293699151611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7003588076028233062141925 1313172764255293699151611)
      ·
        refine ⟨1969759146382940548727417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1313172764255293699151611 1969759146382940548727417)
        ·
          refine ⟨1477319359787205411545563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1969759146382940548727417 1477319359787205411545563)
          ·
            refine ⟨2215979039680808117318345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1477319359787205411545563 2215979039680808117318345)
            ·
              refine ⟨1661984279760606087988759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2215979039680808117318345 1661984279760606087988759)
              ·
                refine ⟨2492976419640909131983139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1661984279760606087988759 2492976419640909131983139)
                ·
                  refine ⟨3739464629461363697974709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2492976419640909131983139 3739464629461363697974709)
                  ·
                    refine ⟨350574809012002846685129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3739464629461363697974709 350574809012002846685129)
                    ·
                      rfl

theorem cell23_2048226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_2048226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048226 prefixEnd_2048226 := by exact prefixLift 2048226
  have htrace : WordTrace (prefixWord ++ tailWord_2048226) baseStart_2048226 baseEnd_2048226 := by
    simpa [prefixWord, tailWord_2048226, baseEnd_2048226] using wordTrace_append hprefix tailTrace_2048226
  have hstable : (prefixWord ++ tailWord_2048226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048226).length < 2 ^ (prefixWord ++ tailWord_2048226).sum := by decide
  have hdescent : baseEnd_2048226 < baseStart_2048226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048304 : List Nat := [2, 1, 1, 1, 2, 2, 2, 2, 3, 7]
def baseStart_2048304 : Nat := 118140960795 + 2048304 * 2 ^ 59
def prefixEnd_2048304 : Nat := 4983230072969 + 3 ^ 40 * 2048304 * 2
def baseEnd_2048304 : Nat := 350588159509019744960009

theorem tailTrace_2048304 : CollatzResearch.WordTrace tailWord_2048304 prefixEnd_2048304 350588159509019744960009 := by
  unfold tailWord_2048304
  simp only [CollatzResearch.WordTrace]
  refine ⟨37353892185675952658759983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49805189580901270211679977 37353892185675952658759983)
  ·
    refine ⟨56030838278513928988139975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37353892185675952658759983 56030838278513928988139975)
    ·
      refine ⟨84046257417770893482209963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56030838278513928988139975 84046257417770893482209963)
      ·
        refine ⟨126069386126656340223314945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84046257417770893482209963 126069386126656340223314945)
        ·
          refine ⟨94552039594992255167486209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126069386126656340223314945 94552039594992255167486209)
          ·
            refine ⟨70914029696244191375614657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94552039594992255167486209 70914029696244191375614657)
            ·
              refine ⟨53185522272183143531710993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70914029696244191375614657 53185522272183143531710993)
              ·
                refine ⟨39889141704137357648783245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53185522272183143531710993 39889141704137357648783245)
                ·
                  refine ⟨14958428139051509118293717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39889141704137357648783245 14958428139051509118293717)
                  ·
                    refine ⟨350588159509019744960009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14958428139051509118293717 350588159509019744960009)
                    ·
                      rfl

theorem cell23_2048304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 3, 7].length) (baseStart_2048304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048304 prefixEnd_2048304 := by exact prefixLift 2048304
  have htrace : WordTrace (prefixWord ++ tailWord_2048304) baseStart_2048304 baseEnd_2048304 := by
    simpa [prefixWord, tailWord_2048304, baseEnd_2048304] using wordTrace_append hprefix tailTrace_2048304
  have hstable : (prefixWord ++ tailWord_2048304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048304).length < 2 ^ (prefixWord ++ tailWord_2048304).sum := by decide
  have hdescent : baseEnd_2048304 < baseStart_2048304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048308 : List Nat := [2, 5, 1, 1, 1, 2, 3, 1, 7]
def baseStart_2048308 : Nat := 118140960795 + 2048308 * 2 ^ 59
def prefixEnd_2048308 : Nat := 4983230072969 + 3 ^ 40 * 2048308 * 2
def baseEnd_2048308 : Nat := 116862948049964135470001

theorem tailTrace_2048308 : CollatzResearch.WordTrace tailWord_2048308 prefixEnd_2048308 116862948049964135470001 := by
  unfold tailWord_2048308
  simp only [CollatzResearch.WordTrace]
  refine ⟨37353965131668707000332789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49805286842224942667110385 37353965131668707000332789)
  ·
    refine ⟨3501934231093941281281199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37353965131668707000332789 3501934231093941281281199)
    ·
      refine ⟨5252901346640911921921799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3501934231093941281281199 5252901346640911921921799)
      ·
        refine ⟨7879352019961367882882699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5252901346640911921921799 7879352019961367882882699)
        ·
          refine ⟨11819028029942051824324049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7879352019961367882882699 11819028029942051824324049)
          ·
            refine ⟨8864271022456538868243037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11819028029942051824324049 8864271022456538868243037)
            ·
              refine ⟨3324101633421202075591139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8864271022456538868243037 3324101633421202075591139)
              ·
                refine ⟨4986152450131803113386709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3324101633421202075591139 4986152450131803113386709)
                ·
                  refine ⟨116862948049964135470001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4986152450131803113386709 116862948049964135470001)
                  ·
                    rfl

theorem cell23_2048308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_2048308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048308 prefixEnd_2048308 := by exact prefixLift 2048308
  have htrace : WordTrace (prefixWord ++ tailWord_2048308) baseStart_2048308 baseEnd_2048308 := by
    simpa [prefixWord, tailWord_2048308, baseEnd_2048308] using wordTrace_append hprefix tailTrace_2048308
  have hstable : (prefixWord ++ tailWord_2048308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048308).length < 2 ^ (prefixWord ++ tailWord_2048308).sum := by decide
  have hdescent : baseEnd_2048308 < baseStart_2048308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048385 : List Nat := [1, 2, 4, 3, 1, 2, 1, 2, 3, 4]
def baseStart_2048385 : Nat := 118140960795 + 2048385 * 2 ^ 59
def prefixEnd_2048385 : Nat := 4983230072969 + 3 ^ 40 * 2048385 * 2
def baseEnd_2048385 : Nat := 350602023486691139322385

theorem tailTrace_2048385 : CollatzResearch.WordTrace tailWord_2048385 prefixEnd_2048385 350602023486691139322385 := by
  unfold tailWord_2048385
  simp only [CollatzResearch.WordTrace]
  refine ⟨74710738684058456151218609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49807159122705637434145739 74710738684058456151218609)
  ·
    refine ⟨56033054013043842113413957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74710738684058456151218609 56033054013043842113413957)
    ·
      refine ⟨10506197627445720396265117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56033054013043842113413957 10506197627445720396265117)
      ·
        refine ⟨3939824110292145148599419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10506197627445720396265117 3939824110292145148599419)
        ·
          refine ⟨5909736165438217722899129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3939824110292145148599419 5909736165438217722899129)
          ·
            refine ⟨4432302124078663292174347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5909736165438217722899129 4432302124078663292174347)
            ·
              refine ⟨6648453186117994938261521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4432302124078663292174347 6648453186117994938261521)
              ·
                refine ⟨4986339889588496203696141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6648453186117994938261521 4986339889588496203696141)
                ·
                  refine ⟨1869877458595686076386053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4986339889588496203696141 1869877458595686076386053)
                  ·
                    refine ⟨350602023486691139322385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1869877458595686076386053 350602023486691139322385)
                    ·
                      rfl

theorem cell23_2048385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_2048385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048385 prefixEnd_2048385 := by exact prefixLift 2048385
  have htrace : WordTrace (prefixWord ++ tailWord_2048385) baseStart_2048385 baseEnd_2048385 := by
    simpa [prefixWord, tailWord_2048385, baseEnd_2048385] using wordTrace_append hprefix tailTrace_2048385
  have hstable : (prefixWord ++ tailWord_2048385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048385).length < 2 ^ (prefixWord ++ tailWord_2048385).sum := by decide
  have hdescent : baseEnd_2048385 < baseStart_2048385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048395 : List Nat := [1, 1, 1, 1, 4, 6, 1, 1, 2, 2, 3]
def baseStart_2048395 : Nat := 118140960795 + 2048395 * 2 ^ 59
def prefixEnd_2048395 : Nat := 4983230072969 + 3 ^ 40 * 2048395 * 2
def baseEnd_2048395 : Nat := 1051811205266618378842109

theorem tailTrace_2048395 : CollatzResearch.WordTrace tailWord_2048395 prefixEnd_2048395 1051811205266618378842109 := by
  unfold tailWord_2048395
  simp only [CollatzResearch.WordTrace]
  refine ⟨74711103414022227859082639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49807402276014818572721759 74711103414022227859082639)
  ·
    refine ⟨112066655121033341788623959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74711103414022227859082639 112066655121033341788623959)
    ·
      refine ⟨168099982681550012682935939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112066655121033341788623959 168099982681550012682935939)
      ·
        refine ⟨252149974022325019024403909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168099982681550012682935939 252149974022325019024403909)
        ·
          refine ⟨47278120129185941067075733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 252149974022325019024403909 47278120129185941067075733)
          ·
            refine ⟨2216161881055590987519175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 47278120129185941067075733 2216161881055590987519175)
            ·
              refine ⟨3324242821583386481278763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2216161881055590987519175 3324242821583386481278763)
              ·
                refine ⟨4986364232375079721918145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3324242821583386481278763 4986364232375079721918145)
                ·
                  refine ⟨3739773174281309791438609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4986364232375079721918145 3739773174281309791438609)
                  ·
                    refine ⟨2804829880710982343578957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3739773174281309791438609 2804829880710982343578957)
                    ·
                      refine ⟨1051811205266618378842109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2804829880710982343578957 1051811205266618378842109)
                      ·
                        rfl

theorem cell23_2048395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 2, 2, 3].length) (baseStart_2048395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048395 prefixEnd_2048395 := by exact prefixLift 2048395
  have htrace : WordTrace (prefixWord ++ tailWord_2048395) baseStart_2048395 baseEnd_2048395 := by
    simpa [prefixWord, tailWord_2048395, baseEnd_2048395] using wordTrace_append hprefix tailTrace_2048395
  have hstable : (prefixWord ++ tailWord_2048395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048395).length < 2 ^ (prefixWord ++ tailWord_2048395).sum := by decide
  have hdescent : baseEnd_2048395 < baseStart_2048395 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048445 : List Nat := [1, 4, 1, 2, 2, 3, 2, 2, 1, 5]
def baseStart_2048445 : Nat := 118140960795 + 2048445 * 2 ^ 59
def prefixEnd_2048445 : Nat := 4983230072969 + 3 ^ 40 * 2048445 * 2
def baseEnd_2048445 : Nat := 350612293099781061072293

theorem tailTrace_2048445 : CollatzResearch.WordTrace tailWord_2048445 prefixEnd_2048445 350612293099781061072293 := by
  unfold tailWord_2048445
  simp only [CollatzResearch.WordTrace]
  refine ⟨74712927063841086398402789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49808618042560724265601859 74712927063841086398402789)
  ·
    refine ⟨14008673824470203699700523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74712927063841086398402789 14008673824470203699700523)
    ·
      refine ⟨21013010736705305549550785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14008673824470203699700523 21013010736705305549550785)
      ·
        refine ⟨15759758052528979162163089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21013010736705305549550785 15759758052528979162163089)
        ·
          refine ⟨11819818539396734371622317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15759758052528979162163089 11819818539396734371622317)
          ·
            refine ⟨4432431952273775389358369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11819818539396734371622317 4432431952273775389358369)
            ·
              refine ⟨3324323964205331542018777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4432431952273775389358369 3324323964205331542018777)
              ·
                refine ⟨2493242973153998656514083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3324323964205331542018777 2493242973153998656514083)
                ·
                  refine ⟨3739864459730997984771125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2493242973153998656514083 3739864459730997984771125)
                  ·
                    refine ⟨350612293099781061072293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3739864459730997984771125 350612293099781061072293)
                    ·
                      rfl

theorem cell23_2048445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 2, 1, 5].length) (baseStart_2048445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048445 prefixEnd_2048445 := by exact prefixLift 2048445
  have htrace : WordTrace (prefixWord ++ tailWord_2048445) baseStart_2048445 baseEnd_2048445 := by
    simpa [prefixWord, tailWord_2048445, baseEnd_2048445] using wordTrace_append hprefix tailTrace_2048445
  have hstable : (prefixWord ++ tailWord_2048445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048445).length < 2 ^ (prefixWord ++ tailWord_2048445).sum := by decide
  have hdescent : baseEnd_2048445 < baseStart_2048445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048448 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 1, 8, 2]
def baseStart_2048448 : Nat := 118140960795 + 2048448 * 2 ^ 59
def prefixEnd_2048448 : Nat := 4983230072969 + 3 ^ 40 * 2048448 * 2
def baseEnd_2048448 : Nat := 1051838419741306671479365

theorem tailTrace_2048448 : CollatzResearch.WordTrace tailWord_2048448 prefixEnd_2048448 1051838419741306671479365 := by
  unfold tailWord_2048448
  simp only [CollatzResearch.WordTrace]
  refine ⟨37356518241415108955380999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49808690988553478607174665 37356518241415108955380999)
  ·
    refine ⟨56034777362122663433071499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37356518241415108955380999 56034777362122663433071499)
    ·
      refine ⟨84052166043183995149607249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56034777362122663433071499 84052166043183995149607249)
      ·
        refine ⟨63039124532387996362205437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84052166043183995149607249 63039124532387996362205437)
        ·
          refine ⟨23639671699645498635827039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63039124532387996362205437 23639671699645498635827039)
          ·
            refine ⟨35459507549468247953740559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23639671699645498635827039 35459507549468247953740559)
            ·
              refine ⟨53189261324202371930610839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35459507549468247953740559 53189261324202371930610839)
              ·
                refine ⟨79783891986303557895916259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53189261324202371930610839 79783891986303557895916259)
                ·
                  refine ⟨119675837979455336843874389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79783891986303557895916259 119675837979455336843874389)
                  ·
                    refine ⟨1402451226321742228639153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 119675837979455336843874389 1402451226321742228639153)
                    ·
                      refine ⟨1051838419741306671479365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1402451226321742228639153 1051838419741306671479365)
                      ·
                        rfl

theorem cell23_2048448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 1, 8, 2].length) (baseStart_2048448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048448 prefixEnd_2048448 := by exact prefixLift 2048448
  have htrace : WordTrace (prefixWord ++ tailWord_2048448) baseStart_2048448 baseEnd_2048448 := by
    simpa [prefixWord, tailWord_2048448, baseEnd_2048448] using wordTrace_append hprefix tailTrace_2048448
  have hstable : (prefixWord ++ tailWord_2048448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048448).length < 2 ^ (prefixWord ++ tailWord_2048448).sum := by decide
  have hdescent : baseEnd_2048448 < baseStart_2048448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048451 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 5]
def baseStart_2048451 : Nat := 118140960795 + 2048451 * 2 ^ 59
def prefixEnd_2048451 : Nat := 4983230072969 + 3 ^ 40 * 2048451 * 2
def baseEnd_2048451 : Nat := 1051839960183270159741851

theorem tailTrace_2048451 : CollatzResearch.WordTrace tailWord_2048451 prefixEnd_2048451 1051839960183270159741851 := by
  unfold tailWord_2048451
  simp only [CollatzResearch.WordTrace]
  refine ⟨74713145901819349423121207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49808763934546232948747471 74713145901819349423121207)
  ·
    refine ⟨112069718852729024134681811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74713145901819349423121207 112069718852729024134681811)
    ·
      refine ⟨168104578279093536202022717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112069718852729024134681811 168104578279093536202022717)
      ·
        refine ⟨63039216854660076075758519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168104578279093536202022717 63039216854660076075758519)
        ·
          refine ⟨94558825281990114113637779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63039216854660076075758519 94558825281990114113637779)
          ·
            refine ⟨141838237922985171170456669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94558825281990114113637779 141838237922985171170456669)
            ·
              refine ⟨53189339221119439188921251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141838237922985171170456669 53189339221119439188921251)
              ·
                refine ⟨79784008831679158783381877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53189339221119439188921251 79784008831679158783381877)
                ·
                  refine ⟨7479750827969921135942051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79784008831679158783381877 7479750827969921135942051)
                  ·
                    refine ⟨11219626241954881703913077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7479750827969921135942051 11219626241954881703913077)
                    ·
                      refine ⟨1051839960183270159741851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11219626241954881703913077 1051839960183270159741851)
                      ·
                        rfl

theorem cell23_2048451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 5].length) (baseStart_2048451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048451 prefixEnd_2048451 := by exact prefixLift 2048451
  have htrace : WordTrace (prefixWord ++ tailWord_2048451) baseStart_2048451 baseEnd_2048451 := by
    simpa [prefixWord, tailWord_2048451, baseEnd_2048451] using wordTrace_append hprefix tailTrace_2048451
  have hstable : (prefixWord ++ tailWord_2048451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048451).length < 2 ^ (prefixWord ++ tailWord_2048451).sum := by decide
  have hdescent : baseEnd_2048451 < baseStart_2048451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048458 : List Nat := [3, 1, 2, 1, 2, 2, 1, 1, 6, 4]
def baseStart_2048458 : Nat := 118140960795 + 2048458 * 2 ^ 59
def prefixEnd_2048458 : Nat := 4983230072969 + 3 ^ 40 * 2048458 * 2
def baseEnd_2048458 : Nat := 350614518182617210784773

theorem tailTrace_2048458 : CollatzResearch.WordTrace tailWord_2048458 prefixEnd_2048458 350614518182617210784773 := by
  unfold tailWord_2048458
  simp only [CollatzResearch.WordTrace]
  refine ⟨18678350303198497404656507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49808934141862659745750685 18678350303198497404656507)
  ·
    refine ⟨28017525454797746106984761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18678350303198497404656507 28017525454797746106984761)
    ·
      refine ⟨21013144091098309580238571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28017525454797746106984761 21013144091098309580238571)
      ·
        refine ⟨31519716136647464370357857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21013144091098309580238571 31519716136647464370357857)
        ·
          refine ⟨23639787102485598277768393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31519716136647464370357857 23639787102485598277768393)
          ·
            refine ⟨17729840326864198708326295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23639787102485598277768393 17729840326864198708326295)
            ·
              refine ⟨26594760490296298062489443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17729840326864198708326295 26594760490296298062489443)
              ·
                refine ⟨39892140735444447093734165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26594760490296298062489443 39892140735444447093734165)
                ·
                  refine ⟨1869944096973958457518789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 39892140735444447093734165 1869944096973958457518789)
                  ·
                    refine ⟨350614518182617210784773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1869944096973958457518789 350614518182617210784773)
                    ·
                      rfl

theorem cell23_2048458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 6, 4].length) (baseStart_2048458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048458 prefixEnd_2048458 := by exact prefixLift 2048458
  have htrace : WordTrace (prefixWord ++ tailWord_2048458) baseStart_2048458 baseEnd_2048458 := by
    simpa [prefixWord, tailWord_2048458, baseEnd_2048458] using wordTrace_append hprefix tailTrace_2048458
  have hstable : (prefixWord ++ tailWord_2048458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048458).length < 2 ^ (prefixWord ++ tailWord_2048458).sum := by decide
  have hdescent : baseEnd_2048458 < baseStart_2048458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048465 : List Nat := [1, 2, 2, 1, 2, 1, 1, 4, 5, 2, 2]
def baseStart_2048465 : Nat := 118140960795 + 2048465 * 2 ^ 59
def prefixEnd_2048465 : Nat := 4983230072969 + 3 ^ 40 * 2048465 * 2
def baseEnd_2048465 : Nat := 1051847148912433104966787

theorem tailTrace_2048465 : CollatzResearch.WordTrace tailWord_2048465 prefixEnd_2048465 1051847148912433104966787 := by
  unfold tailWord_2048465
  simp only [CollatzResearch.WordTrace]
  refine ⟨74713656523768629814130849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49809104349179086542753899 74713656523768629814130849)
  ·
    refine ⟨56035242392826472360598137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74713656523768629814130849 56035242392826472360598137)
    ·
      refine ⟨42026431794619854270448603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56035242392826472360598137 42026431794619854270448603)
      ·
        refine ⟨63039647691929781405672905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42026431794619854270448603 63039647691929781405672905)
        ·
          refine ⟨47279735768947336054254679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63039647691929781405672905 47279735768947336054254679)
          ·
            refine ⟨70919603653421004081382019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47279735768947336054254679 70919603653421004081382019)
            ·
              refine ⟨106379405480131506122073029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70919603653421004081382019 106379405480131506122073029)
              ·
                refine ⟨19946138527524657397888693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106379405480131506122073029 19946138527524657397888693)
                ·
                  refine ⟨1869950486955436631052065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19946138527524657397888693 1869950486955436631052065)
                  ·
                    refine ⟨1402462865216577473289049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1869950486955436631052065 1402462865216577473289049)
                    ·
                      refine ⟨1051847148912433104966787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1402462865216577473289049 1051847148912433104966787)
                      ·
                        rfl

theorem cell23_2048465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 5, 2, 2].length) (baseStart_2048465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048465 prefixEnd_2048465 := by exact prefixLift 2048465
  have htrace : WordTrace (prefixWord ++ tailWord_2048465) baseStart_2048465 baseEnd_2048465 := by
    simpa [prefixWord, tailWord_2048465, baseEnd_2048465] using wordTrace_append hprefix tailTrace_2048465
  have hstable : (prefixWord ++ tailWord_2048465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048465).length < 2 ^ (prefixWord ++ tailWord_2048465).sum := by decide
  have hdescent : baseEnd_2048465 < baseStart_2048465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048488 : List Nat := [2, 1, 4, 1, 1, 4, 2, 8]
def baseStart_2048488 : Nat := 118140960795 + 2048488 * 2 ^ 59
def prefixEnd_2048488 : Nat := 4983230072969 + 3 ^ 40 * 2048488 * 2
def baseEnd_2048488 : Nat := 38957739221018019073303

theorem tailTrace_2048488 : CollatzResearch.WordTrace tailWord_2048488 prefixEnd_2048488 38957739221018019073303 := by
  unfold tailWord_2048488
  simp only [CollatzResearch.WordTrace]
  refine ⟨37357247701342652371109059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49809663601790203161478745 37357247701342652371109059)
  ·
    refine ⟨56035871552013978556663589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37357247701342652371109059 56035871552013978556663589)
    ·
      refine ⟨10506725916002620979374423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56035871552013978556663589 10506725916002620979374423)
      ·
        refine ⟨15760088874003931469061635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10506725916002620979374423 15760088874003931469061635)
        ·
          refine ⟨23640133311005897203592453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15760088874003931469061635 23640133311005897203592453)
          ·
            refine ⟨4432524995813605725673585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23640133311005897203592453 4432524995813605725673585)
            ·
              refine ⟨3324393746860204294255189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4432524995813605725673585 3324393746860204294255189)
              ·
                refine ⟨38957739221018019073303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3324393746860204294255189 38957739221018019073303)
                ·
                  rfl

theorem cell23_2048488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 8].length) (baseStart_2048488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048488 prefixEnd_2048488 := by exact prefixLift 2048488
  have htrace : WordTrace (prefixWord ++ tailWord_2048488) baseStart_2048488 baseEnd_2048488 := by
    simpa [prefixWord, tailWord_2048488, baseEnd_2048488] using wordTrace_append hprefix tailTrace_2048488
  have hstable : (prefixWord ++ tailWord_2048488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048488).length < 2 ^ (prefixWord ++ tailWord_2048488).sum := by decide
  have hdescent : baseEnd_2048488 < baseStart_2048488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048491 : List Nat := [1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 6]
def baseStart_2048491 : Nat := 118140960795 + 2048491 * 2 ^ 59
def prefixEnd_2048491 : Nat := 4983230072969 + 3 ^ 40 * 2048491 * 2
def baseEnd_2048491 : Nat := 1051860499409450003241667

theorem tailTrace_2048491 : CollatzResearch.WordTrace tailWord_2048491 prefixEnd_2048491 1051860499409450003241667 := by
  unfold tailWord_2048491
  simp only [CollatzResearch.WordTrace]
  refine ⟨74714604821674436254577327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49809736547782957503051551 74714604821674436254577327)
  ·
    refine ⟨112071907232511654381865991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74714604821674436254577327 112071907232511654381865991)
    ·
      refine ⟨168107860848767481572798987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112071907232511654381865991 168107860848767481572798987)
      ·
        refine ⟨252161791273151222359198481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168107860848767481572798987 252161791273151222359198481)
        ·
          refine ⟨189121343454863416769398861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252161791273151222359198481 189121343454863416769398861)
          ·
            refine ⟨70920503795573781288524573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189121343454863416769398861 70920503795573781288524573)
            ·
              refine ⟨26595188923340167983196715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70920503795573781288524573 26595188923340167983196715)
              ·
                refine ⟨39892783385010251974795073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26595188923340167983196715 39892783385010251974795073)
                ·
                  refine ⟨29919587538757688981096305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39892783385010251974795073 29919587538757688981096305)
                  ·
                    refine ⟨22439690654068266735822229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29919587538757688981096305 22439690654068266735822229)
                    ·
                      refine ⟨1051860499409450003241667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22439690654068266735822229 1051860499409450003241667)
                      ·
                        rfl

theorem cell23_2048491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 6].length) (baseStart_2048491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048491 prefixEnd_2048491 := by exact prefixLift 2048491
  have htrace : WordTrace (prefixWord ++ tailWord_2048491) baseStart_2048491 baseEnd_2048491 := by
    simpa [prefixWord, tailWord_2048491, baseEnd_2048491] using wordTrace_append hprefix tailTrace_2048491
  have hstable : (prefixWord ++ tailWord_2048491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048491).length < 2 ^ (prefixWord ++ tailWord_2048491).sum := by decide
  have hdescent : baseEnd_2048491 < baseStart_2048491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048519 : List Nat := [1, 1, 4, 3, 3, 1, 3, 1, 1, 2, 3]
def baseStart_2048519 : Nat := 118140960795 + 2048519 * 2 ^ 59
def prefixEnd_2048519 : Nat := 4983230072969 + 3 ^ 40 * 2048519 * 2
def baseEnd_2048519 : Nat := 1051874876867775893691539

theorem tailTrace_2048519 : CollatzResearch.WordTrace tailWord_2048519 prefixEnd_2048519 1051874876867775893691539 := by
  unfold tailWord_2048519
  simp only [CollatzResearch.WordTrace]
  refine ⟨74715626065572997036596611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49810417377048664691064407 74715626065572997036596611)
  ·
    refine ⟨112073439098359495554894917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74715626065572997036596611 112073439098359495554894917)
    ·
      refine ⟨21013769830942405416542797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112073439098359495554894917 21013769830942405416542797)
      ·
        refine ⟨7880163686603402031203549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21013769830942405416542797 7880163686603402031203549)
        ·
          refine ⟨2955061382476275761701331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7880163686603402031203549 2955061382476275761701331)
          ·
            refine ⟨4432592073714413642551997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2955061382476275761701331 4432592073714413642551997)
            ·
              refine ⟨1662222027642905115956999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4432592073714413642551997 1662222027642905115956999)
              ·
                refine ⟨2493333041464357673935499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1662222027642905115956999 2493333041464357673935499)
                ·
                  refine ⟨3739999562196536510903249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2493333041464357673935499 3739999562196536510903249)
                  ·
                    refine ⟨2804999671647402383177437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3739999562196536510903249 2804999671647402383177437)
                    ·
                      refine ⟨1051874876867775893691539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2804999671647402383177437 1051874876867775893691539)
                      ·
                        rfl

theorem cell23_2048519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_2048519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048519 prefixEnd_2048519 := by exact prefixLift 2048519
  have htrace : WordTrace (prefixWord ++ tailWord_2048519) baseStart_2048519 baseEnd_2048519 := by
    simpa [prefixWord, tailWord_2048519, baseEnd_2048519] using wordTrace_append hprefix tailTrace_2048519
  have hstable : (prefixWord ++ tailWord_2048519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048519).length < 2 ^ (prefixWord ++ tailWord_2048519).sum := by decide
  have hdescent : baseEnd_2048519 < baseStart_2048519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048538 : List Nat := [3, 1, 1, 3, 1, 1, 3, 1, 2, 3, 4]
def baseStart_2048538 : Nat := 118140960795 + 2048538 * 2 ^ 59
def prefixEnd_2048538 : Nat := 4983230072969 + 3 ^ 40 * 2048538 * 2
def baseEnd_2048538 : Nat := 1051884633000211319353951

theorem tailTrace_2048538 : CollatzResearch.WordTrace tailWord_2048538 prefixEnd_2048538 1051884633000211319353951 := by
  unfold tailWord_2048538
  simp only [CollatzResearch.WordTrace]
  refine ⟨18679079763126040820384567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49810879368336108854358845 18679079763126040820384567)
  ·
    refine ⟨28018619644689061230576851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18679079763126040820384567 28018619644689061230576851)
    ·
      refine ⟨42027929467033591845865277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28018619644689061230576851 42027929467033591845865277)
      ·
        refine ⟨15760473550137596942199479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42027929467033591845865277 15760473550137596942199479)
        ·
          refine ⟨23640710325206395413299219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15760473550137596942199479 23640710325206395413299219)
          ·
            refine ⟨35461065487809593119948829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23640710325206395413299219 35461065487809593119948829)
            ·
              refine ⟨13297899557928597419980811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35461065487809593119948829 13297899557928597419980811)
              ·
                refine ⟨19946849336892896129971217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13297899557928597419980811 19946849336892896129971217)
                ·
                  refine ⟨14960137002669672097478413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19946849336892896129971217 14960137002669672097478413)
                  ·
                    refine ⟨5610051376001127036554405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14960137002669672097478413 5610051376001127036554405)
                    ·
                      refine ⟨1051884633000211319353951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5610051376001127036554405 1051884633000211319353951)
                      ·
                        rfl

theorem cell23_2048538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_2048538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048538 prefixEnd_2048538 := by exact prefixLift 2048538
  have htrace : WordTrace (prefixWord ++ tailWord_2048538) baseStart_2048538 baseEnd_2048538 := by
    simpa [prefixWord, tailWord_2048538, baseEnd_2048538] using wordTrace_append hprefix tailTrace_2048538
  have hstable : (prefixWord ++ tailWord_2048538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048538).length < 2 ^ (prefixWord ++ tailWord_2048538).sum := by decide
  have hdescent : baseEnd_2048538 < baseStart_2048538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048568 : List Nat := [2, 1, 2, 1, 4, 1, 1, 2, 1, 4, 4]
def baseStart_2048568 : Nat := 118140960795 + 2048568 * 2 ^ 59
def prefixEnd_2048568 : Nat := 4983230072969 + 3 ^ 40 * 2048568 * 2
def baseEnd_2048568 : Nat := 1051900037419846201978813

theorem tailTrace_2048568 : CollatzResearch.WordTrace tailWord_2048568 prefixEnd_2048568 1051900037419846201978813 := by
  unfold tailWord_2048568
  simp only [CollatzResearch.WordTrace]
  refine ⟨37358706621197739202565179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49811608828263652270086905 37358706621197739202565179)
  ·
    refine ⟨56038059931796608803847769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37358706621197739202565179 56038059931796608803847769)
    ·
      refine ⟨42028544948847456602885827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56038059931796608803847769 42028544948847456602885827)
      ·
        refine ⟨63042817423271184904328741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42028544948847456602885827 63042817423271184904328741)
        ·
          refine ⟨11820528266863347169561639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63042817423271184904328741 11820528266863347169561639)
          ·
            refine ⟨17730792400295020754342459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11820528266863347169561639 17730792400295020754342459)
            ·
              refine ⟨26596188600442531131513689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17730792400295020754342459 26596188600442531131513689)
              ·
                refine ⟨19947141450331898348635267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26596188600442531131513689 19947141450331898348635267)
                ·
                  refine ⟨29920712175497847522952901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19947141450331898348635267 29920712175497847522952901)
                  ·
                    refine ⟨5610133532905846410553669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29920712175497847522952901 5610133532905846410553669)
                    ·
                      refine ⟨1051900037419846201978813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5610133532905846410553669 1051900037419846201978813)
                      ·
                        rfl

theorem cell23_2048568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 1, 4, 4].length) (baseStart_2048568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048568 prefixEnd_2048568 := by exact prefixLift 2048568
  have htrace : WordTrace (prefixWord ++ tailWord_2048568) baseStart_2048568 baseEnd_2048568 := by
    simpa [prefixWord, tailWord_2048568, baseEnd_2048568] using wordTrace_append hprefix tailTrace_2048568
  have hstable : (prefixWord ++ tailWord_2048568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048568).length < 2 ^ (prefixWord ++ tailWord_2048568).sum := by decide
  have hdescent : baseEnd_2048568 < baseStart_2048568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048572 : List Nat := [2, 2, 2, 2, 3, 1, 2, 2, 1, 4, 2]
def baseStart_2048572 : Nat := 118140960795 + 2048572 * 2 ^ 59
def prefixEnd_2048572 : Nat := 4983230072969 + 3 ^ 40 * 2048572 * 2
def baseEnd_2048572 : Nat := 1051902091342464186328795

theorem tailTrace_2048572 : CollatzResearch.WordTrace tailWord_2048572 prefixEnd_2048572 1051902091342464186328795 := by
  unfold tailWord_2048572
  simp only [CollatzResearch.WordTrace]
  refine ⟨37358779567190493544137985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49811706089587324725517313 37358779567190493544137985)
  ·
    refine ⟨28019084675392870158103489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37358779567190493544137985 28019084675392870158103489)
    ·
      refine ⟨21014313506544652618577617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28019084675392870158103489 21014313506544652618577617)
      ·
        refine ⟨15760735129908489463933213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21014313506544652618577617 15760735129908489463933213)
        ·
          refine ⟨5910275673715683548974955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15760735129908489463933213 5910275673715683548974955)
          ·
            refine ⟨8865413510573525323462433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5910275673715683548974955 8865413510573525323462433)
            ·
              refine ⟨6649060132930143992596825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8865413510573525323462433 6649060132930143992596825)
              ·
                refine ⟨4986795099697607994447619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6649060132930143992596825 4986795099697607994447619)
                ·
                  refine ⟨7480192649546411991671429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4986795099697607994447619 7480192649546411991671429)
                  ·
                    refine ⟨1402536121789952248438393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7480192649546411991671429 1402536121789952248438393)
                    ·
                      refine ⟨1051902091342464186328795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1402536121789952248438393 1051902091342464186328795)
                      ·
                        rfl

theorem cell23_2048572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 1, 4, 2].length) (baseStart_2048572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048572 prefixEnd_2048572 := by exact prefixLift 2048572
  have htrace : WordTrace (prefixWord ++ tailWord_2048572) baseStart_2048572 baseEnd_2048572 := by
    simpa [prefixWord, tailWord_2048572, baseEnd_2048572] using wordTrace_append hprefix tailTrace_2048572
  have hstable : (prefixWord ++ tailWord_2048572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048572).length < 2 ^ (prefixWord ++ tailWord_2048572).sum := by decide
  have hdescent : baseEnd_2048572 < baseStart_2048572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048582 : List Nat := [6, 1, 1, 1, 2, 1, 1, 2, 2, 6]
def baseStart_2048582 : Nat := 118140960795 + 2048582 * 2 ^ 59
def prefixEnd_2048582 : Nat := 4983230072969 + 3 ^ 40 * 2048582 * 2
def baseEnd_2048582 : Nat := 350635742049669715734583

theorem tailTrace_2048582 : CollatzResearch.WordTrace tailWord_2048582 prefixEnd_2048582 350635742049669715734583 := by
  unfold tailWord_2048582
  simp only [CollatzResearch.WordTrace]
  refine ⟨2334935120760773712379375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 49811949242896505864093333 2334935120760773712379375)
  ·
    refine ⟨3502402681141160568569063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2334935120760773712379375 3502402681141160568569063)
    ·
      refine ⟨5253604021711740852853595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3502402681141160568569063 5253604021711740852853595)
      ·
        refine ⟨7880406032567611279280393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5253604021711740852853595 7880406032567611279280393)
        ·
          refine ⟨5910304524425708459460295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7880406032567611279280393 5910304524425708459460295)
          ·
            refine ⟨8865456786638562689190443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5910304524425708459460295 8865456786638562689190443)
            ·
              refine ⟨13298185179957844033785665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8865456786638562689190443 13298185179957844033785665)
              ·
                refine ⟨9973638884968383025339249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13298185179957844033785665 9973638884968383025339249)
                ·
                  refine ⟨7480229163726287269004437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9973638884968383025339249 7480229163726287269004437)
                  ·
                    refine ⟨350635742049669715734583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7480229163726287269004437 350635742049669715734583)
                    ·
                      rfl

theorem cell23_2048582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_2048582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048582 prefixEnd_2048582 := by exact prefixLift 2048582
  have htrace : WordTrace (prefixWord ++ tailWord_2048582) baseStart_2048582 baseEnd_2048582 := by
    simpa [prefixWord, tailWord_2048582, baseEnd_2048582] using wordTrace_append hprefix tailTrace_2048582
  have hstable : (prefixWord ++ tailWord_2048582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048582).length < 2 ^ (prefixWord ++ tailWord_2048582).sum := by decide
  have hdescent : baseEnd_2048582 < baseStart_2048582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048608 : List Nat := [2, 1, 1, 3, 2, 1, 3, 2, 1, 7]
def baseStart_2048608 : Nat := 118140960795 + 2048608 * 2 ^ 59
def prefixEnd_2048608 : Nat := 4983230072969 + 3 ^ 40 * 2048608 * 2
def baseEnd_2048608 : Nat := 350640192215342015159543

theorem tailTrace_2048608 : CollatzResearch.WordTrace tailWord_2048608 prefixEnd_2048608 350640192215342015159543 := by
  unfold tailWord_2048608
  simp only [CollatzResearch.WordTrace]
  refine ⟨37359436081125282618293239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49812581441500376824390985 37359436081125282618293239)
  ·
    refine ⟨56039154121687923927439859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37359436081125282618293239 56039154121687923927439859)
    ·
      refine ⟨84058731182531885891159789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56039154121687923927439859 84058731182531885891159789)
      ·
        refine ⟨31522024193449457209184921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84058731182531885891159789 31522024193449457209184921)
        ·
          refine ⟨23641518145087092906888691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31522024193449457209184921 23641518145087092906888691)
          ·
            refine ⟨35462277217630639360333037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23641518145087092906888691 35462277217630639360333037)
            ·
              refine ⟨13298353956611489760124889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35462277217630639360333037 13298353956611489760124889)
              ·
                refine ⟨9973765467458617320093667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13298353956611489760124889 9973765467458617320093667)
                ·
                  refine ⟨14960648201187925980140501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9973765467458617320093667 14960648201187925980140501)
                  ·
                    refine ⟨350640192215342015159543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14960648201187925980140501 350640192215342015159543)
                    ·
                      rfl

theorem cell23_2048608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 1, 7].length) (baseStart_2048608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048608 prefixEnd_2048608 := by exact prefixLift 2048608
  have htrace : WordTrace (prefixWord ++ tailWord_2048608) baseStart_2048608 baseEnd_2048608 := by
    simpa [prefixWord, tailWord_2048608, baseEnd_2048608] using wordTrace_append hprefix tailTrace_2048608
  have hstable : (prefixWord ++ tailWord_2048608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048608).length < 2 ^ (prefixWord ++ tailWord_2048608).sum := by decide
  have hdescent : baseEnd_2048608 < baseStart_2048608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048645 : List Nat := [1, 3, 1, 1, 4, 2, 1, 1, 4, 1, 4]
def baseStart_2048645 : Nat := 118140960795 + 2048645 * 2 ^ 59
def prefixEnd_2048645 : Nat := 4983230072969 + 3 ^ 40 * 2048645 * 2
def baseEnd_2048645 : Nat := 1051939575430242400715959

theorem tailTrace_2048645 : CollatzResearch.WordTrace tailWord_2048645 prefixEnd_2048645 1051939575430242400715959 := by
  unfold tailWord_2048645
  simp only [CollatzResearch.WordTrace]
  refine ⟨74720221663116520555683389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49813481108744347037122259 74720221663116520555683389)
  ·
    refine ⟨28020083123668695208381271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74720221663116520555683389 28020083123668695208381271)
    ·
      refine ⟨42030124685503042812571907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28020083123668695208381271 42030124685503042812571907)
      ·
        refine ⟨63045187028254564218857861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42030124685503042812571907 63045187028254564218857861)
        ·
          refine ⟨11820972567797730791035849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63045187028254564218857861 11820972567797730791035849)
          ·
            refine ⟨8865729425848298093276887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11820972567797730791035849 8865729425848298093276887)
            ·
              refine ⟨13298594138772447139915331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8865729425848298093276887 13298594138772447139915331)
              ·
                refine ⟨19947891208158670709872997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13298594138772447139915331 19947891208158670709872997)
                ·
                  refine ⟨3740229601529750758101187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19947891208158670709872997 3740229601529750758101187)
                  ·
                    refine ⟨5610344402294626137151781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3740229601529750758101187 5610344402294626137151781)
                    ·
                      refine ⟨1051939575430242400715959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5610344402294626137151781 1051939575430242400715959)
                      ·
                        rfl

theorem cell23_2048645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 4, 1, 4].length) (baseStart_2048645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048645 prefixEnd_2048645 := by exact prefixLift 2048645
  have htrace : WordTrace (prefixWord ++ tailWord_2048645) baseStart_2048645 baseEnd_2048645 := by
    simpa [prefixWord, tailWord_2048645, baseEnd_2048645] using wordTrace_append hprefix tailTrace_2048645
  have hstable : (prefixWord ++ tailWord_2048645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048645).length < 2 ^ (prefixWord ++ tailWord_2048645).sum := by decide
  have hdescent : baseEnd_2048645 < baseStart_2048645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048665 : List Nat := [1, 2, 1, 2, 1, 2, 3, 2, 4, 2, 3]
def baseStart_2048665 : Nat := 118140960795 + 2048665 * 2 ^ 59
def prefixEnd_2048665 : Nat := 4983230072969 + 3 ^ 40 * 2048665 * 2
def baseEnd_2048665 : Nat := 1051949845043332322465867

theorem tailTrace_2048665 : CollatzResearch.WordTrace tailWord_2048665 prefixEnd_2048665 1051949845043332322465867 := by
  unfold tailWord_2048665
  simp only [CollatzResearch.WordTrace]
  refine ⟨74720951123044063971411449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49813967415362709314274299 74720951123044063971411449)
  ·
    refine ⟨56040713342283047978558587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74720951123044063971411449 56040713342283047978558587)
    ·
      refine ⟨84061070013424571967837881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56040713342283047978558587 84061070013424571967837881)
      ·
        refine ⟨63045802510068428975878411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84061070013424571967837881 63045802510068428975878411)
        ·
          refine ⟨94568703765102643463817617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63045802510068428975878411 94568703765102643463817617)
          ·
            refine ⟨70926527823826982597863213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94568703765102643463817617 70926527823826982597863213)
            ·
              refine ⟨26597447933935118474198705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70926527823826982597863213 26597447933935118474198705)
              ·
                refine ⟨19948085950451338855649029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26597447933935118474198705 19948085950451338855649029)
                ·
                  refine ⟨3740266115709626035434193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19948085950451338855649029 3740266115709626035434193)
                  ·
                    refine ⟨2805199586782219526575645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3740266115709626035434193 2805199586782219526575645)
                    ·
                      refine ⟨1051949845043332322465867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2805199586782219526575645 1051949845043332322465867)
                      ·
                        rfl

theorem cell23_2048665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 4, 2, 3].length) (baseStart_2048665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048665 prefixEnd_2048665 := by exact prefixLift 2048665
  have htrace : WordTrace (prefixWord ++ tailWord_2048665) baseStart_2048665 baseEnd_2048665 := by
    simpa [prefixWord, tailWord_2048665, baseEnd_2048665] using wordTrace_append hprefix tailTrace_2048665
  have hstable : (prefixWord ++ tailWord_2048665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048665).length < 2 ^ (prefixWord ++ tailWord_2048665).sum := by decide
  have hdescent : baseEnd_2048665 < baseStart_2048665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048688 : List Nat := [2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 8]
def baseStart_2048688 : Nat := 118140960795 + 2048688 * 2 ^ 59
def prefixEnd_2048688 : Nat := 4983230072969 + 3 ^ 40 * 2048688 * 2
def baseEnd_2048688 : Nat := 1051961655098385732478261

theorem tailTrace_2048688 : CollatzResearch.WordTrace tailWord_2048688 prefixEnd_2048688 1051961655098385732478261 := by
  unfold tailWord_2048688
  simp only [CollatzResearch.WordTrace]
  refine ⟨37360895000980369449749359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49814526667973825932999145 37360895000980369449749359)
  ·
    refine ⟨56041342501470554174624039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37360895000980369449749359 56041342501470554174624039)
    ·
      refine ⟨84062013752205831261936059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56041342501470554174624039 84062013752205831261936059)
      ·
        refine ⟨126093020628308746892904089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84062013752205831261936059 126093020628308746892904089)
        ·
          refine ⟨94569765471231560169678067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126093020628308746892904089 94569765471231560169678067)
          ·
            refine ⟨141854648206847340254517101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94569765471231560169678067 141854648206847340254517101)
            ·
              refine ⟨53195493077567752595443913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141854648206847340254517101 53195493077567752595443913)
              ·
                refine ⟨39896619808175814446582935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53195493077567752595443913 39896619808175814446582935)
                ·
                  refine ⟨59844929712263721669874403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39896619808175814446582935 59844929712263721669874403)
                  ·
                    refine ⟨89767394568395582504811605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59844929712263721669874403 89767394568395582504811605)
                    ·
                      refine ⟨1051961655098385732478261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 89767394568395582504811605 1051961655098385732478261)
                      ·
                        rfl

theorem cell23_2048688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 8].length) (baseStart_2048688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048688 prefixEnd_2048688 := by exact prefixLift 2048688
  have htrace : WordTrace (prefixWord ++ tailWord_2048688) baseStart_2048688 baseEnd_2048688 := by
    simpa [prefixWord, tailWord_2048688, baseEnd_2048688] using wordTrace_append hprefix tailTrace_2048688
  have hstable : (prefixWord ++ tailWord_2048688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048688).length < 2 ^ (prefixWord ++ tailWord_2048688).sum := by decide
  have hdescent : baseEnd_2048688 < baseStart_2048688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048702 : List Nat := [4, 2, 1, 1, 2, 1, 4, 2, 6]
def baseStart_2048702 : Nat := 118140960795 + 2048702 * 2 ^ 59
def prefixEnd_2048702 : Nat := 4983230072969 + 3 ^ 40 * 2048702 * 2
def baseEnd_2048702 : Nat := 116885427091949853078133

theorem tailTrace_2048702 : CollatzResearch.WordTrace tailWord_2048702 prefixEnd_2048702 116885427091949853078133 := by
  unfold tailWord_2048702
  simp only [CollatzResearch.WordTrace]
  refine ⟨9340287577988752411313545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49814867082606679527005573 9340287577988752411313545)
  ·
    refine ⟨7005215683491564308485159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9340287577988752411313545 7005215683491564308485159)
    ·
      refine ⟨10507823525237346462727739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7005215683491564308485159 10507823525237346462727739)
      ·
        refine ⟨15761735287856019694091609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10507823525237346462727739 15761735287856019694091609)
        ·
          refine ⟨11821301465892014770568707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15761735287856019694091609 11821301465892014770568707)
          ·
            refine ⟨17731952198838022155853061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11821301465892014770568707 17731952198838022155853061)
            ·
              refine ⟨3324741037282129154222449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17731952198838022155853061 3324741037282129154222449)
              ·
                refine ⟨2493555777961596865666837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3324741037282129154222449 2493555777961596865666837)
                ·
                  refine ⟨116885427091949853078133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2493555777961596865666837 116885427091949853078133)
                  ·
                    rfl

theorem cell23_2048702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 2, 6].length) (baseStart_2048702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048702 prefixEnd_2048702 := by exact prefixLift 2048702
  have htrace : WordTrace (prefixWord ++ tailWord_2048702) baseStart_2048702 baseEnd_2048702 := by
    simpa [prefixWord, tailWord_2048702, baseEnd_2048702] using wordTrace_append hprefix tailTrace_2048702
  have hstable : (prefixWord ++ tailWord_2048702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048702).length < 2 ^ (prefixWord ++ tailWord_2048702).sum := by decide
  have hdescent : baseEnd_2048702 < baseStart_2048702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048739 : List Nat := [1, 1, 1, 7, 1, 2, 1, 1, 1, 5, 2]
def baseStart_2048739 : Nat := 118140960795 + 2048739 * 2 ^ 59
def prefixEnd_2048739 : Nat := 4983230072969 + 3 ^ 40 * 2048739 * 2
def baseEnd_2048739 : Nat := 1051987842611765032940527

theorem tailTrace_2048739 : CollatzResearch.WordTrace tailWord_2048739 prefixEnd_2048739 1051987842611765032940527 := by
  unfold tailWord_2048739
  simp only [CollatzResearch.WordTrace]
  refine ⟨74723650124775974609605271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49815766749850649739736847 74723650124775974609605271)
  ·
    refine ⟨112085475187163961914407907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74723650124775974609605271 112085475187163961914407907)
    ·
      refine ⟨168128212780745942871611861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112085475187163961914407907 168128212780745942871611861)
      ·
        refine ⟨3940504987048733036053403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 168128212780745942871611861 3940504987048733036053403)
        ·
          refine ⟨5910757480573099554080105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3940504987048733036053403 5910757480573099554080105)
          ·
            refine ⟨4433068110429824665560079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5910757480573099554080105 4433068110429824665560079)
            ·
              refine ⟨6649602165644736998340119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4433068110429824665560079 6649602165644736998340119)
              ·
                refine ⟨9974403248467105497510179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6649602165644736998340119 9974403248467105497510179)
                ·
                  refine ⟨14961604872700658246265269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9974403248467105497510179 14961604872700658246265269)
                  ·
                    refine ⟨1402650456815686710587369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14961604872700658246265269 1402650456815686710587369)
                    ·
                      refine ⟨1051987842611765032940527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1402650456815686710587369 1051987842611765032940527)
                      ·
                        rfl

theorem cell23_2048739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_2048739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048739 prefixEnd_2048739 := by exact prefixLift 2048739
  have htrace : WordTrace (prefixWord ++ tailWord_2048739) baseStart_2048739 baseEnd_2048739 := by
    simpa [prefixWord, tailWord_2048739, baseEnd_2048739] using wordTrace_append hprefix tailTrace_2048739
  have hstable : (prefixWord ++ tailWord_2048739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048739).length < 2 ^ (prefixWord ++ tailWord_2048739).sum := by decide
  have hdescent : baseEnd_2048739 < baseStart_2048739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048745 : List Nat := [1, 2, 1, 1, 1, 2, 6, 2, 1, 6]
def baseStart_2048745 : Nat := 118140960795 + 2048745 * 2 ^ 59
def prefixEnd_2048745 : Nat := 4983230072969 + 3 ^ 40 * 2048745 * 2
def baseEnd_2048745 : Nat := 350663641165230669821833

theorem tailTrace_2048745 : CollatzResearch.WordTrace tailWord_2048745 prefixEnd_2048745 350663641165230669821833 := by
  unfold tailWord_2048745
  simp only [CollatzResearch.WordTrace]
  refine ⟨74723868962754237634323689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49815912641836158422882459 74723868962754237634323689)
  ·
    refine ⟨56042901722065678225742767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74723868962754237634323689 56042901722065678225742767)
    ·
      refine ⟨84064352583098517338614151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56042901722065678225742767 84064352583098517338614151)
      ·
        refine ⟨126096528874647776007921227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84064352583098517338614151 126096528874647776007921227)
        ·
          refine ⟨189144793311971664011881841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126096528874647776007921227 189144793311971664011881841)
          ·
            refine ⟨141858594983978748008911381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189144793311971664011881841 141858594983978748008911381)
            ·
              refine ⟨6649621639874003812917721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 141858594983978748008911381 6649621639874003812917721)
              ·
                refine ⟨4987216229905502859688291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6649621639874003812917721 4987216229905502859688291)
                ·
                  refine ⟨7480824344858254289532437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4987216229905502859688291 7480824344858254289532437)
                  ·
                    refine ⟨350663641165230669821833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7480824344858254289532437 350663641165230669821833)
                    ·
                      rfl

theorem cell23_2048745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 6].length) (baseStart_2048745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048745 prefixEnd_2048745 := by exact prefixLift 2048745
  have htrace : WordTrace (prefixWord ++ tailWord_2048745) baseStart_2048745 baseEnd_2048745 := by
    simpa [prefixWord, tailWord_2048745, baseEnd_2048745] using wordTrace_append hprefix tailTrace_2048745
  have hstable : (prefixWord ++ tailWord_2048745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048745).length < 2 ^ (prefixWord ++ tailWord_2048745).sum := by decide
  have hdescent : baseEnd_2048745 < baseStart_2048745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048752 : List Nat := [2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 4]
def baseStart_2048752 : Nat := 118140960795 + 2048752 * 2 ^ 59
def prefixEnd_2048752 : Nat := 4983230072969 + 3 ^ 40 * 2048752 * 2
def baseEnd_2048752 : Nat := 1051994517860273482077967

theorem tailTrace_2048752 : CollatzResearch.WordTrace tailWord_2048752 prefixEnd_2048752 1051994517860273482077967 := by
  unfold tailWord_2048752
  simp only [CollatzResearch.WordTrace]
  refine ⟨37362062136864438914914255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49816082849152585219885673 37362062136864438914914255)
  ·
    refine ⟨56043093205296658372371383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37362062136864438914914255 56043093205296658372371383)
    ·
      refine ⟨84064639807944987558557075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56043093205296658372371383 84064639807944987558557075)
      ·
        refine ⟨126096959711917481337835613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84064639807944987558557075 126096959711917481337835613)
        ·
          refine ⟨47286359891969055501688355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126096959711917481337835613 47286359891969055501688355)
          ·
            refine ⟨70929539837953583252532533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47286359891969055501688355 70929539837953583252532533)
            ·
              refine ⟨6649644359808148429924925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70929539837953583252532533 6649644359808148429924925)
              ·
                refine ⟨2493616634928055661221847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6649644359808148429924925 2493616634928055661221847)
                ·
                  refine ⟨3740424952392083491832771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2493616634928055661221847 3740424952392083491832771)
                  ·
                    refine ⟨5610637428588125237749157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3740424952392083491832771 5610637428588125237749157)
                    ·
                      refine ⟨1051994517860273482077967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5610637428588125237749157 1051994517860273482077967)
                      ·
                        rfl

theorem cell23_2048752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 4].length) (baseStart_2048752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048752 prefixEnd_2048752 := by exact prefixLift 2048752
  have htrace : WordTrace (prefixWord ++ tailWord_2048752) baseStart_2048752 baseEnd_2048752 := by
    simpa [prefixWord, tailWord_2048752, baseEnd_2048752] using wordTrace_append hprefix tailTrace_2048752
  have hstable : (prefixWord ++ tailWord_2048752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048752).length < 2 ^ (prefixWord ++ tailWord_2048752).sum := by decide
  have hdescent : baseEnd_2048752 < baseStart_2048752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048755 : List Nat := [1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 5]
def baseStart_2048755 : Nat := 118140960795 + 2048755 * 2 ^ 59
def prefixEnd_2048755 : Nat := 4983230072969 + 3 ^ 40 * 2048755 * 2
def baseEnd_2048755 : Nat := 1051996058302236970340453

theorem tailTrace_2048755 : CollatzResearch.WordTrace tailWord_2048755 prefixEnd_2048755 1051996058302236970340453 := by
  unfold tailWord_2048755
  simp only [CollatzResearch.WordTrace]
  refine ⟨74724233692718009342187719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49816155795145339561458479 74724233692718009342187719)
  ·
    refine ⟨112086350539077014013281579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74724233692718009342187719 112086350539077014013281579)
    ·
      refine ⟨168129525808615521019922369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112086350539077014013281579 168129525808615521019922369)
      ·
        refine ⟨126097144356461640764941777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168129525808615521019922369 126097144356461640764941777)
        ·
          refine ⟨94572858267346230573706333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126097144356461640764941777 94572858267346230573706333)
          ·
            refine ⟨35464821850254836465139875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94572858267346230573706333 35464821850254836465139875)
            ·
              refine ⟨53197232775382254697709813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35464821850254836465139875 53197232775382254697709813)
              ·
                refine ⟨4987240572692086377910295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53197232775382254697709813 4987240572692086377910295)
                ·
                  refine ⟨7480860859038129566865443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4987240572692086377910295 7480860859038129566865443)
                  ·
                    refine ⟨11221291288557194350298165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7480860859038129566865443 11221291288557194350298165)
                    ·
                      refine ⟨1051996058302236970340453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11221291288557194350298165 1051996058302236970340453)
                      ·
                        rfl

theorem cell23_2048755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 5].length) (baseStart_2048755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048755 prefixEnd_2048755 := by exact prefixLift 2048755
  have htrace : WordTrace (prefixWord ++ tailWord_2048755) baseStart_2048755 baseEnd_2048755 := by
    simpa [prefixWord, tailWord_2048755, baseEnd_2048755] using wordTrace_append hprefix tailTrace_2048755
  have hstable : (prefixWord ++ tailWord_2048755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048755).length < 2 ^ (prefixWord ++ tailWord_2048755).sum := by decide
  have hdescent : baseEnd_2048755 < baseStart_2048755 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048765 : List Nat := [1, 4, 1, 1, 1, 1, 4, 2, 1, 1, 6]
def baseStart_2048765 : Nat := 118140960795 + 2048765 * 2 ^ 59
def prefixEnd_2048765 : Nat := 4983230072969 + 3 ^ 40 * 2048765 * 2
def baseEnd_2048765 : Nat := 1052001193108781931215407

theorem tailTrace_2048765 : CollatzResearch.WordTrace tailWord_2048765 prefixEnd_2048765 1052001193108781931215407 := by
  unfold tailWord_2048765
  simp only [CollatzResearch.WordTrace]
  refine ⟨74724598422681781050051749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49816398948454520700034499 74724598422681781050051749)
  ·
    refine ⟨14010862204252833946884703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74724598422681781050051749 14010862204252833946884703)
    ·
      refine ⟨21016293306379250920327055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14010862204252833946884703 21016293306379250920327055)
      ·
        refine ⟨31524439959568876380490583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21016293306379250920327055 31524439959568876380490583)
        ·
          refine ⟨47286659939353314570735875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31524439959568876380490583 47286659939353314570735875)
          ·
            refine ⟨70929989909029971856103813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47286659939353314570735875 70929989909029971856103813)
            ·
              refine ⟨13299373107943119723019465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70929989909029971856103813 13299373107943119723019465)
              ·
                refine ⟨9974529830957339792264599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13299373107943119723019465 9974529830957339792264599)
                ·
                  refine ⟨14961794746436009688396899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9974529830957339792264599 14961794746436009688396899)
                  ·
                    refine ⟨22442692119654014532595349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14961794746436009688396899 22442692119654014532595349)
                    ·
                      refine ⟨1052001193108781931215407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22442692119654014532595349 1052001193108781931215407)
                      ·
                        rfl

theorem cell23_2048765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_2048765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048765 prefixEnd_2048765 := by exact prefixLift 2048765
  have htrace : WordTrace (prefixWord ++ tailWord_2048765) baseStart_2048765 baseEnd_2048765 := by
    simpa [prefixWord, tailWord_2048765, baseEnd_2048765] using wordTrace_append hprefix tailTrace_2048765
  have hstable : (prefixWord ++ tailWord_2048765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048765).length < 2 ^ (prefixWord ++ tailWord_2048765).sum := by decide
  have hdescent : baseEnd_2048765 < baseStart_2048765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048772 : List Nat := [2, 3, 2, 2, 1, 1, 3, 2, 1, 1, 5]
def baseStart_2048772 : Nat := 118140960795 + 2048772 * 2 ^ 59
def prefixEnd_2048772 : Nat := 4983230072969 + 3 ^ 40 * 2048772 * 2
def baseEnd_2048772 : Nat := 1052004787473363403827875

theorem tailTrace_2048772 : CollatzResearch.WordTrace tailWord_2048772 prefixEnd_2048772 1052004787473363403827875 := by
  unfold tailWord_2048772
  simp only [CollatzResearch.WordTrace]
  refine ⟨37362426866828210622778285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49816569155770947497037713 37362426866828210622778285)
  ·
    refine ⟨14010910075060578983541857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37362426866828210622778285 14010910075060578983541857)
    ·
      refine ⟨10508182556295434237656393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14010910075060578983541857 10508182556295434237656393)
      ·
        refine ⟨7881136917221575678242295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10508182556295434237656393 7881136917221575678242295)
        ·
          refine ⟨11821705375832363517363443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7881136917221575678242295 11821705375832363517363443)
          ·
            refine ⟨17732558063748545276045165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11821705375832363517363443 17732558063748545276045165)
            ·
              refine ⟨6649709273905704478516937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17732558063748545276045165 6649709273905704478516937)
              ·
                refine ⟨4987281955429278358887703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6649709273905704478516937 4987281955429278358887703)
                ·
                  refine ⟨7480922933143917538331555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4987281955429278358887703 7480922933143917538331555)
                  ·
                    refine ⟨11221384399715876307497333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7480922933143917538331555 11221384399715876307497333)
                    ·
                      refine ⟨1052004787473363403827875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11221384399715876307497333 1052004787473363403827875)
                      ·
                        rfl

theorem cell23_2048772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_2048772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048772 prefixEnd_2048772 := by exact prefixLift 2048772
  have htrace : WordTrace (prefixWord ++ tailWord_2048772) baseStart_2048772 baseEnd_2048772 := by
    simpa [prefixWord, tailWord_2048772, baseEnd_2048772] using wordTrace_append hprefix tailTrace_2048772
  have hstable : (prefixWord ++ tailWord_2048772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048772).length < 2 ^ (prefixWord ++ tailWord_2048772).sum := by decide
  have hdescent : baseEnd_2048772 < baseStart_2048772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048789 : List Nat := [1, 3, 2, 1, 2, 2, 4, 2, 1, 2, 3]
def baseStart_2048789 : Nat := 118140960795 + 2048789 * 2 ^ 59
def prefixEnd_2048789 : Nat := 4983230072969 + 3 ^ 40 * 2048789 * 2
def baseEnd_2048789 : Nat := 1052013516644489837315297

theorem tailTrace_2048789 : CollatzResearch.WordTrace tailWord_2048789 prefixEnd_2048789 1052013516644489837315297 := by
  unfold tailWord_2048789
  simp only [CollatzResearch.WordTrace]
  refine ⟨74725473774594833148925421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49816982516396555432616947 74725473774594833148925421)
  ·
    refine ⟨28022052665473062430847033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74725473774594833148925421 28022052665473062430847033)
    ·
      refine ⟨21016539499104796823135275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28022052665473062430847033 21016539499104796823135275)
      ·
        refine ⟨31524809248657195234702913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21016539499104796823135275 31524809248657195234702913)
        ·
          refine ⟨23643606936492896426027185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31524809248657195234702913 23643606936492896426027185)
          ·
            refine ⟨17732705202369672319520389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23643606936492896426027185 17732705202369672319520389)
            ·
              refine ⟨3324882225444313559910073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17732705202369672319520389 3324882225444313559910073)
              ·
                refine ⟨2493661669083235169932555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3324882225444313559910073 2493661669083235169932555)
                ·
                  refine ⟨3740492503624852754898833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2493661669083235169932555 3740492503624852754898833)
                  ·
                    refine ⟨2805369377718639566174125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3740492503624852754898833 2805369377718639566174125)
                    ·
                      refine ⟨1052013516644489837315297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2805369377718639566174125 1052013516644489837315297)
                      ·
                        rfl

theorem cell23_2048789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 2, 1, 2, 3].length) (baseStart_2048789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048789 prefixEnd_2048789 := by exact prefixLift 2048789
  have htrace : WordTrace (prefixWord ++ tailWord_2048789) baseStart_2048789 baseEnd_2048789 := by
    simpa [prefixWord, tailWord_2048789, baseEnd_2048789] using wordTrace_append hprefix tailTrace_2048789
  have hstable : (prefixWord ++ tailWord_2048789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048789).length < 2 ^ (prefixWord ++ tailWord_2048789).sum := by decide
  have hdescent : baseEnd_2048789 < baseStart_2048789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048797 : List Nat := [1, 4, 2, 4, 2, 1, 1, 3, 1, 1, 3]
def baseStart_2048797 : Nat := 118140960795 + 2048797 * 2 ^ 59
def prefixEnd_2048797 : Nat := 4983230072969 + 3 ^ 40 * 2048797 * 2
def baseEnd_2048797 : Nat := 1052017624489725806015261

theorem tailTrace_2048797 : CollatzResearch.WordTrace tailWord_2048797 prefixEnd_2048797 1052017624489725806015261 := by
  unfold tailWord_2048797
  simp only [CollatzResearch.WordTrace]
  refine ⟨74725765558565850515216645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49817177039043900343477763 74725765558565850515216645)
  ·
    refine ⟨14011081042231096971603121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74725765558565850515216645 14011081042231096971603121)
    ·
      refine ⟨10508310781673322728702341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14011081042231096971603121 10508310781673322728702341)
      ·
        refine ⟨1970308271563748011631689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10508310781673322728702341 1970308271563748011631689)
        ·
          refine ⟨1477731203672811008723767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1970308271563748011631689 1477731203672811008723767)
          ·
            refine ⟨2216596805509216513085651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1477731203672811008723767 2216596805509216513085651)
            ·
              refine ⟨3324895208263824769628477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2216596805509216513085651 3324895208263824769628477)
              ·
                refine ⟨1246835703098934288610679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3324895208263824769628477 1246835703098934288610679)
                ·
                  refine ⟨1870253554648401432916019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1246835703098934288610679 1870253554648401432916019)
                  ·
                    refine ⟨2805380331972602149374029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1870253554648401432916019 2805380331972602149374029)
                    ·
                      refine ⟨1052017624489725806015261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2805380331972602149374029 1052017624489725806015261)
                      ·
                        rfl

theorem cell23_2048797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_2048797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048797 prefixEnd_2048797 := by exact prefixLift 2048797
  have htrace : WordTrace (prefixWord ++ tailWord_2048797) baseStart_2048797 baseEnd_2048797 := by
    simpa [prefixWord, tailWord_2048797, baseEnd_2048797] using wordTrace_append hprefix tailTrace_2048797
  have hstable : (prefixWord ++ tailWord_2048797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048797).length < 2 ^ (prefixWord ++ tailWord_2048797).sum := by decide
  have hdescent : baseEnd_2048797 < baseStart_2048797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048819 : List Nat := [1, 1, 1, 2, 6, 1, 2, 1, 4, 1, 3]
def baseStart_2048819 : Nat := 118140960795 + 2048819 * 2 ^ 59
def prefixEnd_2048819 : Nat := 4983230072969 + 3 ^ 40 * 2048819 * 2
def baseEnd_2048819 : Nat := 1052028921064124719940159

theorem tailTrace_2048819 : CollatzResearch.WordTrace tailWord_2048819 prefixEnd_2048819 1052028921064124719940159 := by
  unfold tailWord_2048819
  simp only [CollatzResearch.WordTrace]
  refine ⟨74726567964486148272517511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49817711976324098848345007 74726567964486148272517511)
  ·
    refine ⟨112089851946729222408776267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74726567964486148272517511 112089851946729222408776267)
    ·
      refine ⟨168134777920093833613164401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112089851946729222408776267 168134777920093833613164401)
      ·
        refine ⟨126101083440070375209873301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168134777920093833613164401 126101083440070375209873301)
        ·
          refine ⟨5910988286253298837962811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 126101083440070375209873301 5910988286253298837962811)
          ·
            refine ⟨8866482429379948256944217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5910988286253298837962811 8866482429379948256944217)
            ·
              refine ⟨6649861822034961192708163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8866482429379948256944217 6649861822034961192708163)
              ·
                refine ⟨9974792733052441789062245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6649861822034961192708163 9974792733052441789062245)
                ·
                  refine ⟨1870273637447332835449171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9974792733052441789062245 1870273637447332835449171)
                  ·
                    refine ⟨2805410456170999253173757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1870273637447332835449171 2805410456170999253173757)
                    ·
                      refine ⟨1052028921064124719940159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2805410456170999253173757 1052028921064124719940159)
                      ·
                        rfl

theorem cell23_2048819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 4, 1, 3].length) (baseStart_2048819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048819 prefixEnd_2048819 := by exact prefixLift 2048819
  have htrace : WordTrace (prefixWord ++ tailWord_2048819) baseStart_2048819 baseEnd_2048819 := by
    simpa [prefixWord, tailWord_2048819, baseEnd_2048819] using wordTrace_append hprefix tailTrace_2048819
  have hstable : (prefixWord ++ tailWord_2048819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048819).length < 2 ^ (prefixWord ++ tailWord_2048819).sum := by decide
  have hdescent : baseEnd_2048819 < baseStart_2048819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048820 : List Nat := [2, 5, 1, 1, 3, 2, 1, 1, 3, 2, 2]
def baseStart_2048820 : Nat := 118140960795 + 2048820 * 2 ^ 59
def prefixEnd_2048820 : Nat := 4983230072969 + 3 ^ 40 * 2048820 * 2
def baseEnd_2048820 : Nat := 1052029434544779216027655

theorem tailTrace_2048820 : CollatzResearch.WordTrace tailWord_2048820 prefixEnd_2048820 1052029434544779216027655 := by
  unfold tailWord_2048820
  simp only [CollatzResearch.WordTrace]
  refine ⟨37363302218741262721651957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49817736291655016962202609 37363302218741262721651957)
  ·
    refine ⟨3502809583006993380154871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37363302218741262721651957 3502809583006993380154871)
    ·
      refine ⟨5254214374510490070232307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3502809583006993380154871 5254214374510490070232307)
      ·
        refine ⟨7881321561765735105348461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5254214374510490070232307 7881321561765735105348461)
        ·
          refine ⟨2955495585662150664505673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7881321561765735105348461 2955495585662150664505673)
          ·
            refine ⟨2216621689246612998379255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2955495585662150664505673 2216621689246612998379255)
            ·
              refine ⟨3324932533869919497568883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2216621689246612998379255 3324932533869919497568883)
              ·
                refine ⟨4987398800804879246353325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3324932533869919497568883 4987398800804879246353325)
                ·
                  refine ⟨1870274550301829717382497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4987398800804879246353325 1870274550301829717382497)
                  ·
                    refine ⟨1402705912726372288036873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1870274550301829717382497 1402705912726372288036873)
                    ·
                      refine ⟨1052029434544779216027655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1402705912726372288036873 1052029434544779216027655)
                      ·
                        rfl

theorem cell23_2048820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_2048820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048820 prefixEnd_2048820 := by exact prefixLift 2048820
  have htrace : WordTrace (prefixWord ++ tailWord_2048820) baseStart_2048820 baseEnd_2048820 := by
    simpa [prefixWord, tailWord_2048820, baseEnd_2048820] using wordTrace_append hprefix tailTrace_2048820
  have hstable : (prefixWord ++ tailWord_2048820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048820).length < 2 ^ (prefixWord ++ tailWord_2048820).sum := by decide
  have hdescent : baseEnd_2048820 < baseStart_2048820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048830 : List Nat := [4, 2, 1, 2, 4, 1, 2, 1, 2, 4]
def baseStart_2048830 : Nat := 118140960795 + 2048830 * 2 ^ 59
def prefixEnd_2048830 : Nat := 4983230072969 + 3 ^ 40 * 2048830 * 2
def baseEnd_2048830 : Nat := 350678189783774725634203

theorem tailTrace_2048830 : CollatzResearch.WordTrace tailWord_2048830 prefixEnd_2048830 350678189783774725634203 := by
  unfold tailWord_2048830
  simp only [CollatzResearch.WordTrace]
  refine ⟨9340871145930787143895993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49817979444964198100778629 9340871145930787143895993)
  ·
    refine ⟨7005653359448090357921995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9340871145930787143895993 7005653359448090357921995)
    ·
      refine ⟨10508480039172135536882993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7005653359448090357921995 10508480039172135536882993)
      ·
        refine ⟨7881360029379101652662245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10508480039172135536882993 7881360029379101652662245)
        ·
          refine ⟨1477755005508581559874171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7881360029379101652662245 1477755005508581559874171)
          ·
            refine ⟨2216632508262872339811257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1477755005508581559874171 2216632508262872339811257)
            ·
              refine ⟨1662474381197154254858443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2216632508262872339811257 1662474381197154254858443)
              ·
                refine ⟨2493711571795731382287665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1662474381197154254858443 2493711571795731382287665)
                ·
                  refine ⟨1870283678846798536715749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2493711571795731382287665 1870283678846798536715749)
                  ·
                    refine ⟨350678189783774725634203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1870283678846798536715749 350678189783774725634203)
                    ·
                      rfl

theorem cell23_2048830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_2048830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048830 prefixEnd_2048830 := by exact prefixLift 2048830
  have htrace : WordTrace (prefixWord ++ tailWord_2048830) baseStart_2048830 baseEnd_2048830 := by
    simpa [prefixWord, tailWord_2048830, baseEnd_2048830] using wordTrace_append hprefix tailTrace_2048830
  have hstable : (prefixWord ++ tailWord_2048830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048830).length < 2 ^ (prefixWord ++ tailWord_2048830).sum := by decide
  have hdescent : baseEnd_2048830 < baseStart_2048830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048835 : List Nat := [1, 1, 1, 3, 1, 4, 2, 1, 1, 8]
def baseStart_2048835 : Nat := 118140960795 + 2048835 * 2 ^ 59
def prefixEnd_2048835 : Nat := 4983230072969 + 3 ^ 40 * 2048835 * 2
def baseEnd_2048835 : Nat := 350679045584865552446695

theorem tailTrace_2048835 : CollatzResearch.WordTrace tailWord_2048835 prefixEnd_2048835 350679045584865552446695 := by
  unfold tailWord_2048835
  simp only [CollatzResearch.WordTrace]
  refine ⟨74727151532428183005099959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49818101021618788670066639 74727151532428183005099959)
  ·
    refine ⟨112090727298642274507649939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74727151532428183005099959 112090727298642274507649939)
    ·
      refine ⟨168136090947963411761474909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112090727298642274507649939 168136090947963411761474909)
      ·
        refine ⟨63051034105486279410553091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168136090947963411761474909 63051034105486279410553091)
        ·
          refine ⟨94576551158229419115829637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63051034105486279410553091 94576551158229419115829637)
          ·
            refine ⟨17733103342168016084218057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94576551158229419115829637 17733103342168016084218057)
            ·
              refine ⟨13299827506626012063163543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17733103342168016084218057 13299827506626012063163543)
              ·
                refine ⟨19949741259939018094745315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13299827506626012063163543 19949741259939018094745315)
                ·
                  refine ⟨29924611889908527142117973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19949741259939018094745315 29924611889908527142117973)
                  ·
                    refine ⟨350679045584865552446695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 29924611889908527142117973 350679045584865552446695)
                    ·
                      rfl

theorem cell23_2048835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 8].length) (baseStart_2048835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048835 prefixEnd_2048835 := by exact prefixLift 2048835
  have htrace : WordTrace (prefixWord ++ tailWord_2048835) baseStart_2048835 baseEnd_2048835 := by
    simpa [prefixWord, tailWord_2048835, baseEnd_2048835] using wordTrace_append hprefix tailTrace_2048835
  have hstable : (prefixWord ++ tailWord_2048835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048835).length < 2 ^ (prefixWord ++ tailWord_2048835).sum := by decide
  have hdescent : baseEnd_2048835 < baseStart_2048835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048865 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 11]
def baseStart_2048865 : Nat := 118140960795 + 2048865 * 2 ^ 59
def prefixEnd_2048865 : Nat := 4983230072969 + 3 ^ 40 * 2048865 * 2
def baseEnd_2048865 : Nat := 116894726797136837773883

theorem tailTrace_2048865 : CollatzResearch.WordTrace tailWord_2048865 prefixEnd_2048865 116894726797136837773883 := by
  unfold tailWord_2048865
  simp only [CollatzResearch.WordTrace]
  refine ⟨74728245722319498128692049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49818830481546332085794699 74728245722319498128692049)
  ·
    refine ⟨56046184291739623596519037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74728245722319498128692049 56046184291739623596519037)
    ·
      refine ⟨21017319109402358848694639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56046184291739623596519037 21017319109402358848694639)
      ·
        refine ⟨31525978664103538273041959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21017319109402358848694639 31525978664103538273041959)
        ·
          refine ⟨47288967996155307409562939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31525978664103538273041959 47288967996155307409562939)
          ·
            refine ⟨70933451994232961114344409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47288967996155307409562939 70933451994232961114344409)
            ·
              refine ⟨53200088995674720835758307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70933451994232961114344409 53200088995674720835758307)
              ·
                refine ⟨79800133493512081253637461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53200088995674720835758307 79800133493512081253637461)
                ·
                  refine ⟨116894726797136837773883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 79800133493512081253637461 116894726797136837773883)
                  ·
                    rfl

theorem cell23_2048865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 11].length) (baseStart_2048865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048865 prefixEnd_2048865 := by exact prefixLift 2048865
  have htrace : WordTrace (prefixWord ++ tailWord_2048865) baseStart_2048865 baseEnd_2048865 := by
    simpa [prefixWord, tailWord_2048865, baseEnd_2048865] using wordTrace_append hprefix tailTrace_2048865
  have hstable : (prefixWord ++ tailWord_2048865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048865).length < 2 ^ (prefixWord ++ tailWord_2048865).sum := by decide
  have hdescent : baseEnd_2048865 < baseStart_2048865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048875 : List Nat := [1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 7]
def baseStart_2048875 : Nat := 118140960795 + 2048875 * 2 ^ 59
def prefixEnd_2048875 : Nat := 4983230072969 + 3 ^ 40 * 2048875 * 2
def baseEnd_2048875 : Nat := 1052057675980776500839901

theorem tailTrace_2048875 : CollatzResearch.WordTrace tailWord_2048875 prefixEnd_2048875 1052057675980776500839901 := by
  unfold tailWord_2048875
  simp only [CollatzResearch.WordTrace]
  refine ⟨74728610452283269836556079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49819073634855513224370719 74728610452283269836556079)
  ·
    refine ⟨112092915678424904754834119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74728610452283269836556079 112092915678424904754834119)
    ·
      refine ⟨168139373517637357132251179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112092915678424904754834119 168139373517637357132251179)
      ·
        refine ⟨252209060276456035698376769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168139373517637357132251179 252209060276456035698376769)
        ·
          refine ⟨189156795207342026773782577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252209060276456035698376769 189156795207342026773782577)
          ·
            refine ⟨141867596405506520080336933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189156795207342026773782577 141867596405506520080336933)
            ·
              refine ⟨26600174326032472515063175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141867596405506520080336933 26600174326032472515063175)
              ·
                refine ⟨39900261489048708772594763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26600174326032472515063175 39900261489048708772594763)
                ·
                  refine ⟨59850392233573063158892145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39900261489048708772594763 59850392233573063158892145)
                  ·
                    refine ⟨44887794175179797369169109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59850392233573063158892145 44887794175179797369169109)
                    ·
                      refine ⟨1052057675980776500839901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 44887794175179797369169109 1052057675980776500839901)
                      ·
                        rfl

theorem cell23_2048875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 7].length) (baseStart_2048875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048875 prefixEnd_2048875 := by exact prefixLift 2048875
  have htrace : WordTrace (prefixWord ++ tailWord_2048875) baseStart_2048875 baseEnd_2048875 := by
    simpa [prefixWord, tailWord_2048875, baseEnd_2048875] using wordTrace_append hprefix tailTrace_2048875
  have hstable : (prefixWord ++ tailWord_2048875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048875).length < 2 ^ (prefixWord ++ tailWord_2048875).sum := by decide
  have hdescent : baseEnd_2048875 < baseStart_2048875 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048916 : List Nat := [2, 4, 2, 1, 1, 1, 4, 3, 5]
def baseStart_2048916 : Nat := 118140960795 + 2048916 * 2 ^ 59
def prefixEnd_2048916 : Nat := 4983230072969 + 3 ^ 40 * 2048916 * 2
def baseEnd_2048916 : Nat := 116897636520845648936357

theorem tailTrace_2048916 : CollatzResearch.WordTrace tailWord_2048916 prefixEnd_2048916 116897636520845648936357 := by
  unfold tailWord_2048916
  simp only [CollatzResearch.WordTrace]
  refine ⟨37365052922567366919399301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49820070563423155892532401 37365052922567366919399301)
  ·
    refine ⟨7005947422981381297387369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37365052922567366919399301 7005947422981381297387369)
    ·
      refine ⟨5254460567236035973040527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7005947422981381297387369 5254460567236035973040527)
      ·
        refine ⟨7881690850854053959560791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5254460567236035973040527 7881690850854053959560791)
        ·
          refine ⟨11822536276281080939341187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7881690850854053959560791 11822536276281080939341187)
          ·
            refine ⟨17733804414421621409011781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11822536276281080939341187 17733804414421621409011781)
            ·
              refine ⟨3325088327704054014189709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17733804414421621409011781 3325088327704054014189709)
              ·
                refine ⟨1246908122889020255321141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3325088327704054014189709 1246908122889020255321141)
                ·
                  refine ⟨116897636520845648936357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1246908122889020255321141 116897636520845648936357)
                  ·
                    rfl

theorem cell23_2048916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 3, 5].length) (baseStart_2048916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048916 prefixEnd_2048916 := by exact prefixLift 2048916
  have htrace : WordTrace (prefixWord ++ tailWord_2048916) baseStart_2048916 baseEnd_2048916 := by
    simpa [prefixWord, tailWord_2048916, baseEnd_2048916] using wordTrace_append hprefix tailTrace_2048916
  have hstable : (prefixWord ++ tailWord_2048916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048916).length < 2 ^ (prefixWord ++ tailWord_2048916).sum := by decide
  have hdescent : baseEnd_2048916 < baseStart_2048916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048972 : List Nat := [2, 2, 1, 4, 1, 1, 1, 1, 10]
def baseStart_2048972 : Nat := 118140960795 + 2048972 * 2 ^ 59
def prefixEnd_2048972 : Nat := 4983230072969 + 3 ^ 40 * 2048972 * 2
def baseEnd_2048972 : Nat := 116900831511584735702995

theorem tailTrace_2048972 : CollatzResearch.WordTrace tailWord_2048972 prefixEnd_2048972 116900831511584735702995 := by
  unfold tailWord_2048972
  simp only [CollatzResearch.WordTrace]
  refine ⟨37366074166465927701418585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49821432221954570268558113 37366074166465927701418585)
  ·
    refine ⟨28024555624849445776063939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37366074166465927701418585 28024555624849445776063939)
    ·
      refine ⟨42036833437274168664095909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28024555624849445776063939 42036833437274168664095909)
      ·
        refine ⟨7881906269488906624517983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42036833437274168664095909 7881906269488906624517983)
        ·
          refine ⟨11822859404233359936776975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7881906269488906624517983 11822859404233359936776975)
          ·
            refine ⟨17734289106350039905165463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11822859404233359936776975 17734289106350039905165463)
            ·
              refine ⟨26601433659525059857748195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17734289106350039905165463 26601433659525059857748195)
              ·
                refine ⟨39902150489287589786622293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26601433659525059857748195 39902150489287589786622293)
                ·
                  refine ⟨116900831511584735702995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 39902150489287589786622293 116900831511584735702995)
                  ·
                    rfl

theorem cell23_2048972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 10].length) (baseStart_2048972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048972 prefixEnd_2048972 := by exact prefixLift 2048972
  have htrace : WordTrace (prefixWord ++ tailWord_2048972) baseStart_2048972 baseEnd_2048972 := by
    simpa [prefixWord, tailWord_2048972, baseEnd_2048972] using wordTrace_append hprefix tailTrace_2048972
  have hstable : (prefixWord ++ tailWord_2048972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048972).length < 2 ^ (prefixWord ++ tailWord_2048972).sum := by decide
  have hdescent : baseEnd_2048972 < baseStart_2048972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048986 : List Nat := [3, 1, 1, 2, 4, 2, 1, 2, 2, 2, 3]
def baseStart_2048986 : Nat := 118140960795 + 2048986 * 2 ^ 59
def prefixEnd_2048986 : Nat := 4983230072969 + 3 ^ 40 * 2048986 * 2
def baseEnd_2048986 : Nat := 1052114672333425566551891

theorem tailTrace_2048986 : CollatzResearch.WordTrace tailWord_2048986 prefixEnd_2048986 1052114672333425566551891 := by
  unfold tailWord_2048986
  simp only [CollatzResearch.WordTrace]
  refine ⟨18683164738720283948461703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49821772636587423862564541 18683164738720283948461703)
  ·
    refine ⟨28024747108080425922692555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18683164738720283948461703 28024747108080425922692555)
    ·
      refine ⟨42037120662120638884038833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28024747108080425922692555 42037120662120638884038833)
      ·
        refine ⟨31527840496590479163029125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42037120662120638884038833 31527840496590479163029125)
        ·
          refine ⟨5911470093110714843067961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31527840496590479163029125 5911470093110714843067961)
          ·
            refine ⟨4433602569833036132300971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5911470093110714843067961 4433602569833036132300971)
            ·
              refine ⟨6650403854749554198451457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4433602569833036132300971 6650403854749554198451457)
              ·
                refine ⟨4987802891062165648838593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6650403854749554198451457 4987802891062165648838593)
                ·
                  refine ⟨3740852168296624236628945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4987802891062165648838593 3740852168296624236628945)
                  ·
                    refine ⟨2805639126222468177471709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3740852168296624236628945 2805639126222468177471709)
                    ·
                      refine ⟨1052114672333425566551891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2805639126222468177471709 1052114672333425566551891)
                      ·
                        rfl

theorem cell23_2048986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 2, 2, 3].length) (baseStart_2048986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048986 prefixEnd_2048986 := by exact prefixLift 2048986
  have htrace : WordTrace (prefixWord ++ tailWord_2048986) baseStart_2048986 baseEnd_2048986 := by
    simpa [prefixWord, tailWord_2048986, baseEnd_2048986] using wordTrace_append hprefix tailTrace_2048986
  have hstable : (prefixWord ++ tailWord_2048986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048986).length < 2 ^ (prefixWord ++ tailWord_2048986).sum := by decide
  have hdescent : baseEnd_2048986 < baseStart_2048986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048989 : List Nat := [1, 4, 3, 1, 2, 1, 2, 1, 8]
def baseStart_2048989 : Nat := 118140960795 + 2048989 * 2 ^ 59
def prefixEnd_2048989 : Nat := 4983230072969 + 3 ^ 40 * 2048989 * 2
def baseEnd_2048989 : Nat := 116901801419487672757153

theorem tailTrace_2048989 : CollatzResearch.WordTrace tailWord_2048989 prefixEnd_2048989 116901801419487672757153 := by
  unfold tailWord_2048989
  simp only [CollatzResearch.WordTrace]
  refine ⟨74732768373870267306206021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49821845582580178204137347 74732768373870267306206021)
  ·
    refine ⟨14012394070100675119913629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74732768373870267306206021 14012394070100675119913629)
    ·
      refine ⟨5254647776287753169967611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14012394070100675119913629 5254647776287753169967611)
      ·
        refine ⟨7881971664431629754951417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5254647776287753169967611 7881971664431629754951417)
        ·
          refine ⟨5911478748323722316213563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7881971664431629754951417 5911478748323722316213563)
          ·
            refine ⟨8867218122485583474320345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5911478748323722316213563 8867218122485583474320345)
            ·
              refine ⟨6650413591864187605740259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8867218122485583474320345 6650413591864187605740259)
              ·
                refine ⟨9975620387796281408610389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6650413591864187605740259 9975620387796281408610389)
                ·
                  refine ⟨116901801419487672757153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9975620387796281408610389 116901801419487672757153)
                  ·
                    rfl

theorem cell23_2048989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 8].length) (baseStart_2048989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2048989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2048989 prefixEnd_2048989 := by exact prefixLift 2048989
  have htrace : WordTrace (prefixWord ++ tailWord_2048989) baseStart_2048989 baseEnd_2048989 := by
    simpa [prefixWord, tailWord_2048989, baseEnd_2048989] using wordTrace_append hprefix tailTrace_2048989
  have hstable : (prefixWord ++ tailWord_2048989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048989).length < 2 ^ (prefixWord ++ tailWord_2048989).sum := by decide
  have hdescent : baseEnd_2048989 < baseStart_2048989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049006 : List Nat := [4, 1, 2, 1, 4, 1, 1, 3, 6]
def baseStart_2049006 : Nat := 118140960795 + 2049006 * 2 ^ 59
def prefixEnd_2049006 : Nat := 4983230072969 + 3 ^ 40 * 2049006 * 2
def baseEnd_2049006 : Nat := 116902771327390609811311

theorem tailTrace_2049006 : CollatzResearch.WordTrace tailWord_2049006 prefixEnd_2049006 116902771327390609811311 := by
  unfold tailWord_2049006
  simp only [CollatzResearch.WordTrace]
  refine ⟨9341673551851084901196859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49822258943205786139716581 9341673551851084901196859)
  ·
    refine ⟨14012510327776627351795289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9341673551851084901196859 14012510327776627351795289)
    ·
      refine ⟨10509382745832470513846467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14012510327776627351795289 10509382745832470513846467)
      ·
        refine ⟨15764074118748705770769701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10509382745832470513846467 15764074118748705770769701)
        ·
          refine ⟨2955763897265382332019319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15764074118748705770769701 2955763897265382332019319)
          ·
            refine ⟨4433645845898073498028979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2955763897265382332019319 4433645845898073498028979)
            ·
              refine ⟨6650468768847110247043469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4433645845898073498028979 6650468768847110247043469)
              ·
                refine ⟨2493925788317666342641301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6650468768847110247043469 2493925788317666342641301)
                ·
                  refine ⟨116902771327390609811311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2493925788317666342641301 116902771327390609811311)
                  ·
                    rfl

theorem cell23_2049006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 3, 6].length) (baseStart_2049006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2049006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2049006 prefixEnd_2049006 := by exact prefixLift 2049006
  have htrace : WordTrace (prefixWord ++ tailWord_2049006) baseStart_2049006 baseEnd_2049006 := by
    simpa [prefixWord, tailWord_2049006, baseEnd_2049006] using wordTrace_append hprefix tailTrace_2049006
  have hstable : (prefixWord ++ tailWord_2049006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049006).length < 2 ^ (prefixWord ++ tailWord_2049006).sum := by decide
  have hdescent : baseEnd_2049006 < baseStart_2049006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049039 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 3, 8, 2]
def baseStart_2049039 : Nat := 118140960795 + 2049039 * 2 ^ 59
def prefixEnd_2049039 : Nat := 4983230072969 + 3 ^ 40 * 2049039 * 2
def baseEnd_2049039 : Nat := 1052141886808113859189147

theorem tailTrace_2049039 : CollatzResearch.WordTrace tailWord_2049039 prefixEnd_2049039 1052141886808113859189147 := by
  unfold tailWord_2049039
  simp only [CollatzResearch.WordTrace]
  refine ⟨74734592023689125845526171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49823061349126083897017447 74734592023689125845526171)
  ·
    refine ⟨112101888035533688768289257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74734592023689125845526171 112101888035533688768289257)
    ·
      refine ⟨84076416026650266576216943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112101888035533688768289257 84076416026650266576216943)
      ·
        refine ⟨126114624039975399864325415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84076416026650266576216943 126114624039975399864325415)
        ·
          refine ⟨189171936059963099796488123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126114624039975399864325415 189171936059963099796488123)
          ·
            refine ⟨283757904089944649694732185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189171936059963099796488123 283757904089944649694732185)
            ·
              refine ⟨212818428067458487271049139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283757904089944649694732185 212818428067458487271049139)
              ·
                refine ⟨319227642101187730906573709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212818428067458487271049139 319227642101187730906573709)
                ·
                  refine ⟨119710365787945399089965141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 319227642101187730906573709 119710365787945399089965141)
                  ·
                    refine ⟨1402855849077485145585529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 119710365787945399089965141 1402855849077485145585529)
                    ·
                      refine ⟨1052141886808113859189147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1402855849077485145585529 1052141886808113859189147)
                      ·
                        rfl

theorem cell23_2049039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 8, 2].length) (baseStart_2049039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2049039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2049039 prefixEnd_2049039 := by exact prefixLift 2049039
  have htrace : WordTrace (prefixWord ++ tailWord_2049039) baseStart_2049039 baseEnd_2049039 := by
    simpa [prefixWord, tailWord_2049039, baseEnd_2049039] using wordTrace_append hprefix tailTrace_2049039
  have hstable : (prefixWord ++ tailWord_2049039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049039).length < 2 ^ (prefixWord ++ tailWord_2049039).sum := by decide
  have hdescent : baseEnd_2049039 < baseStart_2049039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049049 : List Nat := [1, 2, 1, 2, 1, 1, 4, 3, 4, 4]
def baseStart_2049049 : Nat := 118140960795 + 2049049 * 2 ^ 59
def prefixEnd_2049049 : Nat := 4983230072969 + 3 ^ 40 * 2049049 * 2
def baseEnd_2049049 : Nat := 350715673871552940021367

theorem tailTrace_2049049 : CollatzResearch.WordTrace tailWord_2049049 prefixEnd_2049049 350715673871552940021367 := by
  unfold tailWord_2049049
  simp only [CollatzResearch.WordTrace]
  refine ⟨74734956753652897553390201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49823304502435265035593467 74734956753652897553390201)
  ·
    refine ⟨56051217565239673165042651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74734956753652897553390201 56051217565239673165042651)
    ·
      refine ⟨84076826347859509747563977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56051217565239673165042651 84076826347859509747563977)
      ·
        refine ⟨63057619760894632310672983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84076826347859509747563977 63057619760894632310672983)
        ·
          refine ⟨94586429641341948466009475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63057619760894632310672983 94586429641341948466009475)
          ·
            refine ⟨141879644462012922699014213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94586429641341948466009475 141879644462012922699014213)
            ·
              refine ⟨26602433336627423006065165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141879644462012922699014213 26602433336627423006065165)
              ·
                refine ⟨9975912501235283627274437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26602433336627423006065165 9975912501235283627274437)
                ·
                  refine ⟨1870483593981615680113957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9975912501235283627274437 1870483593981615680113957)
                  ·
                    refine ⟨350715673871552940021367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1870483593981615680113957 350715673871552940021367)
                    ·
                      rfl

theorem cell23_2049049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 4, 4].length) (baseStart_2049049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2049049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2049049 prefixEnd_2049049 := by exact prefixLift 2049049
  have htrace : WordTrace (prefixWord ++ tailWord_2049049) baseStart_2049049 baseEnd_2049049 := by
    simpa [prefixWord, tailWord_2049049, baseEnd_2049049] using wordTrace_append hprefix tailTrace_2049049
  have hstable : (prefixWord ++ tailWord_2049049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049049).length < 2 ^ (prefixWord ++ tailWord_2049049).sum := by decide
  have hdescent : baseEnd_2049049 < baseStart_2049049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049073 : List Nat := [1, 2, 2, 3, 1, 2, 3, 2, 3, 2, 2]
def baseStart_2049073 : Nat := 118140960795 + 2049073 * 2 ^ 59
def prefixEnd_2049073 : Nat := 4983230072969 + 3 ^ 40 * 2049073 * 2
def baseEnd_2049073 : Nat := 1052159345150366726163991

theorem tailTrace_2049073 : CollatzResearch.WordTrace tailWord_2049073 prefixEnd_2049073 1052159345150366726163991 := by
  unfold tailWord_2049073
  simp only [CollatzResearch.WordTrace]
  refine ⟨74735832105565949652263873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49823888070377299768175915 74735832105565949652263873)
  ·
    refine ⟨56051874079174462239197905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74735832105565949652263873 56051874079174462239197905)
    ·
      refine ⟨42038905559380846679398429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56051874079174462239197905 42038905559380846679398429)
      ·
        refine ⟨15764589584767817504774411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42038905559380846679398429 15764589584767817504774411)
        ·
          refine ⟨23646884377151726257161617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15764589584767817504774411 23646884377151726257161617)
          ·
            refine ⟨17735163282863794692871213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23646884377151726257161617 17735163282863794692871213)
            ·
              refine ⟨6650686231073923009826705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17735163282863794692871213 6650686231073923009826705)
              ·
                refine ⟨4988014673305442257370029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6650686231073923009826705 4988014673305442257370029)
                ·
                  refine ⟨1870505502489540846513761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4988014673305442257370029 1870505502489540846513761)
                  ·
                    refine ⟨1402879126867155634885321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1870505502489540846513761 1402879126867155634885321)
                    ·
                      refine ⟨1052159345150366726163991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1402879126867155634885321 1052159345150366726163991)
                      ·
                        rfl

theorem cell23_2049073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 3, 2, 2].length) (baseStart_2049073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2049073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2049073 prefixEnd_2049073 := by exact prefixLift 2049073
  have htrace : WordTrace (prefixWord ++ tailWord_2049073) baseStart_2049073 baseEnd_2049073 := by
    simpa [prefixWord, tailWord_2049073, baseEnd_2049073] using wordTrace_append hprefix tailTrace_2049073
  have hstable : (prefixWord ++ tailWord_2049073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049073).length < 2 ^ (prefixWord ++ tailWord_2049073).sum := by decide
  have hdescent : baseEnd_2049073 < baseStart_2049073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049093 : List Nat := [1, 3, 1, 1, 1, 3, 6, 1, 1, 2, 3]
def baseStart_2049093 : Nat := 118140960795 + 2049093 * 2 ^ 59
def prefixEnd_2049093 : Nat := 4983230072969 + 3 ^ 40 * 2049093 * 2
def baseEnd_2049093 : Nat := 1052169614763456647913899

theorem tailTrace_2049093 : CollatzResearch.WordTrace tailWord_2049093 prefixEnd_2049093 1052169614763456647913899 := by
  unfold tailWord_2049093
  simp only [CollatzResearch.WordTrace]
  refine ⟨74736561565493493067991933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49824374376995662045327955 74736561565493493067991933)
  ·
    refine ⟨28026210587060059900496975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74736561565493493067991933 28026210587060059900496975)
    ·
      refine ⟨42039315880590089850745463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28026210587060059900496975 42039315880590089850745463)
      ·
        refine ⟨63058973820885134776118195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42039315880590089850745463 63058973820885134776118195)
        ·
          refine ⟨94588460731327702164177293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63058973820885134776118195 94588460731327702164177293)
          ·
            refine ⟨35470672774247888311566485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94588460731327702164177293 35470672774247888311566485)
            ·
              refine ⟨1662687786292869764604679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35470672774247888311566485 1662687786292869764604679)
              ·
                refine ⟨2494031679439304646907019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1662687786292869764604679 2494031679439304646907019)
                ·
                  refine ⟨3741047519158956970360529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2494031679439304646907019 3741047519158956970360529)
                  ·
                    refine ⟨2805785639369217727770397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3741047519158956970360529 2805785639369217727770397)
                    ·
                      refine ⟨1052169614763456647913899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2805785639369217727770397 1052169614763456647913899)
                      ·
                        rfl

theorem cell23_2049093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 1, 1, 2, 3].length) (baseStart_2049093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2049093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2049093 prefixEnd_2049093 := by exact prefixLift 2049093
  have htrace : WordTrace (prefixWord ++ tailWord_2049093) baseStart_2049093 baseEnd_2049093 := by
    simpa [prefixWord, tailWord_2049093, baseEnd_2049093] using wordTrace_append hprefix tailTrace_2049093
  have hstable : (prefixWord ++ tailWord_2049093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049093).length < 2 ^ (prefixWord ++ tailWord_2049093).sum := by decide
  have hdescent : baseEnd_2049093 < baseStart_2049093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049110 : List Nat := [5, 2, 2, 1, 2, 1, 1, 2, 1, 1, 5]
def baseStart_2049110 : Nat := 118140960795 + 2049110 * 2 ^ 59
def prefixEnd_2049110 : Nat := 4983230072969 + 3 ^ 40 * 2049110 * 2
def baseEnd_2049110 : Nat := 1052178343934583081401321

theorem tailTrace_2049110 : CollatzResearch.WordTrace tailWord_2049110 prefixEnd_2049110 1052178343934583081401321 := by
  unfold tailWord_2049110
  simp only [CollatzResearch.WordTrace]
  refine ⟨4671073850401994060710049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49824787737621269980907189 4671073850401994060710049)
  ·
    refine ⟨3503305387801495545532537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4671073850401994060710049 3503305387801495545532537)
    ·
      refine ⟨2627479040851121659149403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3503305387801495545532537 2627479040851121659149403)
      ·
        refine ⟨3941218561276682488724105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2627479040851121659149403 3941218561276682488724105)
        ·
          refine ⟨2955913920957511866543079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3941218561276682488724105 2955913920957511866543079)
          ·
            refine ⟨4433870881436267799814619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2955913920957511866543079 4433870881436267799814619)
            ·
              refine ⟨6650806322154401699721929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4433870881436267799814619 6650806322154401699721929)
              ·
                refine ⟨4988104741615801274791447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6650806322154401699721929 4988104741615801274791447)
                ·
                  refine ⟨7482157112423701912187171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4988104741615801274791447 7482157112423701912187171)
                  ·
                    refine ⟨11223235668635552868280757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7482157112423701912187171 11223235668635552868280757)
                    ·
                      refine ⟨1052178343934583081401321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11223235668635552868280757 1052178343934583081401321)
                      ·
                        rfl

theorem cell23_2049110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_2049110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2049110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2049110 prefixEnd_2049110 := by exact prefixLift 2049110
  have htrace : WordTrace (prefixWord ++ tailWord_2049110) baseStart_2049110 baseEnd_2049110 := by
    simpa [prefixWord, tailWord_2049110, baseEnd_2049110] using wordTrace_append hprefix tailTrace_2049110
  have hstable : (prefixWord ++ tailWord_2049110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049110).length < 2 ^ (prefixWord ++ tailWord_2049110).sum := by decide
  have hdescent : baseEnd_2049110 < baseStart_2049110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049117 : List Nat := [1, 4, 4, 1, 2, 1, 3, 1, 2, 4]
def baseStart_2049117 : Nat := 118140960795 + 2049117 * 2 ^ 59
def prefixEnd_2049117 : Nat := 4983230072969 + 3 ^ 40 * 2049117 * 2
def baseEnd_2049117 : Nat := 350727312766388184671263

theorem tailTrace_2049117 : CollatzResearch.WordTrace tailWord_2049117 prefixEnd_2049117 350727312766388184671263 := by
  unfold tailWord_2049117
  simp only [CollatzResearch.WordTrace]
  refine ⟨74737436917406545166865605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49824957944937696777910403 74737436917406545166865605)
  ·
    refine ⟨14013269422013727218787301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74737436917406545166865605 14013269422013727218787301)
    ·
      refine ⟨2627488016627573853522619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14013269422013727218787301 2627488016627573853522619)
      ·
        refine ⟨3941232024941360780283929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2627488016627573853522619 3941232024941360780283929)
        ·
          refine ⟨2955924018706020585212947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3941232024941360780283929 2955924018706020585212947)
          ·
            refine ⟨4433886028059030877819421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2955924018706020585212947 4433886028059030877819421)
            ·
              refine ⟨1662707260522136579182283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4433886028059030877819421 1662707260522136579182283)
              ·
                refine ⟨2494060890783204868773425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1662707260522136579182283 2494060890783204868773425)
                ·
                  refine ⟨1870545668087403651580069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2494060890783204868773425 1870545668087403651580069)
                  ·
                    refine ⟨350727312766388184671263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1870545668087403651580069 350727312766388184671263)
                    ·
                      rfl

theorem cell23_2049117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_2049117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2049117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2049117 prefixEnd_2049117 := by exact prefixLift 2049117
  have htrace : WordTrace (prefixWord ++ tailWord_2049117) baseStart_2049117 baseEnd_2049117 := by
    simpa [prefixWord, tailWord_2049117, baseEnd_2049117] using wordTrace_append hprefix tailTrace_2049117
  have hstable : (prefixWord ++ tailWord_2049117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049117).length < 2 ^ (prefixWord ++ tailWord_2049117).sum := by decide
  have hdescent : baseEnd_2049117 < baseStart_2049117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049141 : List Nat := [1, 3, 4, 3, 1, 2, 1, 3, 1, 2, 2]
def baseStart_2049141 : Nat := 118140960795 + 2049141 * 2 ^ 59
def prefixEnd_2049141 : Nat := 4983230072969 + 3 ^ 40 * 2049141 * 2
def baseEnd_2049141 : Nat := 1052194261834872460113679

theorem tailTrace_2049141 : CollatzResearch.WordTrace tailWord_2049141 prefixEnd_2049141 1052194261834872460113679 := by
  unfold tailWord_2049141
  simp only [CollatzResearch.WordTrace]
  refine ⟨74738312269319597265739277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49825541512879731510492851 74738312269319597265739277)
  ·
    refine ⟨28026867100994848974652229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74738312269319597265739277 28026867100994848974652229)
    ·
      refine ⟨5255037581436534182747293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28026867100994848974652229 5255037581436534182747293)
      ·
        refine ⟨1970639093038700318530235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5255037581436534182747293 1970639093038700318530235)
        ·
          refine ⟨2955958639558050477795353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1970639093038700318530235 2955958639558050477795353)
          ·
            refine ⟨2216968979668537858346515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2955958639558050477795353 2216968979668537858346515)
            ·
              refine ⟨3325453469502806787519773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2216968979668537858346515 3325453469502806787519773)
              ·
                refine ⟨1247045051063552545319915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3325453469502806787519773 1247045051063552545319915)
                ·
                  refine ⟨1870567576595328817979873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1247045051063552545319915 1870567576595328817979873)
                  ·
                    refine ⟨1402925682446496613484905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1870567576595328817979873 1402925682446496613484905)
                    ·
                      refine ⟨1052194261834872460113679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1402925682446496613484905 1052194261834872460113679)
                      ·
                        rfl

theorem cell23_2049141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_2049141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2049141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2049141 prefixEnd_2049141 := by exact prefixLift 2049141
  have htrace : WordTrace (prefixWord ++ tailWord_2049141) baseStart_2049141 baseEnd_2049141 := by
    simpa [prefixWord, tailWord_2049141, baseEnd_2049141] using wordTrace_append hprefix tailTrace_2049141
  have hstable : (prefixWord ++ tailWord_2049141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049141).length < 2 ^ (prefixWord ++ tailWord_2049141).sum := by decide
  have hdescent : baseEnd_2049141 < baseStart_2049141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049199 : List Nat := [1, 1, 2, 1, 2, 3, 2, 3, 1, 7]
def baseStart_2049199 : Nat := 118140960795 + 2049199 * 2 ^ 59
def prefixEnd_2049199 : Nat := 4983230072969 + 3 ^ 40 * 2049199 * 2
def baseEnd_2049199 : Nat := 350741347904277744396137

theorem tailTrace_2049199 : CollatzResearch.WordTrace tailWord_2049199 prefixEnd_2049199 350741347904277744396137 := by
  unfold tailWord_2049199
  simp only [CollatzResearch.WordTrace]
  refine ⟨74740427703109473171350651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49826951802072982114233767 74740427703109473171350651)
  ·
    refine ⟨112110641554664209757025977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74740427703109473171350651 112110641554664209757025977)
    ·
      refine ⟨84082981165998157317769483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112110641554664209757025977 84082981165998157317769483)
      ·
        refine ⟨126124471748997235976654225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84082981165998157317769483 126124471748997235976654225)
        ·
          refine ⟨94593353811747926982490669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126124471748997235976654225 94593353811747926982490669)
          ·
            refine ⟨35472507679405472618434001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94593353811747926982490669 35472507679405472618434001)
            ·
              refine ⟨26604380759554104463825501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35472507679405472618434001 26604380759554104463825501)
              ·
                refine ⟨9976642784832789173934563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26604380759554104463825501 9976642784832789173934563)
                ·
                  refine ⟨14964964177249183760901845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9976642784832789173934563 14964964177249183760901845)
                  ·
                    refine ⟨350741347904277744396137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14964964177249183760901845 350741347904277744396137)
                    ·
                      rfl

theorem cell23_2049199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 7].length) (baseStart_2049199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2049199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2049199 prefixEnd_2049199 := by exact prefixLift 2049199
  have htrace : WordTrace (prefixWord ++ tailWord_2049199) baseStart_2049199 baseEnd_2049199 := by
    simpa [prefixWord, tailWord_2049199, baseEnd_2049199] using wordTrace_append hprefix tailTrace_2049199
  have hstable : (prefixWord ++ tailWord_2049199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049199).length < 2 ^ (prefixWord ++ tailWord_2049199).sum := by decide
  have hdescent : baseEnd_2049199 < baseStart_2049199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049220 : List Nat := [2, 3, 3, 1, 3, 1, 1, 4, 5]
def baseStart_2049220 : Nat := 118140960795 + 2049220 * 2 ^ 59
def prefixEnd_2049220 : Nat := 4983230072969 + 3 ^ 40 * 2049220 * 2
def baseEnd_2049220 : Nat := 116914980756286405669535

theorem tailTrace_2049220 : CollatzResearch.WordTrace tailWord_2049220 prefixEnd_2049220 116914980756286405669535 := by
  unfold tailWord_2049220
  simp only [CollatzResearch.WordTrace]
  refine ⟨37370596818016696878932557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49827462424022262505243409 37370596818016696878932557)
  ·
    refine ⟨14013973806756261329599709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37370596818016696878932557 14013973806756261329599709)
    ·
      refine ⟨5255240177533597998599891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14013973806756261329599709 5255240177533597998599891)
      ·
        refine ⟨7882860266300396997899837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5255240177533597998599891 7882860266300396997899837)
        ·
          refine ⟨2956072599862648874212439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7882860266300396997899837 2956072599862648874212439)
          ·
            refine ⟨4434108899793973311318659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2956072599862648874212439 4434108899793973311318659)
            ·
              refine ⟨6651163349690959966977989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4434108899793973311318659 6651163349690959966977989)
              ·
                refine ⟨1247093128067054993808373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6651163349690959966977989 1247093128067054993808373)
                ·
                  refine ⟨116914980756286405669535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1247093128067054993808373 116914980756286405669535)
                  ·
                    rfl

theorem cell23_2049220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 4, 5].length) (baseStart_2049220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2049220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2049220 prefixEnd_2049220 := by exact prefixLift 2049220
  have htrace : WordTrace (prefixWord ++ tailWord_2049220) baseStart_2049220 baseEnd_2049220 := by
    simpa [prefixWord, tailWord_2049220, baseEnd_2049220] using wordTrace_append hprefix tailTrace_2049220
  have hstable : (prefixWord ++ tailWord_2049220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049220).length < 2 ^ (prefixWord ++ tailWord_2049220).sum := by decide
  have hdescent : baseEnd_2049220 < baseStart_2049220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049226 : List Nat := [3, 1, 2, 1, 3, 2, 2, 1, 1, 2, 5]
def baseStart_2049226 : Nat := 118140960795 + 2049226 * 2 ^ 59
def prefixEnd_2049226 : Nat := 4983230072969 + 3 ^ 40 * 2049226 * 2
def baseEnd_2049226 : Nat := 1052237907690504627550787

theorem tailTrace_2049226 : CollatzResearch.WordTrace tailWord_2049226 prefixEnd_2049226 1052237907690504627550787 := by
  unfold tailWord_2049226
  simp only [CollatzResearch.WordTrace]
  refine ⟨18685353118502914195645883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49827608316007771188389021 18685353118502914195645883)
  ·
    refine ⟨28028029677754371293468825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18685353118502914195645883 28028029677754371293468825)
    ·
      refine ⟨21021022258315778470101619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28028029677754371293468825 21021022258315778470101619)
      ·
        refine ⟨31531533387473667705152429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21021022258315778470101619 31531533387473667705152429)
        ·
          refine ⟨11824325020302625389432161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31531533387473667705152429 11824325020302625389432161)
          ·
            refine ⟨8868243765226969042074121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11824325020302625389432161 8868243765226969042074121)
            ·
              refine ⟨6651182823920226781555591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8868243765226969042074121 6651182823920226781555591)
              ·
                refine ⟨9976774235880340172333387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6651182823920226781555591 9976774235880340172333387)
                ·
                  refine ⟨14965161353820510258500081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9976774235880340172333387 14965161353820510258500081)
                  ·
                    refine ⟨11223871015365382693875061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14965161353820510258500081 11223871015365382693875061)
                    ·
                      refine ⟨1052237907690504627550787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11223871015365382693875061 1052237907690504627550787)
                      ·
                        rfl

theorem cell23_2049226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_2049226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2049226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2049226 prefixEnd_2049226 := by exact prefixLift 2049226
  have htrace : WordTrace (prefixWord ++ tailWord_2049226) baseStart_2049226 baseEnd_2049226 := by
    simpa [prefixWord, tailWord_2049226, baseEnd_2049226] using wordTrace_append hprefix tailTrace_2049226
  have hstable : (prefixWord ++ tailWord_2049226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049226).length < 2 ^ (prefixWord ++ tailWord_2049226).sum := by decide
  have hdescent : baseEnd_2049226 < baseStart_2049226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049253 : List Nat := [1, 3, 1, 4, 3, 1, 1, 1, 1, 3, 4]
def baseStart_2049253 : Nat := 118140960795 + 2049253 * 2 ^ 59
def prefixEnd_2049253 : Nat := 4983230072969 + 3 ^ 40 * 2049253 * 2
def baseEnd_2049253 : Nat := 1052251771668176021913163

theorem tailTrace_2049253 : CollatzResearch.WordTrace tailWord_2049253 prefixEnd_2049253 1052251771668176021913163 := by
  unfold tailWord_2049253
  simp only [CollatzResearch.WordTrace]
  refine ⟨74742397244913840393816413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49828264829942560262544275 74742397244913840393816413)
  ·
    refine ⟨28028398966842690147681155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74742397244913840393816413 28028398966842690147681155)
    ·
      refine ⟨42042598450264035221521733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28028398966842690147681155 42042598450264035221521733)
      ·
        refine ⟨7882987209424506604035325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42042598450264035221521733 7882987209424506604035325)
        ·
          refine ⟨2956120203534189976513247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7882987209424506604035325 2956120203534189976513247)
          ·
            refine ⟨4434180305301284964769871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2956120203534189976513247 4434180305301284964769871)
            ·
              refine ⟨6651270457951927447154807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4434180305301284964769871 6651270457951927447154807)
              ·
                refine ⟨9976905686927891170732211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6651270457951927447154807 9976905686927891170732211)
                ·
                  refine ⟨14965358530391836756098317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9976905686927891170732211 14965358530391836756098317)
                  ·
                    refine ⟨5612009448896938783536869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14965358530391836756098317 5612009448896938783536869)
                    ·
                      refine ⟨1052251771668176021913163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5612009448896938783536869 1052251771668176021913163)
                      ·
                        rfl

theorem cell23_2049253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_2049253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2049253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2049253 prefixEnd_2049253 := by exact prefixLift 2049253
  have htrace : WordTrace (prefixWord ++ tailWord_2049253) baseStart_2049253 baseEnd_2049253 := by
    simpa [prefixWord, tailWord_2049253, baseEnd_2049253] using wordTrace_append hprefix tailTrace_2049253
  have hstable : (prefixWord ++ tailWord_2049253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049253).length < 2 ^ (prefixWord ++ tailWord_2049253).sum := by decide
  have hdescent : baseEnd_2049253 < baseStart_2049253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049314 : List Nat := [3, 3, 1, 1, 4, 2, 1, 3, 1, 4]
def baseStart_2049314 : Nat := 118140960795 + 2049314 * 2 ^ 59
def prefixEnd_2049314 : Nat := 4983230072969 + 3 ^ 40 * 2049314 * 2
def baseEnd_2049314 : Nat := 350761031329366761083461

theorem tailTrace_2049314 : CollatzResearch.WordTrace tailWord_2049314 prefixEnd_2049314 350761031329366761083461 := by
  unfold tailWord_2049314
  simp only [CollatzResearch.WordTrace]
  refine ⟨18686155524423211952946749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49829748065128565207857997 18686155524423211952946749)
  ·
    refine ⟨7007308321658704482355031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18686155524423211952946749 7007308321658704482355031)
    ·
      refine ⟨10510962482488056723532547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7007308321658704482355031 10510962482488056723532547)
      ·
        refine ⟨15766443723732085085298821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10510962482488056723532547 15766443723732085085298821)
        ·
          refine ⟨2956208198199765953493529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15766443723732085085298821 2956208198199765953493529)
          ·
            refine ⟨2217156148649824465120147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2956208198199765953493529 2217156148649824465120147)
            ·
              refine ⟨3325734222974736697680221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2217156148649824465120147 3325734222974736697680221)
              ·
                refine ⟨1247150333615526261630083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3325734222974736697680221 1247150333615526261630083)
                ·
                  refine ⟨1870725500423289392445125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1247150333615526261630083 1870725500423289392445125)
                  ·
                    refine ⟨350761031329366761083461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1870725500423289392445125 350761031329366761083461)
                    ·
                      rfl

theorem cell23_2049314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_2049314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2049314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2049314 prefixEnd_2049314 := by exact prefixLift 2049314
  have htrace : WordTrace (prefixWord ++ tailWord_2049314) baseStart_2049314 baseEnd_2049314 := by
    simpa [prefixWord, tailWord_2049314, baseEnd_2049314] using wordTrace_append hprefix tailTrace_2049314
  have hstable : (prefixWord ++ tailWord_2049314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049314).length < 2 ^ (prefixWord ++ tailWord_2049314).sum := by decide
  have hdescent : baseEnd_2049314 < baseStart_2049314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049330 : List Nat := [3, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2]
def baseStart_2049330 : Nat := 118140960795 + 2049330 * 2 ^ 59
def prefixEnd_2049330 : Nat := 4983230072969 + 3 ^ 40 * 2049330 * 2
def baseEnd_2049330 : Nat := 1052291309678572220650309

theorem tailTrace_2049330 : CollatzResearch.WordTrace tailWord_2049330 prefixEnd_2049330 1052291309678572220650309 := by
  unfold tailWord_2049330
  simp only [CollatzResearch.WordTrace]
  refine ⟨18686301416408720636092361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49830137110423255029579629 18686301416408720636092361)
  ·
    refine ⟨14014726062306540477069271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18686301416408720636092361 14014726062306540477069271)
    ·
      refine ⟨21022089093459810715603907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14014726062306540477069271 21022089093459810715603907)
      ·
        refine ⟨31533133640189716073405861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21022089093459810715603907 31533133640189716073405861)
        ·
          refine ⟨5912462557535571763763599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31533133640189716073405861 5912462557535571763763599)
          ·
            refine ⟨8868693836303357645645399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5912462557535571763763599 8868693836303357645645399)
            ·
              refine ⟨13303040754455036468468099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8868693836303357645645399 13303040754455036468468099)
              ·
                refine ⟨19954561131682554702702149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13303040754455036468468099 19954561131682554702702149)
                ·
                  refine ⟨3741480212190479006756653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19954561131682554702702149 3741480212190479006756653)
                  ·
                    refine ⟨1403055079571429627533745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3741480212190479006756653 1403055079571429627533745)
                    ·
                      refine ⟨1052291309678572220650309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1403055079571429627533745 1052291309678572220650309)
                      ·
                        rfl

theorem cell23_2049330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2].length) (baseStart_2049330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2049330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2049330 prefixEnd_2049330 := by exact prefixLift 2049330
  have htrace : WordTrace (prefixWord ++ tailWord_2049330) baseStart_2049330 baseEnd_2049330 := by
    simpa [prefixWord, tailWord_2049330, baseEnd_2049330] using wordTrace_append hprefix tailTrace_2049330
  have hstable : (prefixWord ++ tailWord_2049330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049330).length < 2 ^ (prefixWord ++ tailWord_2049330).sum := by decide
  have hdescent : baseEnd_2049330 < baseStart_2049330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049357 : List Nat := [1, 6, 1, 3, 1, 1, 1, 1, 3, 5]
def baseStart_2049357 : Nat := 118140960795 + 2049357 * 2 ^ 59
def prefixEnd_2049357 : Nat := 4983230072969 + 3 ^ 40 * 2049357 * 2
def baseEnd_2049357 : Nat := 350768391218747871670895

theorem tailTrace_2049357 : CollatzResearch.WordTrace tailWord_2049357 prefixEnd_2049357 350768391218747871670895 := by
  unfold tailWord_2049357
  simp only [CollatzResearch.WordTrace]
  refine ⟨74746190436537066155602325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49830793624358044103734883 74746190436537066155602325)
  ·
    refine ⟨3503727676712674976043859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 74746190436537066155602325 3503727676712674976043859)
    ·
      refine ⟨5255591515069012464065789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3503727676712674976043859 5255591515069012464065789)
      ·
        refine ⟨1970846818150879674024671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5255591515069012464065789 1970846818150879674024671)
        ·
          refine ⟨2956270227226319511037007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1970846818150879674024671 2956270227226319511037007)
          ·
            refine ⟨4434405340839479266555511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2956270227226319511037007 4434405340839479266555511)
            ·
              refine ⟨6651608011259218899833267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4434405340839479266555511 6651608011259218899833267)
              ·
                refine ⟨9977412016888828349749901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6651608011259218899833267 9977412016888828349749901)
                ·
                  refine ⟨3741529506333310631156213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9977412016888828349749901 3741529506333310631156213)
                  ·
                    refine ⟨350768391218747871670895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3741529506333310631156213 350768391218747871670895)
                    ·
                      rfl

theorem cell23_2049357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_2049357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2049357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2049357 prefixEnd_2049357 := by exact prefixLift 2049357
  have htrace : WordTrace (prefixWord ++ tailWord_2049357) baseStart_2049357 baseEnd_2049357 := by
    simpa [prefixWord, tailWord_2049357, baseEnd_2049357] using wordTrace_append hprefix tailTrace_2049357
  have hstable : (prefixWord ++ tailWord_2049357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049357).length < 2 ^ (prefixWord ++ tailWord_2049357).sum := by decide
  have hdescent : baseEnd_2049357 < baseStart_2049357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049360 : List Nat := [2, 1, 1, 1, 1, 5, 2, 1, 5, 2, 2]
def baseStart_2049360 : Nat := 118140960795 + 2049360 * 2 ^ 59
def prefixEnd_2049360 : Nat := 4983230072969 + 3 ^ 40 * 2049360 * 2
def baseEnd_2049360 : Nat := 1052306714098207103275171

theorem tailTrace_2049360 : CollatzResearch.WordTrace tailWord_2049360 prefixEnd_2049360 1052306714098207103275171 := by
  unfold tailWord_2049360
  simp only [CollatzResearch.WordTrace]
  refine ⟨37373149927763098833980767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49830866570350798445307689 37373149927763098833980767)
  ·
    refine ⟨56059724891644648250971151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37373149927763098833980767 56059724891644648250971151)
    ·
      refine ⟨84089587337466972376456727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56059724891644648250971151 84089587337466972376456727)
      ·
        refine ⟨126134381006200458564685091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84089587337466972376456727 126134381006200458564685091)
        ·
          refine ⟨189201571509300687847027637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126134381006200458564685091 189201571509300687847027637)
          ·
            refine ⟨17737647328996939485658841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 189201571509300687847027637 17737647328996939485658841)
            ·
              refine ⟨13303235496747704614244131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17737647328996939485658841 13303235496747704614244131)
              ·
                refine ⟨19954853245121556921366197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13303235496747704614244131 19954853245121556921366197)
                ·
                  refine ⟨1870767491730145961378081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19954853245121556921366197 1870767491730145961378081)
                  ·
                    refine ⟨1403075618797609471033561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1870767491730145961378081 1403075618797609471033561)
                    ·
                      refine ⟨1052306714098207103275171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1403075618797609471033561 1052306714098207103275171)
                      ·
                        rfl

theorem cell23_2049360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 5, 2, 2].length) (baseStart_2049360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2049360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2049360 prefixEnd_2049360 := by exact prefixLift 2049360
  have htrace : WordTrace (prefixWord ++ tailWord_2049360) baseStart_2049360 baseEnd_2049360 := by
    simpa [prefixWord, tailWord_2049360, baseEnd_2049360] using wordTrace_append hprefix tailTrace_2049360
  have hstable : (prefixWord ++ tailWord_2049360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049360).length < 2 ^ (prefixWord ++ tailWord_2049360).sum := by decide
  have hdescent : baseEnd_2049360 < baseStart_2049360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049363 : List Nat := [1, 1, 1, 2, 1, 1, 7, 1, 3, 2, 3]
def baseStart_2049363 : Nat := 118140960795 + 2049363 * 2 ^ 59
def prefixEnd_2049363 : Nat := 4983230072969 + 3 ^ 40 * 2049363 * 2
def baseEnd_2049363 : Nat := 1052308254540170591537657

theorem tailTrace_2049363 : CollatzResearch.WordTrace tailWord_2049363 prefixEnd_2049363 1052308254540170591537657 := by
  unfold tailWord_2049363
  simp only [CollatzResearch.WordTrace]
  refine ⟨74746409274515329180320743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49830939516343552786880495 74746409274515329180320743)
  ·
    refine ⟨112119613911772993770481115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74746409274515329180320743 112119613911772993770481115)
    ·
      refine ⟨168179420867659490655721673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112119613911772993770481115 168179420867659490655721673)
      ·
        refine ⟨126134565650744617991791255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168179420867659490655721673 126134565650744617991791255)
        ·
          refine ⟨189201848476116926987686883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126134565650744617991791255 189201848476116926987686883)
          ·
            refine ⟨283802772714175390481530325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189201848476116926987686883 283802772714175390481530325)
            ·
              refine ⟨6651627485488485714410867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 283802772714175390481530325 6651627485488485714410867)
              ·
                refine ⟨9977441228232728571616301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6651627485488485714410867 9977441228232728571616301)
                ·
                  refine ⟨3741540460587273214356113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9977441228232728571616301 3741540460587273214356113)
                  ·
                    refine ⟨2806155345440454910767085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3741540460587273214356113 2806155345440454910767085)
                    ·
                      refine ⟨1052308254540170591537657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2806155345440454910767085 1052308254540170591537657)
                      ·
                        rfl

theorem cell23_2049363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 3, 2, 3].length) (baseStart_2049363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2049363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2049363 prefixEnd_2049363 := by exact prefixLift 2049363
  have htrace : WordTrace (prefixWord ++ tailWord_2049363) baseStart_2049363 baseEnd_2049363 := by
    simpa [prefixWord, tailWord_2049363, baseEnd_2049363] using wordTrace_append hprefix tailTrace_2049363
  have hstable : (prefixWord ++ tailWord_2049363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049363).length < 2 ^ (prefixWord ++ tailWord_2049363).sum := by decide
  have hdescent : baseEnd_2049363 < baseStart_2049363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049380 : List Nat := [2, 3, 1, 1, 3, 4, 1, 1, 1, 1, 5]
def baseStart_2049380 : Nat := 118140960795 + 2049380 * 2 ^ 59
def prefixEnd_2049380 : Nat := 4983230072969 + 3 ^ 40 * 2049380 * 2
def baseEnd_2049380 : Nat := 1052316983711297025025079

theorem tailTrace_2049380 : CollatzResearch.WordTrace tailWord_2049380 prefixEnd_2049380 1052316983711297025025079 := by
  unfold tailWord_2049380
  simp only [CollatzResearch.WordTrace]
  refine ⟨37373514657726870541844797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49831352876969160722459729 37373514657726870541844797)
  ·
    refine ⟨14015067996647576453191799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37373514657726870541844797 14015067996647576453191799)
    ·
      refine ⟨21022601994971364679787699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14015067996647576453191799 21022601994971364679787699)
      ·
        refine ⟨31533902992457047019681549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21022601994971364679787699 31533902992457047019681549)
        ·
          refine ⟨11825213622171392632380581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31533902992457047019681549 11825213622171392632380581)
          ·
            refine ⟨2217227554157136118571359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11825213622171392632380581 2217227554157136118571359)
            ·
              refine ⟨3325841331235704177857039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2217227554157136118571359 3325841331235704177857039)
              ·
                refine ⟨4988761996853556266785559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3325841331235704177857039 4988761996853556266785559)
                ·
                  refine ⟨7483142995280334400178339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4988761996853556266785559 7483142995280334400178339)
                  ·
                    refine ⟨11224714492920501600267509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7483142995280334400178339 11224714492920501600267509)
                    ·
                      refine ⟨1052316983711297025025079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11224714492920501600267509 1052316983711297025025079)
                      ·
                        rfl

theorem cell23_2049380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 1, 1, 5].length) (baseStart_2049380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2049380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2049380 prefixEnd_2049380 := by exact prefixLift 2049380
  have htrace : WordTrace (prefixWord ++ tailWord_2049380) baseStart_2049380 baseEnd_2049380 := by
    simpa [prefixWord, tailWord_2049380, baseEnd_2049380] using wordTrace_append hprefix tailTrace_2049380
  have hstable : (prefixWord ++ tailWord_2049380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049380).length < 2 ^ (prefixWord ++ tailWord_2049380).sum := by decide
  have hdescent : baseEnd_2049380 < baseStart_2049380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049383 : List Nat := [1, 1, 5, 1, 5, 10]
def baseStart_2049383 : Nat := 118140960795 + 2049383 * 2 ^ 59
def prefixEnd_2049383 : Nat := 4983230072969 + 3 ^ 40 * 2049383 * 2
def baseEnd_2049383 : Nat := 4330528905980495939455

theorem tailTrace_2049383 : CollatzResearch.WordTrace tailWord_2049383 prefixEnd_2049383 4330528905980495939455 := by
  unfold tailWord_2049383
  simp only [CollatzResearch.WordTrace]
  refine ⟨74747138734442872596048803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49831425822961915064032535 74747138734442872596048803)
  ·
    refine ⟨112120708101664308894073205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74747138734442872596048803 112120708101664308894073205)
    ·
      refine ⟨10511316384531028958819363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 112120708101664308894073205 10511316384531028958819363)
      ·
        refine ⟨15766974576796543438229045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10511316384531028958819363 15766974576796543438229045)
        ·
          refine ⟨1478153866574675947333973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15766974576796543438229045 1478153866574675947333973)
          ·
            refine ⟨4330528905980495939455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1478153866574675947333973 4330528905980495939455)
            ·
              rfl

theorem cell23_2049383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 10].length) (baseStart_2049383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2049383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2049383 prefixEnd_2049383 := by exact prefixLift 2049383
  have htrace : WordTrace (prefixWord ++ tailWord_2049383) baseStart_2049383 baseEnd_2049383 := by
    simpa [prefixWord, tailWord_2049383, baseEnd_2049383] using wordTrace_append hprefix tailTrace_2049383
  have hstable : (prefixWord ++ tailWord_2049383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049383).length < 2 ^ (prefixWord ++ tailWord_2049383).sum := by decide
  have hdescent : baseEnd_2049383 < baseStart_2049383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049394 : List Nat := [3, 2, 1, 2, 1, 2, 3, 4, 1, 2, 2]
def baseStart_2049394 : Nat := 118140960795 + 2049394 * 2 ^ 59
def prefixEnd_2049394 : Nat := 4983230072969 + 3 ^ 40 * 2049394 * 2
def baseEnd_2049394 : Nat := 1052324172440459970250015

theorem tailTrace_2049394 : CollatzResearch.WordTrace tailWord_2049394 prefixEnd_2049394 1052324172440459970250015 := by
  unfold tailWord_2049394
  simp only [CollatzResearch.WordTrace]
  refine ⟨18686884984350755368674809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49831693291602014316466157 18686884984350755368674809)
  ·
    refine ⟨14015163738263066526506107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18686884984350755368674809 14015163738263066526506107)
    ·
      refine ⟨21022745607394599789759161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14015163738263066526506107 21022745607394599789759161)
      ·
        refine ⟨15767059205545949842319371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21022745607394599789759161 15767059205545949842319371)
        ·
          refine ⟨23650588808318924763479057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15767059205545949842319371 23650588808318924763479057)
          ·
            refine ⟨17737941606239193572609293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23650588808318924763479057 17737941606239193572609293)
            ·
              refine ⟨6651728102339697589728485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17737941606239193572609293 6651728102339697589728485)
              ·
                refine ⟨1247199019188693298074091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6651728102339697589728485 1247199019188693298074091)
                ·
                  refine ⟨1870798528783039947111137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1247199019188693298074091 1870798528783039947111137)
                  ·
                    refine ⟨1403098896587279960333353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1870798528783039947111137 1403098896587279960333353)
                    ·
                      refine ⟨1052324172440459970250015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1403098896587279960333353 1052324172440459970250015)
                      ·
                        rfl

theorem cell23_2049394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 4, 1, 2, 2].length) (baseStart_2049394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2049394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2049394 prefixEnd_2049394 := by exact prefixLift 2049394
  have htrace : WordTrace (prefixWord ++ tailWord_2049394) baseStart_2049394 baseEnd_2049394 := by
    simpa [prefixWord, tailWord_2049394, baseEnd_2049394] using wordTrace_append hprefix tailTrace_2049394
  have hstable : (prefixWord ++ tailWord_2049394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049394).length < 2 ^ (prefixWord ++ tailWord_2049394).sum := by decide
  have hdescent : baseEnd_2049394 < baseStart_2049394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049420 : List Nat := [2, 2, 1, 2, 1, 3, 1, 3, 3, 3, 2]
def baseStart_2049420 : Nat := 118140960795 + 2049420 * 2 ^ 59
def prefixEnd_2049420 : Nat := 4983230072969 + 3 ^ 40 * 2049420 * 2
def baseEnd_2049420 : Nat := 1052337522937476868524895

theorem tailTrace_2049420 : CollatzResearch.WordTrace tailWord_2049420 prefixEnd_2049420 1052337522937476868524895 := by
  unfold tailWord_2049420
  simp only [CollatzResearch.WordTrace]
  refine ⟨37374244117654413957572857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49832325490205885276763809 37374244117654413957572857)
  ·
    refine ⟨28030683088240810468179643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37374244117654413957572857 28030683088240810468179643)
    ·
      refine ⟨42046024632361215702269465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28030683088240810468179643 42046024632361215702269465)
      ·
        refine ⟨31534518474270911776702099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42046024632361215702269465 31534518474270911776702099)
        ·
          refine ⟨47301777711406367665053149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31534518474270911776702099 47301777711406367665053149)
          ·
            refine ⟨17738166641777387874394931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47301777711406367665053149 17738166641777387874394931)
            ·
              refine ⟨26607249962666081811592397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17738166641777387874394931 26607249962666081811592397)
              ·
                refine ⟨9977718735999780679347149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26607249962666081811592397 9977718735999780679347149)
                ·
                  refine ⟨3741644525999917754755181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9977718735999780679347149 3741644525999917754755181)
                  ·
                    refine ⟨1403116697249969158033193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3741644525999917754755181 1403116697249969158033193)
                    ·
                      refine ⟨1052337522937476868524895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1403116697249969158033193 1052337522937476868524895)
                      ·
                        rfl

theorem cell23_2049420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 3, 3, 2].length) (baseStart_2049420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2049420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2049420 prefixEnd_2049420 := by exact prefixLift 2049420
  have htrace : WordTrace (prefixWord ++ tailWord_2049420) baseStart_2049420 baseEnd_2049420 := by
    simpa [prefixWord, tailWord_2049420, baseEnd_2049420] using wordTrace_append hprefix tailTrace_2049420
  have hstable : (prefixWord ++ tailWord_2049420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049420).length < 2 ^ (prefixWord ++ tailWord_2049420).sum := by decide
  have hdescent : baseEnd_2049420 < baseStart_2049420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049463 : List Nat := [1, 1, 3, 1, 3, 2, 1, 3, 2, 2, 4]
def baseStart_2049463 : Nat := 118140960795 + 2049463 * 2 ^ 59
def prefixEnd_2049463 : Nat := 4983230072969 + 3 ^ 40 * 2049463 * 2
def baseEnd_2049463 : Nat := 1052359602605620200287197

theorem tailTrace_2049463 : CollatzResearch.WordTrace tailWord_2049463 prefixEnd_2049463 1052359602605620200287197 := by
  unfold tailWord_2049463
  simp only [CollatzResearch.WordTrace]
  refine ⟨74750056574153046258961043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49833371049435364172640695 74750056574153046258961043)
  ·
    refine ⟨112125084861229569388441565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74750056574153046258961043 112125084861229569388441565)
    ·
      refine ⟨42046906822961088520665587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112125084861229569388441565 42046906822961088520665587)
      ·
        refine ⟨63070360234441632780998381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42046906822961088520665587 63070360234441632780998381)
        ·
          refine ⟨23651385087915612292874393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63070360234441632780998381 23651385087915612292874393)
          ·
            refine ⟨17738538815936709219655795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23651385087915612292874393 17738538815936709219655795)
            ·
              refine ⟨26607808223905063829483693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17738538815936709219655795 26607808223905063829483693)
              ·
                refine ⟨9977928083964398936056385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26607808223905063829483693 9977928083964398936056385)
                ·
                  refine ⟨7483446062973299202042289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9977928083964398936056385 7483446062973299202042289)
                  ·
                    refine ⟨5612584547229974401531717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7483446062973299202042289 5612584547229974401531717)
                    ·
                      refine ⟨1052359602605620200287197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5612584547229974401531717 1052359602605620200287197)
                      ·
                        rfl

theorem cell23_2049463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 2, 4].length) (baseStart_2049463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2049463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2049463 prefixEnd_2049463 := by exact prefixLift 2049463
  have htrace : WordTrace (prefixWord ++ tailWord_2049463) baseStart_2049463 baseEnd_2049463 := by
    simpa [prefixWord, tailWord_2049463, baseEnd_2049463] using wordTrace_append hprefix tailTrace_2049463
  have hstable : (prefixWord ++ tailWord_2049463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049463).length < 2 ^ (prefixWord ++ tailWord_2049463).sum := by decide
  have hdescent : baseEnd_2049463 < baseStart_2049463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049483 : List Nat := [1, 1, 1, 1, 3, 3, 2, 2, 1, 5, 3]
def baseStart_2049483 : Nat := 118140960795 + 2049483 * 2 ^ 59
def prefixEnd_2049483 : Nat := 4983230072969 + 3 ^ 40 * 2049483 * 2
def baseEnd_2049483 : Nat := 1052369872218710122037105

theorem tailTrace_2049483 : CollatzResearch.WordTrace tailWord_2049483 prefixEnd_2049483 1052369872218710122037105 := by
  unfold tailWord_2049483
  simp only [CollatzResearch.WordTrace]
  refine ⟨74750786034080589674689103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49833857356053726449792735 74750786034080589674689103)
  ·
    refine ⟨112126179051120884512033655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74750786034080589674689103 112126179051120884512033655)
    ·
      refine ⟨168189268576681326768050483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112126179051120884512033655 168189268576681326768050483)
      ·
        refine ⟨252283902865021990152075725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168189268576681326768050483 252283902865021990152075725)
        ·
          refine ⟨94606463574383246307028397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252283902865021990152075725 94606463574383246307028397)
          ·
            refine ⟨35477423840393717365135649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94606463574383246307028397 35477423840393717365135649)
            ·
              refine ⟨26608067880295288023851737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35477423840393717365135649 26608067880295288023851737)
              ·
                refine ⟨19956050910221466017888803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26608067880295288023851737 19956050910221466017888803)
                ·
                  refine ⟨29934076365332199026833205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19956050910221466017888803 29934076365332199026833205)
                  ·
                    refine ⟨2806319659249893658765613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29934076365332199026833205 2806319659249893658765613)
                    ·
                      refine ⟨1052369872218710122037105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2806319659249893658765613 1052369872218710122037105)
                      ·
                        rfl

theorem cell23_2049483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 5, 3].length) (baseStart_2049483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2049483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2049483 prefixEnd_2049483 := by exact prefixLift 2049483
  have htrace : WordTrace (prefixWord ++ tailWord_2049483) baseStart_2049483 baseEnd_2049483 := by
    simpa [prefixWord, tailWord_2049483, baseEnd_2049483] using wordTrace_append hprefix tailTrace_2049483
  have hstable : (prefixWord ++ tailWord_2049483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049483).length < 2 ^ (prefixWord ++ tailWord_2049483).sum := by decide
  have hdescent : baseEnd_2049483 < baseStart_2049483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049523 : List Nat := [1, 1, 1, 2, 2, 2, 2, 4, 1, 3, 4]
def baseStart_2049523 : Nat := 118140960795 + 2049523 * 2 ^ 59
def prefixEnd_2049523 : Nat := 4983230072969 + 3 ^ 40 * 2049523 * 2
def baseEnd_2049523 : Nat := 1052390411444889965536921

theorem tailTrace_2049523 : CollatzResearch.WordTrace tailWord_2049523 prefixEnd_2049523 1052390411444889965536921 := by
  unfold tailWord_2049523
  simp only [CollatzResearch.WordTrace]
  refine ⟨74752244953935676506145223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49834829969290451004096815 74752244953935676506145223)
  ·
    refine ⟨112128367430903514759217835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74752244953935676506145223 112128367430903514759217835)
    ·
      refine ⟨168192551146355272138826753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112128367430903514759217835 168192551146355272138826753)
      ·
        refine ⟨126144413359766454104120065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168192551146355272138826753 126144413359766454104120065)
        ·
          refine ⟨94608310019824840578090049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126144413359766454104120065 94608310019824840578090049)
          ·
            refine ⟨70956232514868630433567537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94608310019824840578090049 70956232514868630433567537)
            ·
              refine ⟨53217174386151472825175653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70956232514868630433567537 53217174386151472825175653)
              ·
                refine ⟨9978220197403401154720435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53217174386151472825175653 9978220197403401154720435)
                ·
                  refine ⟨14967330296105101732080653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9978220197403401154720435 14967330296105101732080653)
                  ·
                    refine ⟨5612748861039413149530245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14967330296105101732080653 5612748861039413149530245)
                    ·
                      refine ⟨1052390411444889965536921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5612748861039413149530245 1052390411444889965536921)
                      ·
                        rfl

theorem cell23_2049523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 3, 4].length) (baseStart_2049523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2049523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2049523 prefixEnd_2049523 := by exact prefixLift 2049523
  have htrace : WordTrace (prefixWord ++ tailWord_2049523) baseStart_2049523 baseEnd_2049523 := by
    simpa [prefixWord, tailWord_2049523, baseEnd_2049523] using wordTrace_append hprefix tailTrace_2049523
  have hstable : (prefixWord ++ tailWord_2049523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049523).length < 2 ^ (prefixWord ++ tailWord_2049523).sum := by decide
  have hdescent : baseEnd_2049523 < baseStart_2049523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049537 : List Nat := [1, 2, 4, 1, 4, 1, 2, 1, 2, 5]
def baseStart_2049537 : Nat := 118140960795 + 2049537 * 2 ^ 59
def prefixEnd_2049537 : Nat := 4983230072969 + 3 ^ 40 * 2049537 * 2
def baseEnd_2049537 : Nat := 350799200058017636920619

theorem tailTrace_2049537 : CollatzResearch.WordTrace tailWord_2049537 prefixEnd_2049537 350799200058017636920619 := by
  unfold tailWord_2049537
  simp only [CollatzResearch.WordTrace]
  refine ⟨74752755575884956897154865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49835170383923304598103243 74752755575884956897154865)
  ·
    refine ⟨56064566681913717672866149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74752755575884956897154865 56064566681913717672866149)
    ·
      refine ⟨10512106252858822063662403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56064566681913717672866149 10512106252858822063662403)
      ·
        refine ⟨15768159379288233095493605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10512106252858822063662403 15768159379288233095493605)
        ·
          refine ⟨2956529883616543705405051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15768159379288233095493605 2956529883616543705405051)
          ·
            refine ⟨4434794825424815558107577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2956529883616543705405051 4434794825424815558107577)
            ·
              refine ⟨3326096119068611668580683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4434794825424815558107577 3326096119068611668580683)
              ·
                refine ⟨4989144178602917502871025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3326096119068611668580683 4989144178602917502871025)
                ·
                  refine ⟨3741858133952188127153269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4989144178602917502871025 3741858133952188127153269)
                  ·
                    refine ⟨350799200058017636920619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3741858133952188127153269 350799200058017636920619)
                    ·
                      rfl

theorem cell23_2049537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_2049537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2049537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2049537 prefixEnd_2049537 := by exact prefixLift 2049537
  have htrace : WordTrace (prefixWord ++ tailWord_2049537) baseStart_2049537 baseEnd_2049537 := by
    simpa [prefixWord, tailWord_2049537, baseEnd_2049537] using wordTrace_append hprefix tailTrace_2049537
  have hstable : (prefixWord ++ tailWord_2049537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049537).length < 2 ^ (prefixWord ++ tailWord_2049537).sum := by decide
  have hdescent : baseEnd_2049537 < baseStart_2049537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049553 : List Nat := [1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 6]
def baseStart_2049553 : Nat := 118140960795 + 2049553 * 2 ^ 59
def prefixEnd_2049553 : Nat := 4983230072969 + 3 ^ 40 * 2049553 * 2
def baseEnd_2049553 : Nat := 1052405815864524848161783

theorem tailTrace_2049553 : CollatzResearch.WordTrace tailWord_2049553 prefixEnd_2049553 1052405815864524848161783 := by
  unfold tailWord_2049553
  simp only [CollatzResearch.WordTrace]
  refine ⟨74753339143826991629737313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49835559429217994419824875 74753339143826991629737313)
  ·
    refine ⟨56065004357870243722302985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74753339143826991629737313 56065004357870243722302985)
    ·
      refine ⟨42048753268402682791727239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56065004357870243722302985 42048753268402682791727239)
      ·
        refine ⟨63073129902604024187590859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42048753268402682791727239 63073129902604024187590859)
        ·
          refine ⟨94609694853906036281386289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63073129902604024187590859 94609694853906036281386289)
          ·
            refine ⟨70957271140429527211039717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94609694853906036281386289 70957271140429527211039717)
            ·
              refine ⟨13304488338830536352069947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70957271140429527211039717 13304488338830536352069947)
              ·
                refine ⟨19956732508245804528104921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13304488338830536352069947 19956732508245804528104921)
                ·
                  refine ⟨14967549381184353396078691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19956732508245804528104921 14967549381184353396078691)
                  ·
                    refine ⟨22451324071776530094118037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14967549381184353396078691 22451324071776530094118037)
                    ·
                      refine ⟨1052405815864524848161783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22451324071776530094118037 1052405815864524848161783)
                      ·
                        rfl

theorem cell23_2049553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 6].length) (baseStart_2049553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2049553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2049553 prefixEnd_2049553 := by exact prefixLift 2049553
  have htrace : WordTrace (prefixWord ++ tailWord_2049553) baseStart_2049553 baseEnd_2049553 := by
    simpa [prefixWord, tailWord_2049553, baseEnd_2049553] using wordTrace_append hprefix tailTrace_2049553
  have hstable : (prefixWord ++ tailWord_2049553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049553).length < 2 ^ (prefixWord ++ tailWord_2049553).sum := by decide
  have hdescent : baseEnd_2049553 < baseStart_2049553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049603 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 5]
def baseStart_2049603 : Nat := 118140960795 + 2049603 * 2 ^ 59
def prefixEnd_2049603 : Nat := 4983230072969 + 3 ^ 40 * 2049603 * 2
def baseEnd_2049603 : Nat := 1052431489897249652536553

theorem tailTrace_2049603 : CollatzResearch.WordTrace tailWord_2049603 prefixEnd_2049603 1052431489897249652536553 := by
  unfold tailWord_2049603
  simp only [CollatzResearch.WordTrace]
  refine ⟨74755162793645850169057463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49836775195763900112704975 74755162793645850169057463)
  ·
    refine ⟨112132744190468775253586195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74755162793645850169057463 112132744190468775253586195)
    ·
      refine ⟨168199116285703162880379293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112132744190468775253586195 168199116285703162880379293)
      ·
        refine ⟨63074668607138686080142235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168199116285703162880379293 63074668607138686080142235)
        ·
          refine ⟨94612002910708029120213353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63074668607138686080142235 94612002910708029120213353)
          ·
            refine ⟨70959002183031021840160015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94612002910708029120213353 70959002183031021840160015)
            ·
              refine ⟨106438503274546532760240023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70959002183031021840160015 106438503274546532760240023)
              ·
                refine ⟨159657754911819799140360035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106438503274546532760240023 159657754911819799140360035)
                ·
                  refine ⟨239486632367729698710540053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159657754911819799140360035 239486632367729698710540053)
                  ·
                    refine ⟨11225935892237329627056565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 239486632367729698710540053 11225935892237329627056565)
                    ·
                      refine ⟨1052431489897249652536553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11225935892237329627056565 1052431489897249652536553)
                      ·
                        rfl

theorem cell23_2049603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 5].length) (baseStart_2049603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2049603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2049603 prefixEnd_2049603 := by exact prefixLift 2049603
  have htrace : WordTrace (prefixWord ++ tailWord_2049603) baseStart_2049603 baseEnd_2049603 := by
    simpa [prefixWord, tailWord_2049603, baseEnd_2049603] using wordTrace_append hprefix tailTrace_2049603
  have hstable : (prefixWord ++ tailWord_2049603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049603).length < 2 ^ (prefixWord ++ tailWord_2049603).sum := by decide
  have hdescent : baseEnd_2049603 < baseStart_2049603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049617 : List Nat := [1, 2, 2, 1, 3, 2, 2, 1, 4, 3, 2]
def baseStart_2049617 : Nat := 118140960795 + 2049617 * 2 ^ 59
def prefixEnd_2049617 : Nat := 4983230072969 + 3 ^ 40 * 2049617 * 2
def baseEnd_2049617 : Nat := 1052438678626412597761489

theorem tailTrace_2049617 : CollatzResearch.WordTrace tailWord_2049617 prefixEnd_2049617 1052438678626412597761489 := by
  unfold tailWord_2049617
  simp only [CollatzResearch.WordTrace]
  refine ⟨74755673415595130560067105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49837115610396753706711403 74755673415595130560067105)
  ·
    refine ⟨56066755061696347920050329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74755673415595130560067105 56066755061696347920050329)
    ·
      refine ⟨42050066296272260940037747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56066755061696347920050329 42050066296272260940037747)
      ·
        refine ⟨63075099444408391410056621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42050066296272260940037747 63075099444408391410056621)
        ·
          refine ⟨23653162291653146778771233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63075099444408391410056621 23653162291653146778771233)
          ·
            refine ⟨17739871718739860084078425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23653162291653146778771233 17739871718739860084078425)
            ·
              refine ⟨13304903789054895063058819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17739871718739860084078425 13304903789054895063058819)
              ·
                refine ⟨19957355683582342594588229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13304903789054895063058819 19957355683582342594588229)
                ·
                  refine ⟨3742004190671689236485293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19957355683582342594588229 3742004190671689236485293)
                  ·
                    refine ⟨1403251571501883463681985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3742004190671689236485293 1403251571501883463681985)
                    ·
                      refine ⟨1052438678626412597761489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1403251571501883463681985 1052438678626412597761489)
                      ·
                        rfl

theorem cell23_2049617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 4, 3, 2].length) (baseStart_2049617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2049617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2049617 prefixEnd_2049617 := by exact prefixLift 2049617
  have htrace : WordTrace (prefixWord ++ tailWord_2049617) baseStart_2049617 baseEnd_2049617 := by
    simpa [prefixWord, tailWord_2049617, baseEnd_2049617] using wordTrace_append hprefix tailTrace_2049617
  have hstable : (prefixWord ++ tailWord_2049617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049617).length < 2 ^ (prefixWord ++ tailWord_2049617).sum := by decide
  have hdescent : baseEnd_2049617 < baseStart_2049617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049660 : List Nat := [2, 2, 2, 1, 1, 2, 1, 3, 3, 2, 4]
def baseStart_2049660 : Nat := 118140960795 + 2049660 * 2 ^ 59
def prefixEnd_2049660 : Nat := 4983230072969 + 3 ^ 40 * 2049660 * 2
def baseEnd_2049660 : Nat := 1052460758294555929523791

theorem tailTrace_2049660 : CollatzResearch.WordTrace tailWord_2049660 prefixEnd_2049660 1052460758294555929523791 := by
  unfold tailWord_2049660
  simp only [CollatzResearch.WordTrace]
  refine ⟨37378620877219674451941217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49838161169626232602588289 37378620877219674451941217)
  ·
    refine ⟨28033965657914755838955913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37378620877219674451941217 28033965657914755838955913)
    ·
      refine ⟨21025474243436066879216935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28033965657914755838955913 21025474243436066879216935)
      ·
        refine ⟨31538211365154100318825403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21025474243436066879216935 31538211365154100318825403)
        ·
          refine ⟨47307317047731150478238105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31538211365154100318825403 47307317047731150478238105)
          ·
            refine ⟨35480487785798362858678579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47307317047731150478238105 35480487785798362858678579)
            ·
              refine ⟨53220731678697544288017869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35480487785798362858678579 53220731678697544288017869)
              ·
                refine ⟨19957774379511579108006701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53220731678697544288017869 19957774379511579108006701)
                ·
                  refine ⟨7484165392316842165502513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19957774379511579108006701 7484165392316842165502513)
                  ·
                    refine ⟨5613124044237631624126885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7484165392316842165502513 5613124044237631624126885)
                    ·
                      refine ⟨1052460758294555929523791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5613124044237631624126885 1052460758294555929523791)
                      ·
                        rfl

theorem cell23_2049660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_2049660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2049660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2049660 prefixEnd_2049660 := by exact prefixLift 2049660
  have htrace : WordTrace (prefixWord ++ tailWord_2049660) baseStart_2049660 baseEnd_2049660 := by
    simpa [prefixWord, tailWord_2049660, baseEnd_2049660] using wordTrace_append hprefix tailTrace_2049660
  have hstable : (prefixWord ++ tailWord_2049660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049660).length < 2 ^ (prefixWord ++ tailWord_2049660).sum := by decide
  have hdescent : baseEnd_2049660 < baseStart_2049660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049698 : List Nat := [3, 3, 1, 4, 1, 2, 1, 2, 1, 1, 4]
def baseStart_2049698 : Nat := 118140960795 + 2049698 * 2 ^ 59
def prefixEnd_2049698 : Nat := 4983230072969 + 3 ^ 40 * 2049698 * 2
def baseEnd_2049698 : Nat := 1052480270559426780848617

theorem tailTrace_2049698 : CollatzResearch.WordTrace tailWord_2049698 prefixEnd_2049698 1052480270559426780848617 := by
  unfold tailWord_2049698
  simp only [CollatzResearch.WordTrace]
  refine ⟨18689656932075420348441437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49839085152201120929177165 18689656932075420348441437)
  ·
    refine ⟨7008621349528282630665539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18689656932075420348441437 7008621349528282630665539)
    ·
      refine ⟨10512932024292423945998309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7008621349528282630665539 10512932024292423945998309)
      ·
        refine ⟨1971174754554829489874683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10512932024292423945998309 1971174754554829489874683)
        ·
          refine ⟨2956762131832244234812025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1971174754554829489874683 2956762131832244234812025)
          ·
            refine ⟨2217571598874183176109019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2956762131832244234812025 2217571598874183176109019)
            ·
              refine ⟨3326357398311274764163529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2217571598874183176109019 3326357398311274764163529)
              ·
                refine ⟨2494768048733456073122647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3326357398311274764163529 2494768048733456073122647)
                ·
                  refine ⟨3742152073100184109683971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2494768048733456073122647 3742152073100184109683971)
                  ·
                    refine ⟨5613228109650276164525957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3742152073100184109683971 5613228109650276164525957)
                    ·
                      refine ⟨1052480270559426780848617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5613228109650276164525957 1052480270559426780848617)
                      ·
                        rfl

theorem cell23_2049698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_2049698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2049698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2049698 prefixEnd_2049698 := by exact prefixLift 2049698
  have htrace : WordTrace (prefixWord ++ tailWord_2049698) baseStart_2049698 baseEnd_2049698 := by
    simpa [prefixWord, tailWord_2049698, baseEnd_2049698] using wordTrace_append hprefix tailTrace_2049698
  have hstable : (prefixWord ++ tailWord_2049698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049698).length < 2 ^ (prefixWord ++ tailWord_2049698).sum := by decide
  have hdescent : baseEnd_2049698 < baseStart_2049698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049720 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 4, 3, 4]
def baseStart_2049720 : Nat := 118140960795 + 2049720 * 2 ^ 59
def prefixEnd_2049720 : Nat := 4983230072969 + 3 ^ 40 * 2049720 * 2
def baseEnd_2049720 : Nat := 1052491567133825694773515

theorem tailTrace_2049720 : CollatzResearch.WordTrace tailWord_2049720 prefixEnd_2049720 1052491567133825694773515 := by
  unfold tailWord_2049720
  simp only [CollatzResearch.WordTrace]
  refine ⟨37379715067110989575533307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49839620089481319434044409 37379715067110989575533307)
  ·
    refine ⟨56069572600666484363299961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37379715067110989575533307 56069572600666484363299961)
    ·
      refine ⟨42052179450499863272474971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56069572600666484363299961 42052179450499863272474971)
      ·
        refine ⟨63078269175749794908712457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42052179450499863272474971 63078269175749794908712457)
        ·
          refine ⟨47308701881812346181534343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63078269175749794908712457 47308701881812346181534343)
          ·
            refine ⟨70963052822718519272301515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47308701881812346181534343 70963052822718519272301515)
            ·
              refine ⟨106444579234077778908452273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70963052822718519272301515 106444579234077778908452273)
              ·
                refine ⟨79833434425558334181339205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106444579234077778908452273 79833434425558334181339205)
                ·
                  refine ⟨14968768954792187659001101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79833434425558334181339205 14968768954792187659001101)
                  ·
                    refine ⟨5613288358047070372125413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14968768954792187659001101 5613288358047070372125413)
                    ·
                      refine ⟨1052491567133825694773515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5613288358047070372125413 1052491567133825694773515)
                      ·
                        rfl

theorem cell23_2049720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 4, 3, 4].length) (baseStart_2049720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2049720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2049720 prefixEnd_2049720 := by exact prefixLift 2049720
  have htrace : WordTrace (prefixWord ++ tailWord_2049720) baseStart_2049720 baseEnd_2049720 := by
    simpa [prefixWord, tailWord_2049720, baseEnd_2049720] using wordTrace_append hprefix tailTrace_2049720
  have hstable : (prefixWord ++ tailWord_2049720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049720).length < 2 ^ (prefixWord ++ tailWord_2049720).sum := by decide
  have hdescent : baseEnd_2049720 < baseStart_2049720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049754 : List Nat := [3, 1, 1, 2, 2, 3, 1, 3, 1, 4, 2]
def baseStart_2049754 : Nat := 118140960795 + 2049754 * 2 ^ 59
def prefixEnd_2049754 : Nat := 4983230072969 + 3 ^ 40 * 2049754 * 2
def baseEnd_2049754 : Nat := 1052509025476078561748359

theorem tailTrace_2049754 : CollatzResearch.WordTrace tailWord_2049754 prefixEnd_2049754 1052509025476078561748359 := by
  unfold tailWord_2049754
  simp only [CollatzResearch.WordTrace]
  refine ⟨18690167554024700739451079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49840446810732535305202877 18690167554024700739451079)
  ·
    refine ⟨28035251331037051109176619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18690167554024700739451079 28035251331037051109176619)
    ·
      refine ⟨42052876996555576663764929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28035251331037051109176619 42052876996555576663764929)
      ·
        refine ⟨31539657747416682497823697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42052876996555576663764929 31539657747416682497823697)
        ·
          refine ⟨23654743310562511873367773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31539657747416682497823697 23654743310562511873367773)
          ·
            refine ⟨8870528741460941952512915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23654743310562511873367773 8870528741460941952512915)
            ·
              refine ⟨13305793112191412928769373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8870528741460941952512915 13305793112191412928769373)
              ·
                refine ⟨4989672417071779848288515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13305793112191412928769373 4989672417071779848288515)
                ·
                  refine ⟨7484508625607669772432773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4989672417071779848288515 7484508625607669772432773)
                  ·
                    refine ⟨1403345367301438082331145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7484508625607669772432773 1403345367301438082331145)
                    ·
                      refine ⟨1052509025476078561748359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1403345367301438082331145 1052509025476078561748359)
                      ·
                        rfl

theorem cell23_2049754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 1, 4, 2].length) (baseStart_2049754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2049754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2049754 prefixEnd_2049754 := by exact prefixLift 2049754
  have htrace : WordTrace (prefixWord ++ tailWord_2049754) baseStart_2049754 baseEnd_2049754 := by
    simpa [prefixWord, tailWord_2049754, baseEnd_2049754] using wordTrace_append hprefix tailTrace_2049754
  have hstable : (prefixWord ++ tailWord_2049754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049754).length < 2 ^ (prefixWord ++ tailWord_2049754).sum := by decide
  have hdescent : baseEnd_2049754 < baseStart_2049754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049760 : List Nat := [2, 1, 1, 3, 1, 2, 3, 1, 9]
def baseStart_2049760 : Nat := 118140960795 + 2049760 * 2 ^ 59
def prefixEnd_2049760 : Nat := 4983230072969 + 3 ^ 40 * 2049760 * 2
def baseEnd_2049760 : Nat := 116945789595556170919259

theorem tailTrace_2049760 : CollatzResearch.WordTrace tailWord_2049760 prefixEnd_2049760 116945789595556170919259 := by
  unfold tailWord_2049760
  simp only [CollatzResearch.WordTrace]
  refine ⟨37380444527038532991261367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49840592702718043988348489 37380444527038532991261367)
  ·
    refine ⟨56070666790557799486892051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37380444527038532991261367 56070666790557799486892051)
    ·
      refine ⟨84106000185836699230338077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56070666790557799486892051 84106000185836699230338077)
      ·
        refine ⟨31539750069688762211376779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84106000185836699230338077 31539750069688762211376779)
        ·
          refine ⟨47309625104533143317065169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31539750069688762211376779 47309625104533143317065169)
          ·
            refine ⟨35482218828399857487798877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47309625104533143317065169 35482218828399857487798877)
            ·
              refine ⟨13305832060649946557924579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35482218828399857487798877 13305832060649946557924579)
              ·
                refine ⟨19958748090974919836886869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13305832060649946557924579 19958748090974919836886869)
                ·
                  refine ⟨116945789595556170919259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 19958748090974919836886869 116945789595556170919259)
                  ·
                    rfl

theorem cell23_2049760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 9].length) (baseStart_2049760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2049760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2049760 prefixEnd_2049760 := by exact prefixLift 2049760
  have htrace : WordTrace (prefixWord ++ tailWord_2049760) baseStart_2049760 baseEnd_2049760 := by
    simpa [prefixWord, tailWord_2049760, baseEnd_2049760] using wordTrace_append hprefix tailTrace_2049760
  have hstable : (prefixWord ++ tailWord_2049760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049760).length < 2 ^ (prefixWord ++ tailWord_2049760).sum := by decide
  have hdescent : baseEnd_2049760 < baseStart_2049760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049794 : List Nat := [3, 4, 1, 1, 1, 1, 4, 1, 7]
def baseStart_2049794 : Nat := 118140960795 + 2049794 * 2 ^ 59
def prefixEnd_2049794 : Nat := 4983230072969 + 3 ^ 40 * 2049794 * 2
def baseEnd_2049794 : Nat := 116947729411362045027575

theorem tailTrace_2049794 : CollatzResearch.WordTrace tailWord_2049794 prefixEnd_2049794 116947729411362045027575 := by
  unfold tailWord_2049794
  simp only [CollatzResearch.WordTrace]
  refine ⟨18690532283988472447315109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49841419423969259859506957 18690532283988472447315109)
  ·
    refine ⟨3504474803247838583871583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18690532283988472447315109 3504474803247838583871583)
    ·
      refine ⟨5256712204871757875807375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3504474803247838583871583 5256712204871757875807375)
      ·
        refine ⟨7885068307307636813711063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5256712204871757875807375 7885068307307636813711063)
        ·
          refine ⟨11827602460961455220566595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7885068307307636813711063 11827602460961455220566595)
          ·
            refine ⟨17741403691442182830849893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11827602460961455220566595 17741403691442182830849893)
            ·
              refine ⟨3326513192145409280784355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17741403691442182830849893 3326513192145409280784355)
              ·
                refine ⟨4989769788218113921176533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3326513192145409280784355 4989769788218113921176533)
                ·
                  refine ⟨116947729411362045027575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4989769788218113921176533 116947729411362045027575)
                  ·
                    rfl

theorem cell23_2049794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_2049794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2049794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2049794 prefixEnd_2049794 := by exact prefixLift 2049794
  have htrace : WordTrace (prefixWord ++ tailWord_2049794) baseStart_2049794 baseEnd_2049794 := by
    simpa [prefixWord, tailWord_2049794, baseEnd_2049794] using wordTrace_append hprefix tailTrace_2049794
  have hstable : (prefixWord ++ tailWord_2049794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049794).length < 2 ^ (prefixWord ++ tailWord_2049794).sum := by decide
  have hdescent : baseEnd_2049794 < baseStart_2049794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049827 : List Nat := [1, 1, 1, 4, 2, 1, 4, 1, 1, 3, 4]
def baseStart_2049827 : Nat := 118140960795 + 2049827 * 2 ^ 59
def prefixEnd_2049827 : Nat := 4983230072969 + 3 ^ 40 * 2049827 * 2
def baseEnd_2049827 : Nat := 1052546509563856776135523

theorem tailTrace_2049827 : CollatzResearch.WordTrace tailWord_2049827 prefixEnd_2049827 1052546509563856776135523 := by
  unfold tailWord_2049827
  simp only [CollatzResearch.WordTrace]
  refine ⟨74763332744834336425211735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49842221829889557616807823 74763332744834336425211735)
  ·
    refine ⟨112144999117251504637817603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74763332744834336425211735 112144999117251504637817603)
    ·
      refine ⟨168217498675877256956726405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112144999117251504637817603 168217498675877256956726405)
      ·
        refine ⟨31540781001726985679386201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168217498675877256956726405 31540781001726985679386201)
        ·
          refine ⟨23655585751295239259539651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31540781001726985679386201 23655585751295239259539651)
          ·
            refine ⟨35483378626942858889309477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23655585751295239259539651 35483378626942858889309477)
            ·
              refine ⟨6653133492551786041745527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35483378626942858889309477 6653133492551786041745527)
              ·
                refine ⟨9979700238827679062618291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6653133492551786041745527 9979700238827679062618291)
                ·
                  refine ⟨14969550358241518593927437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9979700238827679062618291 14969550358241518593927437)
                  ·
                    refine ⟨5613581384340569472722789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14969550358241518593927437 5613581384340569472722789)
                    ·
                      refine ⟨1052546509563856776135523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5613581384340569472722789 1052546509563856776135523)
                      ·
                        rfl

theorem cell23_2049827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_2049827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2049827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2049827 prefixEnd_2049827 := by exact prefixLift 2049827
  have htrace : WordTrace (prefixWord ++ tailWord_2049827) baseStart_2049827 baseEnd_2049827 := by
    simpa [prefixWord, tailWord_2049827, baseEnd_2049827] using wordTrace_append hprefix tailTrace_2049827
  have hstable : (prefixWord ++ tailWord_2049827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049827).length < 2 ^ (prefixWord ++ tailWord_2049827).sum := by decide
  have hdescent : baseEnd_2049827 < baseStart_2049827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049847 : List Nat := [1, 1, 3, 1, 2, 1, 2, 2, 3, 4, 3]
def baseStart_2049847 : Nat := 118140960795 + 2049847 * 2 ^ 59
def prefixEnd_2049847 : Nat := 4983230072969 + 3 ^ 40 * 2049847 * 2
def baseEnd_2049847 : Nat := 1052556779176946697885431

theorem tailTrace_2049847 : CollatzResearch.WordTrace tailWord_2049847 prefixEnd_2049847 1052556779176946697885431 := by
  unfold tailWord_2049847
  simp only [CollatzResearch.WordTrace]
  refine ⟨74764062204761879840939795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49842708136507919893959863 74764062204761879840939795)
  ·
    refine ⟨112146093307142819761409693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74764062204761879840939795 112146093307142819761409693)
    ·
      refine ⟨42054784990178557410528635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112146093307142819761409693 42054784990178557410528635)
      ·
        refine ⟨63082177485267836115792953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42054784990178557410528635 63082177485267836115792953)
        ·
          refine ⟨47311633113950877086844715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63082177485267836115792953 47311633113950877086844715)
          ·
            refine ⟨70967449670926315630267073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47311633113950877086844715 70967449670926315630267073)
            ·
              refine ⟨53225587253194736722700305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70967449670926315630267073 53225587253194736722700305)
              ·
                refine ⟨39919190439896052542025229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53225587253194736722700305 39919190439896052542025229)
                ·
                  refine ⟨14969696414961019703259461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39919190439896052542025229 14969696414961019703259461)
                  ·
                    refine ⟨2806818077805191194361149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14969696414961019703259461 2806818077805191194361149)
                    ·
                      refine ⟨1052556779176946697885431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2806818077805191194361149 1052556779176946697885431)
                      ·
                        rfl

theorem cell23_2049847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 4, 3].length) (baseStart_2049847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2049847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2049847 prefixEnd_2049847 := by exact prefixLift 2049847
  have htrace : WordTrace (prefixWord ++ tailWord_2049847) baseStart_2049847 baseEnd_2049847 := by
    simpa [prefixWord, tailWord_2049847, baseEnd_2049847] using wordTrace_append hprefix tailTrace_2049847
  have hstable : (prefixWord ++ tailWord_2049847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049847).length < 2 ^ (prefixWord ++ tailWord_2049847).sum := by decide
  have hdescent : baseEnd_2049847 < baseStart_2049847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049904 : List Nat := [2, 1, 1, 1, 4, 1, 1, 2, 3, 5, 2]
def baseStart_2049904 : Nat := 118140960795 + 2049904 * 2 ^ 59
def prefixEnd_2049904 : Nat := 4983230072969 + 3 ^ 40 * 2049904 * 2
def baseEnd_2049904 : Nat := 1052586047574252974872669

theorem tailTrace_2049904 : CollatzResearch.WordTrace tailWord_2049904 prefixEnd_2049904 1052586047574252974872669 := by
  unfold tailWord_2049904
  simp only [CollatzResearch.WordTrace]
  refine ⟨37383070582777689287882383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49844094110370252383843177 37383070582777689287882383)
  ·
    refine ⟨56074605874166533931823575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37383070582777689287882383 56074605874166533931823575)
    ·
      refine ⟨84111908811249800897735363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56074605874166533931823575 84111908811249800897735363)
      ·
        refine ⟨126167863216874701346603045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84111908811249800897735363 126167863216874701346603045)
        ·
          refine ⟨23656474353164006502488071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126167863216874701346603045 23656474353164006502488071)
          ·
            refine ⟨35484711529746009753732107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23656474353164006502488071 35484711529746009753732107)
            ·
              refine ⟨53227067294619014630598161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35484711529746009753732107 53227067294619014630598161)
              ·
                refine ⟨39920300470964260972948621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53227067294619014630598161 39920300470964260972948621)
                ·
                  refine ⟨14970112676611597864855733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39920300470964260972948621 14970112676611597864855733)
                  ·
                    refine ⟨1403448063432337299830225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14970112676611597864855733 1403448063432337299830225)
                    ·
                      refine ⟨1052586047574252974872669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1403448063432337299830225 1052586047574252974872669)
                      ·
                        rfl

theorem cell23_2049904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 3, 5, 2].length) (baseStart_2049904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2049904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2049904 prefixEnd_2049904 := by exact prefixLift 2049904
  have htrace : WordTrace (prefixWord ++ tailWord_2049904) baseStart_2049904 baseEnd_2049904 := by
    simpa [prefixWord, tailWord_2049904, baseEnd_2049904] using wordTrace_append hprefix tailTrace_2049904
  have hstable : (prefixWord ++ tailWord_2049904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049904).length < 2 ^ (prefixWord ++ tailWord_2049904).sum := by decide
  have hdescent : baseEnd_2049904 < baseStart_2049904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049928 : List Nat := [2, 1, 3, 3, 3, 1, 1, 2, 3, 1, 3]
def baseStart_2049928 : Nat := 118140960795 + 2049928 * 2 ^ 59
def prefixEnd_2049928 : Nat := 4983230072969 + 3 ^ 40 * 2049928 * 2
def baseEnd_2049928 : Nat := 1052598371109960880972559

theorem tailTrace_2049928 : CollatzResearch.WordTrace tailWord_2049928 prefixEnd_2049928 1052598371109960880972559 := by
  unfold tailWord_2049928
  simp only [CollatzResearch.WordTrace]
  refine ⟨37383508258734215337319219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49844677678312287116425625 37383508258734215337319219)
  ·
    refine ⟨56075262388101323005978829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37383508258734215337319219 56075262388101323005978829)
    ·
      refine ⟨21028223395537996127242061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56075262388101323005978829 21028223395537996127242061)
      ·
        refine ⟨7885583773326748547715773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21028223395537996127242061 7885583773326748547715773)
        ·
          refine ⟨2957093914997530705393415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7885583773326748547715773 2957093914997530705393415)
          ·
            refine ⟨4435640872496296058090123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2957093914997530705393415 4435640872496296058090123)
            ·
              refine ⟨6653461308744444087135185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4435640872496296058090123 6653461308744444087135185)
              ·
                refine ⟨4990095981558333065351389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6653461308744444087135185 4990095981558333065351389)
                ·
                  refine ⟨1871285993084374899506771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4990095981558333065351389 1871285993084374899506771)
                  ·
                    refine ⟨2806928989626562349260157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1871285993084374899506771 2806928989626562349260157)
                    ·
                      refine ⟨1052598371109960880972559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2806928989626562349260157 1052598371109960880972559)
                      ·
                        rfl

theorem cell23_2049928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_2049928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2049928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2049928 prefixEnd_2049928 := by exact prefixLift 2049928
  have htrace : WordTrace (prefixWord ++ tailWord_2049928) baseStart_2049928 baseEnd_2049928 := by
    simpa [prefixWord, tailWord_2049928, baseEnd_2049928] using wordTrace_append hprefix tailTrace_2049928
  have hstable : (prefixWord ++ tailWord_2049928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049928).length < 2 ^ (prefixWord ++ tailWord_2049928).sum := by decide
  have hdescent : baseEnd_2049928 < baseStart_2049928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049938 : List Nat := [3, 2, 3, 2, 1, 2, 1, 1, 1, 5, 2]
def baseStart_2049938 : Nat := 118140960795 + 2049938 * 2 ^ 59
def prefixEnd_2049938 : Nat := 4983230072969 + 3 ^ 40 * 2049938 * 2
def baseEnd_2049938 : Nat := 1052603505916505841847513

theorem tailTrace_2049938 : CollatzResearch.WordTrace tailWord_2049938 prefixEnd_2049938 1052603505916505841847513 := by
  unfold tailWord_2049938
  simp only [CollatzResearch.WordTrace]
  refine ⟨18691845311858050595625617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49844920831621468255001645 18691845311858050595625617)
  ·
    refine ⟨14018883983893537946719213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18691845311858050595625617 14018883983893537946719213)
    ·
      refine ⟨5257081493960076730019705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14018883983893537946719213 5257081493960076730019705)
      ·
        refine ⟨3942811120470057547514779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5257081493960076730019705 3942811120470057547514779)
        ·
          refine ⟨5914216680705086321272169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3942811120470057547514779 5914216680705086321272169)
          ·
            refine ⟨4435662510528814740954127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5914216680705086321272169 4435662510528814740954127)
            ·
              refine ⟨6653493765793222111431191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4435662510528814740954127 6653493765793222111431191)
              ·
                refine ⟨9980240648689833167146787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6653493765793222111431191 9980240648689833167146787)
                ·
                  refine ⟨14970360973034749750720181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9980240648689833167146787 14970360973034749750720181)
                  ·
                    refine ⟨1403471341222007789130017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14970360973034749750720181 1403471341222007789130017)
                    ·
                      refine ⟨1052603505916505841847513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1403471341222007789130017 1052603505916505841847513)
                      ·
                        rfl

theorem cell23_2049938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_2049938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2049938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2049938 prefixEnd_2049938 := by exact prefixLift 2049938
  have htrace : WordTrace (prefixWord ++ tailWord_2049938) baseStart_2049938 baseEnd_2049938 := by
    simpa [prefixWord, tailWord_2049938, baseEnd_2049938] using wordTrace_append hprefix tailTrace_2049938
  have hstable : (prefixWord ++ tailWord_2049938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049938).length < 2 ^ (prefixWord ++ tailWord_2049938).sum := by decide
  have hdescent : baseEnd_2049938 < baseStart_2049938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049948 : List Nat := [2, 2, 3, 3, 1, 1, 4, 1, 1, 5]
def baseStart_2049948 : Nat := 118140960795 + 2049948 * 2 ^ 59
def prefixEnd_2049948 : Nat := 4983230072969 + 3 ^ 40 * 2049948 * 2
def baseEnd_2049948 : Nat := 350869546907683600907489

theorem tailTrace_2049948 : CollatzResearch.WordTrace tailWord_2049948 prefixEnd_2049948 350869546907683600907489 := by
  unfold tailWord_2049948
  simp only [CollatzResearch.WordTrace]
  refine ⟨37383872988697987045183249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49845163984930649393577665 37383872988697987045183249)
  ·
    refine ⟨28037904741523490283887437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37383872988697987045183249 28037904741523490283887437)
    ·
      refine ⟨10514214278071308856457789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28037904741523490283887437 10514214278071308856457789)
      ·
        refine ⟨3942830354276740821171671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10514214278071308856457789 3942830354276740821171671)
        ·
          refine ⟨5914245531415111231757507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3942830354276740821171671 5914245531415111231757507)
          ·
            refine ⟨8871368297122666847636261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5914245531415111231757507 8871368297122666847636261)
            ·
              refine ⟨1663381555710500033931799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8871368297122666847636261 1663381555710500033931799)
              ·
                refine ⟨2495072333565750050897699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1663381555710500033931799 2495072333565750050897699)
                ·
                  refine ⟨3742608500348625076346549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2495072333565750050897699 3742608500348625076346549)
                  ·
                    refine ⟨350869546907683600907489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3742608500348625076346549 350869546907683600907489)
                    ·
                      rfl

theorem cell23_2049948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_2049948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2049948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2049948 prefixEnd_2049948 := by exact prefixLift 2049948
  have htrace : WordTrace (prefixWord ++ tailWord_2049948) baseStart_2049948 baseEnd_2049948 := by
    simpa [prefixWord, tailWord_2049948, baseEnd_2049948] using wordTrace_append hprefix tailTrace_2049948
  have hstable : (prefixWord ++ tailWord_2049948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049948).length < 2 ^ (prefixWord ++ tailWord_2049948).sum := by decide
  have hdescent : baseEnd_2049948 < baseStart_2049948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049981 : List Nat := [1, 4, 1, 2, 3, 1, 3, 1, 1, 2, 4]
def baseStart_2049981 : Nat := 118140960795 + 2049981 * 2 ^ 59
def prefixEnd_2049981 : Nat := 4983230072969 + 3 ^ 40 * 2049981 * 2
def baseEnd_2049981 : Nat := 1052625585584649173609815

theorem tailTrace_2049981 : CollatzResearch.WordTrace tailWord_2049981 prefixEnd_2049981 1052625585584649173609815 := by
  unfold tailWord_2049981
  simp only [CollatzResearch.WordTrace]
  refine ⟨74768949586276420726317797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49845966390850947150878531 74768949586276420726317797)
  ·
    refine ⟨14019178047426828886184587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74768949586276420726317797 14019178047426828886184587)
    ·
      refine ⟨21028767071140243329276881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14019178047426828886184587 21028767071140243329276881)
      ·
        refine ⟨15771575303355182496957661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21028767071140243329276881 15771575303355182496957661)
        ·
          refine ⟨5914340738758193436359123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15771575303355182496957661 5914340738758193436359123)
          ·
            refine ⟨8871511108137290154538685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5914340738758193436359123 8871511108137290154538685)
            ·
              refine ⟨3326816665551483807952007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8871511108137290154538685 3326816665551483807952007)
              ·
                refine ⟨4990224998327225711928011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3326816665551483807952007 4990224998327225711928011)
                ·
                  refine ⟨7485337497490838567892017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4990224998327225711928011 7485337497490838567892017)
                  ·
                    refine ⟨5614003123118128925919013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7485337497490838567892017 5614003123118128925919013)
                    ·
                      refine ⟨1052625585584649173609815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5614003123118128925919013 1052625585584649173609815)
                      ·
                        rfl

theorem cell23_2049981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_2049981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2049981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2049981 prefixEnd_2049981 := by exact prefixLift 2049981
  have htrace : WordTrace (prefixWord ++ tailWord_2049981) baseStart_2049981 baseEnd_2049981 := by
    simpa [prefixWord, tailWord_2049981, baseEnd_2049981] using wordTrace_append hprefix tailTrace_2049981
  have hstable : (prefixWord ++ tailWord_2049981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049981).length < 2 ^ (prefixWord ++ tailWord_2049981).sum := by decide
  have hdescent : baseEnd_2049981 < baseStart_2049981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050024 : List Nat := [2, 1, 4, 1, 1, 1, 1, 3, 2, 3, 4]
def baseStart_2050024 : Nat := 118140960795 + 2050024 * 2 ^ 59
def prefixEnd_2050024 : Nat := 4983230072969 + 3 ^ 40 * 2050024 * 2
def baseEnd_2050024 : Nat := 1052647665252792505372117

theorem tailTrace_2050024 : CollatzResearch.WordTrace tailWord_2050024 prefixEnd_2050024 1052647665252792505372117 := by
  unfold tailWord_2050024
  simp only [CollatzResearch.WordTrace]
  refine ⟨37385258962560319535066563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49847011950080426046755417 37385258962560319535066563)
  ·
    refine ⟨56077888443840479302599845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37385258962560319535066563 56077888443840479302599845)
    ·
      refine ⟨10514604083220089869237471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56077888443840479302599845 10514604083220089869237471)
      ·
        refine ⟨15771906124830134803856207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10514604083220089869237471 15771906124830134803856207)
        ·
          refine ⟨23657859187245202205784311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15771906124830134803856207 23657859187245202205784311)
          ·
            refine ⟨35486788780867803308676467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23657859187245202205784311 35486788780867803308676467)
            ·
              refine ⟨53230183171301704963014701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35486788780867803308676467 53230183171301704963014701)
              ·
                refine ⟨19961318689238139361130513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53230183171301704963014701 19961318689238139361130513)
                ·
                  refine ⟨14970989016928604520847885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19961318689238139361130513 14970989016928604520847885)
                  ·
                    refine ⟨5614120881348226695317957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14970989016928604520847885 5614120881348226695317957)
                    ·
                      refine ⟨1052647665252792505372117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5614120881348226695317957 1052647665252792505372117)
                      ·
                        rfl

theorem cell23_2050024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_2050024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2050024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2050024 prefixEnd_2050024 := by exact prefixLift 2050024
  have htrace : WordTrace (prefixWord ++ tailWord_2050024) baseStart_2050024 baseEnd_2050024 := by
    simpa [prefixWord, tailWord_2050024, baseEnd_2050024] using wordTrace_append hprefix tailTrace_2050024
  have hstable : (prefixWord ++ tailWord_2050024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050024).length < 2 ^ (prefixWord ++ tailWord_2050024).sum := by decide
  have hdescent : baseEnd_2050024 < baseStart_2050024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050029 : List Nat := [1, 5, 1, 4, 2, 1, 2, 1, 2, 4]
def baseStart_2050029 : Nat := 118140960795 + 2050029 * 2 ^ 59
def prefixEnd_2050029 : Nat := 4983230072969 + 3 ^ 40 * 2050029 * 2
def baseEnd_2050029 : Nat := 350883410885354995269865

theorem tailTrace_2050029 : CollatzResearch.WordTrace tailWord_2050029 prefixEnd_2050029 350883410885354995269865 := by
  unfold tailWord_2050029
  simp only [CollatzResearch.WordTrace]
  refine ⟨74770700290102524924065141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49847133526735016616043427 74770700290102524924065141)
  ·
    refine ⟨7009753152197111711631107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74770700290102524924065141 7009753152197111711631107)
    ·
      refine ⟨10514629728295667567446661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7009753152197111711631107 10514629728295667567446661)
      ·
        refine ⟨1971493074055437668896249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10514629728295667567446661 1971493074055437668896249)
        ·
          refine ⟨1478619805541578251672187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1971493074055437668896249 1478619805541578251672187)
          ·
            refine ⟨2217929708312367377508281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1478619805541578251672187 2217929708312367377508281)
            ·
              refine ⟨1663447281234275533131211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2217929708312367377508281 1663447281234275533131211)
              ·
                refine ⟨2495170921851413299696817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1663447281234275533131211 2495170921851413299696817)
                ·
                  refine ⟨1871378191388559974772613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2495170921851413299696817 1871378191388559974772613)
                  ·
                    refine ⟨350883410885354995269865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1871378191388559974772613 350883410885354995269865)
                    ·
                      rfl

theorem cell23_2050029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_2050029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2050029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2050029 prefixEnd_2050029 := by exact prefixLift 2050029
  have htrace : WordTrace (prefixWord ++ tailWord_2050029) baseStart_2050029 baseEnd_2050029 := by
    simpa [prefixWord, tailWord_2050029, baseEnd_2050029] using wordTrace_append hprefix tailTrace_2050029
  have hstable : (prefixWord ++ tailWord_2050029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050029).length < 2 ^ (prefixWord ++ tailWord_2050029).sum := by decide
  have hdescent : baseEnd_2050029 < baseStart_2050029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050044 : List Nat := [2, 2, 2, 1, 2, 2, 1, 1, 4, 1, 5]
def baseStart_2050044 : Nat := 118140960795 + 2050044 * 2 ^ 59
def prefixEnd_2050044 : Nat := 4983230072969 + 3 ^ 40 * 2050044 * 2
def baseEnd_2050044 : Nat := 1052657934865882427122025

theorem tailTrace_2050044 : CollatzResearch.WordTrace tailWord_2050044 prefixEnd_2050044 1052657934865882427122025 := by
  unfold tailWord_2050044
  simp only [CollatzResearch.WordTrace]
  refine ⟨37385623692524091242930593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49847498256698788323907457 37385623692524091242930593)
  ·
    refine ⟨28039217769393068432197945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37385623692524091242930593 28039217769393068432197945)
    ·
      refine ⟨21029413327044801324148459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28039217769393068432197945 21029413327044801324148459)
      ·
        refine ⟨31544119990567201986222689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21029413327044801324148459 31544119990567201986222689)
        ·
          refine ⟨23658089992925401489667017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31544119990567201986222689 23658089992925401489667017)
          ·
            refine ⟨17743567494694051117250263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23658089992925401489667017 17743567494694051117250263)
            ·
              refine ⟨26615351242041076675875395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17743567494694051117250263 26615351242041076675875395)
              ·
                refine ⟨39923026863061615013813093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26615351242041076675875395 39923026863061615013813093)
                ·
                  refine ⟨7485567536824052815089955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39923026863061615013813093 7485567536824052815089955)
                  ·
                    refine ⟨11228351305236079222634933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7485567536824052815089955 11228351305236079222634933)
                    ·
                      refine ⟨1052657934865882427122025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11228351305236079222634933 1052657934865882427122025)
                      ·
                        rfl

theorem cell23_2050044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_2050044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2050044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2050044 prefixEnd_2050044 := by exact prefixLift 2050044
  have htrace : WordTrace (prefixWord ++ tailWord_2050044) baseStart_2050044 baseEnd_2050044 := by
    simpa [prefixWord, tailWord_2050044, baseEnd_2050044] using wordTrace_append hprefix tailTrace_2050044
  have hstable : (prefixWord ++ tailWord_2050044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050044).length < 2 ^ (prefixWord ++ tailWord_2050044).sum := by decide
  have hdescent : baseEnd_2050044 < baseStart_2050044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050111 : List Nat := [1, 1, 2, 2, 3, 1, 5, 1, 2, 5]
def baseStart_2050111 : Nat := 118140960795 + 2050111 * 2 ^ 59
def prefixEnd_2050111 : Nat := 4983230072969 + 3 ^ 40 * 2050111 * 2
def baseEnd_2050111 : Nat := 350897446023244554994739

theorem tailTrace_2050111 : CollatzResearch.WordTrace tailWord_2050111 prefixEnd_2050111 350897446023244554994739 := by
  unfold tailWord_2050111
  simp only [CollatzResearch.WordTrace]
  refine ⟨74773691075805452928550187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49849127383870301952366791 74773691075805452928550187)
  ·
    refine ⟨112160536613708179392825281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74773691075805452928550187 112160536613708179392825281)
    ·
      refine ⟨84120402460281134544618961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112160536613708179392825281 84120402460281134544618961)
      ·
        refine ⟨63090301845210850908464221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84120402460281134544618961 63090301845210850908464221)
        ·
          refine ⟨23658863191954069090674083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63090301845210850908464221 23658863191954069090674083)
          ·
            refine ⟨35488294787931103636011125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23658863191954069090674083 35488294787931103636011125)
            ·
              refine ⟨3327027636368540965876043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35488294787931103636011125 3327027636368540965876043)
              ·
                refine ⟨4990541454552811448814065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3327027636368540965876043 4990541454552811448814065)
                ·
                  refine ⟨3742906090914608586610549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4990541454552811448814065 3742906090914608586610549)
                  ·
                    refine ⟨350897446023244554994739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3742906090914608586610549 350897446023244554994739)
                    ·
                      rfl

theorem cell23_2050111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 2, 5].length) (baseStart_2050111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2050111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2050111 prefixEnd_2050111 := by exact prefixLift 2050111
  have htrace : WordTrace (prefixWord ++ tailWord_2050111) baseStart_2050111 baseEnd_2050111 := by
    simpa [prefixWord, tailWord_2050111, baseEnd_2050111] using wordTrace_append hprefix tailTrace_2050111
  have hstable : (prefixWord ++ tailWord_2050111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050111).length < 2 ^ (prefixWord ++ tailWord_2050111).sum := by decide
  have hdescent : baseEnd_2050111 < baseStart_2050111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050148 : List Nat := [2, 3, 1, 1, 2, 1, 4, 1, 2, 4, 2]
def baseStart_2050148 : Nat := 118140960795 + 2050148 * 2 ^ 59
def prefixEnd_2050148 : Nat := 4983230072969 + 3 ^ 40 * 2050148 * 2
def baseEnd_2050148 : Nat := 1052711336853950020221547

theorem tailTrace_2050148 : CollatzResearch.WordTrace tailWord_2050148 prefixEnd_2050148 1052711336853950020221547 := by
  unfold tailWord_2050148
  simp only [CollatzResearch.WordTrace]
  refine ⟨37387520288335704123823549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49850027051114272165098065 37387520288335704123823549)
  ·
    refine ⟨14020320108125889046433831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37387520288335704123823549 14020320108125889046433831)
    ·
      refine ⟨21030480162188833569650747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14020320108125889046433831 21030480162188833569650747)
      ·
        refine ⟨31545720243283250354476121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21030480162188833569650747 31545720243283250354476121)
        ·
          refine ⟨23659290182462437765857091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31545720243283250354476121 23659290182462437765857091)
          ·
            refine ⟨35488935273693656648785637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23659290182462437765857091 35488935273693656648785637)
            ·
              refine ⟨6654175363817560621647307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35488935273693656648785637 6654175363817560621647307)
              ·
                refine ⟨9981263045726340932470961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6654175363817560621647307 9981263045726340932470961)
                ·
                  refine ⟨7485947284294755699353221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9981263045726340932470961 7485947284294755699353221)
                  ·
                    refine ⟨1403615115805266693628729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7485947284294755699353221 1403615115805266693628729)
                    ·
                      refine ⟨1052711336853950020221547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1403615115805266693628729 1052711336853950020221547)
                      ·
                        rfl

theorem cell23_2050148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 2, 4, 2].length) (baseStart_2050148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2050148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2050148 prefixEnd_2050148 := by exact prefixLift 2050148
  have htrace : WordTrace (prefixWord ++ tailWord_2050148) baseStart_2050148 baseEnd_2050148 := by
    simpa [prefixWord, tailWord_2050148, baseEnd_2050148] using wordTrace_append hprefix tailTrace_2050148
  have hstable : (prefixWord ++ tailWord_2050148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050148).length < 2 ^ (prefixWord ++ tailWord_2050148).sum := by decide
  have hdescent : baseEnd_2050148 < baseStart_2050148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050151 : List Nat := [1, 1, 5, 1, 1, 2, 1, 1, 3, 4, 3]
def baseStart_2050151 : Nat := 118140960795 + 2050151 * 2 ^ 59
def prefixEnd_2050151 : Nat := 4983230072969 + 3 ^ 40 * 2050151 * 2
def baseEnd_2050151 : Nat := 1052712877295913508484033

theorem tailTrace_2050151 : CollatzResearch.WordTrace tailWord_2050151 prefixEnd_2050151 1052712877295913508484033 := by
  unfold tailWord_2050151
  simp only [CollatzResearch.WordTrace]
  refine ⟨74775149995660539760006307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49850099997107026506670871 74775149995660539760006307)
  ·
    refine ⟨112162724993490809640009461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74775149995660539760006307 112162724993490809640009461)
    ·
      refine ⟨10515255468139763403750887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 112162724993490809640009461 10515255468139763403750887)
      ·
        refine ⟨15772883202209645105626331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10515255468139763403750887 15772883202209645105626331)
        ·
          refine ⟨23659324803314467658439497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15772883202209645105626331 23659324803314467658439497)
          ·
            refine ⟨17744493602485850743829623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23659324803314467658439497 17744493602485850743829623)
            ·
              refine ⟨26616740403728776115744435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17744493602485850743829623 26616740403728776115744435)
              ·
                refine ⟨39925110605593164173616653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26616740403728776115744435 39925110605593164173616653)
                ·
                  refine ⟨14971916477097436565106245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39925110605593164173616653 14971916477097436565106245)
                  ·
                    refine ⟨2807234339455769355957421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14971916477097436565106245 2807234339455769355957421)
                    ·
                      refine ⟨1052712877295913508484033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2807234339455769355957421 1052712877295913508484033)
                      ·
                        rfl

theorem cell23_2050151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_2050151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2050151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2050151 prefixEnd_2050151 := by exact prefixLift 2050151
  have htrace : WordTrace (prefixWord ++ tailWord_2050151) baseStart_2050151 baseEnd_2050151 := by
    simpa [prefixWord, tailWord_2050151, baseEnd_2050151] using wordTrace_append hprefix tailTrace_2050151
  have hstable : (prefixWord ++ tailWord_2050151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050151).length < 2 ^ (prefixWord ++ tailWord_2050151).sum := by decide
  have hdescent : baseEnd_2050151 < baseStart_2050151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050158 : List Nat := [4, 1, 2, 2, 1, 1, 1, 4, 3, 4]
def baseStart_2050158 : Nat := 118140960795 + 2050158 * 2 ^ 59
def prefixEnd_2050158 : Nat := 4983230072969 + 3 ^ 40 * 2050158 * 2
def baseEnd_2050158 : Nat := 350905490553498327032167

theorem tailTrace_2050158 : CollatzResearch.WordTrace tailWord_2050158 prefixEnd_2050158 350905490553498327032167 := by
  unfold tailWord_2050158
  simp only [CollatzResearch.WordTrace]
  refine ⟨9346925663329397494438891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49850270204423453303674085 9346925663329397494438891)
  ·
    refine ⟨14020388494994096241658337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9346925663329397494438891 14020388494994096241658337)
    ·
      refine ⟨10515291371245572181243753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14020388494994096241658337 10515291371245572181243753)
      ·
        refine ⟨7886468528434179135932815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10515291371245572181243753 7886468528434179135932815)
        ·
          refine ⟨11829702792651268703899223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7886468528434179135932815 11829702792651268703899223)
          ·
            refine ⟨17744554188976903055848835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11829702792651268703899223 17744554188976903055848835)
            ·
              refine ⟨26616831283465354583773253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17744554188976903055848835 26616831283465354583773253)
              ·
                refine ⟨4990655865649753984457485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26616831283465354583773253 4990655865649753984457485)
                ·
                  refine ⟨1871495949618657744171557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4990655865649753984457485 1871495949618657744171557)
                  ·
                    refine ⟨350905490553498327032167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1871495949618657744171557 350905490553498327032167)
                    ·
                      rfl

theorem cell23_2050158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_2050158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2050158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2050158 prefixEnd_2050158 := by exact prefixLift 2050158
  have htrace : WordTrace (prefixWord ++ tailWord_2050158) baseStart_2050158 baseEnd_2050158 := by
    simpa [prefixWord, tailWord_2050158, baseEnd_2050158] using wordTrace_append hprefix tailTrace_2050158
  have hstable : (prefixWord ++ tailWord_2050158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050158).length < 2 ^ (prefixWord ++ tailWord_2050158).sum := by decide
  have hdescent : baseEnd_2050158 < baseStart_2050158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050205 : List Nat := [1, 4, 2, 1, 1, 5, 2, 1, 6]
def baseStart_2050205 : Nat := 118140960795 + 2050205 * 2 ^ 59
def prefixEnd_2050205 : Nat := 4983230072969 + 3 ^ 40 * 2050205 * 2
def baseEnd_2050205 : Nat := 116971178361250699689865

theorem tailTrace_2050205 : CollatzResearch.WordTrace tailWord_2050205 prefixEnd_2050205 116971178361250699689865 := by
  unfold tailWord_2050205
  simp only [CollatzResearch.WordTrace]
  refine ⟨74777119537464906982472069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49851413024976604654981379 74777119537464906982472069)
  ·
    refine ⟨14020709913274670059213513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74777119537464906982472069 14020709913274670059213513)
    ·
      refine ⟨10515532434956002544410135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14020709913274670059213513 10515532434956002544410135)
      ·
        refine ⟨15773298652434003816615203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10515532434956002544410135 15773298652434003816615203)
        ·
          refine ⟨23659947978651005724922805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15773298652434003816615203 23659947978651005724922805)
          ·
            refine ⟨2218120122998531786711513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23659947978651005724922805 2218120122998531786711513)
            ·
              refine ⟨1663590092248898840033635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2218120122998531786711513 1663590092248898840033635)
              ·
                refine ⟨2495385138373348260050453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1663590092248898840033635 2495385138373348260050453)
                ·
                  refine ⟨116971178361250699689865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2495385138373348260050453 116971178361250699689865)
                  ·
                    rfl

theorem cell23_2050205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 1, 6].length) (baseStart_2050205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2050205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2050205 prefixEnd_2050205 := by exact prefixLift 2050205
  have htrace : WordTrace (prefixWord ++ tailWord_2050205) baseStart_2050205 baseEnd_2050205 := by
    simpa [prefixWord, tailWord_2050205, baseEnd_2050205] using wordTrace_append hprefix tailTrace_2050205
  have hstable : (prefixWord ++ tailWord_2050205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050205).length < 2 ^ (prefixWord ++ tailWord_2050205).sum := by decide
  have hdescent : baseEnd_2050205 < baseStart_2050205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050231 : List Nat := [1, 1, 3, 1, 4, 2, 1, 1, 3, 6]
def baseStart_2050231 : Nat := 118140960795 + 2050231 * 2 ^ 59
def prefixEnd_2050231 : Nat := 4983230072969 + 3 ^ 40 * 2050231 * 2
def baseEnd_2050231 : Nat := 350917985249424398494555

theorem tailTrace_2050231 : CollatzResearch.WordTrace tailWord_2050231 prefixEnd_2050231 350917985249424398494555 := by
  unfold tailWord_2050231
  simp only [CollatzResearch.WordTrace]
  refine ⟨74778067835370713422918547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49852045223580475615279031 74778067835370713422918547)
  ·
    refine ⟨112167101753056070134377821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74778067835370713422918547 112167101753056070134377821)
    ·
      refine ⟨42062663157396026300391683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112167101753056070134377821 42062663157396026300391683)
      ·
        refine ⟨63093994736094039450587525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42062663157396026300391683 63093994736094039450587525)
        ·
          refine ⟨11830124013017632396985161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63093994736094039450587525 11830124013017632396985161)
          ·
            refine ⟨8872593009763224297738871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11830124013017632396985161 8872593009763224297738871)
            ·
              refine ⟨13308889514644836446608307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8872593009763224297738871 13308889514644836446608307)
              ·
                refine ⟨19963334271967254669912461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13308889514644836446608307 19963334271967254669912461)
                ·
                  refine ⟨7486250351987720501217173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19963334271967254669912461 7486250351987720501217173)
                  ·
                    refine ⟨350917985249424398494555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7486250351987720501217173 350917985249424398494555)
                    ·
                      rfl

theorem cell23_2050231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 6].length) (baseStart_2050231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2050231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2050231 prefixEnd_2050231 := by exact prefixLift 2050231
  have htrace : WordTrace (prefixWord ++ tailWord_2050231) baseStart_2050231 baseEnd_2050231 := by
    simpa [prefixWord, tailWord_2050231, baseEnd_2050231] using wordTrace_append hprefix tailTrace_2050231
  have hstable : (prefixWord ++ tailWord_2050231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050231).length < 2 ^ (prefixWord ++ tailWord_2050231).sum := by decide
  have hdescent : baseEnd_2050231 < baseStart_2050231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050251 : List Nat := [1, 1, 1, 1, 3, 2, 3, 2, 3, 2, 4]
def baseStart_2050251 : Nat := 118140960795 + 2050251 * 2 ^ 59
def prefixEnd_2050251 : Nat := 4983230072969 + 3 ^ 40 * 2050251 * 2
def baseEnd_2050251 : Nat := 1052764225361363117233573

theorem tailTrace_2050251 : CollatzResearch.WordTrace tailWord_2050251 prefixEnd_2050251 1052764225361363117233573 := by
  unfold tailWord_2050251
  simp only [CollatzResearch.WordTrace]
  refine ⟨74778797295298256838646607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49852531530198837892431071 74778797295298256838646607)
  ·
    refine ⟨112168195942947385257969911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74778797295298256838646607 112168195942947385257969911)
    ·
      refine ⟨168252293914421077886954867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112168195942947385257969911 168252293914421077886954867)
      ·
        refine ⟨252378440871631616830432301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168252293914421077886954867 252378440871631616830432301)
        ·
          refine ⟨94641915326861856311412113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252378440871631616830432301 94641915326861856311412113)
          ·
            refine ⟨70981436495146392233559085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94641915326861856311412113 70981436495146392233559085)
            ·
              refine ⟨26618038685679897087584657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70981436495146392233559085 26618038685679897087584657)
              ·
                refine ⟨19963529014259922815688493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26618038685679897087584657 19963529014259922815688493)
                ·
                  refine ⟨7486323380347471055883185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19963529014259922815688493 7486323380347471055883185)
                  ·
                    refine ⟨5614742535260603291912389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7486323380347471055883185 5614742535260603291912389)
                    ·
                      refine ⟨1052764225361363117233573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5614742535260603291912389 1052764225361363117233573)
                      ·
                        rfl

theorem cell23_2050251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 2, 4].length) (baseStart_2050251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2050251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2050251 prefixEnd_2050251 := by exact prefixLift 2050251
  have htrace : WordTrace (prefixWord ++ tailWord_2050251) baseStart_2050251 baseEnd_2050251 := by
    simpa [prefixWord, tailWord_2050251, baseEnd_2050251] using wordTrace_append hprefix tailTrace_2050251
  have hstable : (prefixWord ++ tailWord_2050251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050251).length < 2 ^ (prefixWord ++ tailWord_2050251).sum := by decide
  have hdescent : baseEnd_2050251 < baseStart_2050251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050255 : List Nat := [1, 1, 2, 1, 1, 3, 4, 3, 3, 2, 2]
def baseStart_2050255 : Nat := 118140960795 + 2050255 * 2 ^ 59
def prefixEnd_2050255 : Nat := 4983230072969 + 3 ^ 40 * 2050255 * 2
def baseEnd_2050255 : Nat := 1052766279283981101583555

theorem tailTrace_2050255 : CollatzResearch.WordTrace tailWord_2050255 prefixEnd_2050255 1052766279283981101583555 := by
  unfold tailWord_2050255
  simp only [CollatzResearch.WordTrace]
  refine ⟨74778943187283765521792219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49852628791522510347861479 74778943187283765521792219)
  ·
    refine ⟨112168414780925648282688329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74778943187283765521792219 112168414780925648282688329)
    ·
      refine ⟨84126311085694236212016247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112168414780925648282688329 84126311085694236212016247)
      ·
        refine ⟨126189466628541354318024371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84126311085694236212016247 126189466628541354318024371)
        ·
          refine ⟨189284199942812031477036557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126189466628541354318024371 189284199942812031477036557)
          ·
            refine ⟨70981574978554511803888709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189284199942812031477036557 70981574978554511803888709)
            ·
              refine ⟨13309045308478970963229133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70981574978554511803888709 13309045308478970963229133)
              ·
                refine ⟨4990891990679614111210925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13309045308478970963229133 4990891990679614111210925)
                ·
                  refine ⟨1871584496504855291704097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4990891990679614111210925 1871584496504855291704097)
                  ·
                    refine ⟨1403688372378641468778073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1871584496504855291704097 1403688372378641468778073)
                    ·
                      refine ⟨1052766279283981101583555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1403688372378641468778073 1052766279283981101583555)
                      ·
                        rfl

theorem cell23_2050255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 3, 2, 2].length) (baseStart_2050255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2050255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2050255 prefixEnd_2050255 := by exact prefixLift 2050255
  have htrace : WordTrace (prefixWord ++ tailWord_2050255) baseStart_2050255 baseEnd_2050255 := by
    simpa [prefixWord, tailWord_2050255, baseEnd_2050255] using wordTrace_append hprefix tailTrace_2050255
  have hstable : (prefixWord ++ tailWord_2050255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050255).length < 2 ^ (prefixWord ++ tailWord_2050255).sum := by decide
  have hdescent : baseEnd_2050255 < baseStart_2050255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050305 : List Nat := [1, 2, 4, 1, 1, 2, 3, 1, 4, 1, 3]
def baseStart_2050305 : Nat := 118140960795 + 2050305 * 2 ^ 59
def prefixEnd_2050305 : Nat := 4983230072969 + 3 ^ 40 * 2050305 * 2
def baseEnd_2050305 : Nat := 1052791953316705905958325

theorem tailTrace_2050305 : CollatzResearch.WordTrace tailWord_2050305 prefixEnd_2050305 1052791953316705905958325 := by
  unfold tailWord_2050305
  simp only [CollatzResearch.WordTrace]
  refine ⟨74780766837102624061112369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49853844558068416040741579 74780766837102624061112369)
  ·
    refine ⟨56085575127826968045834277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74780766837102624061112369 56085575127826968045834277)
    ·
      refine ⟨10516045336467556508593927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56085575127826968045834277 10516045336467556508593927)
      ·
        refine ⟨15774068004701334762890891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10516045336467556508593927 15774068004701334762890891)
        ·
          refine ⟨23661102007052002144336337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15774068004701334762890891 23661102007052002144336337)
          ·
            refine ⟨17745826505289001608252253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23661102007052002144336337 17745826505289001608252253)
            ·
              refine ⟨6654684939483375603094595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17745826505289001608252253 6654684939483375603094595)
              ·
                refine ⟨9982027409225063404641893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6654684939483375603094595 9982027409225063404641893)
                ·
                  refine ⟨1871630139229699388370355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9982027409225063404641893 1871630139229699388370355)
                  ·
                    refine ⟨2807445208844549082555533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1871630139229699388370355 2807445208844549082555533)
                    ·
                      refine ⟨1052791953316705905958325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2807445208844549082555533 1052791953316705905958325)
                      ·
                        rfl

theorem cell23_2050305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_2050305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2050305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2050305 prefixEnd_2050305 := by exact prefixLift 2050305
  have htrace : WordTrace (prefixWord ++ tailWord_2050305) baseStart_2050305 baseEnd_2050305 := by
    simpa [prefixWord, tailWord_2050305, baseEnd_2050305] using wordTrace_append hprefix tailTrace_2050305
  have hstable : (prefixWord ++ tailWord_2050305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050305).length < 2 ^ (prefixWord ++ tailWord_2050305).sum := by decide
  have hdescent : baseEnd_2050305 < baseStart_2050305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050306 : List Nat := [3, 4, 1, 1, 2, 1, 2, 4, 1, 2, 2]
def baseStart_2050306 : Nat := 118140960795 + 2050306 * 2 ^ 59
def prefixEnd_2050306 : Nat := 4983230072969 + 3 ^ 40 * 2050306 * 2
def baseEnd_2050306 : Nat := 1052792466797360402045821

theorem tailTrace_2050306 : CollatzResearch.WordTrace tailWord_2050306 prefixEnd_2050306 1052792466797360402045821 := by
  unfold tailWord_2050306
  simp only [CollatzResearch.WordTrace]
  refine ⟨18695200827524750307974693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49853868873399334154599181 18695200827524750307974693)
  ·
    refine ⟨3505350155160890682745255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18695200827524750307974693 3505350155160890682745255)
    ·
      refine ⟨5258025232741336024117883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3505350155160890682745255 5258025232741336024117883)
      ·
        refine ⟨7887037849112004036176825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5258025232741336024117883 7887037849112004036176825)
        ·
          refine ⟨5915278386834003027132619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7887037849112004036176825 5915278386834003027132619)
          ·
            refine ⟨8872917580251004540698929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5915278386834003027132619 8872917580251004540698929)
            ·
              refine ⟨6654688185188253405524197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8872917580251004540698929 6654688185188253405524197)
              ·
                refine ⟨1247754034722797513535787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6654688185188253405524197 1247754034722797513535787)
                ·
                  refine ⟨1871631052084196270303681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1247754034722797513535787 1871631052084196270303681)
                  ·
                    refine ⟨1403723289063147202727761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1871631052084196270303681 1403723289063147202727761)
                    ·
                      refine ⟨1052792466797360402045821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1403723289063147202727761 1052792466797360402045821)
                      ·
                        rfl

theorem cell23_2050306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_2050306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2050306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2050306 prefixEnd_2050306 := by exact prefixLift 2050306
  have htrace : WordTrace (prefixWord ++ tailWord_2050306) baseStart_2050306 baseEnd_2050306 := by
    simpa [prefixWord, tailWord_2050306, baseEnd_2050306] using wordTrace_append hprefix tailTrace_2050306
  have hstable : (prefixWord ++ tailWord_2050306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050306).length < 2 ^ (prefixWord ++ tailWord_2050306).sum := by decide
  have hdescent : baseEnd_2050306 < baseStart_2050306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050351 : List Nat := [1, 1, 2, 1, 2, 1, 4, 2, 9]
def baseStart_2050351 : Nat := 118140960795 + 2050351 * 2 ^ 59
def prefixEnd_2050351 : Nat := 4983230072969 + 3 ^ 40 * 2050351 * 2
def baseEnd_2050351 : Nat := 116979508158534747331457

theorem tailTrace_2050351 : CollatzResearch.WordTrace tailWord_2050351 prefixEnd_2050351 116979508158534747331457 := by
  unfold tailWord_2050351
  simp only [CollatzResearch.WordTrace]
  refine ⟨74782444594935973917286907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49854963063290649278191271 74782444594935973917286907)
  ·
    refine ⟨112173666892403960875930361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74782444594935973917286907 112173666892403960875930361)
    ·
      refine ⟨84130250169302970656947771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112173666892403960875930361 84130250169302970656947771)
      ·
        refine ⟨126195375253954455985421657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84130250169302970656947771 126195375253954455985421657)
        ·
          refine ⟨94646531440465841989066243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126195375253954455985421657 94646531440465841989066243)
          ·
            refine ⟨141969797160698762983599365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94646531440465841989066243 141969797160698762983599365)
            ·
              refine ⟨26619336967631018059424881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141969797160698762983599365 26619336967631018059424881)
              ·
                refine ⟨19964502725723263544568661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26619336967631018059424881 19964502725723263544568661)
                ·
                  refine ⟨116979508158534747331457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 19964502725723263544568661 116979508158534747331457)
                  ·
                    rfl

theorem cell23_2050351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 9].length) (baseStart_2050351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2050351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2050351 prefixEnd_2050351 := by exact prefixLift 2050351
  have htrace : WordTrace (prefixWord ++ tailWord_2050351) baseStart_2050351 baseEnd_2050351 := by
    simpa [prefixWord, tailWord_2050351, baseEnd_2050351] using wordTrace_append hprefix tailTrace_2050351
  have hstable : (prefixWord ++ tailWord_2050351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050351).length < 2 ^ (prefixWord ++ tailWord_2050351).sum := by decide
  have hdescent : baseEnd_2050351 < baseStart_2050351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050362 : List Nat := [3, 1, 1, 1, 4, 2, 2, 1, 4, 2, 2]
def baseStart_2050362 : Nat := 118140960795 + 2050362 * 2 ^ 59
def prefixEnd_2050362 : Nat := 4983230072969 + 3 ^ 40 * 2050362 * 2
def baseEnd_2050362 : Nat := 1052821221714012182945563

theorem tailTrace_2050362 : CollatzResearch.WordTrace tailWord_2050362 prefixEnd_2050362 1052821221714012182945563 := by
  unfold tailWord_2050362
  simp only [CollatzResearch.WordTrace]
  refine ⟨18695711449474030698984335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49855230531930748530624893 18695711449474030698984335)
  ·
    refine ⟨28043567174211046048476503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18695711449474030698984335 28043567174211046048476503)
    ·
      refine ⟨42065350761316569072714755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28043567174211046048476503 42065350761316569072714755)
      ·
        refine ⟨63098026141974853609072133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42065350761316569072714755 63098026141974853609072133)
        ·
          refine ⟨11830879901620285051701025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63098026141974853609072133 11830879901620285051701025)
          ·
            refine ⟨8873159926215213788775769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11830879901620285051701025 8873159926215213788775769)
            ·
              refine ⟨6654869944661410341581827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8873159926215213788775769 6654869944661410341581827)
              ·
                refine ⟨9982304916992115512372741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6654869944661410341581827 9982304916992115512372741)
                ·
                  refine ⟨1871682171936021658569889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9982304916992115512372741 1871682171936021658569889)
                  ·
                    refine ⟨1403761628952016243927417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1871682171936021658569889 1403761628952016243927417)
                    ·
                      refine ⟨1052821221714012182945563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1403761628952016243927417 1052821221714012182945563)
                      ·
                        rfl

theorem cell23_2050362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 4, 2, 2].length) (baseStart_2050362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2050362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2050362 prefixEnd_2050362 := by exact prefixLift 2050362
  have htrace : WordTrace (prefixWord ++ tailWord_2050362) baseStart_2050362 baseEnd_2050362 := by
    simpa [prefixWord, tailWord_2050362, baseEnd_2050362] using wordTrace_append hprefix tailTrace_2050362
  have hstable : (prefixWord ++ tailWord_2050362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050362).length < 2 ^ (prefixWord ++ tailWord_2050362).sum := by decide
  have hdescent : baseEnd_2050362 < baseStart_2050362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050452 : List Nat := [2, 4, 2, 1, 3, 1, 1, 1, 1, 3, 4]
def baseStart_2050452 : Nat := 118140960795 + 2050452 * 2 ^ 59
def prefixEnd_2050452 : Nat := 4983230072969 + 3 ^ 40 * 2050452 * 2
def baseEnd_2050452 : Nat := 1052867434972916830820149

theorem tailTrace_2050452 : CollatzResearch.WordTrace tailWord_2050452 prefixEnd_2050452 1052867434972916830820149 := by
  unfold tailWord_2050452
  simp only [CollatzResearch.WordTrace]
  refine ⟨37393064183785034083356805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49857418911713378777809073 37393064183785034083356805)
  ·
    refine ⟨7011199534459693890629401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37393064183785034083356805 7011199534459693890629401)
    ·
      refine ⟨5258399650844770417972051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7011199534459693890629401 5258399650844770417972051)
      ·
        refine ⟨7887599476267155626958077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5258399650844770417972051 7887599476267155626958077)
        ·
          refine ⟨2957849803600183360109279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7887599476267155626958077 2957849803600183360109279)
          ·
            refine ⟨4436774705400275040163919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2957849803600183360109279 4436774705400275040163919)
            ·
              refine ⟨6655162058100412560245879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4436774705400275040163919 6655162058100412560245879)
              ·
                refine ⟨9982743087150618840368819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6655162058100412560245879 9982743087150618840368819)
                ·
                  refine ⟨14974114630725928260553229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9982743087150618840368819 14974114630725928260553229)
                  ·
                    refine ⟨5615292986522223097707461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14974114630725928260553229 5615292986522223097707461)
                    ·
                      refine ⟨1052867434972916830820149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5615292986522223097707461 1052867434972916830820149)
                      ·
                        rfl

theorem cell23_2050452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_2050452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2050452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2050452 prefixEnd_2050452 := by exact prefixLift 2050452
  have htrace : WordTrace (prefixWord ++ tailWord_2050452) baseStart_2050452 baseEnd_2050452 := by
    simpa [prefixWord, tailWord_2050452, baseEnd_2050452] using wordTrace_append hprefix tailTrace_2050452
  have hstable : (prefixWord ++ tailWord_2050452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050452).length < 2 ^ (prefixWord ++ tailWord_2050452).sum := by decide
  have hdescent : baseEnd_2050452 < baseStart_2050452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050505 : List Nat := [1, 2, 1, 1, 2, 1, 5, 4, 1, 5]
def baseStart_2050505 : Nat := 118140960795 + 2050505 * 2 ^ 59
def prefixEnd_2050505 : Nat := 4983230072969 + 3 ^ 40 * 2050505 * 2
def baseEnd_2050505 : Nat := 350964883149201707819135

theorem tailTrace_2050505 : CollatzResearch.WordTrace tailWord_2050505 prefixEnd_2050505 350964883149201707819135 := by
  unfold tailWord_2050505
  simp only [CollatzResearch.WordTrace]
  refine ⟨74788061436378058218392969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49858707624252038812261979 74788061436378058218392969)
  ·
    refine ⟨56091046077283543663794727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74788061436378058218392969 56091046077283543663794727)
    ·
      refine ⟨84136569115925315495692091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56091046077283543663794727 84136569115925315495692091)
      ·
        refine ⟨126204853673887973243538137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84136569115925315495692091 126204853673887973243538137)
        ·
          refine ⟨94653640255415979932653603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126204853673887973243538137 94653640255415979932653603)
          ·
            refine ⟨141980460383123969898980405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94653640255415979932653603 141980460383123969898980405)
            ·
              refine ⟨13310668160917872178029413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 141980460383123969898980405 13310668160917872178029413)
              ·
                refine ⟨2495750280172101033380515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13310668160917872178029413 2495750280172101033380515)
                ·
                  refine ⟨3743625420258151550070773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2495750280172101033380515 3743625420258151550070773)
                  ·
                    refine ⟨350964883149201707819135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3743625420258151550070773 350964883149201707819135)
                    ·
                      rfl

theorem cell23_2050505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 4, 1, 5].length) (baseStart_2050505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2050505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2050505 prefixEnd_2050505 := by exact prefixLift 2050505
  have htrace : WordTrace (prefixWord ++ tailWord_2050505) baseStart_2050505 baseEnd_2050505 := by
    simpa [prefixWord, tailWord_2050505, baseEnd_2050505] using wordTrace_append hprefix tailTrace_2050505
  have hstable : (prefixWord ++ tailWord_2050505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050505).length < 2 ^ (prefixWord ++ tailWord_2050505).sum := by decide
  have hdescent : baseEnd_2050505 < baseStart_2050505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050530 : List Nat := [3, 3, 3, 2, 1, 1, 3, 2, 1, 4]
def baseStart_2050530 : Nat := 118140960795 + 2050530 * 2 ^ 59
def prefixEnd_2050530 : Nat := 4983230072969 + 3 ^ 40 * 2050530 * 2
def baseEnd_2050530 : Nat := 350969162154655841881597

theorem tailTrace_2050530 : CollatzResearch.WordTrace tailWord_2050530 prefixEnd_2050530 350969162154655841881597 := by
  unfold tailWord_2050530
  simp only [CollatzResearch.WordTrace]
  refine ⟨18697243315321871872013261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49859315507524991658702029 18697243315321871872013261)
  ·
    refine ⟨7011466243245701952004973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18697243315321871872013261 7011466243245701952004973)
    ·
      refine ⟨2629299841217138232001865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7011466243245701952004973 2629299841217138232001865)
      ·
        refine ⟨1971974880912853674001399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2629299841217138232001865 1971974880912853674001399)
        ·
          refine ⟨2957962321369280511002099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1971974880912853674001399 2957962321369280511002099)
          ·
            refine ⟨4436943482053920766503149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2957962321369280511002099 4436943482053920766503149)
            ·
              refine ⟨1663853805770220287438681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4436943482053920766503149 1663853805770220287438681)
              ·
                refine ⟨1247890354327665215579011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1663853805770220287438681 1247890354327665215579011)
                ·
                  refine ⟨1871835531491497823368517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1247890354327665215579011 1871835531491497823368517)
                  ·
                    refine ⟨350969162154655841881597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1871835531491497823368517 350969162154655841881597)
                    ·
                      rfl

theorem cell23_2050530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_2050530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2050530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2050530 prefixEnd_2050530 := by exact prefixLift 2050530
  have htrace : WordTrace (prefixWord ++ tailWord_2050530) baseStart_2050530 baseEnd_2050530 := by
    simpa [prefixWord, tailWord_2050530, baseEnd_2050530] using wordTrace_append hprefix tailTrace_2050530
  have hstable : (prefixWord ++ tailWord_2050530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050530).length < 2 ^ (prefixWord ++ tailWord_2050530).sum := by decide
  have hdescent : baseEnd_2050530 < baseStart_2050530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050545 : List Nat := [1, 2, 2, 2, 3, 1, 1, 4, 1, 1, 5]
def baseStart_2050545 : Nat := 118140960795 + 2050545 * 2 ^ 59
def prefixEnd_2050545 : Nat := 4983230072969 + 3 ^ 40 * 2050545 * 2
def baseEnd_2050545 : Nat := 1052915188673784966957221

theorem tailTrace_2050545 : CollatzResearch.WordTrace tailWord_2050545 prefixEnd_2050545 1052915188673784966957221 := by
  unfold tailWord_2050545
  simp only [CollatzResearch.WordTrace]
  refine ⟨74789520356233145049849089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49859680237488763366566059 74789520356233145049849089)
  ·
    refine ⟨56092140267174858787386817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74789520356233145049849089 56092140267174858787386817)
    ·
      refine ⟨42069105200381144090540113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56092140267174858787386817 42069105200381144090540113)
      ·
        refine ⟨31551828900285858067905085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42069105200381144090540113 31551828900285858067905085)
        ·
          refine ⟨11831935837607196775464407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31551828900285858067905085 11831935837607196775464407)
          ·
            refine ⟨17747903756410795163196611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11831935837607196775464407 17747903756410795163196611)
            ·
              refine ⟨26621855634616192744794917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17747903756410795163196611 26621855634616192744794917)
              ·
                refine ⟨4991597931490536139649047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26621855634616192744794917 4991597931490536139649047)
                ·
                  refine ⟨7487396897235804209473571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4991597931490536139649047 7487396897235804209473571)
                  ·
                    refine ⟨11231095345853706314210357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7487396897235804209473571 11231095345853706314210357)
                    ·
                      refine ⟨1052915188673784966957221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11231095345853706314210357 1052915188673784966957221)
                      ·
                        rfl

theorem cell23_2050545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_2050545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2050545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2050545 prefixEnd_2050545 := by exact prefixLift 2050545
  have htrace : WordTrace (prefixWord ++ tailWord_2050545) baseStart_2050545 baseEnd_2050545 := by
    simpa [prefixWord, tailWord_2050545, baseEnd_2050545] using wordTrace_append hprefix tailTrace_2050545
  have hstable : (prefixWord ++ tailWord_2050545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050545).length < 2 ^ (prefixWord ++ tailWord_2050545).sum := by decide
  have hdescent : baseEnd_2050545 < baseStart_2050545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050552 : List Nat := [2, 1, 2, 1, 1, 4, 3, 3, 2, 4]
def baseStart_2050552 : Nat := 118140960795 + 2050552 * 2 ^ 59
def prefixEnd_2050552 : Nat := 4983230072969 + 3 ^ 40 * 2050552 * 2
def baseEnd_2050552 : Nat := 350972927679455479856563

theorem tailTrace_2050552 : CollatzResearch.WordTrace tailWord_2050552 prefixEnd_2050552 350972927679455479856563 := by
  unfold tailWord_2050552
  simp only [CollatzResearch.WordTrace]
  refine ⟨37394887833603892622676955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49859850444805190163569273 37394887833603892622676955)
  ·
    refine ⟨56092331750405838934015433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37394887833603892622676955 56092331750405838934015433)
    ·
      refine ⟨42069248812804379200511575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56092331750405838934015433 42069248812804379200511575)
      ·
        refine ⟨63103873219206568800767363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42069248812804379200511575 63103873219206568800767363)
        ·
          refine ⟨94655809828809853201151045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63103873219206568800767363 94655809828809853201151045)
          ·
            refine ⟨17747964342901847475215821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94655809828809853201151045 17747964342901847475215821)
            ·
              refine ⟨6655486628588192803205933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17747964342901847475215821 6655486628588192803205933)
              ·
                refine ⟨2495807485720572301202225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6655486628588192803205933 2495807485720572301202225)
                ·
                  refine ⟨1871855614290429225901669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2495807485720572301202225 1871855614290429225901669)
                  ·
                    refine ⟨350972927679455479856563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1871855614290429225901669 350972927679455479856563)
                    ·
                      rfl

theorem cell23_2050552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 3, 2, 4].length) (baseStart_2050552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2050552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2050552 prefixEnd_2050552 := by exact prefixLift 2050552
  have htrace : WordTrace (prefixWord ++ tailWord_2050552) baseStart_2050552 baseEnd_2050552 := by
    simpa [prefixWord, tailWord_2050552, baseEnd_2050552] using wordTrace_append hprefix tailTrace_2050552
  have hstable : (prefixWord ++ tailWord_2050552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050552).length < 2 ^ (prefixWord ++ tailWord_2050552).sum := by decide
  have hdescent : baseEnd_2050552 < baseStart_2050552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050572 : List Nat := [2, 2, 1, 2, 4, 2, 1, 2, 1, 2, 4]
def baseStart_2050572 : Nat := 118140960795 + 2050572 * 2 ^ 59
def prefixEnd_2050572 : Nat := 4983230072969 + 3 ^ 40 * 2050572 * 2
def baseEnd_2050572 : Nat := 1052929052651456361319597

theorem tailTrace_2050572 : CollatzResearch.WordTrace tailWord_2050572 prefixEnd_2050572 1052929052651456361319597 := by
  unfold tailWord_2050572
  simp only [CollatzResearch.WordTrace]
  refine ⟨37395252563567664330540985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49860336751423552440721313 37395252563567664330540985)
  ·
    refine ⟨28046439422675748247905739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37395252563567664330540985 28046439422675748247905739)
    ·
      refine ⟨42069659134013622371858609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28046439422675748247905739 42069659134013622371858609)
      ·
        refine ⟨31552244350510216778893957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42069659134013622371858609 31552244350510216778893957)
        ·
          refine ⟨5916045815720665646042617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31552244350510216778893957 5916045815720665646042617)
          ·
            refine ⟨4437034361790499234531963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5916045815720665646042617 4437034361790499234531963)
            ·
              refine ⟨6655551542685748851797945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4437034361790499234531963 6655551542685748851797945)
              ·
                refine ⟨4991663657014311638848459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6655551542685748851797945 4991663657014311638848459)
                ·
                  refine ⟨7487495485521467458272689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4991663657014311638848459 7487495485521467458272689)
                  ·
                    refine ⟨5615621614141100593704517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7487495485521467458272689 5615621614141100593704517)
                    ·
                      refine ⟨1052929052651456361319597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5615621614141100593704517 1052929052651456361319597)
                      ·
                        rfl

theorem cell23_2050572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_2050572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2050572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2050572 prefixEnd_2050572 := by exact prefixLift 2050572
  have htrace : WordTrace (prefixWord ++ tailWord_2050572) baseStart_2050572 baseEnd_2050572 := by
    simpa [prefixWord, tailWord_2050572, baseEnd_2050572] using wordTrace_append hprefix tailTrace_2050572
  have hstable : (prefixWord ++ tailWord_2050572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050572).length < 2 ^ (prefixWord ++ tailWord_2050572).sum := by decide
  have hdescent : baseEnd_2050572 < baseStart_2050572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050573 : List Nat := [1, 7, 1, 1, 1, 2, 3, 1, 1, 5]
def baseStart_2050573 : Nat := 118140960795 + 2050573 * 2 ^ 59
def prefixEnd_2050573 : Nat := 4983230072969 + 3 ^ 40 * 2050573 * 2
def baseEnd_2050573 : Nat := 350976522044036952469031

theorem tailTrace_2050573 : CollatzResearch.WordTrace tailWord_2050573 prefixEnd_2050573 350976522044036952469031 := by
  unfold tailWord_2050573
  simp only [CollatzResearch.WordTrace]
  refine ⟨74790541600131705831868373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49860361066754470554578915 74790541600131705831868373)
  ·
    refine ⟨1752903318753086855434415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 74790541600131705831868373 1752903318753086855434415)
    ·
      refine ⟨2629354978129630283151623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1752903318753086855434415 2629354978129630283151623)
      ·
        refine ⟨3944032467194445424727435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2629354978129630283151623 3944032467194445424727435)
        ·
          refine ⟨5916048700791668137091153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3944032467194445424727435 5916048700791668137091153)
          ·
            refine ⟨4437036525593751102818365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5916048700791668137091153 4437036525593751102818365)
            ·
              refine ⟨1663888697097656663556887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4437036525593751102818365 1663888697097656663556887)
              ·
                refine ⟨2495833045646484995335331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1663888697097656663556887 2495833045646484995335331)
                ·
                  refine ⟨3743749568469727493002997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2495833045646484995335331 3743749568469727493002997)
                  ·
                    refine ⟨350976522044036952469031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3743749568469727493002997 350976522044036952469031)
                    ·
                      rfl

theorem cell23_2050573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_2050573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2050573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2050573 prefixEnd_2050573 := by exact prefixLift 2050573
  have htrace : WordTrace (prefixWord ++ tailWord_2050573) baseStart_2050573 baseEnd_2050573 := by
    simpa [prefixWord, tailWord_2050573, baseEnd_2050573] using wordTrace_append hprefix tailTrace_2050573
  have hstable : (prefixWord ++ tailWord_2050573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050573).length < 2 ^ (prefixWord ++ tailWord_2050573).sum := by decide
  have hdescent : baseEnd_2050573 < baseStart_2050573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050575 : List Nat := [1, 1, 2, 1, 1, 1, 2, 5, 3, 3, 3]
def baseStart_2050575 : Nat := 118140960795 + 2050575 * 2 ^ 59
def prefixEnd_2050575 : Nat := 4983230072969 + 3 ^ 40 * 2050575 * 2
def baseEnd_2050575 : Nat := 1052930593093419849582083

theorem tailTrace_2050575 : CollatzResearch.WordTrace tailWord_2050575 prefixEnd_2050575 1052930593093419849582083 := by
  unfold tailWord_2050575
  simp only [CollatzResearch.WordTrace]
  refine ⟨74790614546124460173441179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49860409697416306782294119 74790614546124460173441179)
  ·
    refine ⟨112185921819186690260161769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74790614546124460173441179 112185921819186690260161769)
    ·
      refine ⟨84139441364390017695121327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112185921819186690260161769 84139441364390017695121327)
      ·
        refine ⟨126209162046585026542681991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84139441364390017695121327 126209162046585026542681991)
        ·
          refine ⟨189313743069877539814022987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126209162046585026542681991 189313743069877539814022987)
          ·
            refine ⟨283970614604816309721034481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189313743069877539814022987 283970614604816309721034481)
            ·
              refine ⟨212977960953612232290775861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283970614604816309721034481 212977960953612232290775861)
              ·
                refine ⟨19966683839401146777260237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 212977960953612232290775861 19966683839401146777260237)
                ·
                  refine ⟨7487506439775430041472589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19966683839401146777260237 7487506439775430041472589)
                  ·
                    refine ⟨2807814914915786265552221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7487506439775430041472589 2807814914915786265552221)
                    ·
                      refine ⟨1052930593093419849582083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2807814914915786265552221 1052930593093419849582083)
                      ·
                        rfl

theorem cell23_2050575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 3, 3].length) (baseStart_2050575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2050575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2050575 prefixEnd_2050575 := by exact prefixLift 2050575
  have htrace : WordTrace (prefixWord ++ tailWord_2050575) baseStart_2050575 baseEnd_2050575 := by
    simpa [prefixWord, tailWord_2050575, baseEnd_2050575] using wordTrace_append hprefix tailTrace_2050575
  have hstable : (prefixWord ++ tailWord_2050575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050575).length < 2 ^ (prefixWord ++ tailWord_2050575).sum := by decide
  have hdescent : baseEnd_2050575 < baseStart_2050575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050579 : List Nat := [1, 1, 1, 2, 1, 5, 5, 1, 1, 2, 3]
def baseStart_2050579 : Nat := 118140960795 + 2050579 * 2 ^ 59
def prefixEnd_2050579 : Nat := 4983230072969 + 3 ^ 40 * 2050579 * 2
def baseEnd_2050579 : Nat := 1052932647016037833932065

theorem tailTrace_2050579 : CollatzResearch.WordTrace tailWord_2050579 prefixEnd_2050579 1052932647016037833932065 := by
  unfold tailWord_2050579
  simp only [CollatzResearch.WordTrace]
  refine ⟨74790760438109968856586791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49860506958739979237724527 74790760438109968856586791)
  ·
    refine ⟨112186140657164953284880187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74790760438109968856586791 112186140657164953284880187)
    ·
      refine ⟨168279210985747429927320281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112186140657164953284880187 168279210985747429927320281)
      ·
        refine ⟨126209408239310572445490211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168279210985747429927320281 126209408239310572445490211)
        ·
          refine ⟨189314112358965858668235317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126209408239310572445490211 189314112358965858668235317)
          ·
            refine ⟨17748198033653049250147061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 189314112358965858668235317 17748198033653049250147061)
            ·
              refine ⟨1663893565654973367201287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17748198033653049250147061 1663893565654973367201287)
              ·
                refine ⟨2495840348482460050801931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1663893565654973367201287 2495840348482460050801931)
                ·
                  refine ⟨3743760522723690076202897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2495840348482460050801931 3743760522723690076202897)
                  ·
                    refine ⟨2807820392042767557152173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3743760522723690076202897 2807820392042767557152173)
                    ·
                      refine ⟨1052932647016037833932065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2807820392042767557152173 1052932647016037833932065)
                      ·
                        rfl

theorem cell23_2050579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 1, 1, 2, 3].length) (baseStart_2050579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2050579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2050579 prefixEnd_2050579 := by exact prefixLift 2050579
  have htrace : WordTrace (prefixWord ++ tailWord_2050579) baseStart_2050579 baseEnd_2050579 := by
    simpa [prefixWord, tailWord_2050579, baseEnd_2050579] using wordTrace_append hprefix tailTrace_2050579
  have hstable : (prefixWord ++ tailWord_2050579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050579).length < 2 ^ (prefixWord ++ tailWord_2050579).sum := by decide
  have hdescent : baseEnd_2050579 < baseStart_2050579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050595 : List Nat := [1, 1, 1, 4, 4, 1, 1, 1, 2, 7]
def baseStart_2050595 : Nat := 118140960795 + 2050595 * 2 ^ 59
def prefixEnd_2050595 : Nat := 4983230072969 + 3 ^ 40 * 2050595 * 2
def baseEnd_2050595 : Nat := 350980287568836590443997

theorem tailTrace_2050595 : CollatzResearch.WordTrace tailWord_2050595 prefixEnd_2050595 350980287568836590443997 := by
  unfold tailWord_2050595
  simp only [CollatzResearch.WordTrace]
  refine ⟨74791344006052003589169239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49860896004034669059446159 74791344006052003589169239)
  ·
    refine ⟨112187016009078005383753859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74791344006052003589169239 112187016009078005383753859)
    ·
      refine ⟨168280524013617008075630789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112187016009078005383753859 168280524013617008075630789)
      ·
        refine ⟨31552598252553189014180773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168280524013617008075630789 31552598252553189014180773)
        ·
          refine ⟨5916112172353722940158895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31552598252553189014180773 5916112172353722940158895)
          ·
            refine ⟨8874168258530584410238343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5916112172353722940158895 8874168258530584410238343)
            ·
              refine ⟨13311252387795876615357515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8874168258530584410238343 13311252387795876615357515)
              ·
                refine ⟨19966878581693814923036273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13311252387795876615357515 19966878581693814923036273)
                ·
                  refine ⟨14975158936270361192277205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19966878581693814923036273 14975158936270361192277205)
                  ·
                    refine ⟨350980287568836590443997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14975158936270361192277205 350980287568836590443997)
                    ·
                      rfl

theorem cell23_2050595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 7].length) (baseStart_2050595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2050595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2050595 prefixEnd_2050595 := by exact prefixLift 2050595
  have htrace : WordTrace (prefixWord ++ tailWord_2050595) baseStart_2050595 baseEnd_2050595 := by
    simpa [prefixWord, tailWord_2050595, baseEnd_2050595] using wordTrace_append hprefix tailTrace_2050595
  have hstable : (prefixWord ++ tailWord_2050595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050595).length < 2 ^ (prefixWord ++ tailWord_2050595).sum := by decide
  have hdescent : baseEnd_2050595 < baseStart_2050595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050609 : List Nat := [1, 2, 2, 3, 1, 1, 4, 3, 2, 1, 3]
def baseStart_2050609 : Nat := 118140960795 + 2050609 * 2 ^ 59
def prefixEnd_2050609 : Nat := 4983230072969 + 3 ^ 40 * 2050609 * 2
def baseEnd_2050609 : Nat := 1052948051435672716556927

theorem tailTrace_2050609 : CollatzResearch.WordTrace tailWord_2050609 prefixEnd_2050609 1052948051435672716556927 := by
  unfold tailWord_2050609
  simp only [CollatzResearch.WordTrace]
  refine ⟨74791854628001283980178881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49861236418667522653452587 74791854628001283980178881)
  ·
    refine ⟨56093890971000962985134161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74791854628001283980178881 56093890971000962985134161)
    ·
      refine ⟨42070418228250722238850621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56093890971000962985134161 42070418228250722238850621)
      ·
        refine ⟨15776406835594020839568983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42070418228250722238850621 15776406835594020839568983)
        ·
          refine ⟨23664610253391031259353475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15776406835594020839568983 23664610253391031259353475)
          ·
            refine ⟨35496915380086546889030213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23664610253391031259353475 35496915380086546889030213)
            ·
              refine ⟨6655671633766227541693165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35496915380086546889030213 6655671633766227541693165)
              ·
                refine ⟨2495876862662335328134937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6655671633766227541693165 2495876862662335328134937)
                ·
                  refine ⟨1871907646996751496101203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2495876862662335328134937 1871907646996751496101203)
                  ·
                    refine ⟨2807861470495127244151805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1871907646996751496101203 2807861470495127244151805)
                    ·
                      refine ⟨1052948051435672716556927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2807861470495127244151805 1052948051435672716556927)
                      ·
                        rfl

theorem cell23_2050609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_2050609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2050609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2050609 prefixEnd_2050609 := by exact prefixLift 2050609
  have htrace : WordTrace (prefixWord ++ tailWord_2050609) baseStart_2050609 baseEnd_2050609 := by
    simpa [prefixWord, tailWord_2050609, baseEnd_2050609] using wordTrace_append hprefix tailTrace_2050609
  have hstable : (prefixWord ++ tailWord_2050609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050609).length < 2 ^ (prefixWord ++ tailWord_2050609).sum := by decide
  have hdescent : baseEnd_2050609 < baseStart_2050609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050615 : List Nat := [1, 1, 3, 1, 2, 3, 1, 2, 2, 3, 4]
def baseStart_2050615 : Nat := 118140960795 + 2050615 * 2 ^ 59
def prefixEnd_2050615 : Nat := 4983230072969 + 3 ^ 40 * 2050615 * 2
def baseEnd_2050615 : Nat := 1052951132319599693081899

theorem tailTrace_2050615 : CollatzResearch.WordTrace tailWord_2050615 prefixEnd_2050615 1052951132319599693081899 := by
  unfold tailWord_2050615
  simp only [CollatzResearch.WordTrace]
  refine ⟨74792073465979547004897299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49861382310653031336598199 74792073465979547004897299)
  ·
    refine ⟨112188110198969320507345949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74792073465979547004897299 112188110198969320507345949)
    ·
      refine ⟨42070541324613495190254731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112188110198969320507345949 42070541324613495190254731)
      ·
        refine ⟨63105811986920242785382097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42070541324613495190254731 63105811986920242785382097)
        ·
          refine ⟨47329358990190182089036573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63105811986920242785382097 47329358990190182089036573)
          ·
            refine ⟨17748509621321318283388715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47329358990190182089036573 17748509621321318283388715)
            ·
              refine ⟨26622764431981977425083073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17748509621321318283388715 26622764431981977425083073)
              ·
                refine ⟨19967073323986483068812305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26622764431981977425083073 19967073323986483068812305)
                ·
                  refine ⟨14975304992989862301609229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19967073323986483068812305 14975304992989862301609229)
                  ·
                    refine ⟨5615739372371198363103461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14975304992989862301609229 5615739372371198363103461)
                    ·
                      refine ⟨1052951132319599693081899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5615739372371198363103461 1052951132319599693081899)
                      ·
                        rfl

theorem cell23_2050615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 3, 4].length) (baseStart_2050615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2050615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2050615 prefixEnd_2050615 := by exact prefixLift 2050615
  have htrace : WordTrace (prefixWord ++ tailWord_2050615) baseStart_2050615 baseEnd_2050615 := by
    simpa [prefixWord, tailWord_2050615, baseEnd_2050615] using wordTrace_append hprefix tailTrace_2050615
  have hstable : (prefixWord ++ tailWord_2050615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050615).length < 2 ^ (prefixWord ++ tailWord_2050615).sum := by decide
  have hdescent : baseEnd_2050615 < baseStart_2050615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050630 : List Nat := [6, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3]
def baseStart_2050630 : Nat := 118140960795 + 2050630 * 2 ^ 59
def prefixEnd_2050630 : Nat := 4983230072969 + 3 ^ 40 * 2050630 * 2
def baseEnd_2050630 : Nat := 1052958834529417134394331

theorem tailTrace_2050630 : CollatzResearch.WordTrace tailWord_2050630 prefixEnd_2050630 1052958834529417134394331 := by
  unfold tailWord_2050630
  simp only [CollatzResearch.WordTrace]
  refine ⟨2337269392528912642709167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 49861747040616803044462229 2337269392528912642709167)
  ·
    refine ⟨3505904088793368964063751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2337269392528912642709167 3505904088793368964063751)
    ·
      refine ⟨5258856133190053446095627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3505904088793368964063751 5258856133190053446095627)
      ·
        refine ⟨7888284199785080169143441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5258856133190053446095627 7888284199785080169143441)
        ·
          refine ⟨5916213149838810126857581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7888284199785080169143441 5916213149838810126857581)
          ·
            refine ⟨2218579931189553797571593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5916213149838810126857581 2218579931189553797571593)
            ·
              refine ⟨1663934948392165348178695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2218579931189553797571593 1663934948392165348178695)
              ·
                refine ⟨2495902422588248022268043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1663934948392165348178695 2495902422588248022268043)
                ·
                  refine ⟨3743853633882372033402065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2495902422588248022268043 3743853633882372033402065)
                  ·
                    refine ⟨2807890225411779025051549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3743853633882372033402065 2807890225411779025051549)
                    ·
                      refine ⟨1052958834529417134394331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2807890225411779025051549 1052958834529417134394331)
                      ·
                        rfl

theorem cell23_2050630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_2050630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2050630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2050630 prefixEnd_2050630 := by exact prefixLift 2050630
  have htrace : WordTrace (prefixWord ++ tailWord_2050630) baseStart_2050630 baseEnd_2050630 := by
    simpa [prefixWord, tailWord_2050630, baseEnd_2050630] using wordTrace_append hprefix tailTrace_2050630
  have hstable : (prefixWord ++ tailWord_2050630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050630).length < 2 ^ (prefixWord ++ tailWord_2050630).sum := by decide
  have hdescent : baseEnd_2050630 < baseStart_2050630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050635 : List Nat := [1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 5]
def baseStart_2050635 : Nat := 118140960795 + 2050635 * 2 ^ 59
def prefixEnd_2050635 : Nat := 4983230072969 + 3 ^ 40 * 2050635 * 2
def baseEnd_2050635 : Nat := 1052961401932689614831807

theorem tailTrace_2050635 : CollatzResearch.WordTrace tailWord_2050635 prefixEnd_2050635 1052961401932689614831807 := by
  unfold tailWord_2050635
  simp only [CollatzResearch.WordTrace]
  refine ⟨74792802925907090420625359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49861868617271393613750239 74792802925907090420625359)
  ·
    refine ⟨112189204388860635630938039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74792802925907090420625359 112189204388860635630938039)
    ·
      refine ⟨168283806583290953446407059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112189204388860635630938039 168283806583290953446407059)
      ·
        refine ⟨252425709874936430169610589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168283806583290953446407059 252425709874936430169610589)
        ·
          refine ⟨94659641203101161313603971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252425709874936430169610589 94659641203101161313603971)
          ·
            refine ⟨141989461804651741970405957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94659641203101161313603971 141989461804651741970405957)
            ·
              refine ⟨26623024088372201619451117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141989461804651741970405957 26623024088372201619451117)
              ·
                refine ⟨9983634033139575607294169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26623024088372201619451117 9983634033139575607294169)
                ·
                  refine ⟨7487725524854681705470627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9983634033139575607294169 7487725524854681705470627)
                  ·
                    refine ⟨11231588287282022558205941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7487725524854681705470627 11231588287282022558205941)
                    ·
                      refine ⟨1052961401932689614831807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11231588287282022558205941 1052961401932689614831807)
                      ·
                        rfl

theorem cell23_2050635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 5].length) (baseStart_2050635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2050635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2050635 prefixEnd_2050635 := by exact prefixLift 2050635
  have htrace : WordTrace (prefixWord ++ tailWord_2050635) baseStart_2050635 baseEnd_2050635 := by
    simpa [prefixWord, tailWord_2050635, baseEnd_2050635] using wordTrace_append hprefix tailTrace_2050635
  have hstable : (prefixWord ++ tailWord_2050635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050635).length < 2 ^ (prefixWord ++ tailWord_2050635).sum := by decide
  have hdescent : baseEnd_2050635 < baseStart_2050635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050712 : List Nat := [2, 1, 2, 4, 1, 1, 3, 1, 1, 2, 5]
def baseStart_2050712 : Nat := 118140960795 + 2050712 * 2 ^ 59
def prefixEnd_2050712 : Nat := 4983230072969 + 3 ^ 40 * 2050712 * 2
def baseEnd_2050712 : Nat := 1053000939943085813568953

theorem tailTrace_2050712 : CollatzResearch.WordTrace tailWord_2050712 prefixEnd_2050712 1053000939943085813568953 := by
  unfold tailWord_2050712
  simp only [CollatzResearch.WordTrace]
  refine ⟨37397805673314066285589195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49863740897752088380785593 37397805673314066285589195)
  ·
    refine ⟨56096708509971099428383793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37397805673314066285589195 56096708509971099428383793)
    ·
      refine ⟨42072531382478324571287845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56096708509971099428383793 42072531382478324571287845)
      ·
        refine ⟨7888599634214685857116471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42072531382478324571287845 7888599634214685857116471)
        ·
          refine ⟨11832899451322028785674707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7888599634214685857116471 11832899451322028785674707)
          ·
            refine ⟨17749349176983043178512061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11832899451322028785674707 17749349176983043178512061)
            ·
              refine ⟨6656005941368641191942023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17749349176983043178512061 6656005941368641191942023)
              ·
                refine ⟨9984008912052961787913035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6656005941368641191942023 9984008912052961787913035)
                ·
                  refine ⟨14976013368079442681869553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9984008912052961787913035 14976013368079442681869553)
                  ·
                    refine ⟨11232010026059582011402165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14976013368079442681869553 11232010026059582011402165)
                    ·
                      refine ⟨1053000939943085813568953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11232010026059582011402165 1053000939943085813568953)
                      ·
                        rfl

theorem cell23_2050712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_2050712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2050712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2050712 prefixEnd_2050712 := by exact prefixLift 2050712
  have htrace : WordTrace (prefixWord ++ tailWord_2050712) baseStart_2050712 baseEnd_2050712 := by
    simpa [prefixWord, tailWord_2050712, baseEnd_2050712] using wordTrace_append hprefix tailTrace_2050712
  have hstable : (prefixWord ++ tailWord_2050712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050712).length < 2 ^ (prefixWord ++ tailWord_2050712).sum := by decide
  have hdescent : baseEnd_2050712 < baseStart_2050712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050739 : List Nat := [1, 1, 1, 2, 3, 5, 2, 1, 2, 1, 4]
def baseStart_2050739 : Nat := 118140960795 + 2050739 * 2 ^ 59
def prefixEnd_2050739 : Nat := 4983230072969 + 3 ^ 40 * 2050739 * 2
def baseEnd_2050739 : Nat := 1053014803920757207931329

theorem tailTrace_2050739 : CollatzResearch.WordTrace tailWord_2050739 prefixEnd_2050739 1053014803920757207931329 := by
  unfold tailWord_2050739
  simp only [CollatzResearch.WordTrace]
  refine ⟨74796596117530316182411271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49864397411686877454940847 74796596117530316182411271)
  ·
    refine ⟨112194894176295474273616907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74796596117530316182411271 112194894176295474273616907)
    ·
      refine ⟨168292341264443211410425361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112194894176295474273616907 168292341264443211410425361)
      ·
        refine ⟨126219255948332408557819021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168292341264443211410425361 126219255948332408557819021)
        ·
          refine ⟨47332220980624653209182133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126219255948332408557819021 47332220980624653209182133)
          ·
            refine ⟨4437395716933561238360825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47332220980624653209182133 4437395716933561238360825)
            ·
              refine ⟨3328046787700170928770619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4437395716933561238360825 3328046787700170928770619)
              ·
                refine ⟨4992070181550256393155929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3328046787700170928770619 4992070181550256393155929)
                ·
                  refine ⟨3744052636162692294866947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4992070181550256393155929 3744052636162692294866947)
                  ·
                    refine ⟨5616078954244038442300421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3744052636162692294866947 5616078954244038442300421)
                    ·
                      refine ⟨1053014803920757207931329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5616078954244038442300421 1053014803920757207931329)
                      ·
                        rfl

theorem cell23_2050739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 2, 1, 4].length) (baseStart_2050739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2050739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2050739 prefixEnd_2050739 := by exact prefixLift 2050739
  have htrace : WordTrace (prefixWord ++ tailWord_2050739) baseStart_2050739 baseEnd_2050739 := by
    simpa [prefixWord, tailWord_2050739, baseEnd_2050739] using wordTrace_append hprefix tailTrace_2050739
  have hstable : (prefixWord ++ tailWord_2050739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050739).length < 2 ^ (prefixWord ++ tailWord_2050739).sum := by decide
  have hdescent : baseEnd_2050739 < baseStart_2050739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050773 : List Nat := [1, 3, 2, 5, 1, 1, 1, 1, 2, 4, 2]
def baseStart_2050773 : Nat := 118140960795 + 2050773 * 2 ^ 59
def prefixEnd_2050773 : Nat := 4983230072969 + 3 ^ 40 * 2050773 * 2
def baseEnd_2050773 : Nat := 1053032262263010074906173

theorem tailTrace_2050773 : CollatzResearch.WordTrace tailWord_2050773 prefixEnd_2050773 1053032262263010074906173 := by
  unfold tailWord_2050773
  simp only [CollatzResearch.WordTrace]
  refine ⟨74797836199407139989148973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49865224132938093326099315 74797836199407139989148973)
  ·
    refine ⟨28049188574777677495930865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74797836199407139989148973 28049188574777677495930865)
    ·
      refine ⟨21036891431083258121948149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28049188574777677495930865 21036891431083258121948149)
      ·
        refine ⟨1972208571664055448932639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21036891431083258121948149 1972208571664055448932639)
        ·
          refine ⟨2958312857496083173398959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1972208571664055448932639 2958312857496083173398959)
          ·
            refine ⟨4437469286244124760098439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2958312857496083173398959 4437469286244124760098439)
            ·
              refine ⟨6656203929366187140147659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4437469286244124760098439 6656203929366187140147659)
              ·
                refine ⟨9984305894049280710221489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6656203929366187140147659 9984305894049280710221489)
                ·
                  refine ⟨7488229420536960532666117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9984305894049280710221489 7488229420536960532666117)
                  ·
                    refine ⟨1404043016350680099874897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7488229420536960532666117 1404043016350680099874897)
                    ·
                      refine ⟨1053032262263010074906173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1404043016350680099874897 1053032262263010074906173)
                      ·
                        rfl

theorem cell23_2050773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_2050773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2050773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2050773 prefixEnd_2050773 := by exact prefixLift 2050773
  have htrace : WordTrace (prefixWord ++ tailWord_2050773) baseStart_2050773 baseEnd_2050773 := by
    simpa [prefixWord, tailWord_2050773, baseEnd_2050773] using wordTrace_append hprefix tailTrace_2050773
  have hstable : (prefixWord ++ tailWord_2050773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050773).length < 2 ^ (prefixWord ++ tailWord_2050773).sum := by decide
  have hdescent : baseEnd_2050773 < baseStart_2050773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050806 : List Nat := [5, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3]
def baseStart_2050806 : Nat := 118140960795 + 2050806 * 2 ^ 59
def prefixEnd_2050806 : Nat := 4983230072969 + 3 ^ 40 * 2050806 * 2
def baseEnd_2050806 : Nat := 1053049207124608445793521

theorem tailTrace_2050806 : CollatzResearch.WordTrace tailWord_2050806 prefixEnd_2050806 1053049207124608445793521 := by
  unfold tailWord_2050806
  simp only [CollatzResearch.WordTrace]
  refine ⟨4674939988017974164068767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49866026538858391083400181 4674939988017974164068767)
  ·
    refine ⟨7012409982026961246103151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4674939988017974164068767 7012409982026961246103151)
    ·
      refine ⟨10518614973040441869154727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7012409982026961246103151 10518614973040441869154727)
      ·
        refine ⟨15777922459560662803732091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10518614973040441869154727 15777922459560662803732091)
        ·
          refine ⟨23666883689340994205598137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15777922459560662803732091 23666883689340994205598137)
          ·
            refine ⟨17750162767005745654198603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23666883689340994205598137 17750162767005745654198603)
            ·
              refine ⟨26625244150508618481297905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17750162767005745654198603 26625244150508618481297905)
              ·
                refine ⟨19968933112881463860973429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26625244150508618481297905 19968933112881463860973429)
                ·
                  refine ⟨1872087479332637236966259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19968933112881463860973429 1872087479332637236966259)
                  ·
                    refine ⟨2808131218998955855449389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1872087479332637236966259 2808131218998955855449389)
                    ·
                      refine ⟨1053049207124608445793521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2808131218998955855449389 1053049207124608445793521)
                      ·
                        rfl

theorem cell23_2050806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_2050806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2050806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2050806 prefixEnd_2050806 := by exact prefixLift 2050806
  have htrace : WordTrace (prefixWord ++ tailWord_2050806) baseStart_2050806 baseEnd_2050806 := by
    simpa [prefixWord, tailWord_2050806, baseEnd_2050806] using wordTrace_append hprefix tailTrace_2050806
  have hstable : (prefixWord ++ tailWord_2050806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050806).length < 2 ^ (prefixWord ++ tailWord_2050806).sum := by decide
  have hdescent : baseEnd_2050806 < baseStart_2050806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050823 : List Nat := [1, 1, 4, 4, 1, 2, 2, 1, 3, 1, 3]
def baseStart_2050823 : Nat := 118140960795 + 2050823 * 2 ^ 59
def prefixEnd_2050823 : Nat := 4983230072969 + 3 ^ 40 * 2050823 * 2
def baseEnd_2050823 : Nat := 1053057936295734879280943

theorem tailTrace_2050823 : CollatzResearch.WordTrace tailWord_2050823 prefixEnd_2050823 1053057936295734879280943 := by
  unfold tailWord_2050823
  simp only [CollatzResearch.WordTrace]
  refine ⟨74799659849225998528469123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49866439899483999018979415 74799659849225998528469123)
  ·
    refine ⟨112199489773838997792703685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74799659849225998528469123 112199489773838997792703685)
    ·
      refine ⟨21037404332594812086131941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112199489773838997792703685 21037404332594812086131941)
      ·
        refine ⟨3944513312361527266149739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21037404332594812086131941 3944513312361527266149739)
        ·
          refine ⟨5916769968542290899224609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3944513312361527266149739 5916769968542290899224609)
          ·
            refine ⟨4437577476406718174418457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5916769968542290899224609 4437577476406718174418457)
            ·
              refine ⟨3328183107305038630813843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4437577476406718174418457 3328183107305038630813843)
              ·
                refine ⟨4992274660957557946220765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3328183107305038630813843 4992274660957557946220765)
                ·
                  refine ⟨1872102997859084229832787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4992274660957557946220765 1872102997859084229832787)
                  ·
                    refine ⟨2808154496788626344749181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1872102997859084229832787 2808154496788626344749181)
                    ·
                      refine ⟨1053057936295734879280943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2808154496788626344749181 1053057936295734879280943)
                      ·
                        rfl

theorem cell23_2050823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_2050823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2050823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2050823 prefixEnd_2050823 := by exact prefixLift 2050823
  have htrace : WordTrace (prefixWord ++ tailWord_2050823) baseStart_2050823 baseEnd_2050823 := by
    simpa [prefixWord, tailWord_2050823, baseEnd_2050823] using wordTrace_append hprefix tailTrace_2050823
  have hstable : (prefixWord ++ tailWord_2050823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050823).length < 2 ^ (prefixWord ++ tailWord_2050823).sum := by decide
  have hdescent : baseEnd_2050823 < baseStart_2050823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050866 : List Nat := [3, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3]
def baseStart_2050866 : Nat := 118140960795 + 2050866 * 2 ^ 59
def prefixEnd_2050866 : Nat := 4983230072969 + 3 ^ 40 * 2050866 * 2
def baseEnd_2050866 : Nat := 1053080015963878211043245

theorem tailTrace_2050866 : CollatzResearch.WordTrace tailWord_2050866 prefixEnd_2050866 1053080015963878211043245 := by
  unfold tailWord_2050866
  simp only [CollatzResearch.WordTrace]
  refine ⟨18700307047017554218071113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49867485458713477914856301 18700307047017554218071113)
  ·
    refine ⟨14025230285263165663553335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18700307047017554218071113 14025230285263165663553335)
    ·
      refine ⟨21037845427894748495330003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14025230285263165663553335 21037845427894748495330003)
      ·
        refine ⟨31556768141842122742995005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21037845427894748495330003 31556768141842122742995005)
        ·
          refine ⟨11833788053190796028623127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31556768141842122742995005 11833788053190796028623127)
          ·
            refine ⟨17750682079786194042934691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11833788053190796028623127 17750682079786194042934691)
            ·
              refine ⟨26626023119679291064402037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17750682079786194042934691 26626023119679291064402037)
              ·
                refine ⟨2496189667469933537287691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26626023119679291064402037 2496189667469933537287691)
                ·
                  refine ⟨3744284501204900305931537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2496189667469933537287691 3744284501204900305931537)
                  ·
                    refine ⟨2808213375903675229448653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3744284501204900305931537 2808213375903675229448653)
                    ·
                      refine ⟨1053080015963878211043245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2808213375903675229448653 1053080015963878211043245)
                      ·
                        rfl

theorem cell23_2050866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3].length) (baseStart_2050866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2050866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2050866 prefixEnd_2050866 := by exact prefixLift 2050866
  have htrace : WordTrace (prefixWord ++ tailWord_2050866) baseStart_2050866 baseEnd_2050866 := by
    simpa [prefixWord, tailWord_2050866, baseEnd_2050866] using wordTrace_append hprefix tailTrace_2050866
  have hstable : (prefixWord ++ tailWord_2050866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050866).length < 2 ^ (prefixWord ++ tailWord_2050866).sum := by decide
  have hdescent : baseEnd_2050866 < baseStart_2050866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050869 : List Nat := [1, 3, 3, 1, 3, 3, 9]
def baseStart_2050869 : Nat := 118140960795 + 2050869 * 2 ^ 59
def prefixEnd_2050869 : Nat := 4983230072969 + 3 ^ 40 * 2050869 * 2
def baseEnd_2050869 : Nat := 13001006869207922213651

theorem tailTrace_2050869 : CollatzResearch.WordTrace tailWord_2050869 prefixEnd_2050869 13001006869207922213651 := by
  unfold tailWord_2050869
  simp only [CollatzResearch.WordTrace]
  refine ⟨74801337607059348384643661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49867558404706232256429107 74801337607059348384643661)
  ·
    refine ⟨28050501602647255644241373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74801337607059348384643661 28050501602647255644241373)
    ·
      refine ⟨10518938100992720866590515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28050501602647255644241373 10518938100992720866590515)
      ·
        refine ⟨15778407151489081299885773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10518938100992720866590515 15778407151489081299885773)
        ·
          refine ⟨5916902681808405487457165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15778407151489081299885773 5916902681808405487457165)
          ·
            refine ⟨2218838505678152057796437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5916902681808405487457165 2218838505678152057796437)
            ·
              refine ⟨13001006869207922213651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2218838505678152057796437 13001006869207922213651)
              ·
                rfl

theorem cell23_2050869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 9].length) (baseStart_2050869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2050869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2050869 prefixEnd_2050869 := by exact prefixLift 2050869
  have htrace : WordTrace (prefixWord ++ tailWord_2050869) baseStart_2050869 baseEnd_2050869 := by
    simpa [prefixWord, tailWord_2050869, baseEnd_2050869] using wordTrace_append hprefix tailTrace_2050869
  have hstable : (prefixWord ++ tailWord_2050869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050869).length < 2 ^ (prefixWord ++ tailWord_2050869).sum := by decide
  have hdescent : baseEnd_2050869 < baseStart_2050869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050900 : List Nat := [2, 4, 1, 1, 4, 2, 1, 2, 1, 2, 3]
def baseStart_2050900 : Nat := 118140960795 + 2050900 * 2 ^ 59
def prefixEnd_2050900 : Nat := 4983230072969 + 3 ^ 40 * 2050900 * 2
def baseEnd_2050900 : Nat := 1053097474306131078018089

theorem tailTrace_2050900 : CollatzResearch.WordTrace tailWord_2050900 prefixEnd_2050900 1053097474306131078018089 := by
  unfold tailWord_2050900
  simp only [CollatzResearch.WordTrace]
  refine ⟨37401234134973520339511077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49868312179964693786014769 37401234134973520339511077)
  ·
    refine ⟨7012731400307535063658327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37401234134973520339511077 7012731400307535063658327)
    ·
      refine ⟨10519097100461302595487491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7012731400307535063658327 10519097100461302595487491)
      ·
        refine ⟨15778645650691953893231237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10519097100461302595487491 15778645650691953893231237)
        ·
          refine ⟨2958496059504741354980857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15778645650691953893231237 2958496059504741354980857)
          ·
            refine ⟨2218872044628556016235643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2958496059504741354980857 2218872044628556016235643)
            ·
              refine ⟨3328308066942834024353465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2218872044628556016235643 3328308066942834024353465)
              ·
                refine ⟨2496231050207125518265099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3328308066942834024353465 2496231050207125518265099)
                ·
                  refine ⟨3744346575310688277397649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2496231050207125518265099 3744346575310688277397649)
                  ·
                    refine ⟨2808259931483016208048237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3744346575310688277397649 2808259931483016208048237)
                    ·
                      refine ⟨1053097474306131078018089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2808259931483016208048237 1053097474306131078018089)
                      ·
                        rfl

theorem cell23_2050900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_2050900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2050900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2050900 prefixEnd_2050900 := by exact prefixLift 2050900
  have htrace : WordTrace (prefixWord ++ tailWord_2050900) baseStart_2050900 baseEnd_2050900 := by
    simpa [prefixWord, tailWord_2050900, baseEnd_2050900] using wordTrace_append hprefix tailTrace_2050900
  have hstable : (prefixWord ++ tailWord_2050900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050900).length < 2 ^ (prefixWord ++ tailWord_2050900).sum := by decide
  have hdescent : baseEnd_2050900 < baseStart_2050900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050939 : List Nat := [1, 1, 1, 1, 1, 5, 3, 1, 2, 4, 3]
def baseStart_2050939 : Nat := 118140960795 + 2050939 * 2 ^ 59
def prefixEnd_2050939 : Nat := 4983230072969 + 3 ^ 40 * 2050939 * 2
def baseEnd_2050939 : Nat := 1053117500051656425430409

theorem tailTrace_2050939 : CollatzResearch.WordTrace tailWord_2050939 prefixEnd_2050939 1053117500051656425430409 := by
  unfold tailWord_2050939
  simp only [CollatzResearch.WordTrace]
  refine ⟨74803890716805750339691871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49869260477870500226461247 74803890716805750339691871)
  ·
    refine ⟨112205836075208625509537807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74803890716805750339691871 112205836075208625509537807)
    ·
      refine ⟨168308754112812938264306711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112205836075208625509537807 168308754112812938264306711)
      ·
        refine ⟨252463131169219407396460067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168308754112812938264306711 252463131169219407396460067)
        ·
          refine ⟨378694696753829111094690101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252463131169219407396460067 378694696753829111094690101)
          ·
            refine ⟨35502627820671479165127197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 378694696753829111094690101 35502627820671479165127197)
            ·
              refine ⟨13313485432751804686922699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35502627820671479165127197 13313485432751804686922699)
              ·
                refine ⟨19970228149127707030384049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13313485432751804686922699 19970228149127707030384049)
                ·
                  refine ⟨14977671111845780272788037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19970228149127707030384049 14977671111845780272788037)
                  ·
                    refine ⟨2808313333471083801147757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14977671111845780272788037 2808313333471083801147757)
                    ·
                      refine ⟨1053117500051656425430409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2808313333471083801147757 1053117500051656425430409)
                      ·
                        rfl

theorem cell23_2050939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 4, 3].length) (baseStart_2050939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2050939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2050939 prefixEnd_2050939 := by exact prefixLift 2050939
  have htrace : WordTrace (prefixWord ++ tailWord_2050939) baseStart_2050939 baseEnd_2050939 := by
    simpa [prefixWord, tailWord_2050939, baseEnd_2050939] using wordTrace_append hprefix tailTrace_2050939
  have hstable : (prefixWord ++ tailWord_2050939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050939).length < 2 ^ (prefixWord ++ tailWord_2050939).sum := by decide
  have hdescent : baseEnd_2050939 < baseStart_2050939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050949 : List Nat := [1, 3, 1, 1, 3, 3, 1, 1, 1, 4, 4]
def baseStart_2050949 : Nat := 118140960795 + 2050949 * 2 ^ 59
def prefixEnd_2050949 : Nat := 4983230072969 + 3 ^ 40 * 2050949 * 2
def baseEnd_2050949 : Nat := 1053122634858201386305363

theorem tailTrace_2050949 : CollatzResearch.WordTrace tailWord_2050949 prefixEnd_2050949 1053122634858201386305363 := by
  unfold tailWord_2050949
  simp only [CollatzResearch.WordTrace]
  refine ⟨74804255446769522047555901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49869503631179681365037267 74804255446769522047555901)
  ·
    refine ⟨28051595792538570767833463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74804255446769522047555901 28051595792538570767833463)
    ·
      refine ⟨42077393688807856151750195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28051595792538570767833463 42077393688807856151750195)
      ·
        refine ⟨63116090533211784227625293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42077393688807856151750195 63116090533211784227625293)
        ·
          refine ⟨23668533949954419085359485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63116090533211784227625293 23668533949954419085359485)
          ·
            refine ⟨8875700231232907157009807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23668533949954419085359485 8875700231232907157009807)
            ·
              refine ⟨13313550346849360735514711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8875700231232907157009807 13313550346849360735514711)
              ·
                refine ⟨19970325520274041103272067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13313550346849360735514711 19970325520274041103272067)
                ·
                  refine ⟨29955488280411061654908101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19970325520274041103272067 29955488280411061654908101)
                  ·
                    refine ⟨5616654052577074060295269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29955488280411061654908101 5616654052577074060295269)
                    ·
                      refine ⟨1053122634858201386305363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5616654052577074060295269 1053122634858201386305363)
                      ·
                        rfl

theorem cell23_2050949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 4, 4].length) (baseStart_2050949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2050949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2050949 prefixEnd_2050949 := by exact prefixLift 2050949
  have htrace : WordTrace (prefixWord ++ tailWord_2050949) baseStart_2050949 baseEnd_2050949 := by
    simpa [prefixWord, tailWord_2050949, baseEnd_2050949] using wordTrace_append hprefix tailTrace_2050949
  have hstable : (prefixWord ++ tailWord_2050949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050949).length < 2 ^ (prefixWord ++ tailWord_2050949).sum := by decide
  have hdescent : baseEnd_2050949 < baseStart_2050949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050953 : List Nat := [1, 2, 1, 1, 5, 3, 2, 1, 1, 4, 2]
def baseStart_2050953 : Nat := 118140960795 + 2050953 * 2 ^ 59
def prefixEnd_2050953 : Nat := 4983230072969 + 3 ^ 40 * 2050953 * 2
def baseEnd_2050953 : Nat := 1053124688780819370655345

theorem tailTrace_2050953 : CollatzResearch.WordTrace tailWord_2050953 prefixEnd_2050953 1053124688780819370655345 := by
  unfold tailWord_2050953
  simp only [CollatzResearch.WordTrace]
  refine ⟨74804401338755030730701513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49869600892503353820467675 74804401338755030730701513)
  ·
    refine ⟨56103301004066273048026135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74804401338755030730701513 56103301004066273048026135)
    ·
      refine ⟨84154951506099409572039203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56103301004066273048026135 84154951506099409572039203)
      ·
        refine ⟨126232427259149114358058805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84154951506099409572039203 126232427259149114358058805)
        ·
          refine ⟨11834290055545229471068013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 126232427259149114358058805 11834290055545229471068013)
          ·
            refine ⟨4437858770829461051650505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11834290055545229471068013 4437858770829461051650505)
            ·
              refine ⟨3328394078122095788737879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4437858770829461051650505 3328394078122095788737879)
              ·
                refine ⟨4992591117183143683106819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3328394078122095788737879 4992591117183143683106819)
                ·
                  refine ⟨7488886675774715524660229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4992591117183143683106819 7488886675774715524660229)
                  ·
                    refine ⟨1404166251707759160873793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7488886675774715524660229 1404166251707759160873793)
                    ·
                      refine ⟨1053124688780819370655345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1404166251707759160873793 1053124688780819370655345)
                      ·
                        rfl

theorem cell23_2050953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 4, 2].length) (baseStart_2050953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2050953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2050953 prefixEnd_2050953 := by exact prefixLift 2050953
  have htrace : WordTrace (prefixWord ++ tailWord_2050953) baseStart_2050953 baseEnd_2050953 := by
    simpa [prefixWord, tailWord_2050953, baseEnd_2050953] using wordTrace_append hprefix tailTrace_2050953
  have hstable : (prefixWord ++ tailWord_2050953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050953).length < 2 ^ (prefixWord ++ tailWord_2050953).sum := by decide
  have hdescent : baseEnd_2050953 < baseStart_2050953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050969 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 3, 5, 3]
def baseStart_2050969 : Nat := 118140960795 + 2050969 * 2 ^ 59
def prefixEnd_2050969 : Nat := 4983230072969 + 3 ^ 40 * 2050969 * 2
def baseEnd_2050969 : Nat := 1053132904471291308055271

theorem tailTrace_2050969 : CollatzResearch.WordTrace tailWord_2050969 prefixEnd_2050969 1053132904471291308055271 := by
  unfold tailWord_2050969
  simp only [CollatzResearch.WordTrace]
  refine ⟨74804984906697065463283961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49869989937798043642189307 74804984906697065463283961)
  ·
    refine ⟨56103738680022799097462971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74804984906697065463283961 56103738680022799097462971)
    ·
      refine ⟨84155608020034198646194457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56103738680022799097462971 84155608020034198646194457)
      ·
        refine ⟨63116706015025648984645843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84155608020034198646194457 63116706015025648984645843)
        ·
          refine ⟨94675059022538473476968765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63116706015025648984645843 94675059022538473476968765)
          ·
            refine ⟨35503147133451927553863287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94675059022538473476968765 35503147133451927553863287)
            ·
              refine ⟨53254720700177891330794931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35503147133451927553863287 53254720700177891330794931)
              ·
                refine ⟨79882081050266836996192397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53254720700177891330794931 79882081050266836996192397)
                ·
                  refine ⟨29955780393850063873572149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79882081050266836996192397 29955780393850063873572149)
                  ·
                    refine ⟨2808354411923443488147389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29955780393850063873572149 2808354411923443488147389)
                    ·
                      refine ⟨1053132904471291308055271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2808354411923443488147389 1053132904471291308055271)
                      ·
                        rfl

theorem cell23_2050969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 5, 3].length) (baseStart_2050969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2050969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2050969 prefixEnd_2050969 := by exact prefixLift 2050969
  have htrace : WordTrace (prefixWord ++ tailWord_2050969) baseStart_2050969 baseEnd_2050969 := by
    simpa [prefixWord, tailWord_2050969, baseEnd_2050969] using wordTrace_append hprefix tailTrace_2050969
  have hstable : (prefixWord ++ tailWord_2050969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050969).length < 2 ^ (prefixWord ++ tailWord_2050969).sum := by decide
  have hdescent : baseEnd_2050969 < baseStart_2050969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050976 : List Nat := [2, 1, 1, 4, 1, 1, 3, 5, 5]
def baseStart_2050976 : Nat := 118140960795 + 2050976 * 2 ^ 59
def prefixEnd_2050976 : Nat := 4983230072969 + 3 ^ 40 * 2050976 * 2
def baseEnd_2050976 : Nat := 117015166537319197851971

theorem tailTrace_2050976 : CollatzResearch.WordTrace tailWord_2050976 prefixEnd_2050976 117015166537319197851971 := by
  unfold tailWord_2050976
  simp only [CollatzResearch.WordTrace]
  refine ⟨37402620108835852829394391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49870160145114470439192521 37402620108835852829394391)
  ·
    refine ⟨56103930163253779244091587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37402620108835852829394391 56103930163253779244091587)
    ·
      refine ⟨84155895244880668866137381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56103930163253779244091587 84155895244880668866137381)
      ·
        refine ⟨15779230358415125412400759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84155895244880668866137381 15779230358415125412400759)
        ·
          refine ⟨23668845537622688118601139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15779230358415125412400759 23668845537622688118601139)
          ·
            refine ⟨35503268306434032177901709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23668845537622688118601139 35503268306434032177901709)
            ·
              refine ⟨13313725614912762066713141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35503268306434032177901709 13313725614912762066713141)
              ·
                refine ⟨1248161776398071443754357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13313725614912762066713141 1248161776398071443754357)
                ·
                  refine ⟨117015166537319197851971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1248161776398071443754357 117015166537319197851971)
                  ·
                    rfl

theorem cell23_2050976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 5, 5].length) (baseStart_2050976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2050976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2050976 prefixEnd_2050976 := by exact prefixLift 2050976
  have htrace : WordTrace (prefixWord ++ tailWord_2050976) baseStart_2050976 baseEnd_2050976 := by
    simpa [prefixWord, tailWord_2050976, baseEnd_2050976] using wordTrace_append hprefix tailTrace_2050976
  have hstable : (prefixWord ++ tailWord_2050976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050976).length < 2 ^ (prefixWord ++ tailWord_2050976).sum := by decide
  have hdescent : baseEnd_2050976 < baseStart_2050976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050999 : List Nat := [1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 5]
def baseStart_2050999 : Nat := 118140960795 + 2050999 * 2 ^ 59
def prefixEnd_2050999 : Nat := 4983230072969 + 3 ^ 40 * 2050999 * 2
def baseEnd_2050999 : Nat := 1053148308890926190680133

theorem tailTrace_2050999 : CollatzResearch.WordTrace tailWord_2050999 prefixEnd_2050999 1053148308890926190680133 := by
  unfold tailWord_2050999
  simp only [CollatzResearch.WordTrace]
  refine ⟨74806079096588380586876051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49870719397725587057917367 74806079096588380586876051)
  ·
    refine ⟨112209118644882570880314077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74806079096588380586876051 112209118644882570880314077)
    ·
      refine ⟨42078419491830964080117779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112209118644882570880314077 42078419491830964080117779)
      ·
        refine ⟨63117629237746446120176669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42078419491830964080117779 63117629237746446120176669)
        ·
          refine ⟨23669110964154917295066251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63117629237746446120176669 23669110964154917295066251)
          ·
            refine ⟨35503666446232375942599377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23669110964154917295066251 35503666446232375942599377)
            ·
              refine ⟨26627749834674281956949533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35503666446232375942599377 26627749834674281956949533)
              ·
                refine ⟨9985406188002855733856075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26627749834674281956949533 9985406188002855733856075)
                ·
                  refine ⟨14978109282004283600784113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9985406188002855733856075 14978109282004283600784113)
                  ·
                    refine ⟨11233581961503212700588085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14978109282004283600784113 11233581961503212700588085)
                    ·
                      refine ⟨1053148308890926190680133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11233581961503212700588085 1053148308890926190680133)
                      ·
                        rfl

theorem cell23_2050999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 5].length) (baseStart_2050999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2050999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2050999 prefixEnd_2050999 := by exact prefixLift 2050999
  have htrace : WordTrace (prefixWord ++ tailWord_2050999) baseStart_2050999 baseEnd_2050999 := by
    simpa [prefixWord, tailWord_2050999, baseEnd_2050999] using wordTrace_append hprefix tailTrace_2050999
  have hstable : (prefixWord ++ tailWord_2050999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050999).length < 2 ^ (prefixWord ++ tailWord_2050999).sum := by decide
  have hdescent : baseEnd_2050999 < baseStart_2050999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051089 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 7]
def baseStart_2051089 : Nat := 118140960795 + 2051089 * 2 ^ 59
def prefixEnd_2051089 : Nat := 4983230072969 + 3 ^ 40 * 2051089 * 2
def baseEnd_2051089 : Nat := 1053194522149830838554719

theorem tailTrace_2051089 : CollatzResearch.WordTrace tailWord_2051089 prefixEnd_2051089 1053194522149830838554719 := by
  unfold tailWord_2051089
  simp only [CollatzResearch.WordTrace]
  refine ⟨74809361666262325957652321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49872907777508217305101547 74809361666262325957652321)
  ·
    refine ⟨56107021249696744468239241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74809361666262325957652321 56107021249696744468239241)
    ·
      refine ⟨42080265937272558351179431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56107021249696744468239241 42080265937272558351179431)
      ·
        refine ⟨63120398905908837526769147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42080265937272558351179431 63120398905908837526769147)
        ·
          refine ⟨94680598358863256290153721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63120398905908837526769147 94680598358863256290153721)
          ·
            refine ⟨71010448769147442217615291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94680598358863256290153721 71010448769147442217615291)
            ·
              refine ⟨106515673153721163326422937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71010448769147442217615291 106515673153721163326422937)
              ·
                refine ⟨79886754865290872494817203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106515673153721163326422937 79886754865290872494817203)
                ·
                  refine ⟨119830132297936308742225805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79886754865290872494817203 119830132297936308742225805)
                  ·
                    refine ⟨44936299611726115778334677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 119830132297936308742225805 44936299611726115778334677)
                    ·
                      refine ⟨1053194522149830838554719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 44936299611726115778334677 1053194522149830838554719)
                      ·
                        rfl

theorem cell23_2051089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 7].length) (baseStart_2051089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2051089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2051089 prefixEnd_2051089 := by exact prefixLift 2051089
  have htrace : WordTrace (prefixWord ++ tailWord_2051089) baseStart_2051089 baseEnd_2051089 := by
    simpa [prefixWord, tailWord_2051089, baseEnd_2051089] using wordTrace_append hprefix tailTrace_2051089
  have hstable : (prefixWord ++ tailWord_2051089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051089).length < 2 ^ (prefixWord ++ tailWord_2051089).sum := by decide
  have hdescent : baseEnd_2051089 < baseStart_2051089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051116 : List Nat := [2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 4]
def baseStart_2051116 : Nat := 118140960795 + 2051116 * 2 ^ 59
def prefixEnd_2051116 : Nat := 4983230072969 + 3 ^ 40 * 2051116 * 2
def baseEnd_2051116 : Nat := 1053208386127502232917095

theorem tailTrace_2051116 : CollatzResearch.WordTrace tailWord_2051116 prefixEnd_2051116 1053208386127502232917095 := by
  unfold tailWord_2051116
  simp only [CollatzResearch.WordTrace]
  refine ⟨37405173218582254784442601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49873564291443006379256801 37405173218582254784442601)
  ·
    refine ⟨28053879913936691088331951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37405173218582254784442601 28053879913936691088331951)
    ·
      refine ⟨42080819870905036632497927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28053879913936691088331951 42080819870905036632497927)
      ·
        refine ⟨63121229806357554948746891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42080819870905036632497927 63121229806357554948746891)
        ·
          refine ⟨94681844709536332423120337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63121229806357554948746891 94681844709536332423120337)
          ·
            refine ⟨71011383532152249317340253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94681844709536332423120337 71011383532152249317340253)
            ·
              refine ⟨26629268824557093494002595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71011383532152249317340253 26629268824557093494002595)
              ·
                refine ⟨39943903236835640241003893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26629268824557093494002595 39943903236835640241003893)
                ·
                  refine ⟨3744740928453341272594115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39943903236835640241003893 3744740928453341272594115)
                  ·
                    refine ⟨5617111392680011908891173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3744740928453341272594115 5617111392680011908891173)
                    ·
                      refine ⟨1053208386127502232917095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5617111392680011908891173 1053208386127502232917095)
                      ·
                        rfl

theorem cell23_2051116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 4].length) (baseStart_2051116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2051116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2051116 prefixEnd_2051116 := by exact prefixLift 2051116
  have htrace : WordTrace (prefixWord ++ tailWord_2051116) baseStart_2051116 baseEnd_2051116 := by
    simpa [prefixWord, tailWord_2051116, baseEnd_2051116] using wordTrace_append hprefix tailTrace_2051116
  have hstable : (prefixWord ++ tailWord_2051116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051116).length < 2 ^ (prefixWord ++ tailWord_2051116).sum := by decide
  have hdescent : baseEnd_2051116 < baseStart_2051116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051133 : List Nat := [1, 4, 1, 3, 1, 2, 2, 1, 3, 1, 4]
def baseStart_2051133 : Nat := 118140960795 + 2051133 * 2 ^ 59
def prefixEnd_2051133 : Nat := 4983230072969 + 3 ^ 40 * 2051133 * 2
def baseEnd_2051133 : Nat := 1053217115298628666404517

theorem tailTrace_2051133 : CollatzResearch.WordTrace tailWord_2051133 prefixEnd_2051133 1053217115298628666404517 := by
  unfold tailWord_2051133
  simp only [CollatzResearch.WordTrace]
  refine ⟨74810966478102921472254053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49873977652068614314836035 74810966478102921472254053)
  ·
    refine ⟨14027056214644297776047635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74810966478102921472254053 14027056214644297776047635)
    ·
      refine ⟨21040584321966446664071453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14027056214644297776047635 21040584321966446664071453)
      ·
        refine ⟨7890219120737417499026795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21040584321966446664071453 7890219120737417499026795)
        ·
          refine ⟨11835328681106126248540193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7890219120737417499026795 11835328681106126248540193)
          ·
            refine ⟨8876496510829594686405145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11835328681106126248540193 8876496510829594686405145)
            ·
              refine ⟨6657372383122196014803859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8876496510829594686405145 6657372383122196014803859)
              ·
                refine ⟨9986058574683294022205789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6657372383122196014803859 9986058574683294022205789)
                ·
                  refine ⟨3744771965506235258327171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9986058574683294022205789 3744771965506235258327171)
                  ·
                    refine ⟨5617157948259352887490757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3744771965506235258327171 5617157948259352887490757)
                    ·
                      refine ⟨1053217115298628666404517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5617157948259352887490757 1053217115298628666404517)
                      ·
                        rfl

theorem cell23_2051133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_2051133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2051133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2051133 prefixEnd_2051133 := by exact prefixLift 2051133
  have htrace : WordTrace (prefixWord ++ tailWord_2051133) baseStart_2051133 baseEnd_2051133 := by
    simpa [prefixWord, tailWord_2051133, baseEnd_2051133] using wordTrace_append hprefix tailTrace_2051133
  have hstable : (prefixWord ++ tailWord_2051133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051133).length < 2 ^ (prefixWord ++ tailWord_2051133).sum := by decide
  have hdescent : baseEnd_2051133 < baseStart_2051133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051150 : List Nat := [4, 1, 1, 1, 1, 3, 1, 2, 5, 2, 2]
def baseStart_2051150 : Nat := 118140960795 + 2051150 * 2 ^ 59
def prefixEnd_2051150 : Nat := 4983230072969 + 3 ^ 40 * 2051150 * 2
def baseEnd_2051150 : Nat := 1053225844469755099891939

theorem tailTrace_2051150 : CollatzResearch.WordTrace tailWord_2051150 prefixEnd_2051150 1053225844469755099891939 := by
  unfold tailWord_2051150
  simp only [CollatzResearch.WordTrace]
  refine ⟨9351448314880166671952863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49874391012694222250415269 9351448314880166671952863)
  ·
    refine ⟨14027172472320250007929295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9351448314880166671952863 14027172472320250007929295)
    ·
      refine ⟨21040758708480375011893943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14027172472320250007929295 21040758708480375011893943)
      ·
        refine ⟨31561138062720562517840915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21040758708480375011893943 31561138062720562517840915)
        ·
          refine ⟨47341707094080843776761373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31561138062720562517840915 47341707094080843776761373)
          ·
            refine ⟨17753140160280316416285515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47341707094080843776761373 17753140160280316416285515)
            ·
              refine ⟨26629710240420474624428273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17753140160280316416285515 26629710240420474624428273)
              ·
                refine ⟨19972282680315355968321205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26629710240420474624428273 19972282680315355968321205)
                ·
                  refine ⟨1872401501279564622030113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19972282680315355968321205 1872401501279564622030113)
                  ·
                    refine ⟨1404301125959673466522585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1872401501279564622030113 1404301125959673466522585)
                    ·
                      refine ⟨1053225844469755099891939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1404301125959673466522585 1053225844469755099891939)
                      ·
                        rfl

theorem cell23_2051150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 5, 2, 2].length) (baseStart_2051150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2051150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2051150 prefixEnd_2051150 := by exact prefixLift 2051150
  have htrace : WordTrace (prefixWord ++ tailWord_2051150) baseStart_2051150 baseEnd_2051150 := by
    simpa [prefixWord, tailWord_2051150, baseEnd_2051150] using wordTrace_append hprefix tailTrace_2051150
  have hstable : (prefixWord ++ tailWord_2051150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051150).length < 2 ^ (prefixWord ++ tailWord_2051150).sum := by decide
  have hdescent : baseEnd_2051150 < baseStart_2051150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051167 : List Nat := [1, 1, 2, 3, 1, 1, 3, 6, 1, 2, 2]
def baseStart_2051167 : Nat := 118140960795 + 2051167 * 2 ^ 59
def prefixEnd_2051167 : Nat := 4983230072969 + 3 ^ 40 * 2051167 * 2
def baseEnd_2051167 : Nat := 1053234573640881533379361

theorem tailTrace_2051167 : CollatzResearch.WordTrace tailWord_2051167 prefixEnd_2051167 1053234573640881533379361 := by
  unfold tailWord_2051167
  simp only [CollatzResearch.WordTrace]
  refine ⟨74812206559979745278991755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49874804373319830185994503 74812206559979745278991755)
  ·
    refine ⟨112218309839969617918487633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74812206559979745278991755 112218309839969617918487633)
    ·
      refine ⟨84163732379977213438865725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112218309839969617918487633 84163732379977213438865725)
      ·
        refine ⟨31561399642491455039574647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84163732379977213438865725 31561399642491455039574647)
        ·
          refine ⟨47342099463737182559361971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31561399642491455039574647 47342099463737182559361971)
          ·
            refine ⟨71013149195605773839042957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47342099463737182559361971 71013149195605773839042957)
            ·
              refine ⟨26629930948352165189641109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71013149195605773839042957 26629930948352165189641109)
              ·
                refine ⟨1248278013204007743264427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26629930948352165189641109 1248278013204007743264427)
                ·
                  refine ⟨1872417019806011614896641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1248278013204007743264427 1872417019806011614896641)
                  ·
                    refine ⟨1404312764854508711172481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1872417019806011614896641 1404312764854508711172481)
                    ·
                      refine ⟨1053234573640881533379361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1404312764854508711172481 1053234573640881533379361)
                      ·
                        rfl

theorem cell23_2051167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 6, 1, 2, 2].length) (baseStart_2051167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2051167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2051167 prefixEnd_2051167 := by exact prefixLift 2051167
  have htrace : WordTrace (prefixWord ++ tailWord_2051167) baseStart_2051167 baseEnd_2051167 := by
    simpa [prefixWord, tailWord_2051167, baseEnd_2051167] using wordTrace_append hprefix tailTrace_2051167
  have hstable : (prefixWord ++ tailWord_2051167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051167).length < 2 ^ (prefixWord ++ tailWord_2051167).sum := by decide
  have hdescent : baseEnd_2051167 < baseStart_2051167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051170 : List Nat := [3, 3, 2, 2, 1, 2, 1, 2, 1, 1, 5]
def baseStart_2051170 : Nat := 118140960795 + 2051170 * 2 ^ 59
def prefixEnd_2051170 : Nat := 4983230072969 + 3 ^ 40 * 2051170 * 2
def baseEnd_2051170 : Nat := 1053236114082845021641847

theorem tailTrace_2051170 : CollatzResearch.WordTrace tailWord_2051170 prefixEnd_2051170 1053236114082845021641847 := by
  unfold tailWord_2051170
  simp only [CollatzResearch.WordTrace]
  refine ⟨18703078994742219197837741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49874877319312584527567309 18703078994742219197837741)
  ·
    refine ⟨7013654623028332199189153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18703078994742219197837741 7013654623028332199189153)
    ·
      refine ⟨5260240967271249149391865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7013654623028332199189153 5260240967271249149391865)
      ·
        refine ⟨3945180725453436862043899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5260240967271249149391865 3945180725453436862043899)
        ·
          refine ⟨5917771088180155293065849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3945180725453436862043899 5917771088180155293065849)
          ·
            refine ⟨4438328316135116469799387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5917771088180155293065849 4438328316135116469799387)
            ·
              refine ⟨6657492474202674704699081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4438328316135116469799387 6657492474202674704699081)
              ·
                refine ⟨4993119355652006028524311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6657492474202674704699081 4993119355652006028524311)
                ·
                  refine ⟨7489679033478009042786467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4993119355652006028524311 7489679033478009042786467)
                  ·
                    refine ⟨11234518550217013564179701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7489679033478009042786467 11234518550217013564179701)
                    ·
                      refine ⟨1053236114082845021641847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11234518550217013564179701 1053236114082845021641847)
                      ·
                        rfl

theorem cell23_2051170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_2051170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2051170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2051170 prefixEnd_2051170 := by exact prefixLift 2051170
  have htrace : WordTrace (prefixWord ++ tailWord_2051170) baseStart_2051170 baseEnd_2051170 := by
    simpa [prefixWord, tailWord_2051170, baseEnd_2051170] using wordTrace_append hprefix tailTrace_2051170
  have hstable : (prefixWord ++ tailWord_2051170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051170).length < 2 ^ (prefixWord ++ tailWord_2051170).sum := by decide
  have hdescent : baseEnd_2051170 < baseStart_2051170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051196 : List Nat := [2, 2, 2, 1, 1, 3, 1, 1, 1, 4, 5]
def baseStart_2051196 : Nat := 118140960795 + 2051196 * 2 ^ 59
def prefixEnd_2051196 : Nat := 4983230072969 + 3 ^ 40 * 2051196 * 2
def baseEnd_2051196 : Nat := 1053249464579861919916727

theorem tailTrace_2051196 : CollatzResearch.WordTrace tailWord_2051196 prefixEnd_2051196 1053249464579861919916727 := by
  unfold tailWord_2051196
  simp only [CollatzResearch.WordTrace]
  refine ⟨37406632138437341615898721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49875509517916455487864961 37406632138437341615898721)
  ·
    refine ⟨28054974103828006211924041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37406632138437341615898721 28054974103828006211924041)
    ·
      refine ⟨21041230577871004658943031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28054974103828006211924041 21041230577871004658943031)
      ·
        refine ⟨31561845866806506988414547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21041230577871004658943031 31561845866806506988414547)
        ·
          refine ⟨47342768800209760482621821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31561845866806506988414547 47342768800209760482621821)
          ·
            refine ⟨17753538300078660180983183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47342768800209760482621821 17753538300078660180983183)
            ·
              refine ⟨26630307450117990271474775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17753538300078660180983183 26630307450117990271474775)
              ·
                refine ⟨39945461175176985407212163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26630307450117990271474775 39945461175176985407212163)
                ·
                  refine ⟨59918191762765478110818245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39945461175176985407212163 59918191762765478110818245)
                  ·
                    refine ⟨11234660955518527145778421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59918191762765478110818245 11234660955518527145778421)
                    ·
                      refine ⟨1053249464579861919916727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11234660955518527145778421 1053249464579861919916727)
                      ·
                        rfl

theorem cell23_2051196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_2051196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2051196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2051196 prefixEnd_2051196 := by exact prefixLift 2051196
  have htrace : WordTrace (prefixWord ++ tailWord_2051196) baseStart_2051196 baseEnd_2051196 := by
    simpa [prefixWord, tailWord_2051196, baseEnd_2051196] using wordTrace_append hprefix tailTrace_2051196
  have hstable : (prefixWord ++ tailWord_2051196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051196).length < 2 ^ (prefixWord ++ tailWord_2051196).sum := by decide
  have hdescent : baseEnd_2051196 < baseStart_2051196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051201 : List Nat := [1, 2, 4, 2, 2, 3, 1, 3, 1, 2, 2]
def baseStart_2051201 : Nat := 118140960795 + 2051201 * 2 ^ 59
def prefixEnd_2051201 : Nat := 4983230072969 + 3 ^ 40 * 2051201 * 2
def baseEnd_2051201 : Nat := 1053252031983134400354205

theorem tailTrace_2051201 : CollatzResearch.WordTrace tailWord_2051201 prefixEnd_2051201 1053252031983134400354205 := by
  unfold tailWord_2051201
  simp only [CollatzResearch.WordTrace]
  refine ⟨74813446641856569085729457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49875631094571046057152971 74813446641856569085729457)
  ·
    refine ⟨56110084981392426814297093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74813446641856569085729457 56110084981392426814297093)
    ·
      refine ⟨10520640934011080027680705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56110084981392426814297093 10520640934011080027680705)
      ·
        refine ⟨7890480700508310020760529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10520640934011080027680705 7890480700508310020760529)
        ·
          refine ⟨5917860525381232515570397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7890480700508310020760529 5917860525381232515570397)
          ·
            refine ⟨2219197697017962193338899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5917860525381232515570397 2219197697017962193338899)
            ·
              refine ⟨3328796545526943290008349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2219197697017962193338899 3328796545526943290008349)
              ·
                refine ⟨1248298704572603733753131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3328796545526943290008349 1248298704572603733753131)
                ·
                  refine ⟨1872448056858905600629697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1248298704572603733753131 1872448056858905600629697)
                  ·
                    refine ⟨1404336042644179200472273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1872448056858905600629697 1404336042644179200472273)
                    ·
                      refine ⟨1053252031983134400354205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1404336042644179200472273 1053252031983134400354205)
                      ·
                        rfl

theorem cell23_2051201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_2051201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2051201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2051201 prefixEnd_2051201 := by exact prefixLift 2051201
  have htrace : WordTrace (prefixWord ++ tailWord_2051201) baseStart_2051201 baseEnd_2051201 := by
    simpa [prefixWord, tailWord_2051201, baseEnd_2051201] using wordTrace_append hprefix tailTrace_2051201
  have hstable : (prefixWord ++ tailWord_2051201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051201).length < 2 ^ (prefixWord ++ tailWord_2051201).sum := by decide
  have hdescent : baseEnd_2051201 < baseStart_2051201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051216 : List Nat := [2, 1, 1, 1, 1, 1, 4, 4, 2, 6]
def baseStart_2051216 : Nat := 118140960795 + 2051216 * 2 ^ 59
def prefixEnd_2051216 : Nat := 4983230072969 + 3 ^ 40 * 2051216 * 2
def baseEnd_2051216 : Nat := 351086578064317280555545

theorem tailTrace_2051216 : CollatzResearch.WordTrace tailWord_2051216 prefixEnd_2051216 351086578064317280555545 := by
  unfold tailWord_2051216
  simp only [CollatzResearch.WordTrace]
  refine ⟨37406996868401113323762751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49875995824534817765017001 37406996868401113323762751)
  ·
    refine ⟨56110495302601669985644127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37406996868401113323762751 56110495302601669985644127)
    ·
      refine ⟨84165742953902504978466191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56110495302601669985644127 84165742953902504978466191)
      ·
        refine ⟨126248614430853757467699287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84165742953902504978466191 126248614430853757467699287)
        ·
          refine ⟨189372921646280636201548931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126248614430853757467699287 189372921646280636201548931)
          ·
            refine ⟨284059382469420954302323397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189372921646280636201548931 284059382469420954302323397)
            ·
              refine ⟨53261134213016428931685637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 284059382469420954302323397 53261134213016428931685637)
              ·
                refine ⟨9986462664940580424691057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53261134213016428931685637 9986462664940580424691057)
                ·
                  refine ⟨7489846998705435318518293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9986462664940580424691057 7489846998705435318518293)
                  ·
                    refine ⟨351086578064317280555545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7489846998705435318518293 351086578064317280555545)
                    ·
                      rfl

theorem cell23_2051216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 2, 6].length) (baseStart_2051216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2051216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2051216 prefixEnd_2051216 := by exact prefixLift 2051216
  have htrace : WordTrace (prefixWord ++ tailWord_2051216) baseStart_2051216 baseEnd_2051216 := by
    simpa [prefixWord, tailWord_2051216, baseEnd_2051216] using wordTrace_append hprefix tailTrace_2051216
  have hstable : (prefixWord ++ tailWord_2051216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051216).length < 2 ^ (prefixWord ++ tailWord_2051216).sum := by decide
  have hdescent : baseEnd_2051216 < baseStart_2051216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051234 : List Nat := [3, 3, 1, 3, 2, 1, 1, 3, 2, 1, 3]
def baseStart_2051234 : Nat := 118140960795 + 2051234 * 2 ^ 59
def prefixEnd_2051234 : Nat := 4983230072969 + 3 ^ 40 * 2051234 * 2
def baseEnd_2051234 : Nat := 1053268976844732771241553

theorem tailTrace_2051234 : CollatzResearch.WordTrace tailWord_2051234 prefixEnd_2051234 1053268976844732771241553 := by
  unfold tailWord_2051234
  simp only [CollatzResearch.WordTrace]
  refine ⟨18703662562684253930420189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49876433500491343814453837 18703662562684253930420189)
  ·
    refine ⟨7013873461006595223907571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18703662562684253930420189 7013873461006595223907571)
    ·
      refine ⟨10520810191509892835861357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7013873461006595223907571 10520810191509892835861357)
      ·
        refine ⟨3945303821816209813448009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10520810191509892835861357 3945303821816209813448009)
        ·
          refine ⟨2958977866362157360086007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3945303821816209813448009 2958977866362157360086007)
          ·
            refine ⟨4438466799543236040129011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2958977866362157360086007 4438466799543236040129011)
            ·
              refine ⟨6657700199314854060193517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4438466799543236040129011 6657700199314854060193517)
              ·
                refine ⟨2496637574743070272572569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6657700199314854060193517 2496637574743070272572569)
                ·
                  refine ⟨1872478181057302704429427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2496637574743070272572569 1872478181057302704429427)
                  ·
                    refine ⟨2808717271585954056644141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1872478181057302704429427 2808717271585954056644141)
                    ·
                      refine ⟨1053268976844732771241553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2808717271585954056644141 1053268976844732771241553)
                      ·
                        rfl

theorem cell23_2051234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_2051234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2051234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2051234 prefixEnd_2051234 := by exact prefixLift 2051234
  have htrace : WordTrace (prefixWord ++ tailWord_2051234) baseStart_2051234 baseEnd_2051234 := by
    simpa [prefixWord, tailWord_2051234, baseEnd_2051234] using wordTrace_append hprefix tailTrace_2051234
  have hstable : (prefixWord ++ tailWord_2051234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051234).length < 2 ^ (prefixWord ++ tailWord_2051234).sum := by decide
  have hdescent : baseEnd_2051234 < baseStart_2051234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051256 : List Nat := [2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 7]
def baseStart_2051256 : Nat := 118140960795 + 2051256 * 2 ^ 59
def prefixEnd_2051256 : Nat := 4983230072969 + 3 ^ 40 * 2051256 * 2
def baseEnd_2051256 : Nat := 1053280273419131685166451

theorem tailTrace_2051256 : CollatzResearch.WordTrace tailWord_2051256 prefixEnd_2051256 1053280273419131685166451 := by
  unfold tailWord_2051256
  simp only [CollatzResearch.WordTrace]
  refine ⟨37407726328328656739490811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49876968437771542319321081 37407726328328656739490811)
  ·
    refine ⟨56111589492492985109236217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37407726328328656739490811 56111589492492985109236217)
    ·
      refine ⟨42083692119369738831927163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56111589492492985109236217 42083692119369738831927163)
      ·
        refine ⟨63125538179054608247890745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42083692119369738831927163 63125538179054608247890745)
        ·
          refine ⟨47344153634290956185918059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63125538179054608247890745 47344153634290956185918059)
          ·
            refine ⟨71016230451436434278877089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47344153634290956185918059 71016230451436434278877089)
            ·
              refine ⟨53262172838577325709157817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71016230451436434278877089 53262172838577325709157817)
              ·
                refine ⟨39946629628932994281868363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53262172838577325709157817 39946629628932994281868363)
                ·
                  refine ⟨59919944443399491422802545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39946629628932994281868363 59919944443399491422802545)
                  ·
                    refine ⟨44939958332549618567101909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59919944443399491422802545 44939958332549618567101909)
                    ·
                      refine ⟨1053280273419131685166451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 44939958332549618567101909 1053280273419131685166451)
                      ·
                        rfl

theorem cell23_2051256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 7].length) (baseStart_2051256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2051256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2051256 prefixEnd_2051256 := by exact prefixLift 2051256
  have htrace : WordTrace (prefixWord ++ tailWord_2051256) baseStart_2051256 baseEnd_2051256 := by
    simpa [prefixWord, tailWord_2051256, baseEnd_2051256] using wordTrace_append hprefix tailTrace_2051256
  have hstable : (prefixWord ++ tailWord_2051256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051256).length < 2 ^ (prefixWord ++ tailWord_2051256).sum := by decide
  have hdescent : baseEnd_2051256 < baseStart_2051256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051274 : List Nat := [3, 1, 2, 1, 3, 3, 2, 2, 2, 2, 2]
def baseStart_2051274 : Nat := 118140960795 + 2051274 * 2 ^ 59
def prefixEnd_2051274 : Nat := 4983230072969 + 3 ^ 40 * 2051274 * 2
def baseEnd_2051274 : Nat := 1053289516070912614741369

theorem tailTrace_2051274 : CollatzResearch.WordTrace tailWord_2051274 prefixEnd_2051274 1053289516070912614741369 := by
  unfold tailWord_2051274
  simp only [CollatzResearch.WordTrace]
  refine ⟨18704027292648025638284219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49877406113728068368757917 18704027292648025638284219)
  ·
    refine ⟨28056040938972038457426329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18704027292648025638284219 28056040938972038457426329)
    ·
      refine ⟨21042030704229028843069747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28056040938972038457426329 21042030704229028843069747)
      ·
        refine ⟨31563046056343543264604621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21042030704229028843069747 31563046056343543264604621)
        ·
          refine ⟨11836142271128828724226733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31563046056343543264604621 11836142271128828724226733)
          ·
            refine ⟨4438553351673310771585025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11836142271128828724226733 4438553351673310771585025)
            ·
              refine ⟨3328915013754983078688769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4438553351673310771585025 3328915013754983078688769)
              ·
                refine ⟨2496686260316237309016577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3328915013754983078688769 2496686260316237309016577)
                ·
                  refine ⟨1872514695237177981762433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2496686260316237309016577 1872514695237177981762433)
                  ·
                    refine ⟨1404386021427883486321825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1872514695237177981762433 1404386021427883486321825)
                    ·
                      refine ⟨1053289516070912614741369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1404386021427883486321825 1053289516070912614741369)
                      ·
                        rfl

theorem cell23_2051274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 2, 2, 2, 2].length) (baseStart_2051274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2051274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2051274 prefixEnd_2051274 := by exact prefixLift 2051274
  have htrace : WordTrace (prefixWord ++ tailWord_2051274) baseStart_2051274 baseEnd_2051274 := by
    simpa [prefixWord, tailWord_2051274, baseEnd_2051274] using wordTrace_append hprefix tailTrace_2051274
  have hstable : (prefixWord ++ tailWord_2051274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051274).length < 2 ^ (prefixWord ++ tailWord_2051274).sum := by decide
  have hdescent : baseEnd_2051274 < baseStart_2051274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051310 : List Nat := [4, 1, 2, 1, 1, 1, 5, 1, 2, 5]
def baseStart_2051310 : Nat := 118140960795 + 2051310 * 2 ^ 59
def prefixEnd_2051310 : Nat := 4983230072969 + 3 ^ 40 * 2051310 * 2
def baseEnd_2051310 : Nat := 351102667124824824630401

theorem tailTrace_2051310 : CollatzResearch.WordTrace tailWord_2051310 prefixEnd_2051310 351102667124824824630401 := by
  unfold tailWord_2051310
  simp only [CollatzResearch.WordTrace]
  refine ⟨9352177774807710087680923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49878281465641120467631589 9352177774807710087680923)
  ·
    refine ⟨14028266662211565131521385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9352177774807710087680923 14028266662211565131521385)
    ·
      refine ⟨10521199996658673848641039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14028266662211565131521385 10521199996658673848641039)
      ·
        refine ⟨15781799994988010772961559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10521199996658673848641039 15781799994988010772961559)
        ·
          refine ⟨23672699992482016159442339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15781799994988010772961559 23672699992482016159442339)
          ·
            refine ⟨35509049988723024239163509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23672699992482016159442339 35509049988723024239163509)
            ·
              refine ⟨3328973436442783522421579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35509049988723024239163509 3328973436442783522421579)
              ·
                refine ⟨4993460154664175283632369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3328973436442783522421579 4993460154664175283632369)
                ·
                  refine ⟨3745095115998131462724277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4993460154664175283632369 3745095115998131462724277)
                  ·
                    refine ⟨351102667124824824630401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3745095115998131462724277 351102667124824824630401)
                    ·
                      rfl

theorem cell23_2051310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_2051310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2051310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2051310 prefixEnd_2051310 := by exact prefixLift 2051310
  have htrace : WordTrace (prefixWord ++ tailWord_2051310) baseStart_2051310 baseEnd_2051310 := by
    simpa [prefixWord, tailWord_2051310, baseEnd_2051310] using wordTrace_append hprefix tailTrace_2051310
  have hstable : (prefixWord ++ tailWord_2051310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051310).length < 2 ^ (prefixWord ++ tailWord_2051310).sum := by decide
  have hdescent : baseEnd_2051310 < baseStart_2051310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051340 : List Nat := [2, 2, 1, 2, 2, 3, 1, 3, 3, 4]
def baseStart_2051340 : Nat := 118140960795 + 2051340 * 2 ^ 59
def prefixEnd_2051340 : Nat := 4983230072969 + 3 ^ 40 * 2051340 * 2
def baseEnd_2051340 : Nat := 351107801931369785505355

theorem tailTrace_2051340 : CollatzResearch.WordTrace tailWord_2051340 prefixEnd_2051340 351107801931369785505355 := by
  unfold tailWord_2051340
  simp only [CollatzResearch.WordTrace]
  refine ⟨37409258194176497912519737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49879010925568663883359649 37409258194176497912519737)
  ·
    refine ⟨28056943645632373434389803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37409258194176497912519737 28056943645632373434389803)
    ·
      refine ⟨42085415468448560151584705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28056943645632373434389803 42085415468448560151584705)
      ·
        refine ⟨31564061601336420113688529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42085415468448560151584705 31564061601336420113688529)
        ·
          refine ⟨23673046201002315085266397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31564061601336420113688529 23673046201002315085266397)
          ·
            refine ⟨8877392325375868156974899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23673046201002315085266397 8877392325375868156974899)
            ·
              refine ⟨13316088488063802235462349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8877392325375868156974899 13316088488063802235462349)
              ·
                refine ⟨4993533183023925838298381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13316088488063802235462349 4993533183023925838298381)
                ·
                  refine ⟨1872574943633972189361893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4993533183023925838298381 1872574943633972189361893)
                  ·
                    refine ⟨351107801931369785505355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1872574943633972189361893 351107801931369785505355)
                    ·
                      rfl

theorem cell23_2051340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 3, 4].length) (baseStart_2051340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2051340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2051340 prefixEnd_2051340 := by exact prefixLift 2051340
  have htrace : WordTrace (prefixWord ++ tailWord_2051340) baseStart_2051340 baseEnd_2051340 := by
    simpa [prefixWord, tailWord_2051340, baseEnd_2051340] using wordTrace_append hprefix tailTrace_2051340
  have hstable : (prefixWord ++ tailWord_2051340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051340).length < 2 ^ (prefixWord ++ tailWord_2051340).sum := by decide
  have hdescent : baseEnd_2051340 < baseStart_2051340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051357 : List Nat := [1, 4, 2, 3, 1, 1, 2, 2, 3, 4]
def baseStart_2051357 : Nat := 118140960795 + 2051357 * 2 ^ 59
def prefixEnd_2051357 : Nat := 4983230072969 + 3 ^ 40 * 2051357 * 2
def baseEnd_2051357 : Nat := 351110711655078596667829

theorem tailTrace_2051357 : CollatzResearch.WordTrace tailWord_2051357 prefixEnd_2051357 351110711655078596667829 := by
  unfold tailWord_2051357
  simp only [CollatzResearch.WordTrace]
  refine ⟨74819136429291407728408325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49879424286194271818938883 74819136429291407728408325)
  ·
    refine ⟨14028588080492138949076561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74819136429291407728408325 14028588080492138949076561)
    ·
      refine ⟨10521441060369104211807421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14028588080492138949076561 10521441060369104211807421)
      ·
        refine ⟨3945540397638414079427783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10521441060369104211807421 3945540397638414079427783)
        ·
          refine ⟨5918310596457621119141675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3945540397638414079427783 5918310596457621119141675)
          ·
            refine ⟨8877465894686431678712513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5918310596457621119141675 8877465894686431678712513)
            ·
              refine ⟨6658099421014823759034385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8877465894686431678712513 6658099421014823759034385)
              ·
                refine ⟨4993574565761117819275789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6658099421014823759034385 4993574565761117819275789)
                ·
                  refine ⟨1872590462160419182228421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4993574565761117819275789 1872590462160419182228421)
                  ·
                    refine ⟨351110711655078596667829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1872590462160419182228421 351110711655078596667829)
                    ·
                      rfl

theorem cell23_2051357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_2051357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2051357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2051357 prefixEnd_2051357 := by exact prefixLift 2051357
  have htrace : WordTrace (prefixWord ++ tailWord_2051357) baseStart_2051357 baseEnd_2051357 := by
    simpa [prefixWord, tailWord_2051357, baseEnd_2051357] using wordTrace_append hprefix tailTrace_2051357
  have hstable : (prefixWord ++ tailWord_2051357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051357).length < 2 ^ (prefixWord ++ tailWord_2051357).sum := by decide
  have hdescent : baseEnd_2051357 < baseStart_2051357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051370 : List Nat := [3, 1, 4, 2, 1, 1, 1, 2, 8]
def baseStart_2051370 : Nat := 118140960795 + 2051370 * 2 ^ 59
def prefixEnd_2051370 : Nat := 4983230072969 + 3 ^ 40 * 2051370 * 2
def baseEnd_2051370 : Nat := 117037645579304915460103

theorem tailTrace_2051370 : CollatzResearch.WordTrace tailWord_2051370 prefixEnd_2051370 117037645579304915460103 := by
  unfold tailWord_2051370
  simp only [CollatzResearch.WordTrace]
  refine ⟨18704902644561077737157891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49879740385496207299087709 18704902644561077737157891)
  ·
    refine ⟨28057353966841616605736837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18704902644561077737157891 28057353966841616605736837)
    ·
      refine ⟨5260753868782803113575657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28057353966841616605736837 5260753868782803113575657)
      ·
        refine ⟨3945565401587102335181743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5260753868782803113575657 3945565401587102335181743)
        ·
          refine ⟨5918348102380653502772615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3945565401587102335181743 5918348102380653502772615)
          ·
            refine ⟨8877522153570980254158923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5918348102380653502772615 8877522153570980254158923)
            ·
              refine ⟨13316283230356470381238385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8877522153570980254158923 13316283230356470381238385)
              ·
                refine ⟨9987212422767352785928789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13316283230356470381238385 9987212422767352785928789)
                ·
                  refine ⟨117037645579304915460103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9987212422767352785928789 117037645579304915460103)
                  ·
                    rfl

theorem cell23_2051370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 8].length) (baseStart_2051370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2051370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2051370 prefixEnd_2051370 := by exact prefixLift 2051370
  have htrace : WordTrace (prefixWord ++ tailWord_2051370) baseStart_2051370 baseEnd_2051370 := by
    simpa [prefixWord, tailWord_2051370, baseEnd_2051370] using wordTrace_append hprefix tailTrace_2051370
  have hstable : (prefixWord ++ tailWord_2051370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051370).length < 2 ^ (prefixWord ++ tailWord_2051370).sum := by decide
  have hdescent : baseEnd_2051370 < baseStart_2051370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051383 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 7, 5]
def baseStart_2051383 : Nat := 118140960795 + 2051383 * 2 ^ 59
def prefixEnd_2051383 : Nat := 4983230072969 + 3 ^ 40 * 2051383 * 2
def baseEnd_2051383 : Nat := 351115161820750896092789

theorem tailTrace_2051383 : CollatzResearch.WordTrace tailWord_2051383 prefixEnd_2051383 351115161820750896092789 := by
  unfold tailWord_2051383
  simp only [CollatzResearch.WordTrace]
  refine ⟨74820084727197214168854803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49880056484798142779236535 74820084727197214168854803)
  ·
    refine ⟨112230127090795821253282205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74820084727197214168854803 112230127090795821253282205)
    ·
      refine ⟨42086297659048432969980827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112230127090795821253282205 42086297659048432969980827)
      ·
        refine ⟨63129446488572649454971241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42086297659048432969980827 63129446488572649454971241)
        ·
          refine ⟨47347084866429487091228431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63129446488572649454971241 47347084866429487091228431)
          ·
            refine ⟨71020627299644230636842647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47347084866429487091228431 71020627299644230636842647)
            ·
              refine ⟨106530940949466345955263971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71020627299644230636842647 106530940949466345955263971)
              ·
                refine ⟨159796411424199518932895957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106530940949466345955263971 159796411424199518932895957)
                ·
                  refine ⟨3745228392754676224989749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 159796411424199518932895957 3745228392754676224989749)
                  ·
                    refine ⟨351115161820750896092789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3745228392754676224989749 351115161820750896092789)
                    ·
                      rfl

theorem cell23_2051383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 7, 5].length) (baseStart_2051383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2051383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2051383 prefixEnd_2051383 := by exact prefixLift 2051383
  have htrace : WordTrace (prefixWord ++ tailWord_2051383) baseStart_2051383 baseEnd_2051383 := by
    simpa [prefixWord, tailWord_2051383, baseEnd_2051383] using wordTrace_append hprefix tailTrace_2051383
  have hstable : (prefixWord ++ tailWord_2051383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051383).length < 2 ^ (prefixWord ++ tailWord_2051383).sum := by decide
  have hdescent : baseEnd_2051383 < baseStart_2051383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051424 : List Nat := [2, 1, 1, 3, 4, 2, 2, 1, 2, 3, 2]
def baseStart_2051424 : Nat := 118140960795 + 2051424 * 2 ^ 59
def prefixEnd_2051424 : Nat := 4983230072969 + 3 ^ 40 * 2051424 * 2
def baseEnd_2051424 : Nat := 1053366538169087027865679

theorem tailTrace_2051424 : CollatzResearch.WordTrace tailWord_2051424 prefixEnd_2051424 1053366538169087027865679 := by
  unfold tailWord_2051424
  simp only [CollatzResearch.WordTrace]
  refine ⟨37410790060024339085548663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49881053413365785447398217 37410790060024339085548663)
  ·
    refine ⟨56116185090036508628322995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37410790060024339085548663 56116185090036508628322995)
    ·
      refine ⟨84174277635054762942484493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56116185090036508628322995 84174277635054762942484493)
      ·
        refine ⟨31565354113145536103431685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84174277635054762942484493 31565354113145536103431685)
        ·
          refine ⟨5918503896214788019393441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31565354113145536103431685 5918503896214788019393441)
          ·
            refine ⟨4438877922161091014545081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5918503896214788019393441 4438877922161091014545081)
            ·
              refine ⟨3329158441620818260908811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4438877922161091014545081 3329158441620818260908811)
              ·
                refine ⟨4993737662431227391363217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3329158441620818260908811 4993737662431227391363217)
                ·
                  refine ⟨3745303246823420543522413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4993737662431227391363217 3745303246823420543522413)
                  ·
                    refine ⟨1404488717558782703820905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3745303246823420543522413 1404488717558782703820905)
                    ·
                      refine ⟨1053366538169087027865679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1404488717558782703820905 1053366538169087027865679)
                      ·
                        rfl

theorem cell23_2051424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 2, 3, 2].length) (baseStart_2051424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2051424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2051424 prefixEnd_2051424 := by exact prefixLift 2051424
  have htrace : WordTrace (prefixWord ++ tailWord_2051424) baseStart_2051424 baseEnd_2051424 := by
    simpa [prefixWord, tailWord_2051424, baseEnd_2051424] using wordTrace_append hprefix tailTrace_2051424
  have hstable : (prefixWord ++ tailWord_2051424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051424).length < 2 ^ (prefixWord ++ tailWord_2051424).sum := by decide
  have hdescent : baseEnd_2051424 < baseStart_2051424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051433 : List Nat := [1, 2, 1, 1, 1, 3, 2, 2, 3, 1, 6]
def baseStart_2051433 : Nat := 118140960795 + 2051433 * 2 ^ 59
def prefixEnd_2051433 : Nat := 4983230072969 + 3 ^ 40 * 2051433 * 2
def baseEnd_2051433 : Nat := 1053371159494977492653137

theorem tailTrace_2051433 : CollatzResearch.WordTrace tailWord_2051433 prefixEnd_2051433 1053371159494977492653137 := by
  unfold tailWord_2051433
  simp only [CollatzResearch.WordTrace]
  refine ⟨74821908377016072708174953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49881272251344048472116635 74821908377016072708174953)
  ·
    refine ⟨56116431282762054531131215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74821908377016072708174953 56116431282762054531131215)
    ·
      refine ⟨84174646924143081796696823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56116431282762054531131215 84174646924143081796696823)
      ·
        refine ⟨126261970386214622695045235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84174646924143081796696823 126261970386214622695045235)
        ·
          refine ⟨189392955579321934042567853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126261970386214622695045235 189392955579321934042567853)
          ·
            refine ⟨71022358342245725265962945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189392955579321934042567853 71022358342245725265962945)
            ·
              refine ⟨53266768756684293949472209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71022358342245725265962945 53266768756684293949472209)
              ·
                refine ⟨39950076567513220462104157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53266768756684293949472209 39950076567513220462104157)
                ·
                  refine ⟨14981278712817457673289059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39950076567513220462104157 14981278712817457673289059)
                  ·
                    refine ⟨22471918069226186509933589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14981278712817457673289059 22471918069226186509933589)
                    ·
                      refine ⟨1053371159494977492653137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22471918069226186509933589 1053371159494977492653137)
                      ·
                        rfl

theorem cell23_2051433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 1, 6].length) (baseStart_2051433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2051433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2051433 prefixEnd_2051433 := by exact prefixLift 2051433
  have htrace : WordTrace (prefixWord ++ tailWord_2051433) baseStart_2051433 baseEnd_2051433 := by
    simpa [prefixWord, tailWord_2051433, baseEnd_2051433] using wordTrace_append hprefix tailTrace_2051433
  have hstable : (prefixWord ++ tailWord_2051433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051433).length < 2 ^ (prefixWord ++ tailWord_2051433).sum := by decide
  have hdescent : baseEnd_2051433 < baseStart_2051433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051447 : List Nat := [1, 1, 3, 1, 1, 2, 6, 2, 2, 4]
def baseStart_2051447 : Nat := 118140960795 + 2051447 * 2 ^ 59
def prefixEnd_2051447 : Nat := 4983230072969 + 3 ^ 40 * 2051447 * 2
def baseEnd_2051447 : Nat := 351126116074713479292691

theorem tailTrace_2051447 : CollatzResearch.WordTrace tailWord_2051447 prefixEnd_2051447 351126116074713479292691 := by
  unfold tailWord_2051447
  simp only [CollatzResearch.WordTrace]
  refine ⟨74822418998965353099184595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49881612665976902066123063 74822418998965353099184595)
  ·
    refine ⟨112233628498448029648776893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74822418998965353099184595 112233628498448029648776893)
    ·
      refine ⟨42087610686918011118291335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112233628498448029648776893 42087610686918011118291335)
      ·
        refine ⟨63131416030377016677437003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42087610686918011118291335 63131416030377016677437003)
        ·
          refine ⟨94697124045565525016155505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63131416030377016677437003 94697124045565525016155505)
          ·
            refine ⟨71022843034174143762116629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94697124045565525016155505 71022843034174143762116629)
            ·
              refine ⟨3329195767226912988849217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 71022843034174143762116629 3329195767226912988849217)
              ·
                refine ⟨2496896825420184741636913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3329195767226912988849217 2496896825420184741636913)
                ·
                  refine ⟨1872672619065138556227685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2496896825420184741636913 1872672619065138556227685)
                  ·
                    refine ⟨351126116074713479292691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1872672619065138556227685 351126116074713479292691)
                    ·
                      rfl

theorem cell23_2051447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 2, 2, 4].length) (baseStart_2051447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2051447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2051447 prefixEnd_2051447 := by exact prefixLift 2051447
  have htrace : WordTrace (prefixWord ++ tailWord_2051447) baseStart_2051447 baseEnd_2051447 := by
    simpa [prefixWord, tailWord_2051447, baseEnd_2051447] using wordTrace_append hprefix tailTrace_2051447
  have hstable : (prefixWord ++ tailWord_2051447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051447).length < 2 ^ (prefixWord ++ tailWord_2051447).sum := by decide
  have hdescent : baseEnd_2051447 < baseStart_2051447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051460 : List Nat := [2, 3, 2, 1, 1, 3, 3, 8]
def baseStart_2051460 : Nat := 118140960795 + 2051460 * 2 ^ 59
def prefixEnd_2051460 : Nat := 4983230072969 + 3 ^ 40 * 2051460 * 2
def baseEnd_2051460 : Nat := 39014260128616625445019

theorem tailTrace_2051460 : CollatzResearch.WordTrace tailWord_2051460 prefixEnd_2051460 39014260128616625445019 := by
  unfold tailWord_2051460
  simp only [CollatzResearch.WordTrace]
  refine ⟨37411446573959128159703917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49881928765278837546271889 37411446573959128159703917)
  ·
    refine ⟨14029292465234673059888969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37411446573959128159703917 14029292465234673059888969)
    ·
      refine ⟨10521969348926004794916727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14029292465234673059888969 10521969348926004794916727)
      ·
        refine ⟨15782954023389007192375091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10521969348926004794916727 15782954023389007192375091)
        ·
          refine ⟨23674431035083510788562637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15782954023389007192375091 23674431035083510788562637)
          ·
            refine ⟨8877911638156316545710989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23674431035083510788562637 8877911638156316545710989)
            ·
              refine ⟨3329216864308618704641621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8877911638156316545710989 3329216864308618704641621)
              ·
                refine ⟨39014260128616625445019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3329216864308618704641621 39014260128616625445019)
                ·
                  rfl

theorem cell23_2051460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 8].length) (baseStart_2051460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2051460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2051460 prefixEnd_2051460 := by exact prefixLift 2051460
  have htrace : WordTrace (prefixWord ++ tailWord_2051460) baseStart_2051460 baseEnd_2051460 := by
    simpa [prefixWord, tailWord_2051460, baseEnd_2051460] using wordTrace_append hprefix tailTrace_2051460
  have hstable : (prefixWord ++ tailWord_2051460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051460).length < 2 ^ (prefixWord ++ tailWord_2051460).sum := by decide
  have hdescent : baseEnd_2051460 < baseStart_2051460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051483 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 7]
def baseStart_2051483 : Nat := 118140960795 + 2051483 * 2 ^ 59
def prefixEnd_2051483 : Nat := 4983230072969 + 3 ^ 40 * 2051483 * 2
def baseEnd_2051483 : Nat := 1053396833527702297027907

theorem tailTrace_2051483 : CollatzResearch.WordTrace tailWord_2051483 prefixEnd_2051483 1053396833527702297027907 := by
  unfold tailWord_2051483
  simp only [CollatzResearch.WordTrace]
  refine ⟨74823732026834931247495103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49882488017889954164996735 74823732026834931247495103)
  ·
    refine ⟨112235598040252396871242655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74823732026834931247495103 112235598040252396871242655)
    ·
      refine ⟨168353397060378595306863983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112235598040252396871242655 168353397060378595306863983)
      ·
        refine ⟨252530095590567892960295975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168353397060378595306863983 252530095590567892960295975)
        ·
          refine ⟨378795143385851839440443963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252530095590567892960295975 378795143385851839440443963)
          ·
            refine ⟨568192715078777759160665945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378795143385851839440443963 568192715078777759160665945)
            ·
              refine ⟨426144536309083319370499459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 568192715078777759160665945 426144536309083319370499459)
              ·
                refine ⟨639216804463624979055749189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 426144536309083319370499459 639216804463624979055749189)
                ·
                  refine ⟨119853150836929683572952973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 639216804463624979055749189 119853150836929683572952973)
                  ·
                    refine ⟨44944931563848631339857365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 119853150836929683572952973 44944931563848631339857365)
                    ·
                      refine ⟨1053396833527702297027907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 44944931563848631339857365 1053396833527702297027907)
                      ·
                        rfl

theorem cell23_2051483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 7].length) (baseStart_2051483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2051483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2051483 prefixEnd_2051483 := by exact prefixLift 2051483
  have htrace : WordTrace (prefixWord ++ tailWord_2051483) baseStart_2051483 baseEnd_2051483 := by
    simpa [prefixWord, tailWord_2051483, baseEnd_2051483] using wordTrace_append hprefix tailTrace_2051483
  have hstable : (prefixWord ++ tailWord_2051483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051483).length < 2 ^ (prefixWord ++ tailWord_2051483).sum := by decide
  have hdescent : baseEnd_2051483 < baseStart_2051483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051487 : List Nat := [1, 1, 2, 5, 1, 2, 2, 2, 1, 3, 3]
def baseStart_2051487 : Nat := 118140960795 + 2051487 * 2 ^ 59
def prefixEnd_2051487 : Nat := 4983230072969 + 3 ^ 40 * 2051487 * 2
def baseEnd_2051487 : Nat := 1053398887450320281377889

theorem tailTrace_2051487 : CollatzResearch.WordTrace tailWord_2051487 prefixEnd_2051487 1053398887450320281377889 := by
  unfold tailWord_2051487
  simp only [CollatzResearch.WordTrace]
  refine ⟨74823877918820439930640715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49882585279213626620427143 74823877918820439930640715)
  ·
    refine ⟨112235816878230659895961073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74823877918820439930640715 112235816878230659895961073)
    ·
      refine ⟨84176862658672994921970805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112235816878230659895961073 84176862658672994921970805)
      ·
        refine ⟨7891580874250593273934763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84176862658672994921970805 7891580874250593273934763)
        ·
          refine ⟨11837371311375889910902145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7891580874250593273934763 11837371311375889910902145)
          ·
            refine ⟨8878028483531917433176609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11837371311375889910902145 8878028483531917433176609)
            ·
              refine ⟨6658521362648938074882457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8878028483531917433176609 6658521362648938074882457)
              ·
                refine ⟨4993891021986703556161843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6658521362648938074882457 4993891021986703556161843)
                ·
                  refine ⟨7490836532980055334242765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4993891021986703556161843 7490836532980055334242765)
                  ·
                    refine ⟨2809063699867520750341037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7490836532980055334242765 2809063699867520750341037)
                    ·
                      refine ⟨1053398887450320281377889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2809063699867520750341037 1053398887450320281377889)
                      ·
                        rfl

theorem cell23_2051487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_2051487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2051487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2051487 prefixEnd_2051487 := by exact prefixLift 2051487
  have htrace : WordTrace (prefixWord ++ tailWord_2051487) baseStart_2051487 baseEnd_2051487 := by
    simpa [prefixWord, tailWord_2051487, baseEnd_2051487] using wordTrace_append hprefix tailTrace_2051487
  have hstable : (prefixWord ++ tailWord_2051487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051487).length < 2 ^ (prefixWord ++ tailWord_2051487).sum := by decide
  have hdescent : baseEnd_2051487 < baseStart_2051487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051520 : List Nat := [2, 1, 1, 2, 3, 1, 4, 1, 2, 6]
def baseStart_2051520 : Nat := 118140960795 + 2051520 * 2 ^ 59
def prefixEnd_2051520 : Nat := 4983230072969 + 3 ^ 40 * 2051520 * 2
def baseEnd_2051520 : Nat := 351138610770639550755079

theorem tailTrace_2051520 : CollatzResearch.WordTrace tailWord_2051520 prefixEnd_2051520 351138610770639550755079 := by
  unfold tailWord_2051520
  simp only [CollatzResearch.WordTrace]
  refine ⟨37412540763850443283296007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49883387685133924377728009 37412540763850443283296007)
  ·
    refine ⟨56118811145775664924944011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37412540763850443283296007 56118811145775664924944011)
    ·
      refine ⟨84178216718663497387416017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56118811145775664924944011 84178216718663497387416017)
      ·
        refine ⟨63133662538997623040562013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84178216718663497387416017 63133662538997623040562013)
        ·
          refine ⟨23675123452124108640210755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63133662538997623040562013 23675123452124108640210755)
          ·
            refine ⟨35512685178186162960316133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23675123452124108640210755 35512685178186162960316133)
            ·
              refine ⟨6658628470909905555059275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35512685178186162960316133 6658628470909905555059275)
              ·
                refine ⟨9987942706364858332588913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6658628470909905555059275 9987942706364858332588913)
                ·
                  refine ⟨7490957029773643749441685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9987942706364858332588913 7490957029773643749441685)
                  ·
                    refine ⟨351138610770639550755079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7490957029773643749441685 351138610770639550755079)
                    ·
                      rfl

theorem cell23_2051520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 2, 6].length) (baseStart_2051520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2051520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2051520 prefixEnd_2051520 := by exact prefixLift 2051520
  have htrace : WordTrace (prefixWord ++ tailWord_2051520) baseStart_2051520 baseEnd_2051520 := by
    simpa [prefixWord, tailWord_2051520, baseEnd_2051520] using wordTrace_append hprefix tailTrace_2051520
  have hstable : (prefixWord ++ tailWord_2051520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051520).length < 2 ^ (prefixWord ++ tailWord_2051520).sum := by decide
  have hdescent : baseEnd_2051520 < baseStart_2051520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051544 : List Nat := [2, 1, 2, 2, 2, 1, 3, 2, 4, 2, 2]
def baseStart_2051544 : Nat := 118140960795 + 2051544 * 2 ^ 59
def prefixEnd_2051544 : Nat := 4983230072969 + 3 ^ 40 * 2051544 * 2
def baseEnd_2051544 : Nat := 1053428155847626558365127

theorem tailTrace_2051544 : CollatzResearch.WordTrace tailWord_2051544 prefixEnd_2051544 1053428155847626558365127 := by
  unfold tailWord_2051544
  simp only [CollatzResearch.WordTrace]
  refine ⟨37412978439806969332732843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49883971253075959110310457 37412978439806969332732843)
  ·
    refine ⟨56119467659710453999099265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37412978439806969332732843 56119467659710453999099265)
    ·
      refine ⟨42089600744782840499324449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56119467659710453999099265 42089600744782840499324449)
      ·
        refine ⟨31567200558587130374493337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42089600744782840499324449 31567200558587130374493337)
        ·
          refine ⟨23675400418940347780870003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31567200558587130374493337 23675400418940347780870003)
          ·
            refine ⟨35513100628410521671305005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23675400418940347780870003 35513100628410521671305005)
            ·
              refine ⟨13317412735653945626739377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35513100628410521671305005 13317412735653945626739377)
              ·
                refine ⟨9988059551740459220054533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13317412735653945626739377 9988059551740459220054533)
                ·
                  refine ⟨1872761165951336103760225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9988059551740459220054533 1872761165951336103760225)
                  ·
                    refine ⟨1404570874463502077820169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1872761165951336103760225 1404570874463502077820169)
                    ·
                      refine ⟨1053428155847626558365127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1404570874463502077820169 1053428155847626558365127)
                      ·
                        rfl

theorem cell23_2051544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 4, 2, 2].length) (baseStart_2051544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2051544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2051544 prefixEnd_2051544 := by exact prefixLift 2051544
  have htrace : WordTrace (prefixWord ++ tailWord_2051544) baseStart_2051544 baseEnd_2051544 := by
    simpa [prefixWord, tailWord_2051544, baseEnd_2051544] using wordTrace_append hprefix tailTrace_2051544
  have hstable : (prefixWord ++ tailWord_2051544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051544).length < 2 ^ (prefixWord ++ tailWord_2051544).sum := by decide
  have hdescent : baseEnd_2051544 < baseStart_2051544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051560 : List Nat := [2, 1, 4, 1, 1, 2, 1, 1, 1, 2, 7]
def baseStart_2051560 : Nat := 118140960795 + 2051560 * 2 ^ 59
def prefixEnd_2051560 : Nat := 4983230072969 + 3 ^ 40 * 2051560 * 2
def baseEnd_2051560 : Nat := 1053436371538098495765053

theorem tailTrace_2051560 : CollatzResearch.WordTrace tailWord_2051560 prefixEnd_2051560 1053436371538098495765053 := by
  unfold tailWord_2051560
  simp only [CollatzResearch.WordTrace]
  refine ⟨37413270223777986699024067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49884360298370648932032089 37413270223777986699024067)
  ·
    refine ⟨56119905335666980048536101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37413270223777986699024067 56119905335666980048536101)
    ·
      refine ⟨10522482250437558759100519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56119905335666980048536101 10522482250437558759100519)
      ·
        refine ⟨15783723375656338138650779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10522482250437558759100519 15783723375656338138650779)
        ·
          refine ⟨23675585063484507207976169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15783723375656338138650779 23675585063484507207976169)
          ·
            refine ⟨17756688797613380405982127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23675585063484507207976169 17756688797613380405982127)
            ·
              refine ⟨26635033196420070608973191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17756688797613380405982127 26635033196420070608973191)
              ·
                refine ⟨39952549794630105913459787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26635033196420070608973191 39952549794630105913459787)
                ·
                  refine ⟨59928824691945158870189681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39952549794630105913459787 59928824691945158870189681)
                  ·
                    refine ⟨44946618518958869152642261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59928824691945158870189681 44946618518958869152642261)
                    ·
                      refine ⟨1053436371538098495765053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 44946618518958869152642261 1053436371538098495765053)
                      ·
                        rfl

theorem cell23_2051560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_2051560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2051560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2051560 prefixEnd_2051560 := by exact prefixLift 2051560
  have htrace : WordTrace (prefixWord ++ tailWord_2051560) baseStart_2051560 baseEnd_2051560 := by
    simpa [prefixWord, tailWord_2051560, baseEnd_2051560] using wordTrace_append hprefix tailTrace_2051560
  have hstable : (prefixWord ++ tailWord_2051560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051560).length < 2 ^ (prefixWord ++ tailWord_2051560).sum := by decide
  have hdescent : baseEnd_2051560 < baseStart_2051560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051567 : List Nat := [1, 1, 2, 1, 4, 1, 2, 6, 5]
def baseStart_2051567 : Nat := 118140960795 + 2051567 * 2 ^ 59
def prefixEnd_2051567 : Nat := 4983230072969 + 3 ^ 40 * 2051567 * 2
def baseEnd_2051567 : Nat := 117048885100297774264169

theorem tailTrace_2051567 : CollatzResearch.WordTrace tailWord_2051567 prefixEnd_2051567 117048885100297774264169 := by
  unfold tailWord_2051567
  simp only [CollatzResearch.WordTrace]
  refine ⟨74826795758530613593552955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49884530505687075729035303 74826795758530613593552955)
  ·
    refine ⟨112240193637795920390329433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74826795758530613593552955 112240193637795920390329433)
    ·
      refine ⟨84180145228346940292747075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112240193637795920390329433 84180145228346940292747075)
      ·
        refine ⟨126270217842520410439120613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84180145228346940292747075 126270217842520410439120613)
        ·
          refine ⟨23675665845472576957335115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126270217842520410439120613 23675665845472576957335115)
          ·
            refine ⟨35513498768208865436002673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23675665845472576957335115 35513498768208865436002673)
            ·
              refine ⟨26635124076156649077002005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35513498768208865436002673 26635124076156649077002005)
              ·
                refine ⟨1248521441069842925484469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26635124076156649077002005 1248521441069842925484469)
                ·
                  refine ⟨117048885100297774264169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1248521441069842925484469 117048885100297774264169)
                  ·
                    rfl

theorem cell23_2051567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 6, 5].length) (baseStart_2051567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2051567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2051567 prefixEnd_2051567 := by exact prefixLift 2051567
  have htrace : WordTrace (prefixWord ++ tailWord_2051567) baseStart_2051567 baseEnd_2051567 := by
    simpa [prefixWord, tailWord_2051567, baseEnd_2051567] using wordTrace_append hprefix tailTrace_2051567
  have hstable : (prefixWord ++ tailWord_2051567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051567).length < 2 ^ (prefixWord ++ tailWord_2051567).sum := by decide
  have hdescent : baseEnd_2051567 < baseStart_2051567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051580 : List Nat := [2, 2, 2, 1, 2, 1, 2, 1, 3, 7]
def baseStart_2051580 : Nat := 118140960795 + 2051580 * 2 ^ 59
def prefixEnd_2051580 : Nat := 4983230072969 + 3 ^ 40 * 2051580 * 2
def baseEnd_2051580 : Nat := 351148880383729472504987

theorem tailTrace_2051580 : CollatzResearch.WordTrace tailWord_2051580 prefixEnd_2051580 351148880383729472504987 := by
  unfold tailWord_2051580
  simp only [CollatzResearch.WordTrace]
  refine ⟨37413634953741758406888097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49884846604989011209184129 37413634953741758406888097)
  ·
    refine ⟨28060226215306318805166073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37413634953741758406888097 28060226215306318805166073)
    ·
      refine ⟨21045169661479739103874555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28060226215306318805166073 21045169661479739103874555)
      ·
        refine ⟨31567754492219608655811833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21045169661479739103874555 31567754492219608655811833)
        ·
          refine ⟨23675815869164706491858875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31567754492219608655811833 23675815869164706491858875)
          ·
            refine ⟨35513723803747059737788313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23675815869164706491858875 35513723803747059737788313)
            ·
              refine ⟨26635292852810294803341235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35513723803747059737788313 26635292852810294803341235)
              ·
                refine ⟨39952939279215442205011853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26635292852810294803341235 39952939279215442205011853)
                ·
                  refine ⟨14982352229705790826879445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39952939279215442205011853 14982352229705790826879445)
                  ·
                    refine ⟨351148880383729472504987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14982352229705790826879445 351148880383729472504987)
                    ·
                      rfl

theorem cell23_2051580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 3, 7].length) (baseStart_2051580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2051580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2051580 prefixEnd_2051580 := by exact prefixLift 2051580
  have htrace : WordTrace (prefixWord ++ tailWord_2051580) baseStart_2051580 baseEnd_2051580 := by
    simpa [prefixWord, tailWord_2051580, baseEnd_2051580] using wordTrace_append hprefix tailTrace_2051580
  have hstable : (prefixWord ++ tailWord_2051580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051580).length < 2 ^ (prefixWord ++ tailWord_2051580).sum := by decide
  have hdescent : baseEnd_2051580 < baseStart_2051580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051582 : List Nat := [4, 2, 2, 3, 2, 1, 1, 2, 1, 3, 2]
def baseStart_2051582 : Nat := 118140960795 + 2051582 * 2 ^ 59
def prefixEnd_2051582 : Nat := 4983230072969 + 3 ^ 40 * 2051582 * 2
def baseEnd_2051582 : Nat := 1053447668112497409689953

theorem tailTrace_2051582 : CollatzResearch.WordTrace tailWord_2051582 prefixEnd_2051582 1053447668112497409689953 := by
  unfold tailWord_2051582
  simp only [CollatzResearch.WordTrace]
  refine ⟨9353417856684533894418625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49884895235650847436899333 9353417856684533894418625)
  ·
    refine ⟨7015063392513400420813969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9353417856684533894418625 7015063392513400420813969)
    ·
      refine ⟨5261297544385050315610477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7015063392513400420813969 5261297544385050315610477)
      ·
        refine ⟨1972986579144393868353929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5261297544385050315610477 1972986579144393868353929)
        ·
          refine ⟨1479739934358295401265447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1972986579144393868353929 1479739934358295401265447)
          ·
            refine ⟨2219609901537443101898171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1479739934358295401265447 2219609901537443101898171)
            ·
              refine ⟨3329414852306164652847257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2219609901537443101898171 3329414852306164652847257)
              ·
                refine ⟨2497061139229623489635443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3329414852306164652847257 2497061139229623489635443)
                ·
                  refine ⟨3745591708844435234453165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2497061139229623489635443 3745591708844435234453165)
                  ·
                    refine ⟨1404596890816663212919937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3745591708844435234453165 1404596890816663212919937)
                    ·
                      refine ⟨1053447668112497409689953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1404596890816663212919937 1053447668112497409689953)
                      ·
                        rfl

theorem cell23_2051582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_2051582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2051582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2051582 prefixEnd_2051582 := by exact prefixLift 2051582
  have htrace : WordTrace (prefixWord ++ tailWord_2051582) baseStart_2051582 baseEnd_2051582 := by
    simpa [prefixWord, tailWord_2051582, baseEnd_2051582] using wordTrace_append hprefix tailTrace_2051582
  have hstable : (prefixWord ++ tailWord_2051582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051582).length < 2 ^ (prefixWord ++ tailWord_2051582).sum := by decide
  have hdescent : baseEnd_2051582 < baseStart_2051582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051587 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 4, 5, 2]
def baseStart_2051587 : Nat := 118140960795 + 2051587 * 2 ^ 59
def prefixEnd_2051587 : Nat := 4983230072969 + 3 ^ 40 * 2051587 * 2
def baseEnd_2051587 : Nat := 1053450235515769890127429

theorem tailTrace_2051587 : CollatzResearch.WordTrace tailWord_2051587 prefixEnd_2051587 1053450235515769890127429 := by
  unfold tailWord_2051587
  simp only [CollatzResearch.WordTrace]
  refine ⟨74827525218458157009281015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49885016812305438006187343 74827525218458157009281015)
  ·
    refine ⟨112241287827687235513921523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74827525218458157009281015 112241287827687235513921523)
    ·
      refine ⟨168361931741530853270882285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112241287827687235513921523 168361931741530853270882285)
      ·
        refine ⟨63135724403074069976580857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168361931741530853270882285 63135724403074069976580857)
        ·
          refine ⟨47351793302305552482435643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63135724403074069976580857 47351793302305552482435643)
          ·
            refine ⟨71027689953458328723653465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47351793302305552482435643 71027689953458328723653465)
            ·
              refine ⟨53270767465093746542740099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71027689953458328723653465 53270767465093746542740099)
              ·
                refine ⟨79906151197640619814110149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53270767465093746542740099 79906151197640619814110149)
                ·
                  refine ⟨14982403349557616215145653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79906151197640619814110149 14982403349557616215145653)
                  ·
                    refine ⟨1404600314021026520169905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14982403349557616215145653 1404600314021026520169905)
                    ·
                      refine ⟨1053450235515769890127429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1404600314021026520169905 1053450235515769890127429)
                      ·
                        rfl

theorem cell23_2051587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 5, 2].length) (baseStart_2051587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2051587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2051587 prefixEnd_2051587 := by exact prefixLift 2051587
  have htrace : WordTrace (prefixWord ++ tailWord_2051587) baseStart_2051587 baseEnd_2051587 := by
    simpa [prefixWord, tailWord_2051587, baseEnd_2051587] using wordTrace_append hprefix tailTrace_2051587
  have hstable : (prefixWord ++ tailWord_2051587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051587).length < 2 ^ (prefixWord ++ tailWord_2051587).sum := by decide
  have hdescent : baseEnd_2051587 < baseStart_2051587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051687 : List Nat := [1, 1, 5, 1, 1, 1, 2, 1, 5, 5]
def baseStart_2051687 : Nat := 118140960795 + 2051687 * 2 ^ 59
def prefixEnd_2051687 : Nat := 4983230072969 + 3 ^ 40 * 2051687 * 2
def baseEnd_2051687 : Nat := 351167194527073166292323

theorem tailTrace_2051687 : CollatzResearch.WordTrace tailWord_2051687 prefixEnd_2051687 351167194527073166292323 := by
  unfold tailWord_2051687
  simp only [CollatzResearch.WordTrace]
  refine ⟨74831172518095874087921315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49887448345397249391947543 74831172518095874087921315)
  ·
    refine ⟨112246758777143811131881973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74831172518095874087921315 112246758777143811131881973)
    ·
      refine ⟨10523133635357232293613935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 112246758777143811131881973 10523133635357232293613935)
      ·
        refine ⟨15784700453035848440420903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10523133635357232293613935 15784700453035848440420903)
        ·
          refine ⟨23677050679553772660631355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15784700453035848440420903 23677050679553772660631355)
          ·
            refine ⟨35515576019330658990947033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23677050679553772660631355 35515576019330658990947033)
            ·
              refine ⟨26636682014497994243210275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35515576019330658990947033 26636682014497994243210275)
              ·
                refine ⟨39955023021746991364815413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26636682014497994243210275 39955023021746991364815413)
                ·
                  refine ⟨3745783408288780440451445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39955023021746991364815413 3745783408288780440451445)
                  ·
                    refine ⟨351167194527073166292323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3745783408288780440451445 351167194527073166292323)
                    ·
                      rfl

theorem cell23_2051687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_2051687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2051687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2051687 prefixEnd_2051687 := by exact prefixLift 2051687
  have htrace : WordTrace (prefixWord ++ tailWord_2051687) baseStart_2051687 baseEnd_2051687 := by
    simpa [prefixWord, tailWord_2051687, baseEnd_2051687] using wordTrace_append hprefix tailTrace_2051687
  have hstable : (prefixWord ++ tailWord_2051687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051687).length < 2 ^ (prefixWord ++ tailWord_2051687).sum := by decide
  have hdescent : baseEnd_2051687 < baseStart_2051687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051717 : List Nat := [1, 3, 1, 1, 4, 1, 2, 1, 3, 6]
def baseStart_2051717 : Nat := 118140960795 + 2051717 * 2 ^ 59
def prefixEnd_2051717 : Nat := 4983230072969 + 3 ^ 40 * 2051717 * 2
def baseEnd_2051717 : Nat := 351172329333618127167277

theorem tailTrace_2051717 : CollatzResearch.WordTrace tailWord_2051717 prefixEnd_2051717 351172329333618127167277 := by
  unfold tailWord_2051717
  simp only [CollatzResearch.WordTrace]
  refine ⟨74832266707987189211513405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49888177805324792807675603 74832266707987189211513405)
  ·
    refine ⟨28062100015495195954317527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74832266707987189211513405 28062100015495195954317527)
    ·
      refine ⟨42093150023242793931476291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28062100015495195954317527 42093150023242793931476291)
      ·
        refine ⟨63139725034864190897214437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42093150023242793931476291 63139725034864190897214437)
        ·
          refine ⟨11838698444037035793227707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63139725034864190897214437 11838698444037035793227707)
          ·
            refine ⟨17758047666055553689841561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11838698444037035793227707 17758047666055553689841561)
            ·
              refine ⟨13318535749541665267381171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17758047666055553689841561 13318535749541665267381171)
              ·
                refine ⟨19977803624312497901071757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13318535749541665267381171 19977803624312497901071757)
                ·
                  refine ⟨7491676359117186712901909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19977803624312497901071757 7491676359117186712901909)
                  ·
                    refine ⟨351172329333618127167277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7491676359117186712901909 351172329333618127167277)
                    ·
                      rfl

theorem cell23_2051717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 6].length) (baseStart_2051717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2051717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2051717 prefixEnd_2051717 := by exact prefixLift 2051717
  have htrace : WordTrace (prefixWord ++ tailWord_2051717) baseStart_2051717 baseEnd_2051717 := by
    simpa [prefixWord, tailWord_2051717, baseEnd_2051717] using wordTrace_append hprefix tailTrace_2051717
  have hstable : (prefixWord ++ tailWord_2051717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051717).length < 2 ^ (prefixWord ++ tailWord_2051717).sum := by decide
  have hdescent : baseEnd_2051717 < baseStart_2051717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051724 : List Nat := [2, 2, 1, 2, 1, 1, 3, 5, 1, 1, 4]
def baseStart_2051724 : Nat := 118140960795 + 2051724 * 2 ^ 59
def prefixEnd_2051724 : Nat := 4983230072969 + 3 ^ 40 * 2051724 * 2
def baseEnd_2051724 : Nat := 1053520582365435854114299

theorem tailTrace_2051724 : CollatzResearch.WordTrace tailWord_2051724 prefixEnd_2051724 1053520582365435854114299 := by
  unfold tailWord_2051724
  simp only [CollatzResearch.WordTrace]
  refine ⟨37416261009480914703509113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49888348012641219604678817 37416261009480914703509113)
  ·
    refine ⟨28062195757110686027631835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37416261009480914703509113 28062195757110686027631835)
    ·
      refine ⟨42093293635666029041447753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28062195757110686027631835 42093293635666029041447753)
      ·
        refine ⟨31569970226749521781085815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42093293635666029041447753 31569970226749521781085815)
        ·
          refine ⟨47354955340124282671628723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31569970226749521781085815 47354955340124282671628723)
          ·
            refine ⟨71032433010186424007443085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47354955340124282671628723 71032433010186424007443085)
            ·
              refine ⟨26637162378819909002791157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71032433010186424007443085 26637162378819909002791157)
              ·
                refine ⟨2497233973014366469011671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26637162378819909002791157 2497233973014366469011671)
                ·
                  refine ⟨3745850959521549703517507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2497233973014366469011671 3745850959521549703517507)
                  ·
                    refine ⟨5618776439282324555276261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3745850959521549703517507 5618776439282324555276261)
                    ·
                      refine ⟨1053520582365435854114299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5618776439282324555276261 1053520582365435854114299)
                      ·
                        rfl

theorem cell23_2051724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 5, 1, 1, 4].length) (baseStart_2051724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2051724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2051724 prefixEnd_2051724 := by exact prefixLift 2051724
  have htrace : WordTrace (prefixWord ++ tailWord_2051724) baseStart_2051724 baseEnd_2051724 := by
    simpa [prefixWord, tailWord_2051724, baseEnd_2051724] using wordTrace_append hprefix tailTrace_2051724
  have hstable : (prefixWord ++ tailWord_2051724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051724).length < 2 ^ (prefixWord ++ tailWord_2051724).sum := by decide
  have hdescent : baseEnd_2051724 < baseStart_2051724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051735 : List Nat := [1, 1, 3, 3, 2, 3, 3, 2, 1, 1, 3]
def baseStart_2051735 : Nat := 118140960795 + 2051735 * 2 ^ 59
def prefixEnd_2051735 : Nat := 4983230072969 + 3 ^ 40 * 2051735 * 2
def baseEnd_2051735 : Nat := 1053526230652635311076749

theorem tailTrace_2051735 : CollatzResearch.WordTrace tailWord_2051735 prefixEnd_2051735 1053526230652635311076749 := by
  unfold tailWord_2051735
  simp only [CollatzResearch.WordTrace]
  refine ⟨74832923221921978285668659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49888615481281318857112439 74832923221921978285668659)
  ·
    refine ⟨112249384832882967428502989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74832923221921978285668659 112249384832882967428502989)
    ·
      refine ⟨42093519312331112785688621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112249384832882967428502989 42093519312331112785688621)
      ·
        refine ⟨15785069742124167294633233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42093519312331112785688621 15785069742124167294633233)
        ·
          refine ⟨11838802306593125470974925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15785069742124167294633233 11838802306593125470974925)
          ·
            refine ⟨4439550864972422051615597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11838802306593125470974925 4439550864972422051615597)
            ·
              refine ⟨1664831574364658269355849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4439550864972422051615597 1664831574364658269355849)
              ·
                refine ⟨1248623680773493702016887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1664831574364658269355849 1248623680773493702016887)
                ·
                  refine ⟨1872935521160240553025331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1248623680773493702016887 1872935521160240553025331)
                  ·
                    refine ⟨2809403281740360829537997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1872935521160240553025331 2809403281740360829537997)
                    ·
                      refine ⟨1053526230652635311076749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2809403281740360829537997 1053526230652635311076749)
                      ·
                        rfl

theorem cell23_2051735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 2, 1, 1, 3].length) (baseStart_2051735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2051735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2051735 prefixEnd_2051735 := by exact prefixLift 2051735
  have htrace : WordTrace (prefixWord ++ tailWord_2051735) baseStart_2051735 baseEnd_2051735 := by
    simpa [prefixWord, tailWord_2051735, baseEnd_2051735] using wordTrace_append hprefix tailTrace_2051735
  have hstable : (prefixWord ++ tailWord_2051735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051735).length < 2 ^ (prefixWord ++ tailWord_2051735).sum := by decide
  have hdescent : baseEnd_2051735 < baseStart_2051735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051737 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 5, 2, 4]
def baseStart_2051737 : Nat := 118140960795 + 2051737 * 2 ^ 59
def prefixEnd_2051737 : Nat := 4983230072969 + 3 ^ 40 * 2051737 * 2
def baseEnd_2051737 : Nat := 1053527257613944303251739

theorem tailTrace_2051737 : CollatzResearch.WordTrace tailWord_2051737 prefixEnd_2051737 1053527257613944303251739 := by
  unfold tailWord_2051737
  simp only [CollatzResearch.WordTrace]
  refine ⟨74832996167914732627241465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49888664111943155084827643 74832996167914732627241465)
  ·
    refine ⟨56124747125936049470431099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74832996167914732627241465 56124747125936049470431099)
    ·
      refine ⟨84187120688904074205646649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56124747125936049470431099 84187120688904074205646649)
      ·
        refine ⟨63140340516678055654234987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84187120688904074205646649 63140340516678055654234987)
        ·
          refine ⟨94710510775017083481352481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63140340516678055654234987 94710510775017083481352481)
          ·
            refine ⟨71032883081262812611014361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94710510775017083481352481 71032883081262812611014361)
            ·
              refine ⟨53274662310947109458260771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71032883081262812611014361 53274662310947109458260771)
              ·
                refine ⟨79911993466420664187391157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53274662310947109458260771 79911993466420664187391157)
                ·
                  refine ⟨7491749387476937267567921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79911993466420664187391157 7491749387476937267567921)
                  ·
                    refine ⟨5618812040607702950675941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7491749387476937267567921 5618812040607702950675941)
                    ·
                      refine ⟨1053527257613944303251739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5618812040607702950675941 1053527257613944303251739)
                      ·
                        rfl

theorem cell23_2051737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 2, 4].length) (baseStart_2051737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2051737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2051737 prefixEnd_2051737 := by exact prefixLift 2051737
  have htrace : WordTrace (prefixWord ++ tailWord_2051737) baseStart_2051737 baseEnd_2051737 := by
    simpa [prefixWord, tailWord_2051737, baseEnd_2051737] using wordTrace_append hprefix tailTrace_2051737
  have hstable : (prefixWord ++ tailWord_2051737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051737).length < 2 ^ (prefixWord ++ tailWord_2051737).sum := by decide
  have hdescent : baseEnd_2051737 < baseStart_2051737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051744 : List Nat := [2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 5]
def baseStart_2051744 : Nat := 118140960795 + 2051744 * 2 ^ 59
def prefixEnd_2051744 : Nat := 4983230072969 + 3 ^ 40 * 2051744 * 2
def baseEnd_2051744 : Nat := 1053530851978525775864207

theorem tailTrace_2051744 : CollatzResearch.WordTrace tailWord_2051744 prefixEnd_2051744 1053530851978525775864207 := by
  unfold tailWord_2051744
  simp only [CollatzResearch.WordTrace]
  refine ⟨37416625739444686411373143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49888834319259581881830857 37416625739444686411373143)
  ·
    refine ⟨56124938609167029617059715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37416625739444686411373143 56124938609167029617059715)
    ·
      refine ⟨84187407913750544425589573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56124938609167029617059715 84187407913750544425589573)
      ·
        refine ⟨15785138983828227079798045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84187407913750544425589573 15785138983828227079798045)
        ·
          refine ⟨5919427118935585154924267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15785138983828227079798045 5919427118935585154924267)
          ·
            refine ⟨8879140678403377732386401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5919427118935585154924267 8879140678403377732386401)
            ·
              refine ⟨6659355508802533299289801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8879140678403377732386401 6659355508802533299289801)
              ·
                refine ⟨4994516631601899974467351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6659355508802533299289801 4994516631601899974467351)
                ·
                  refine ⟨7491774947402849961701027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4994516631601899974467351 7491774947402849961701027)
                  ·
                    refine ⟨11237662421104274942551541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7491774947402849961701027 11237662421104274942551541)
                    ·
                      refine ⟨1053530851978525775864207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11237662421104274942551541 1053530851978525775864207)
                      ·
                        rfl

theorem cell23_2051744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_2051744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2051744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2051744 prefixEnd_2051744 := by exact prefixLift 2051744
  have htrace : WordTrace (prefixWord ++ tailWord_2051744) baseStart_2051744 baseEnd_2051744 := by
    simpa [prefixWord, tailWord_2051744, baseEnd_2051744] using wordTrace_append hprefix tailTrace_2051744
  have hstable : (prefixWord ++ tailWord_2051744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051744).length < 2 ^ (prefixWord ++ tailWord_2051744).sum := by decide
  have hdescent : baseEnd_2051744 < baseStart_2051744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051747 : List Nat := [1, 1, 1, 4, 1, 1, 6, 8]
def baseStart_2051747 : Nat := 118140960795 + 2051747 * 2 ^ 59
def prefixEnd_2051747 : Nat := 4983230072969 + 3 ^ 40 * 2051747 * 2
def baseEnd_2051747 : Nat := 39019718237795898671359

theorem tailTrace_2051747 : CollatzResearch.WordTrace tailWord_2051747 prefixEnd_2051747 39019718237795898671359 := by
  unfold tailWord_2051747
  simp only [CollatzResearch.WordTrace]
  refine ⟨74833360897878504335105495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49888907265252336223403663 74833360897878504335105495)
  ·
    refine ⟨112250041346817756502658243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74833360897878504335105495 112250041346817756502658243)
    ·
      refine ⟨168375062020226634753987365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112250041346817756502658243 168375062020226634753987365)
      ·
        refine ⟨31570324128792494016372631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168375062020226634753987365 31570324128792494016372631)
        ·
          refine ⟨47355486193188741024558947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31570324128792494016372631 47355486193188741024558947)
          ·
            refine ⟨71033229289783111536838421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47355486193188741024558947 71033229289783111536838421)
            ·
              refine ⟨3329682622958583353289301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 71033229289783111536838421 3329682622958583353289301)
              ·
                refine ⟨39019718237795898671359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3329682622958583353289301 39019718237795898671359)
                ·
                  rfl

theorem cell23_2051747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 8].length) (baseStart_2051747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2051747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2051747 prefixEnd_2051747 := by exact prefixLift 2051747
  have htrace : WordTrace (prefixWord ++ tailWord_2051747) baseStart_2051747 baseEnd_2051747 := by
    simpa [prefixWord, tailWord_2051747, baseEnd_2051747] using wordTrace_append hprefix tailTrace_2051747
  have hstable : (prefixWord ++ tailWord_2051747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051747).length < 2 ^ (prefixWord ++ tailWord_2051747).sum := by decide
  have hdescent : baseEnd_2051747 < baseStart_2051747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051758 : List Nat := [4, 1, 4, 1, 2, 1, 1, 1, 3, 1, 4]
def baseStart_2051758 : Nat := 118140960795 + 2051758 * 2 ^ 59
def prefixEnd_2051758 : Nat := 4983230072969 + 3 ^ 40 * 2051758 * 2
def baseEnd_2051758 : Nat := 1053538040707688721089143

theorem tailTrace_2051758 : CollatzResearch.WordTrace tailWord_2051758 prefixEnd_2051758 1053538040707688721089143 := by
  unfold tailWord_2051758
  simp only [CollatzResearch.WordTrace]
  refine ⟨9354220262604831651719491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49889174733892435475837285 9354220262604831651719491)
  ·
    refine ⟨14031330393907247477579237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9354220262604831651719491 14031330393907247477579237)
    ·
      refine ⟨2630874448857608902046107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14031330393907247477579237 2630874448857608902046107)
      ·
        refine ⟨3946311673286413353069161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2630874448857608902046107 3946311673286413353069161)
        ·
          refine ⟨2959733754964810014801871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3946311673286413353069161 2959733754964810014801871)
          ·
            refine ⟨4439600632447215022202807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2959733754964810014801871 4439600632447215022202807)
            ·
              refine ⟨6659400948670822533304211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4439600632447215022202807 6659400948670822533304211)
              ·
                refine ⟨9989101423006233799956317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6659400948670822533304211 9989101423006233799956317)
                ·
                  refine ⟨3745913033627337674983619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9989101423006233799956317 3745913033627337674983619)
                  ·
                    refine ⟨5618869550441006512475429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3745913033627337674983619 5618869550441006512475429)
                    ·
                      refine ⟨1053538040707688721089143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5618869550441006512475429 1053538040707688721089143)
                      ·
                        rfl

theorem cell23_2051758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_2051758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2051758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2051758 prefixEnd_2051758 := by exact prefixLift 2051758
  have htrace : WordTrace (prefixWord ++ tailWord_2051758) baseStart_2051758 baseEnd_2051758 := by
    simpa [prefixWord, tailWord_2051758, baseEnd_2051758] using wordTrace_append hprefix tailTrace_2051758
  have hstable : (prefixWord ++ tailWord_2051758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051758).length < 2 ^ (prefixWord ++ tailWord_2051758).sum := by decide
  have hdescent : baseEnd_2051758 < baseStart_2051758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051787 : List Nat := [1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 5]
def baseStart_2051787 : Nat := 118140960795 + 2051787 * 2 ^ 59
def prefixEnd_2051787 : Nat := 4983230072969 + 3 ^ 40 * 2051787 * 2
def baseEnd_2051787 : Nat := 1053552931646669107626509

theorem tailTrace_2051787 : CollatzResearch.WordTrace tailWord_2051787 prefixEnd_2051787 1053552931646669107626509 := by
  unfold tailWord_2051787
  simp only [CollatzResearch.WordTrace]
  refine ⟨74834819817733591166561615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49889879878489060777707743 74834819817733591166561615)
  ·
    refine ⟨112252229726600386749842423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74834819817733591166561615 112252229726600386749842423)
    ·
      refine ⟨168378344589900580124763635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112252229726600386749842423 168378344589900580124763635)
      ·
        refine ⟨252567516884850870187145453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168378344589900580124763635 252567516884850870187145453)
        ·
          refine ⟨94712818831819076320179545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252567516884850870187145453 94712818831819076320179545)
          ·
            refine ⟨71034614123864307240134659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94712818831819076320179545 71034614123864307240134659)
            ·
              refine ⟨106551921185796460860201989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71034614123864307240134659 106551921185796460860201989)
              ·
                refine ⟨19978485222336836411287873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106551921185796460860201989 19978485222336836411287873)
                ·
                  refine ⟨14983863916752627308465905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19978485222336836411287873 14983863916752627308465905)
                  ·
                    refine ⟨11237897937564470481349429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14983863916752627308465905 11237897937564470481349429)
                    ·
                      refine ⟨1053552931646669107626509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11237897937564470481349429 1053552931646669107626509)
                      ·
                        rfl

theorem cell23_2051787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 5].length) (baseStart_2051787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2051787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2051787 prefixEnd_2051787 := by exact prefixLift 2051787
  have htrace : WordTrace (prefixWord ++ tailWord_2051787) baseStart_2051787 baseEnd_2051787 := by
    simpa [prefixWord, tailWord_2051787, baseEnd_2051787] using wordTrace_append hprefix tailTrace_2051787
  have hstable : (prefixWord ++ tailWord_2051787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051787).length < 2 ^ (prefixWord ++ tailWord_2051787).sum := by decide
  have hdescent : baseEnd_2051787 < baseStart_2051787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051794 : List Nat := [3, 2, 2, 2, 2, 1, 1, 1, 2, 7]
def baseStart_2051794 : Nat := 118140960795 + 2051794 * 2 ^ 59
def prefixEnd_2051794 : Nat := 4983230072969 + 3 ^ 40 * 2051794 * 2
def baseEnd_2051794 : Nat := 351185508670416860079659

theorem tailTrace_2051794 : CollatzResearch.WordTrace tailWord_2051794 prefixEnd_2051794 351185508670416860079659 := by
  unfold tailWord_2051794
  simp only [CollatzResearch.WordTrace]
  refine ⟨18708768782177057840516609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49890050085805487574710957 18708768782177057840516609)
  ·
    refine ⟨14031576586632793380387457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18708768782177057840516609 14031576586632793380387457)
    ·
      refine ⟨10523682439974595035290593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14031576586632793380387457 10523682439974595035290593)
      ·
        refine ⟨7892761829980946276467945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10523682439974595035290593 7892761829980946276467945)
        ·
          refine ⟨5919571372485709707350959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7892761829980946276467945 5919571372485709707350959)
          ·
            refine ⟨8879357058728564561026439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5919571372485709707350959 8879357058728564561026439)
            ·
              refine ⟨13319035588092846841539659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8879357058728564561026439 13319035588092846841539659)
              ·
                refine ⟨19978553382139270262309489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13319035588092846841539659 19978553382139270262309489)
                ·
                  refine ⟨14983915036604452696732117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19978553382139270262309489 14983915036604452696732117)
                  ·
                    refine ⟨351185508670416860079659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14983915036604452696732117 351185508670416860079659)
                    ·
                      rfl

theorem cell23_2051794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_2051794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2051794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2051794 prefixEnd_2051794 := by exact prefixLift 2051794
  have htrace : WordTrace (prefixWord ++ tailWord_2051794) baseStart_2051794 baseEnd_2051794 := by
    simpa [prefixWord, tailWord_2051794, baseEnd_2051794] using wordTrace_append hprefix tailTrace_2051794
  have hstable : (prefixWord ++ tailWord_2051794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051794).length < 2 ^ (prefixWord ++ tailWord_2051794).sum := by decide
  have hdescent : baseEnd_2051794 < baseStart_2051794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051801 : List Nat := [1, 2, 1, 2, 3, 3, 1, 2, 3, 3, 2]
def baseStart_2051801 : Nat := 118140960795 + 2051801 * 2 ^ 59
def prefixEnd_2051801 : Nat := 4983230072969 + 3 ^ 40 * 2051801 * 2
def baseEnd_2051801 : Nat := 1053560120375832052851445

theorem tailTrace_2051801 : CollatzResearch.WordTrace tailWord_2051801 prefixEnd_2051801 1053560120375832052851445 := by
  unfold tailWord_2051801
  simp only [CollatzResearch.WordTrace]
  refine ⟨74835330439682871557571257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49890220293121914371714171 74835330439682871557571257)
  ·
    refine ⟨56126497829762153668178443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74835330439682871557571257 56126497829762153668178443)
    ·
      refine ⟨84189746744643230502267665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56126497829762153668178443 84189746744643230502267665)
      ·
        refine ⟨63142310058482422876700749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84189746744643230502267665 63142310058482422876700749)
        ·
          refine ⟨23678366271930908578762781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63142310058482422876700749 23678366271930908578762781)
          ·
            refine ⟨8879387351974090717036043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23678366271930908578762781 8879387351974090717036043)
            ·
              refine ⟨13319081027961136075554065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8879387351974090717036043 13319081027961136075554065)
              ·
                refine ⟨9989310770970852056665549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13319081027961136075554065 9989310770970852056665549)
                ·
                  refine ⟨3745991539114069521249581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9989310770970852056665549 3745991539114069521249581)
                  ·
                    refine ⟨1404746827167776070468593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3745991539114069521249581 1404746827167776070468593)
                    ·
                      refine ⟨1053560120375832052851445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1404746827167776070468593 1053560120375832052851445)
                      ·
                        rfl

theorem cell23_2051801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 3, 3, 2].length) (baseStart_2051801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2051801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2051801 prefixEnd_2051801 := by exact prefixLift 2051801
  have htrace : WordTrace (prefixWord ++ tailWord_2051801) baseStart_2051801 baseEnd_2051801 := by
    simpa [prefixWord, tailWord_2051801, baseEnd_2051801] using wordTrace_append hprefix tailTrace_2051801
  have hstable : (prefixWord ++ tailWord_2051801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051801).length < 2 ^ (prefixWord ++ tailWord_2051801).sum := by decide
  have hdescent : baseEnd_2051801 < baseStart_2051801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051831 : List Nat := [1, 1, 3, 1, 1, 1, 6, 2, 1, 4, 2]
def baseStart_2051831 : Nat := 118140960795 + 2051831 * 2 ^ 59
def prefixEnd_2051831 : Nat := 4983230072969 + 3 ^ 40 * 2051831 * 2
def baseEnd_2051831 : Nat := 1053575524795466935476307

theorem tailTrace_2051831 : CollatzResearch.WordTrace tailWord_2051831 prefixEnd_2051831 1053575524795466935476307 := by
  unfold tailWord_2051831
  simp only [CollatzResearch.WordTrace]
  refine ⟨74836424629574186681163347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49890949753049457787442231 74836424629574186681163347)
  ·
    refine ⟨112254636944361280021745021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74836424629574186681163347 112254636944361280021745021)
    ·
      refine ⟨42095488854135480008154383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112254636944361280021745021 42095488854135480008154383)
      ·
        refine ⟨63143233281203220012231575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42095488854135480008154383 63143233281203220012231575)
        ·
          refine ⟨94714849921804830018347363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63143233281203220012231575 94714849921804830018347363)
          ·
            refine ⟨142072274882707245027521045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94714849921804830018347363 142072274882707245027521045)
            ·
              refine ⟨6659637885126902110665049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 142072274882707245027521045 6659637885126902110665049)
              ·
                refine ⟨4994728413845176582998787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6659637885126902110665049 4994728413845176582998787)
                ·
                  refine ⟨7492092620767764874498181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4994728413845176582998787 7492092620767764874498181)
                  ·
                    refine ⟨1404767366393955913968409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7492092620767764874498181 1404767366393955913968409)
                    ·
                      refine ⟨1053575524795466935476307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1404767366393955913968409 1053575524795466935476307)
                      ·
                        rfl

theorem cell23_2051831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 4, 2].length) (baseStart_2051831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2051831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2051831 prefixEnd_2051831 := by exact prefixLift 2051831
  have htrace : WordTrace (prefixWord ++ tailWord_2051831) baseStart_2051831 baseEnd_2051831 := by
    simpa [prefixWord, tailWord_2051831, baseEnd_2051831] using wordTrace_append hprefix tailTrace_2051831
  have hstable : (prefixWord ++ tailWord_2051831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051831).length < 2 ^ (prefixWord ++ tailWord_2051831).sum := by decide
  have hdescent : baseEnd_2051831 < baseStart_2051831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051848 : List Nat := [2, 1, 3, 2, 2, 1, 3, 1, 4, 2, 2]
def baseStart_2051848 : Nat := 118140960795 + 2051848 * 2 ^ 59
def prefixEnd_2051848 : Nat := 4983230072969 + 3 ^ 40 * 2051848 * 2
def baseEnd_2051848 : Nat := 1053584253966593368963729

theorem tailTrace_2051848 : CollatzResearch.WordTrace tailWord_2051848 prefixEnd_2051848 1053584253966593368963729 := by
  unfold tailWord_2051848
  simp only [CollatzResearch.WordTrace]
  refine ⟨37418522335256299292266099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49891363113675065723021465 37418522335256299292266099)
  ·
    refine ⟨56127783502884448938399149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37418522335256299292266099 56127783502884448938399149)
    ·
      refine ⟨21047918813581668351899681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56127783502884448938399149 21047918813581668351899681)
      ·
        refine ⟨15785939110186251263924761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21047918813581668351899681 15785939110186251263924761)
        ·
          refine ⟨11839454332639688447943571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15785939110186251263924761 11839454332639688447943571)
          ·
            refine ⟨17759181498959532671915357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11839454332639688447943571 17759181498959532671915357)
            ·
              refine ⟨6659693062109824751968259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17759181498959532671915357 6659693062109824751968259)
              ·
                refine ⟨9989539593164737127952389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6659693062109824751968259 9989539593164737127952389)
                ·
                  refine ⟨1873038673718388211491073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9989539593164737127952389 1873038673718388211491073)
                  ·
                    refine ⟨1404779005288791158618305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1873038673718388211491073 1404779005288791158618305)
                    ·
                      refine ⟨1053584253966593368963729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1404779005288791158618305 1053584253966593368963729)
                      ·
                        rfl

theorem cell23_2051848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 4, 2, 2].length) (baseStart_2051848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2051848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2051848 prefixEnd_2051848 := by exact prefixLift 2051848
  have htrace : WordTrace (prefixWord ++ tailWord_2051848) baseStart_2051848 baseEnd_2051848 := by
    simpa [prefixWord, tailWord_2051848, baseEnd_2051848] using wordTrace_append hprefix tailTrace_2051848
  have hstable : (prefixWord ++ tailWord_2051848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051848).length < 2 ^ (prefixWord ++ tailWord_2051848).sum := by decide
  have hdescent : baseEnd_2051848 < baseStart_2051848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051854 : List Nat := [4, 1, 1, 2, 1, 1, 3, 3, 7]
def baseStart_2051854 : Nat := 118140960795 + 2051854 * 2 ^ 59
def prefixEnd_2051854 : Nat := 4983230072969 + 3 ^ 40 * 2051854 * 2
def baseEnd_2051854 : Nat := 117065259427835593943189

theorem tailTrace_2051854 : CollatzResearch.WordTrace tailWord_2051854 prefixEnd_2051854 117065259427835593943189 := by
  unfold tailWord_2051854
  simp only [CollatzResearch.WordTrace]
  refine ⟨9354657938561357701156327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49891509005660574406167077 9354657938561357701156327)
  ·
    refine ⟨14031986907842036551734491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9354657938561357701156327 14031986907842036551734491)
    ·
      refine ⟨21047980361763054827601737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14031986907842036551734491 21047980361763054827601737)
      ·
        refine ⟨15785985271322291120701303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21047980361763054827601737 15785985271322291120701303)
        ·
          refine ⟨23678977906983436681051955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15785985271322291120701303 23678977906983436681051955)
          ·
            refine ⟨35518466860475155021577933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23678977906983436681051955 35518466860475155021577933)
            ·
              refine ⟨13319425072678183133091725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35518466860475155021577933 13319425072678183133091725)
              ·
                refine ⟨4994784402254318674909397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13319425072678183133091725 4994784402254318674909397)
                ·
                  refine ⟨117065259427835593943189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4994784402254318674909397 117065259427835593943189)
                  ·
                    rfl

theorem cell23_2051854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 7].length) (baseStart_2051854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2051854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2051854 prefixEnd_2051854 := by exact prefixLift 2051854
  have htrace : WordTrace (prefixWord ++ tailWord_2051854) baseStart_2051854 baseEnd_2051854 := by
    simpa [prefixWord, tailWord_2051854, baseEnd_2051854] using wordTrace_append hprefix tailTrace_2051854
  have hstable : (prefixWord ++ tailWord_2051854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051854).length < 2 ^ (prefixWord ++ tailWord_2051854).sum := by decide
  have hdescent : baseEnd_2051854 < baseStart_2051854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051884 : List Nat := [2, 2, 1, 1, 1, 5, 2, 1, 1, 7]
def baseStart_2051884 : Nat := 118140960795 + 2051884 * 2 ^ 59
def prefixEnd_2051884 : Nat := 4983230072969 + 3 ^ 40 * 2051884 * 2
def baseEnd_2051884 : Nat := 351200913090051742704521

theorem tailTrace_2051884 : CollatzResearch.WordTrace tailWord_2051884 prefixEnd_2051884 351200913090051742704521 := by
  unfold tailWord_2051884
  simp only [CollatzResearch.WordTrace]
  refine ⟨37419178849191088366421353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49892238465588117821895137 37419178849191088366421353)
  ·
    refine ⟨28064384136893316274816015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37419178849191088366421353 28064384136893316274816015)
    ·
      refine ⟨42096576205339974412224023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28064384136893316274816015 42096576205339974412224023)
      ·
        refine ⟨63144864308009961618336035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42096576205339974412224023 63144864308009961618336035)
        ·
          refine ⟨94717296462014942427504053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63144864308009961618336035 94717296462014942427504053)
          ·
            refine ⟨8879746543313900852578505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94717296462014942427504053 8879746543313900852578505)
            ·
              refine ⟨6659809907485425639433879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8879746543313900852578505 6659809907485425639433879)
              ·
                refine ⟨9989714861228138459150819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6659809907485425639433879 9989714861228138459150819)
                ·
                  refine ⟨14984572291842207688726229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9989714861228138459150819 14984572291842207688726229)
                  ·
                    refine ⟨351200913090051742704521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14984572291842207688726229 351200913090051742704521)
                    ·
                      rfl

theorem cell23_2051884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 7].length) (baseStart_2051884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2051884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2051884 prefixEnd_2051884 := by exact prefixLift 2051884
  have htrace : WordTrace (prefixWord ++ tailWord_2051884) baseStart_2051884 baseEnd_2051884 := by
    simpa [prefixWord, tailWord_2051884, baseEnd_2051884] using wordTrace_append hprefix tailTrace_2051884
  have hstable : (prefixWord ++ tailWord_2051884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051884).length < 2 ^ (prefixWord ++ tailWord_2051884).sum := by decide
  have hdescent : baseEnd_2051884 < baseStart_2051884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051901 : List Nat := [1, 4, 1, 4, 1, 1, 1, 1, 4, 5]
def baseStart_2051901 : Nat := 118140960795 + 2051901 * 2 ^ 59
def prefixEnd_2051901 : Nat := 4983230072969 + 3 ^ 40 * 2051901 * 2
def baseEnd_2051901 : Nat := 351203822813760553866995

theorem tailTrace_2051901 : CollatzResearch.WordTrace tailWord_2051901 prefixEnd_2051901 351203822813760553866995 := by
  unfold tailWord_2051901
  simp only [CollatzResearch.WordTrace]
  refine ⟨74838977739320588636211557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49892651826213725757474371 74838977739320588636211557)
  ·
    refine ⟨14032308326122610369289667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74838977739320588636211557 14032308326122610369289667)
    ·
      refine ⟨21048462489183915553934501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14032308326122610369289667 21048462489183915553934501)
      ·
        refine ⟨3946586716721984166362719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21048462489183915553934501 3946586716721984166362719)
        ·
          refine ⟨5919880075082976249544079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3946586716721984166362719 5919880075082976249544079)
          ·
            refine ⟨8879820112624464374316119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5919880075082976249544079 8879820112624464374316119)
            ·
              refine ⟨13319730168936696561474179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8879820112624464374316119 13319730168936696561474179)
              ·
                refine ⟨19979595253405044842211269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13319730168936696561474179 19979595253405044842211269)
                ·
                  refine ⟨3746174110013445907914613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19979595253405044842211269 3746174110013445907914613)
                  ·
                    refine ⟨351203822813760553866995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3746174110013445907914613 351203822813760553866995)
                    ·
                      rfl

theorem cell23_2051901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 4, 5].length) (baseStart_2051901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2051901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2051901 prefixEnd_2051901 := by exact prefixLift 2051901
  have htrace : WordTrace (prefixWord ++ tailWord_2051901) baseStart_2051901 baseEnd_2051901 := by
    simpa [prefixWord, tailWord_2051901, baseEnd_2051901] using wordTrace_append hprefix tailTrace_2051901
  have hstable : (prefixWord ++ tailWord_2051901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051901).length < 2 ^ (prefixWord ++ tailWord_2051901).sum := by decide
  have hdescent : baseEnd_2051901 < baseStart_2051901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051938 : List Nat := [3, 3, 2, 1, 2, 1, 1, 3, 2, 1, 4]
def baseStart_2051938 : Nat := 118140960795 + 2051938 * 2 ^ 59
def prefixEnd_2051938 : Nat := 4983230072969 + 3 ^ 40 * 2051938 * 2
def baseEnd_2051938 : Nat := 1053630467225498016838315

theorem tailTrace_2051938 : CollatzResearch.WordTrace tailWord_2051938 prefixEnd_2051938 1053630467225498016838315 := by
  unfold tailWord_2051938
  simp only [CollatzResearch.WordTrace]
  refine ⟨18710081810046635988827117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49893551493457695970205645 18710081810046635988827117)
  ·
    refine ⟨7016280678767488495810169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18710081810046635988827117 7016280678767488495810169)
    ·
      refine ⟨5262210509075616371857627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7016280678767488495810169 5262210509075616371857627)
      ·
        refine ⟨7893315763613424557786441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5262210509075616371857627 7893315763613424557786441)
        ·
          refine ⟨5919986822710068418339831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7893315763613424557786441 5919986822710068418339831)
          ·
            refine ⟨8879980234065102627509747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5919986822710068418339831 8879980234065102627509747)
            ·
              refine ⟨13319970351097653941264621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8879980234065102627509747 13319970351097653941264621)
              ·
                refine ⟨4994988881661620227974233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13319970351097653941264621 4994988881661620227974233)
                ·
                  refine ⟨3746241661246215170980675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4994988881661620227974233 3746241661246215170980675)
                  ·
                    refine ⟨5619362491869322756471013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3746241661246215170980675 5619362491869322756471013)
                    ·
                      refine ⟨1053630467225498016838315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5619362491869322756471013 1053630467225498016838315)
                      ·
                        rfl

theorem cell23_2051938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_2051938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2051938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2051938 prefixEnd_2051938 := by exact prefixLift 2051938
  have htrace : WordTrace (prefixWord ++ tailWord_2051938) baseStart_2051938 baseEnd_2051938 := by
    simpa [prefixWord, tailWord_2051938, baseEnd_2051938] using wordTrace_append hprefix tailTrace_2051938
  have hstable : (prefixWord ++ tailWord_2051938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051938).length < 2 ^ (prefixWord ++ tailWord_2051938).sum := by decide
  have hdescent : baseEnd_2051938 < baseStart_2051938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051961 : List Nat := [1, 2, 1, 3, 2, 2, 4, 2, 6]
def baseStart_2051961 : Nat := 118140960795 + 2051961 * 2 ^ 59
def prefixEnd_2051961 : Nat := 4983230072969 + 3 ^ 40 * 2051961 * 2
def baseEnd_2051961 : Nat := 117071364142283491872301

theorem tailTrace_2051961 : CollatzResearch.WordTrace tailWord_2051961 prefixEnd_2051961 117071364142283491872301 := by
  unfold tailWord_2051961
  simp only [CollatzResearch.WordTrace]
  refine ⟨74841166119103218883395737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49894110746068812588930491 74841166119103218883395737)
  ·
    refine ⟨56130874589327414162546803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74841166119103218883395737 56130874589327414162546803)
    ·
      refine ⟨84196311883991121243820205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56130874589327414162546803 84196311883991121243820205)
      ·
        refine ⟨31573616956496670466432577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84196311883991121243820205 31573616956496670466432577)
        ·
          refine ⟨23680212717372502849824433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31573616956496670466432577 23680212717372502849824433)
          ·
            refine ⟨17760159538029377137368325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23680212717372502849824433 17760159538029377137368325)
            ·
              refine ⟨3330029913380508213256561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17760159538029377137368325 3330029913380508213256561)
              ·
                refine ⟨2497522435035381159942421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3330029913380508213256561 2497522435035381159942421)
                ·
                  refine ⟨117071364142283491872301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2497522435035381159942421 117071364142283491872301)
                  ·
                    rfl

theorem cell23_2051961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 2, 6].length) (baseStart_2051961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2051961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2051961 prefixEnd_2051961 := by exact prefixLift 2051961
  have htrace : WordTrace (prefixWord ++ tailWord_2051961) baseStart_2051961 baseEnd_2051961 := by
    simpa [prefixWord, tailWord_2051961, baseEnd_2051961] using wordTrace_append hprefix tailTrace_2051961
  have hstable : (prefixWord ++ tailWord_2051961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051961).length < 2 ^ (prefixWord ++ tailWord_2051961).sum := by decide
  have hdescent : baseEnd_2051961 < baseStart_2051961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051991 : List Nat := [1, 1, 3, 3, 1, 3, 2, 1, 3, 5]
def baseStart_2051991 : Nat := 118140960795 + 2051991 * 2 ^ 59
def prefixEnd_2051991 : Nat := 4983230072969 + 3 ^ 40 * 2051991 * 2
def baseEnd_2051991 : Nat := 351219227233395436491857

theorem tailTrace_2051991 : CollatzResearch.WordTrace tailWord_2051991 prefixEnd_2051991 351219227233395436491857 := by
  unfold tailWord_2051991
  simp only [CollatzResearch.WordTrace]
  refine ⟨74842260308994534006987827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49894840205996356004658551 74842260308994534006987827)
  ·
    refine ⟨112263390463491801010481741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74842260308994534006987827 112263390463491801010481741)
    ·
      refine ⟨42098771423809425378930653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112263390463491801010481741 42098771423809425378930653)
      ·
        refine ⟨15787039283928534517098995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42098771423809425378930653 15787039283928534517098995)
        ·
          refine ⟨23680558925892801775648493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15787039283928534517098995 23680558925892801775648493)
          ·
            refine ⟨8880209597209800665868185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23680558925892801775648493 8880209597209800665868185)
            ·
              refine ⟨6660157197907350499401139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8880209597209800665868185 6660157197907350499401139)
              ·
                refine ⟨9990235796861025749101709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6660157197907350499401139 9990235796861025749101709)
                ·
                  refine ⟨3746338423822884655913141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9990235796861025749101709 3746338423822884655913141)
                  ·
                    refine ⟨351219227233395436491857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3746338423822884655913141 351219227233395436491857)
                    ·
                      rfl

theorem cell23_2051991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 3, 5].length) (baseStart_2051991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2051991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2051991 prefixEnd_2051991 := by exact prefixLift 2051991
  have htrace : WordTrace (prefixWord ++ tailWord_2051991) baseStart_2051991 baseEnd_2051991 := by
    simpa [prefixWord, tailWord_2051991, baseEnd_2051991] using wordTrace_append hprefix tailTrace_2051991
  have hstable : (prefixWord ++ tailWord_2051991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051991).length < 2 ^ (prefixWord ++ tailWord_2051991).sum := by decide
  have hdescent : baseEnd_2051991 < baseStart_2051991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051992 : List Nat := [2, 1, 2, 6, 1, 2, 1, 1, 2, 2, 3]
def baseStart_2051992 : Nat := 118140960795 + 2051992 * 2 ^ 59
def prefixEnd_2051992 : Nat := 4983230072969 + 3 ^ 40 * 2051992 * 2
def baseEnd_2051992 : Nat := 1053658195180840805563067

theorem tailTrace_2051992 : CollatzResearch.WordTrace tailWord_2051992 prefixEnd_2051992 1053658195180840805563067 := by
  unfold tailWord_2051992
  simp only [CollatzResearch.WordTrace]
  refine ⟨37421148390995455588887115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49894864521327274118516153 37421148390995455588887115)
  ·
    refine ⟨56131722586493183383330673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37421148390995455588887115 56131722586493183383330673)
    ·
      refine ⟨42098791939869887537498005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56131722586493183383330673 42098791939869887537498005)
      ·
        refine ⟨1973380872181400978320219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 42098791939869887537498005 1973380872181400978320219)
        ·
          refine ⟨2960071308272101467480329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1973380872181400978320219 2960071308272101467480329)
          ·
            refine ⟨2220053481204076100610247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2960071308272101467480329 2220053481204076100610247)
            ·
              refine ⟨3330080221806114150915371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2220053481204076100610247 3330080221806114150915371)
              ·
                refine ⟨4995120332709171226373057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3330080221806114150915371 4995120332709171226373057)
                ·
                  refine ⟨3746340249531878419779793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4995120332709171226373057 3746340249531878419779793)
                  ·
                    refine ⟨2809755187148908814834845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3746340249531878419779793 2809755187148908814834845)
                    ·
                      refine ⟨1053658195180840805563067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2809755187148908814834845 1053658195180840805563067)
                      ·
                        rfl

theorem cell23_2051992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_2051992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2051992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2051992 prefixEnd_2051992 := by exact prefixLift 2051992
  have htrace : WordTrace (prefixWord ++ tailWord_2051992) baseStart_2051992 baseEnd_2051992 := by
    simpa [prefixWord, tailWord_2051992, baseEnd_2051992] using wordTrace_append hprefix tailTrace_2051992
  have hstable : (prefixWord ++ tailWord_2051992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051992).length < 2 ^ (prefixWord ++ tailWord_2051992).sum := by decide
  have hdescent : baseEnd_2051992 < baseStart_2051992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052031 : List Nat := [1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 5]
def baseStart_2052031 : Nat := 118140960795 + 2052031 * 2 ^ 59
def prefixEnd_2052031 : Nat := 4983230072969 + 3 ^ 40 * 2052031 * 2
def baseEnd_2052031 : Nat := 1053678220926366152975387

theorem tailTrace_2052031 : CollatzResearch.WordTrace tailWord_2052031 prefixEnd_2052031 1053678220926366152975387 := by
  unfold tailWord_2052031
  simp only [CollatzResearch.WordTrace]
  refine ⟨74843719228849620838443947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49895812819233080558962631 74843719228849620838443947)
  ·
    refine ⟨112265578843274431257665921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74843719228849620838443947 112265578843274431257665921)
    ·
      refine ⟨84199184132455823443249441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112265578843274431257665921 84199184132455823443249441)
      ·
        refine ⟨63149388099341867582437081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84199184132455823443249441 63149388099341867582437081)
        ·
          refine ⟨47362041074506400686827811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63149388099341867582437081 47362041074506400686827811)
          ·
            refine ⟨71043061611759601030241717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47362041074506400686827811 71043061611759601030241717)
            ·
              refine ⟨6660287026102462596585161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71043061611759601030241717 6660287026102462596585161)
              ·
                refine ⟨4995215269576846947438871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6660287026102462596585161 4995215269576846947438871)
                ·
                  refine ⟨7492822904365270421158307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4995215269576846947438871 7492822904365270421158307)
                  ·
                    refine ⟨11239234356547905631737461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7492822904365270421158307 11239234356547905631737461)
                    ·
                      refine ⟨1053678220926366152975387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11239234356547905631737461 1053678220926366152975387)
                      ·
                        rfl

theorem cell23_2052031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 5].length) (baseStart_2052031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2052031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2052031 prefixEnd_2052031 := by exact prefixLift 2052031
  have htrace : WordTrace (prefixWord ++ tailWord_2052031) baseStart_2052031 baseEnd_2052031 := by
    simpa [prefixWord, tailWord_2052031, baseEnd_2052031] using wordTrace_append hprefix tailTrace_2052031
  have hstable : (prefixWord ++ tailWord_2052031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052031).length < 2 ^ (prefixWord ++ tailWord_2052031).sum := by decide
  have hdescent : baseEnd_2052031 < baseStart_2052031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052048 : List Nat := [2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 3]
def baseStart_2052048 : Nat := 118140960795 + 2052048 * 2 ^ 59
def prefixEnd_2052048 : Nat := 4983230072969 + 3 ^ 40 * 2052048 * 2
def baseEnd_2052048 : Nat := 1053686950097492586462809

theorem tailTrace_2052048 : CollatzResearch.WordTrace tailWord_2052048 prefixEnd_2052048 1053686950097492586462809 := by
  unfold tailWord_2052048
  simp only [CollatzResearch.WordTrace]
  refine ⟨37422169634894016370906399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49896226179858688494541865 37422169634894016370906399)
  ·
    refine ⟨56133254452341024556359599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37422169634894016370906399 56133254452341024556359599)
    ·
      refine ⟨84199881678511536834539399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56133254452341024556359599 84199881678511536834539399)
      ·
        refine ⟨126299822517767305251809099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84199881678511536834539399 126299822517767305251809099)
        ·
          refine ⟨189449733776650957877713649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126299822517767305251809099 189449733776650957877713649)
          ·
            refine ⟨142087300332488218408285237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189449733776650957877713649 142087300332488218408285237)
            ·
              refine ⟨13320684406170770475776741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142087300332488218408285237 13320684406170770475776741)
              ·
                refine ⟨2497628326157019464208139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13320684406170770475776741 2497628326157019464208139)
                ·
                  refine ⟨3746442489235529196312209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2497628326157019464208139 3746442489235529196312209)
                  ·
                    refine ⟨2809831866926646897234157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3746442489235529196312209 2809831866926646897234157)
                    ·
                      refine ⟨1053686950097492586462809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2809831866926646897234157 1053686950097492586462809)
                      ·
                        rfl

theorem cell23_2052048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 3].length) (baseStart_2052048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2052048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2052048 prefixEnd_2052048 := by exact prefixLift 2052048
  have htrace : WordTrace (prefixWord ++ tailWord_2052048) baseStart_2052048 baseEnd_2052048 := by
    simpa [prefixWord, tailWord_2052048, baseEnd_2052048] using wordTrace_append hprefix tailTrace_2052048
  have hstable : (prefixWord ++ tailWord_2052048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052048).length < 2 ^ (prefixWord ++ tailWord_2052048).sum := by decide
  have hdescent : baseEnd_2052048 < baseStart_2052048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052079 : List Nat := [1, 1, 2, 1, 4, 2, 5, 2, 1, 2, 2]
def baseStart_2052079 : Nat := 118140960795 + 2052079 * 2 ^ 59
def prefixEnd_2052079 : Nat := 4983230072969 + 3 ^ 40 * 2052079 * 2
def baseEnd_2052079 : Nat := 1053702867997781965175167

theorem tailTrace_2052079 : CollatzResearch.WordTrace tailWord_2052079 prefixEnd_2052079 1053702867997781965175167 := by
  unfold tailWord_2052079
  simp only [CollatzResearch.WordTrace]
  refine ⟨74845469932675725036191291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49896979955117150024127527 74845469932675725036191291)
  ·
    refine ⟨112268204899013587554286937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74845469932675725036191291 112268204899013587554286937)
    ·
      refine ⟨84201153674260190665715203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112268204899013587554286937 84201153674260190665715203)
      ·
        refine ⟨126301730511390285998572805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84201153674260190665715203 126301730511390285998572805)
        ·
          refine ⟨23681574470885678624732401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126301730511390285998572805 23681574470885678624732401)
          ·
            refine ⟨17761180853164258968549301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23681574470885678624732401 17761180853164258968549301)
            ·
              refine ⟨1665110704984149278301497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17761180853164258968549301 1665110704984149278301497)
              ·
                refine ⟨1248833028738111958726123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1665110704984149278301497 1248833028738111958726123)
                ·
                  refine ⟨1873249543107167938089185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1248833028738111958726123 1873249543107167938089185)
                  ·
                    refine ⟨1404937157330375953566889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1873249543107167938089185 1404937157330375953566889)
                    ·
                      refine ⟨1053702867997781965175167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1404937157330375953566889 1053702867997781965175167)
                      ·
                        rfl

theorem cell23_2052079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 2, 1, 2, 2].length) (baseStart_2052079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2052079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2052079 prefixEnd_2052079 := by exact prefixLift 2052079
  have htrace : WordTrace (prefixWord ++ tailWord_2052079) baseStart_2052079 baseEnd_2052079 := by
    simpa [prefixWord, tailWord_2052079, baseEnd_2052079] using wordTrace_append hprefix tailTrace_2052079
  have hstable : (prefixWord ++ tailWord_2052079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052079).length < 2 ^ (prefixWord ++ tailWord_2052079).sum := by decide
  have hdescent : baseEnd_2052079 < baseStart_2052079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052109 : List Nat := [1, 7, 1, 2, 1, 1, 1, 2, 1, 2, 4]
def baseStart_2052109 : Nat := 118140960795 + 2052109 * 2 ^ 59
def prefixEnd_2052109 : Nat := 4983230072969 + 3 ^ 40 * 2052109 * 2
def baseEnd_2052109 : Nat := 1053718272417416847800029

theorem tailTrace_2052109 : CollatzResearch.WordTrace tailWord_2052109 prefixEnd_2052109 1053718272417416847800029 := by
  unfold tailWord_2052109
  simp only [CollatzResearch.WordTrace]
  refine ⟨74846564122567040159783381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49897709415044693439855587 74846564122567040159783381)
  ·
    refine ⟨1754216346622665003744923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 74846564122567040159783381 1754216346622665003744923)
    ·
      refine ⟨2631324519933997505617385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1754216346622665003744923 2631324519933997505617385)
      ·
        refine ⟨1973493389950498129213039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2631324519933997505617385 1973493389950498129213039)
        ·
          refine ⟨2960240084925747193819559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1973493389950498129213039 2960240084925747193819559)
          ·
            refine ⟨4440360127388620790729339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2960240084925747193819559 4440360127388620790729339)
            ·
              refine ⟨6660540191082931186094009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4440360127388620790729339 6660540191082931186094009)
              ·
                refine ⟨4995405143312198389570507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6660540191082931186094009 4995405143312198389570507)
                ·
                  refine ⟨7493107714968297584355761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4995405143312198389570507 7493107714968297584355761)
                  ·
                    refine ⟨5619830786226223188266821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7493107714968297584355761 5619830786226223188266821)
                    ·
                      refine ⟨1053718272417416847800029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5619830786226223188266821 1053718272417416847800029)
                      ·
                        rfl

theorem cell23_2052109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_2052109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2052109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2052109 prefixEnd_2052109 := by exact prefixLift 2052109
  have htrace : WordTrace (prefixWord ++ tailWord_2052109) baseStart_2052109 baseEnd_2052109 := by
    simpa [prefixWord, tailWord_2052109, baseEnd_2052109] using wordTrace_append hprefix tailTrace_2052109
  have hstable : (prefixWord ++ tailWord_2052109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052109).length < 2 ^ (prefixWord ++ tailWord_2052109).sum := by decide
  have hdescent : baseEnd_2052109 < baseStart_2052109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052116 : List Nat := [2, 4, 3, 2, 1, 1, 3, 1, 1, 2, 3]
def baseStart_2052116 : Nat := 118140960795 + 2052116 * 2 ^ 59
def prefixEnd_2052116 : Nat := 4983230072969 + 3 ^ 40 * 2052116 * 2
def baseEnd_2052116 : Nat := 1053721866781998320412497

theorem tailTrace_2052116 : CollatzResearch.WordTrace tailWord_2052116 prefixEnd_2052116 1053721866781998320412497 := by
  unfold tailWord_2052116
  simp only [CollatzResearch.WordTrace]
  refine ⟨37423409716770840177644101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49897879622361120236858801 37423409716770840177644101)
  ·
    refine ⟨7016889321894532533308269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37423409716770840177644101 7016889321894532533308269)
    ·
      refine ⟨2631333495710449699990601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7016889321894532533308269 2631333495710449699990601)
      ·
        refine ⟨1973500121782837274992951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2631333495710449699990601 1973500121782837274992951)
        ·
          refine ⟨2960250182674255912489427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1973500121782837274992951 2960250182674255912489427)
          ·
            refine ⟨4440375274011383868734141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2960250182674255912489427 4440375274011383868734141)
            ·
              refine ⟨1665140727754268950775303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4440375274011383868734141 1665140727754268950775303)
              ·
                refine ⟨2497711091631403426162955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1665140727754268950775303 2497711091631403426162955)
                ·
                  refine ⟨3746566637447105139244433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2497711091631403426162955 3746566637447105139244433)
                  ·
                    refine ⟨2809924978085328854433325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3746566637447105139244433 2809924978085328854433325)
                    ·
                      refine ⟨1053721866781998320412497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2809924978085328854433325 1053721866781998320412497)
                      ·
                        rfl

theorem cell23_2052116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_2052116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2052116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2052116 prefixEnd_2052116 := by exact prefixLift 2052116
  have htrace : WordTrace (prefixWord ++ tailWord_2052116) baseStart_2052116 baseEnd_2052116 := by
    simpa [prefixWord, tailWord_2052116, baseEnd_2052116] using wordTrace_append hprefix tailTrace_2052116
  have hstable : (prefixWord ++ tailWord_2052116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052116).length < 2 ^ (prefixWord ++ tailWord_2052116).sum := by decide
  have hdescent : baseEnd_2052116 < baseStart_2052116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052152 : List Nat := [2, 1, 2, 1, 6, 1, 2, 1, 1, 4, 2]
def baseStart_2052152 : Nat := 118140960795 + 2052152 * 2 ^ 59
def prefixEnd_2052152 : Nat := 4983230072969 + 3 ^ 40 * 2052152 * 2
def baseEnd_2052152 : Nat := 1053740352085560179562331

theorem tailTrace_2052152 : CollatzResearch.WordTrace tailWord_2052152 prefixEnd_2052152 1053740352085560179562331 := by
  unfold tailWord_2052152
  simp only [CollatzResearch.WordTrace]
  refine ⟨37424066230705629251799355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49898754974274172335732473 37424066230705629251799355)
  ·
    refine ⟨56136099346058443877699033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37424066230705629251799355 56136099346058443877699033)
    ·
      refine ⟨42102074509543832908274275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56136099346058443877699033 42102074509543832908274275)
      ·
        refine ⟨63153111764315749362411413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42102074509543832908274275 63153111764315749362411413)
        ·
          refine ⟨2960302113952300751363035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 63153111764315749362411413 2960302113952300751363035)
          ·
            refine ⟨4440453170928451127044553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2960302113952300751363035 4440453170928451127044553)
            ·
              refine ⟨3330339878196338345283415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4440453170928451127044553 3330339878196338345283415)
              ·
                refine ⟨4995509817294507517925123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3330339878196338345283415 4995509817294507517925123)
                ·
                  refine ⟨7493264725941761276887685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4995509817294507517925123 7493264725941761276887685)
                  ·
                    refine ⟨1404987136114080239416441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7493264725941761276887685 1404987136114080239416441)
                    ·
                      refine ⟨1053740352085560179562331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1404987136114080239416441 1053740352085560179562331)
                      ·
                        rfl

theorem cell23_2052152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 1, 4, 2].length) (baseStart_2052152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2052152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2052152 prefixEnd_2052152 := by exact prefixLift 2052152
  have htrace : WordTrace (prefixWord ++ tailWord_2052152) baseStart_2052152 baseEnd_2052152 := by
    simpa [prefixWord, tailWord_2052152, baseEnd_2052152] using wordTrace_append hprefix tailTrace_2052152
  have hstable : (prefixWord ++ tailWord_2052152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052152).length < 2 ^ (prefixWord ++ tailWord_2052152).sum := by decide
  have hdescent : baseEnd_2052152 < baseStart_2052152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052171 : List Nat := [1, 1, 1, 1, 3, 1, 2, 5, 1, 7]
def baseStart_2052171 : Nat := 118140960795 + 2052171 * 2 ^ 59
def prefixEnd_2052171 : Nat := 4983230072969 + 3 ^ 40 * 2052171 * 2
def baseEnd_2052171 : Nat := 351250036072665201741581

theorem tailTrace_2052171 : CollatzResearch.WordTrace tailWord_2052171 prefixEnd_2052171 351250036072665201741581 := by
  unfold tailWord_2052171
  simp only [CollatzResearch.WordTrace]
  refine ⟨74848825448342424748540367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49899216965561616499026911 74848825448342424748540367)
  ·
    refine ⟨112273238172513637122810551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74848825448342424748540367 112273238172513637122810551)
    ·
      refine ⟨168409857258770455684215827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112273238172513637122810551 168409857258770455684215827)
      ·
        refine ⟨252614785888155683526323741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168409857258770455684215827 252614785888155683526323741)
        ·
          refine ⟨94730544708058381322371403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252614785888155683526323741 94730544708058381322371403)
          ·
            refine ⟨142095817062087571983557105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94730544708058381322371403 142095817062087571983557105)
            ·
              refine ⟨106571862796565678987667829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142095817062087571983557105 106571862796565678987667829)
              ·
                refine ⟨9991112137178032405093859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106571862796565678987667829 9991112137178032405093859)
                ·
                  refine ⟨14986668205767048607640789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9991112137178032405093859 14986668205767048607640789)
                  ·
                    refine ⟨351250036072665201741581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14986668205767048607640789 351250036072665201741581)
                    ·
                      rfl

theorem cell23_2052171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 7].length) (baseStart_2052171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2052171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2052171 prefixEnd_2052171 := by exact prefixLift 2052171
  have htrace : WordTrace (prefixWord ++ tailWord_2052171) baseStart_2052171 baseEnd_2052171 := by
    simpa [prefixWord, tailWord_2052171, baseEnd_2052171] using wordTrace_append hprefix tailTrace_2052171
  have hstable : (prefixWord ++ tailWord_2052171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052171).length < 2 ^ (prefixWord ++ tailWord_2052171).sum := by decide
  have hdescent : baseEnd_2052171 < baseStart_2052171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052182 : List Nat := [5, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4]
def baseStart_2052182 : Nat := 118140960795 + 2052182 * 2 ^ 59
def prefixEnd_2052182 : Nat := 4983230072969 + 3 ^ 40 * 2052182 * 2
def baseEnd_2052182 : Nat := 1053755756505195062187193

theorem tailTrace_2052182 : CollatzResearch.WordTrace tailWord_2052182 prefixEnd_2052182 1053755756505195062187193 := by
  unfold tailWord_2052182
  simp only [CollatzResearch.WordTrace]
  refine ⟨4678076665706410851699425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49899484434201715751460533 4678076665706410851699425)
  ·
    refine ⟨3508557499279808138774569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4678076665706410851699425 3508557499279808138774569)
    ·
      refine ⟨2631418124459856104080927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3508557499279808138774569 2631418124459856104080927)
      ·
        refine ⟨3947127186689784156121391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2631418124459856104080927 3947127186689784156121391)
        ·
          refine ⟨5920690780034676234182087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3947127186689784156121391 5920690780034676234182087)
          ·
            refine ⟨8881036170052014351273131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5920690780034676234182087 8881036170052014351273131)
            ·
              refine ⟨13321554255078021526909697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8881036170052014351273131 13321554255078021526909697)
              ·
                refine ⟨9991165691308516145182273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13321554255078021526909697 9991165691308516145182273)
                ·
                  refine ⟨7493374268481387108886705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9991165691308516145182273 7493374268481387108886705)
                  ·
                    refine ⟨5620030701361040331665029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7493374268481387108886705 5620030701361040331665029)
                    ·
                      refine ⟨1053755756505195062187193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5620030701361040331665029 1053755756505195062187193)
                      ·
                        rfl

theorem cell23_2052182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_2052182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2052182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2052182 prefixEnd_2052182 := by exact prefixLift 2052182
  have htrace : WordTrace (prefixWord ++ tailWord_2052182) baseStart_2052182 baseEnd_2052182 := by
    simpa [prefixWord, tailWord_2052182, baseEnd_2052182] using wordTrace_append hprefix tailTrace_2052182
  have hstable : (prefixWord ++ tailWord_2052182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052182).length < 2 ^ (prefixWord ++ tailWord_2052182).sum := by decide
  have hdescent : baseEnd_2052182 < baseStart_2052182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052208 : List Nat := [2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 4]
def baseStart_2052208 : Nat := 118140960795 + 2052208 * 2 ^ 59
def prefixEnd_2052208 : Nat := 4983230072969 + 3 ^ 40 * 2052208 * 2
def baseEnd_2052208 : Nat := 1053769107002211960462073

theorem tailTrace_2052208 : CollatzResearch.WordTrace tailWord_2052208 prefixEnd_2052208 1053769107002211960462073 := by
  unfold tailWord_2052208
  simp only [CollatzResearch.WordTrace]
  refine ⟨37425087474604190033818639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49900116632805586711758185 37425087474604190033818639)
  ·
    refine ⟨56137631211906285050727959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37425087474604190033818639 56137631211906285050727959)
    ·
      refine ⟨84206446817859427576091939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56137631211906285050727959 84206446817859427576091939)
      ·
        refine ⟨126309670226789141364137909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84206446817859427576091939 126309670226789141364137909)
        ·
          refine ⟨11841531583761482002887929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 126309670226789141364137909 11841531583761482002887929)
          ·
            refine ⟨8881148687821111502165947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11841531583761482002887929 8881148687821111502165947)
            ·
              refine ⟨13321723031731667253248921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8881148687821111502165947 13321723031731667253248921)
              ·
                refine ⟨9991292273798750439936691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13321723031731667253248921 9991292273798750439936691)
                ·
                  refine ⟨14986938410698125659905037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9991292273798750439936691 14986938410698125659905037)
                  ·
                    refine ⟨5620101904011797122464389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14986938410698125659905037 5620101904011797122464389)
                    ·
                      refine ⟨1053769107002211960462073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5620101904011797122464389 1053769107002211960462073)
                      ·
                        rfl

theorem cell23_2052208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 4].length) (baseStart_2052208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2052208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2052208 prefixEnd_2052208 := by exact prefixLift 2052208
  have htrace : WordTrace (prefixWord ++ tailWord_2052208) baseStart_2052208 baseEnd_2052208 := by
    simpa [prefixWord, tailWord_2052208, baseEnd_2052208] using wordTrace_append hprefix tailTrace_2052208
  have hstable : (prefixWord ++ tailWord_2052208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052208).length < 2 ^ (prefixWord ++ tailWord_2052208).sum := by decide
  have hdescent : baseEnd_2052208 < baseStart_2052208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052245 : List Nat := [1, 3, 2, 1, 1, 1, 5, 2, 2, 2, 3]
def baseStart_2052245 : Nat := 118140960795 + 2052245 * 2 ^ 59
def prefixEnd_2052245 : Nat := 4983230072969 + 3 ^ 40 * 2052245 * 2
def baseEnd_2052245 : Nat := 1053788105786428315699403

theorem tailTrace_2052245 : CollatzResearch.WordTrace tailWord_2052245 prefixEnd_2052245 1053788105786428315699403 := by
  unfold tailWord_2052245
  simp only [CollatzResearch.WordTrace]
  refine ⟨74851524450074335386734189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49901016300049556924489459 74851524450074335386734189)
  ·
    refine ⟨28069321668777875770025321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74851524450074335386734189 28069321668777875770025321)
    ·
      refine ⟨21051991251583406827518991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28069321668777875770025321 21051991251583406827518991)
      ·
        refine ⟨31577986877375110241278487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21051991251583406827518991 31577986877375110241278487)
        ·
          refine ⟨47366980316062665361917731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31577986877375110241278487 47366980316062665361917731)
          ·
            refine ⟨71050470474093998042876597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47366980316062665361917731 71050470474093998042876597)
            ·
              refine ⟨6660981606946312316519681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71050470474093998042876597 6660981606946312316519681)
              ·
                refine ⟨4995736205209734237389761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6660981606946312316519681 4995736205209734237389761)
                ·
                  refine ⟨3746802153907300678042321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4995736205209734237389761 3746802153907300678042321)
                  ·
                    refine ⟨2810101615430475508531741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3746802153907300678042321 2810101615430475508531741)
                    ·
                      refine ⟨1053788105786428315699403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2810101615430475508531741 1053788105786428315699403)
                      ·
                        rfl

theorem cell23_2052245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 2, 2, 3].length) (baseStart_2052245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2052245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2052245 prefixEnd_2052245 := by exact prefixLift 2052245
  have htrace : WordTrace (prefixWord ++ tailWord_2052245) baseStart_2052245 baseEnd_2052245 := by
    simpa [prefixWord, tailWord_2052245, baseEnd_2052245] using wordTrace_append hprefix tailTrace_2052245
  have hstable : (prefixWord ++ tailWord_2052245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052245).length < 2 ^ (prefixWord ++ tailWord_2052245).sum := by decide
  have hdescent : baseEnd_2052245 < baseStart_2052245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052275 : List Nat := [1, 1, 1, 2, 3, 2, 1, 3, 5, 1, 3]
def baseStart_2052275 : Nat := 118140960795 + 2052275 * 2 ^ 59
def prefixEnd_2052275 : Nat := 4983230072969 + 3 ^ 40 * 2052275 * 2
def baseEnd_2052275 : Nat := 1053803510206063198324265

theorem tailTrace_2052275 : CollatzResearch.WordTrace tailWord_2052275 prefixEnd_2052275 1053803510206063198324265 := by
  unfold tailWord_2052275
  simp only [CollatzResearch.WordTrace]
  refine ⟨74852618639965650510326279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49901745759977100340217519 74852618639965650510326279)
  ·
    refine ⟨112278927959948475765489419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74852618639965650510326279 112278927959948475765489419)
    ·
      refine ⟨168418391939922713648234129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112278927959948475765489419 168418391939922713648234129)
      ·
        refine ⟨126313793954942035236175597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168418391939922713648234129 126313793954942035236175597)
        ·
          refine ⟨47367672733103263213565849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126313793954942035236175597 47367672733103263213565849)
          ·
            refine ⟨35525754549827447410174387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47367672733103263213565849 35525754549827447410174387)
            ·
              refine ⟨53288631824741171115261581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35525754549827447410174387 53288631824741171115261581)
              ·
                refine ⟨19983236934277939168223093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53288631824741171115261581 19983236934277939168223093)
                ·
                  refine ⟨1873428462588556797020915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19983236934277939168223093 1873428462588556797020915)
                  ·
                    refine ⟨2810142693882835195531373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1873428462588556797020915 2810142693882835195531373)
                    ·
                      refine ⟨1053803510206063198324265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2810142693882835195531373 1053803510206063198324265)
                      ·
                        rfl

theorem cell23_2052275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 5, 1, 3].length) (baseStart_2052275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2052275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2052275 prefixEnd_2052275 := by exact prefixLift 2052275
  have htrace : WordTrace (prefixWord ++ tailWord_2052275) baseStart_2052275 baseEnd_2052275 := by
    simpa [prefixWord, tailWord_2052275, baseEnd_2052275] using wordTrace_append hprefix tailTrace_2052275
  have hstable : (prefixWord ++ tailWord_2052275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052275).length < 2 ^ (prefixWord ++ tailWord_2052275).sum := by decide
  have hdescent : baseEnd_2052275 < baseStart_2052275 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052325 : List Nat := [1, 3, 1, 4, 2, 1, 1, 3, 1, 6]
def baseStart_2052325 : Nat := 118140960795 + 2052325 * 2 ^ 59
def prefixEnd_2052325 : Nat := 4983230072969 + 3 ^ 40 * 2052325 * 2
def baseEnd_2052325 : Nat := 351276394746262667566345

theorem tailTrace_2052325 : CollatzResearch.WordTrace tailWord_2052325 prefixEnd_2052325 351276394746262667566345 := by
  unfold tailWord_2052325
  simp only [CollatzResearch.WordTrace]
  refine ⟨74854442289784509049646429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49902961526523006033097619 74854442289784509049646429)
  ·
    refine ⟨28070415858669190893617411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74854442289784509049646429 28070415858669190893617411)
    ·
      refine ⟨42105623788003786340426117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28070415858669190893617411 42105623788003786340426117)
      ·
        refine ⟨7894804460250709938829897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42105623788003786340426117 7894804460250709938829897)
        ·
          refine ⟨5921103345188032454122423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7894804460250709938829897 5921103345188032454122423)
          ·
            refine ⟨8881655017782048681183635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5921103345188032454122423 8881655017782048681183635)
            ·
              refine ⟨13322482526673073021775453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8881655017782048681183635 13322482526673073021775453)
              ·
                refine ⟨4995930947502402383165795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13322482526673073021775453 4995930947502402383165795)
                ·
                  refine ⟨7493896421253603574748693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4995930947502402383165795 7493896421253603574748693)
                  ·
                    refine ⟨351276394746262667566345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7493896421253603574748693 351276394746262667566345)
                    ·
                      rfl

theorem cell23_2052325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 6].length) (baseStart_2052325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2052325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2052325 prefixEnd_2052325 := by exact prefixLift 2052325
  have htrace : WordTrace (prefixWord ++ tailWord_2052325) baseStart_2052325 baseEnd_2052325 := by
    simpa [prefixWord, tailWord_2052325, baseEnd_2052325] using wordTrace_append hprefix tailTrace_2052325
  have hstable : (prefixWord ++ tailWord_2052325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052325).length < 2 ^ (prefixWord ++ tailWord_2052325).sum := by decide
  have hdescent : baseEnd_2052325 < baseStart_2052325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052359 : List Nat := [1, 1, 4, 5, 1, 1, 1, 1, 4, 4]
def baseStart_2052359 : Nat := 118140960795 + 2052359 * 2 ^ 59
def prefixEnd_2052359 : Nat := 4983230072969 + 3 ^ 40 * 2052359 * 2
def baseEnd_2052359 : Nat := 351282214193680289891293

theorem tailTrace_2052359 : CollatzResearch.WordTrace tailWord_2052359 prefixEnd_2052359 351282214193680289891293 := by
  unfold tailWord_2052359
  simp only [CollatzResearch.WordTrace]
  refine ⟨74855682371661332856384131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49903788247774221904256087 74855682371661332856384131)
  ·
    refine ⟨112283523557491999284576197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74855682371661332856384131 112283523557491999284576197)
    ·
      refine ⟨21053160667029749865858037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112283523557491999284576197 21053160667029749865858037)
      ·
        refine ⟨1973733812534039049924191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21053160667029749865858037 1973733812534039049924191)
        ·
          refine ⟨2960600718801058574886287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1973733812534039049924191 2960600718801058574886287)
          ·
            refine ⟨4440901078201587862329431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2960600718801058574886287 4440901078201587862329431)
            ·
              refine ⟨6661351617302381793494147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4440901078201587862329431 6661351617302381793494147)
              ·
                refine ⟨9992027425953572690241221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6661351617302381793494147 9992027425953572690241221)
                ·
                  refine ⟨1873505142366294879420229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9992027425953572690241221 1873505142366294879420229)
                  ·
                    refine ⟨351282214193680289891293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1873505142366294879420229 351282214193680289891293)
                    ·
                      rfl

theorem cell23_2052359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 4, 4].length) (baseStart_2052359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2052359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2052359 prefixEnd_2052359 := by exact prefixLift 2052359
  have htrace : WordTrace (prefixWord ++ tailWord_2052359) baseStart_2052359 baseEnd_2052359 := by
    simpa [prefixWord, tailWord_2052359, baseEnd_2052359] using wordTrace_append hprefix tailTrace_2052359
  have hstable : (prefixWord ++ tailWord_2052359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052359).length < 2 ^ (prefixWord ++ tailWord_2052359).sum := by decide
  have hdescent : baseEnd_2052359 < baseStart_2052359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052366 : List Nat := [4, 1, 1, 2, 1, 2, 1, 6, 1, 2, 2]
def baseStart_2052366 : Nat := 118140960795 + 2052366 * 2 ^ 59
def prefixEnd_2052366 : Nat := 4983230072969 + 3 ^ 40 * 2052366 * 2
def baseEnd_2052366 : Nat := 1053850236945622342286347

theorem tailTrace_2052366 : CollatzResearch.WordTrace tailWord_2052366 prefixEnd_2052366 1053850236945622342286347 := by
  unfold tailWord_2052366
  simp only [CollatzResearch.WordTrace]
  refine ⟨9356992210329496631486119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49903958455090648701259301 9356992210329496631486119)
  ·
    refine ⟨14035488315494244947229179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9356992210329496631486119 14035488315494244947229179)
    ·
      refine ⟨21053232473241367420843769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14035488315494244947229179 21053232473241367420843769)
      ·
        refine ⟨15789924354931025565632827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21053232473241367420843769 15789924354931025565632827)
        ·
          refine ⟨23684886532396538348449241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15789924354931025565632827 23684886532396538348449241)
          ·
            refine ⟨17763664899297403761336931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23684886532396538348449241 17763664899297403761336931)
            ·
              refine ⟨26645497348946105642005397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17763664899297403761336931 26645497348946105642005397)
              ·
                refine ⟨1249007688231848701969003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26645497348946105642005397 1249007688231848701969003)
                ·
                  refine ⟨1873511532347773052953505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1249007688231848701969003 1873511532347773052953505)
                  ·
                    refine ⟨1405133649260829789715129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1873511532347773052953505 1405133649260829789715129)
                    ·
                      refine ⟨1053850236945622342286347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1405133649260829789715129 1053850236945622342286347)
                      ·
                        rfl

theorem cell23_2052366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 6, 1, 2, 2].length) (baseStart_2052366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2052366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2052366 prefixEnd_2052366 := by exact prefixLift 2052366
  have htrace : WordTrace (prefixWord ++ tailWord_2052366) baseStart_2052366 baseEnd_2052366 := by
    simpa [prefixWord, tailWord_2052366, baseEnd_2052366] using wordTrace_append hprefix tailTrace_2052366
  have hstable : (prefixWord ++ tailWord_2052366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052366).length < 2 ^ (prefixWord ++ tailWord_2052366).sum := by decide
  have hdescent : baseEnd_2052366 < baseStart_2052366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052389 : List Nat := [1, 3, 1, 2, 6, 1, 2, 7]
def baseStart_2052389 : Nat := 118140960795 + 2052389 * 2 ^ 59
def prefixEnd_2052389 : Nat := 4983230072969 + 3 ^ 40 * 2052389 * 2
def baseEnd_2052389 : Nat := 39031927666691694529583

theorem tailTrace_2052389 : CollatzResearch.WordTrace tailWord_2052389 prefixEnd_2052389 39031927666691694529583 := by
  unfold tailWord_2052389
  simp only [CollatzResearch.WordTrace]
  refine ⟨74856776561552647979976221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49904517707701765319984147 74856776561552647979976221)
  ·
    refine ⟨28071291210582242992491083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74856776561552647979976221 28071291210582242992491083)
    ·
      refine ⟨42106936815873364488736625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28071291210582242992491083 42106936815873364488736625)
      ·
        refine ⟨31580202611905023366552469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42106936815873364488736625 31580202611905023366552469)
        ·
          refine ⟨1480321997433047970307147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31580202611905023366552469 1480321997433047970307147)
          ·
            refine ⟨2220482996149571955460721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1480321997433047970307147 2220482996149571955460721)
            ·
              refine ⟨1665362247112178966595541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2220482996149571955460721 1665362247112178966595541)
              ·
                refine ⟨39031927666691694529583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1665362247112178966595541 39031927666691694529583)
                ·
                  rfl

theorem cell23_2052389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 7].length) (baseStart_2052389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2052389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2052389 prefixEnd_2052389 := by exact prefixLift 2052389
  have htrace : WordTrace (prefixWord ++ tailWord_2052389) baseStart_2052389 baseEnd_2052389 := by
    simpa [prefixWord, tailWord_2052389, baseEnd_2052389] using wordTrace_append hprefix tailTrace_2052389
  have hstable : (prefixWord ++ tailWord_2052389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052389).length < 2 ^ (prefixWord ++ tailWord_2052389).sum := by decide
  have hdescent : baseEnd_2052389 < baseStart_2052389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052425 : List Nat := [1, 2, 1, 1, 2, 3, 1, 3, 2, 4, 3]
def baseStart_2052425 : Nat := 118140960795 + 2052425 * 2 ^ 59
def prefixEnd_2052425 : Nat := 4983230072969 + 3 ^ 40 * 2052425 * 2
def baseEnd_2052425 : Nat := 1053880532304237611448575

theorem tailTrace_2052425 : CollatzResearch.WordTrace tailWord_2052425 prefixEnd_2052425 1053880532304237611448575 := by
  unfold tailWord_2052425
  simp only [CollatzResearch.WordTrace]
  refine ⟨74858089589422226128286729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49905393059614817418857819 74858089589422226128286729)
  ·
    refine ⟨56143567192066669596215047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74858089589422226128286729 56143567192066669596215047)
    ·
      refine ⟨84215350788100004394322571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56143567192066669596215047 84215350788100004394322571)
      ·
        refine ⟨126323026182150006591483857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84215350788100004394322571 126323026182150006591483857)
        ·
          refine ⟨94742269636612504943612893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126323026182150006591483857 94742269636612504943612893)
          ·
            refine ⟨35528351113729689353854835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94742269636612504943612893 35528351113729689353854835)
            ·
              refine ⟨53292526670594534030782253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35528351113729689353854835 53292526670594534030782253)
              ·
                refine ⟨19984697501472950261543345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53292526670594534030782253 19984697501472950261543345)
                ·
                  refine ⟨14988523126104712696157509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19984697501472950261543345 14988523126104712696157509)
                  ·
                    refine ⟨2810348086144633630529533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14988523126104712696157509 2810348086144633630529533)
                    ·
                      refine ⟨1053880532304237611448575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2810348086144633630529533 1053880532304237611448575)
                      ·
                        rfl

theorem cell23_2052425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 4, 3].length) (baseStart_2052425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2052425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2052425 prefixEnd_2052425 := by exact prefixLift 2052425
  have htrace : WordTrace (prefixWord ++ tailWord_2052425) baseStart_2052425 baseEnd_2052425 := by
    simpa [prefixWord, tailWord_2052425, baseEnd_2052425] using wordTrace_append hprefix tailTrace_2052425
  have hstable : (prefixWord ++ tailWord_2052425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052425).length < 2 ^ (prefixWord ++ tailWord_2052425).sum := by decide
  have hdescent : baseEnd_2052425 < baseStart_2052425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052512 : List Nat := [2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 4]
def baseStart_2052512 : Nat := 118140960795 + 2052512 * 2 ^ 59
def prefixEnd_2052512 : Nat := 4983230072969 + 3 ^ 40 * 2052512 * 2
def baseEnd_2052512 : Nat := 1053925205121178771060675

theorem tailTrace_2052512 : CollatzResearch.WordTrace tailWord_2052512 prefixEnd_2052512 1053925205121178771060675 := by
  unfold tailWord_2052512
  simp only [CollatzResearch.WordTrace]
  refine ⟨37430631370053519993351895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49907508493404693324469193 37430631370053519993351895)
  ·
    refine ⟨56145947055080279990027843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37430631370053519993351895 56145947055080279990027843)
    ·
      refine ⟨84218920582620419985041765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56145947055080279990027843 84218920582620419985041765)
      ·
        refine ⟨15791047609241328747195331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84218920582620419985041765 15791047609241328747195331)
        ·
          refine ⟨23686571413861993120792997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15791047609241328747195331 23686571413861993120792997)
          ·
            refine ⟨4441232140099123710148687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23686571413861993120792997 4441232140099123710148687)
            ·
              refine ⟨6661848210148685565223031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4441232140099123710148687 6661848210148685565223031)
              ·
                refine ⟨9992772315223028347834547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6661848210148685565223031 9992772315223028347834547)
                ·
                  refine ⟨14989158472834542521751821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9992772315223028347834547 14989158472834542521751821)
                  ·
                    refine ⟨5620934427312953445656933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14989158472834542521751821 5620934427312953445656933)
                    ·
                      refine ⟨1053925205121178771060675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5620934427312953445656933 1053925205121178771060675)
                      ·
                        rfl

theorem cell23_2052512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_2052512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2052512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2052512 prefixEnd_2052512 := by exact prefixLift 2052512
  have htrace : WordTrace (prefixWord ++ tailWord_2052512) baseStart_2052512 baseEnd_2052512 := by
    simpa [prefixWord, tailWord_2052512, baseEnd_2052512] using wordTrace_append hprefix tailTrace_2052512
  have hstable : (prefixWord ++ tailWord_2052512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052512).length < 2 ^ (prefixWord ++ tailWord_2052512).sum := by decide
  have hdescent : baseEnd_2052512 < baseStart_2052512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052529 : List Nat := [1, 2, 2, 4, 1, 2, 1, 2, 2, 4, 2]
def baseStart_2052529 : Nat := 118140960795 + 2052529 * 2 ^ 59
def prefixEnd_2052529 : Nat := 4983230072969 + 3 ^ 40 * 2052529 * 2
def baseEnd_2052529 : Nat := 1053933934292305204548097

theorem tailTrace_2052529 : CollatzResearch.WordTrace tailWord_2052529 prefixEnd_2052529 1053933934292305204548097 := by
  unfold tailWord_2052529
  simp only [CollatzResearch.WordTrace]
  refine ⟨74861882781045451890072641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49907921854030301260048427 74861882781045451890072641)
  ·
    refine ⟨56146412085784088917554481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74861882781045451890072641 56146412085784088917554481)
    ·
      refine ⟨42109809064338066688165861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56146412085784088917554481 42109809064338066688165861)
      ·
        refine ⟨7895589199563387504031099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42109809064338066688165861 7895589199563387504031099)
        ·
          refine ⟨11843383799345081256046649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7895589199563387504031099 11843383799345081256046649)
          ·
            refine ⟨8882537849508810942034987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11843383799345081256046649 8882537849508810942034987)
            ·
              refine ⟨13323806774263216413052481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8882537849508810942034987 13323806774263216413052481)
              ·
                refine ⟨9992855080697412309789361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13323806774263216413052481 9992855080697412309789361)
                ·
                  refine ⟨7494641310523059232342021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9992855080697412309789361 7494641310523059232342021)
                  ·
                    refine ⟨1405245245723073606064129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7494641310523059232342021 1405245245723073606064129)
                    ·
                      refine ⟨1053933934292305204548097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1405245245723073606064129 1053933934292305204548097)
                      ·
                        rfl

theorem cell23_2052529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_2052529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2052529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2052529 prefixEnd_2052529 := by exact prefixLift 2052529
  have htrace : WordTrace (prefixWord ++ tailWord_2052529) baseStart_2052529 baseEnd_2052529 := by
    simpa [prefixWord, tailWord_2052529, baseEnd_2052529] using wordTrace_append hprefix tailTrace_2052529
  have hstable : (prefixWord ++ tailWord_2052529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052529).length < 2 ^ (prefixWord ++ tailWord_2052529).sum := by decide
  have hdescent : baseEnd_2052529 < baseStart_2052529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
