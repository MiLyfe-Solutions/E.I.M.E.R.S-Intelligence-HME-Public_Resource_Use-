import V185TrunkScan22Chunk177

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1588797 : List Nat := [1, 4, 1, 3, 3, 1, 1, 8]
def baseStart_1588797 : Nat := 118140960795 + 1588797 * 2 ^ 59
def prefixEnd_1588797 : Nat := 4983230072969 + 3 ^ 40 * 1588797 * 2
def baseEnd_1588797 : Nat := 60430853586779670972649

theorem tailTrace_1588797 : CollatzResearch.WordTrace tailWord_1588797 prefixEnd_1588797 60430853586779670972649 := by
  unfold tailWord_1588797
  simp only [CollatzResearch.WordTrace]
  refine ⟨57948187225067288769836645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38632124816711525846557763 57948187225067288769836645)
  ·
    refine ⟨10865285104700116644344371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57948187225067288769836645 10865285104700116644344371)
    ·
      refine ⟨16297927657050174966516557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10865285104700116644344371 16297927657050174966516557)
      ·
        refine ⟨6111722871393815612443709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16297927657050174966516557 6111722871393815612443709)
        ·
          refine ⟨2291896076772680854666391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6111722871393815612443709 2291896076772680854666391)
          ·
            refine ⟨3437844115159021281999587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2291896076772680854666391 3437844115159021281999587)
            ·
              refine ⟨5156766172738531922999381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3437844115159021281999587 5156766172738531922999381)
              ·
                refine ⟨60430853586779670972649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5156766172738531922999381 60430853586779670972649)
                ·
                  rfl

theorem cell22_1588797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 8].length) (baseStart_1588797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1588797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1588797 prefixEnd_1588797 := by exact prefixLift 1588797
  have htrace : WordTrace (prefixWord ++ tailWord_1588797) baseStart_1588797 baseEnd_1588797 := by
    simpa [prefixWord, tailWord_1588797, baseEnd_1588797] using wordTrace_append hprefix tailTrace_1588797
  have hstable : (prefixWord ++ tailWord_1588797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588797).length < 2 ^ (prefixWord ++ tailWord_1588797).sum := by decide
  have hdescent : baseEnd_1588797 < baseStart_1588797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588932 : List Nat := [2, 3, 3, 1, 1, 1, 11]
def baseStart_1588932 : Nat := 118140960795 + 1588932 * 2 ^ 59
def prefixEnd_1588932 : Nat := 4983230072969 + 3 ^ 40 * 1588932 * 2
def baseEnd_1588932 : Nat := 20145329464441543949201

theorem tailTrace_1588932 : CollatzResearch.WordTrace tailWord_1588932 prefixEnd_1588932 20145329464441543949201 := by
  unfold tailWord_1588932
  simp only [CollatzResearch.WordTrace]
  refine ⟨28976555539789103413000525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38635407386385471217334033 28976555539789103413000525)
  ·
    refine ⟨10866208327420913779875197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28976555539789103413000525 10866208327420913779875197)
    ·
      refine ⟨4074828122782842667453199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10866208327420913779875197 4074828122782842667453199)
      ·
        refine ⟨6112242184174264001179799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4074828122782842667453199 6112242184174264001179799)
        ·
          refine ⟨9168363276261396001769699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6112242184174264001179799 9168363276261396001769699)
          ·
            refine ⟨13752544914392094002654549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9168363276261396001769699 13752544914392094002654549)
            ·
              refine ⟨20145329464441543949201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 13752544914392094002654549 20145329464441543949201)
              ·
                rfl

theorem cell22_1588932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 11].length) (baseStart_1588932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1588932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1588932 prefixEnd_1588932 := by exact prefixLift 1588932
  have htrace : WordTrace (prefixWord ++ tailWord_1588932) baseStart_1588932 baseEnd_1588932 := by
    simpa [prefixWord, tailWord_1588932, baseEnd_1588932] using wordTrace_append hprefix tailTrace_1588932
  have hstable : (prefixWord ++ tailWord_1588932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588932).length < 2 ^ (prefixWord ++ tailWord_1588932).sum := by decide
  have hdescent : baseEnd_1588932 < baseStart_1588932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588964 : List Nat := [2, 3, 1, 1, 1, 3, 1, 4, 3, 3]
def baseStart_1588964 : Nat := 118140960795 + 1588964 * 2 ^ 59
def prefixEnd_1588964 : Nat := 4983230072969 + 3 ^ 40 * 1588964 * 2
def baseEnd_1588964 : Nat := 543934849793884269828329

theorem tailTrace_1588964 : CollatzResearch.WordTrace tailWord_1588964 prefixEnd_1588964 543934849793884269828329 := by
  unfold tailWord_1588964
  simp only [CollatzResearch.WordTrace]
  refine ⟨28977139107731138145582973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38636185476974850860777297 28977139107731138145582973)
  ·
    refine ⟨10866427165399176804593615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28977139107731138145582973 10866427165399176804593615)
    ·
      refine ⟨16299640748098765206890423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10866427165399176804593615 16299640748098765206890423)
      ·
        refine ⟨24449461122148147810335635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16299640748098765206890423 24449461122148147810335635)
        ·
          refine ⟨36674191683222221715503453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24449461122148147810335635 36674191683222221715503453)
          ·
            refine ⟨13752821881208333143313795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36674191683222221715503453 13752821881208333143313795)
            ·
              refine ⟨20629232821812499714970693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13752821881208333143313795 20629232821812499714970693)
              ·
                refine ⟨3867981154089843696557005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20629232821812499714970693 3867981154089843696557005)
                ·
                  refine ⟨1450492932783691386208877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3867981154089843696557005 1450492932783691386208877)
                  ·
                    refine ⟨543934849793884269828329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1450492932783691386208877 543934849793884269828329)
                    ·
                      rfl

theorem cell22_1588964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 3, 3].length) (baseStart_1588964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1588964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1588964 prefixEnd_1588964 := by exact prefixLift 1588964
  have htrace : WordTrace (prefixWord ++ tailWord_1588964) baseStart_1588964 baseEnd_1588964 := by
    simpa [prefixWord, tailWord_1588964, baseEnd_1588964] using wordTrace_append hprefix tailTrace_1588964
  have hstable : (prefixWord ++ tailWord_1588964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588964).length < 2 ^ (prefixWord ++ tailWord_1588964).sum := by decide
  have hdescent : baseEnd_1588964 < baseStart_1588964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588977 : List Nat := [1, 2, 2, 2, 2, 3, 1, 2, 7]
def baseStart_1588977 : Nat := 118140960795 + 1588977 * 2 ^ 59
def prefixEnd_1588977 : Nat := 4983230072969 + 3 ^ 40 * 1588977 * 2
def baseEnd_1588977 : Nat := 181313099986518856417763

theorem tailTrace_1588977 : CollatzResearch.WordTrace tailWord_1588977 prefixEnd_1588977 181313099986518856417763 := by
  unfold tailWord_1588977
  simp only [CollatzResearch.WordTrace]
  refine ⟨57954752364415179511389185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38636501576276786340926123 57954752364415179511389185)
  ·
    refine ⟨43466064273311384633541889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57954752364415179511389185 43466064273311384633541889)
    ·
      refine ⟨32599548204983538475156417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43466064273311384633541889 32599548204983538475156417)
      ·
        refine ⟨24449661153737653856367313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32599548204983538475156417 24449661153737653856367313)
        ·
          refine ⟨18337245865303240392275485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24449661153737653856367313 18337245865303240392275485)
          ·
            refine ⟨6876467199488715147103307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18337245865303240392275485 6876467199488715147103307)
            ·
              refine ⟨10314700799233072720654961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6876467199488715147103307 10314700799233072720654961)
              ·
                refine ⟨7736025599424804540491221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10314700799233072720654961 7736025599424804540491221)
                ·
                  refine ⟨181313099986518856417763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7736025599424804540491221 181313099986518856417763)
                  ·
                    rfl

theorem cell22_1588977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 7].length) (baseStart_1588977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1588977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1588977 prefixEnd_1588977 := by exact prefixLift 1588977
  have htrace : WordTrace (prefixWord ++ tailWord_1588977) baseStart_1588977 baseEnd_1588977 := by
    simpa [prefixWord, tailWord_1588977, baseEnd_1588977] using wordTrace_append hprefix tailTrace_1588977
  have hstable : (prefixWord ++ tailWord_1588977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588977).length < 2 ^ (prefixWord ++ tailWord_1588977).sum := by decide
  have hdescent : baseEnd_1588977 < baseStart_1588977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588994 : List Nat := [3, 4, 1, 1, 1, 1, 1, 3, 7]
def baseStart_1588994 : Nat := 118140960795 + 1588994 * 2 ^ 59
def prefixEnd_1588994 : Nat := 4983230072969 + 3 ^ 40 * 1588994 * 2
def baseEnd_1588994 : Nat := 181315039802324730526079

theorem tailTrace_1588994 : CollatzResearch.WordTrace tailWord_1588994 prefixEnd_1588994 181315039802324730526079 := by
  unfold tailWord_1588994
  simp only [CollatzResearch.WordTrace]
  refine ⟨14488843101338397853689509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38636914936902394276505357 14488843101338397853689509)
  ·
    refine ⟨2716658081500949597566783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14488843101338397853689509 2716658081500949597566783)
    ·
      refine ⟨4074987122251424396350175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2716658081500949597566783 4074987122251424396350175)
      ·
        refine ⟨6112480683377136594525263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4074987122251424396350175 6112480683377136594525263)
        ·
          refine ⟨9168721025065704891787895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6112480683377136594525263 9168721025065704891787895)
          ·
            refine ⟨13753081537598557337681843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9168721025065704891787895 13753081537598557337681843)
            ·
              refine ⟨20629622306397836006522765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13753081537598557337681843 20629622306397836006522765)
              ·
                refine ⟨7736108364899188502446037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20629622306397836006522765 7736108364899188502446037)
                ·
                  refine ⟨181315039802324730526079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7736108364899188502446037 181315039802324730526079)
                  ·
                    rfl

theorem cell22_1588994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_1588994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1588994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1588994 prefixEnd_1588994 := by exact prefixLift 1588994
  have htrace : WordTrace (prefixWord ++ tailWord_1588994) baseStart_1588994 baseEnd_1588994 := by
    simpa [prefixWord, tailWord_1588994, baseEnd_1588994] using wordTrace_append hprefix tailTrace_1588994
  have hstable : (prefixWord ++ tailWord_1588994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588994).length < 2 ^ (prefixWord ++ tailWord_1588994).sum := by decide
  have hdescent : baseEnd_1588994 < baseStart_1588994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589024 : List Nat := [2, 1, 1, 5, 1, 1, 3, 1, 3, 4]
def baseStart_1589024 : Nat := 118140960795 + 1589024 * 2 ^ 59
def prefixEnd_1589024 : Nat := 4983230072969 + 3 ^ 40 * 1589024 * 2
def baseEnd_1589024 : Nat := 543955389020064113328145

theorem tailTrace_1589024 : CollatzResearch.WordTrace tailWord_1589024 prefixEnd_1589024 543955389020064113328145 := by
  unfold tailWord_1589024
  simp only [CollatzResearch.WordTrace]
  refine ⟨28978233297622453269175063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38637644396829937692233417 28978233297622453269175063)
  ·
    refine ⟨43467349946433679903762595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28978233297622453269175063 43467349946433679903762595)
    ·
      refine ⟨65201024919650519855643893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43467349946433679903762595 65201024919650519855643893)
      ·
        refine ⟨6112596086217236236466615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65201024919650519855643893 6112596086217236236466615)
        ·
          refine ⟨9168894129325854354699923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6112596086217236236466615 9168894129325854354699923)
          ·
            refine ⟨13753341193988781532049885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9168894129325854354699923 13753341193988781532049885)
            ·
              refine ⟨5157502947745793074518707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13753341193988781532049885 5157502947745793074518707)
              ·
                refine ⟨7736254421618689611778061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5157502947745793074518707 7736254421618689611778061)
                ·
                  refine ⟨2901095408107008604416773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7736254421618689611778061 2901095408107008604416773)
                  ·
                    refine ⟨543955389020064113328145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2901095408107008604416773 543955389020064113328145)
                    ·
                      rfl

theorem cell22_1589024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 3, 4].length) (baseStart_1589024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1589024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1589024 prefixEnd_1589024 := by exact prefixLift 1589024
  have htrace : WordTrace (prefixWord ++ tailWord_1589024) baseStart_1589024 baseEnd_1589024 := by
    simpa [prefixWord, tailWord_1589024, baseEnd_1589024] using wordTrace_append hprefix tailTrace_1589024
  have hstable : (prefixWord ++ tailWord_1589024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589024).length < 2 ^ (prefixWord ++ tailWord_1589024).sum := by decide
  have hdescent : baseEnd_1589024 < baseStart_1589024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589049 : List Nat := [1, 2, 1, 7, 2, 1, 2, 2, 1, 3]
def baseStart_1589049 : Nat := 118140960795 + 1589049 * 2 ^ 59
def prefixEnd_1589049 : Nat := 4983230072969 + 3 ^ 40 * 1589049 * 2
def baseEnd_1589049 : Nat := 543963947030972381453069

theorem tailTrace_1589049 : CollatzResearch.WordTrace tailWord_1589049 prefixEnd_1589049 543963947030972381453069 := by
  unfold tailWord_1589049
  simp only [CollatzResearch.WordTrace]
  refine ⟨57957378420154335808010201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38638252280102890538673467 57957378420154335808010201)
  ·
    refine ⟨43468033815115751856007651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57957378420154335808010201 43468033815115751856007651)
    ·
      refine ⟨65202050722673627784011477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43468033815115751856007651 65202050722673627784011477)
      ·
        refine ⟨1528173063812663151187769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 65202050722673627784011477 1528173063812663151187769)
        ·
          refine ⟨1146129797859497363390827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1528173063812663151187769 1146129797859497363390827)
          ·
            refine ⟨1719194696789246045086241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1146129797859497363390827 1719194696789246045086241)
            ·
              refine ⟨1289396022591934533814681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1719194696789246045086241 1289396022591934533814681)
              ·
                refine ⟨967047016943950900361011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1289396022591934533814681 967047016943950900361011)
                ·
                  refine ⟨1450570525415926350541517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 967047016943950900361011 1450570525415926350541517)
                  ·
                    refine ⟨543963947030972381453069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1450570525415926350541517 543963947030972381453069)
                    ·
                      rfl

theorem cell22_1589049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 2, 1, 3].length) (baseStart_1589049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1589049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1589049 prefixEnd_1589049 := by exact prefixLift 1589049
  have htrace : WordTrace (prefixWord ++ tailWord_1589049) baseStart_1589049 baseEnd_1589049 := by
    simpa [prefixWord, tailWord_1589049, baseEnd_1589049] using wordTrace_append hprefix tailTrace_1589049
  have hstable : (prefixWord ++ tailWord_1589049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589049).length < 2 ^ (prefixWord ++ tailWord_1589049).sum := by decide
  have hdescent : baseEnd_1589049 < baseStart_1589049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589099 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 7, 3]
def baseStart_1589099 : Nat := 118140960795 + 1589099 * 2 ^ 59
def prefixEnd_1589099 : Nat := 4983230072969 + 3 ^ 40 * 1589099 * 2
def baseEnd_1589099 : Nat := 543981063052788917702915

theorem tailTrace_1589099 : CollatzResearch.WordTrace tailWord_1589099 prefixEnd_1589099 543981063052788917702915 := by
  unfold tailWord_1589099
  simp only [CollatzResearch.WordTrace]
  refine ⟨57959202069973194347330351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38639468046648796231553567 57959202069973194347330351)
  ·
    refine ⟨86938803104959791520995527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57959202069973194347330351 86938803104959791520995527)
    ·
      refine ⟨130408204657439687281493291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86938803104959791520995527 130408204657439687281493291)
      ·
        refine ⟨195612306986159530922239937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130408204657439687281493291 195612306986159530922239937)
        ·
          refine ⟨146709230239619648191679953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195612306986159530922239937 146709230239619648191679953)
          ·
            refine ⟨110031922679714736143759965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146709230239619648191679953 110031922679714736143759965)
            ·
              refine ⟨41261971004893026053909987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110031922679714736143759965 41261971004893026053909987)
              ·
                refine ⟨61892956507339539080864981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41261971004893026053909987 61892956507339539080864981)
                ·
                  refine ⟨1450616168140770447207773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 61892956507339539080864981 1450616168140770447207773)
                  ·
                    refine ⟨543981063052788917702915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1450616168140770447207773 543981063052788917702915)
                    ·
                      rfl

theorem cell22_1589099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 7, 3].length) (baseStart_1589099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1589099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1589099 prefixEnd_1589099 := by exact prefixLift 1589099
  have htrace : WordTrace (prefixWord ++ tailWord_1589099) baseStart_1589099 baseEnd_1589099 := by
    simpa [prefixWord, tailWord_1589099, baseEnd_1589099] using wordTrace_append hprefix tailTrace_1589099
  have hstable : (prefixWord ++ tailWord_1589099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589099).length < 2 ^ (prefixWord ++ tailWord_1589099).sum := by decide
  have hdescent : baseEnd_1589099 < baseStart_1589099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589210 : List Nat := [3, 1, 1, 2, 5, 1, 3, 1, 1, 4]
def baseStart_1589210 : Nat := 118140960795 + 1589210 * 2 ^ 59
def prefixEnd_1589210 : Nat := 4983230072969 + 3 ^ 40 * 1589210 * 2
def baseEnd_1589210 : Nat := 544019060621221628177575

theorem tailTrace_1589210 : CollatzResearch.WordTrace tailWord_1589210 prefixEnd_1589210 544019060621221628177575 := by
  unfold tailWord_1589210
  simp only [CollatzResearch.WordTrace]
  refine ⟨14490812643142765076155271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38642167048380706869747389 14490812643142765076155271)
  ·
    refine ⟨21736218964714147614232907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14490812643142765076155271 21736218964714147614232907)
    ·
      refine ⟨32604328447071221421349361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21736218964714147614232907 32604328447071221421349361)
      ·
        refine ⟨24453246335303416066012021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32604328447071221421349361 24453246335303416066012021)
        ·
          refine ⟨2292491843934695256188627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24453246335303416066012021 2292491843934695256188627)
          ·
            refine ⟨3438737765902042884282941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2292491843934695256188627 3438737765902042884282941)
            ·
              refine ⟨1289526662213266081606103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3438737765902042884282941 1289526662213266081606103)
              ·
                refine ⟨1934289993319899122409155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1289526662213266081606103 1934289993319899122409155)
                ·
                  refine ⟨2901434989979848683613733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1934289993319899122409155 2901434989979848683613733)
                  ·
                    refine ⟨544019060621221628177575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2901434989979848683613733 544019060621221628177575)
                    ·
                      rfl

theorem cell22_1589210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 1, 1, 4].length) (baseStart_1589210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1589210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1589210 prefixEnd_1589210 := by exact prefixLift 1589210
  have htrace : WordTrace (prefixWord ++ tailWord_1589210) baseStart_1589210 baseEnd_1589210 := by
    simpa [prefixWord, tailWord_1589210, baseEnd_1589210] using wordTrace_append hprefix tailTrace_1589210
  have hstable : (prefixWord ++ tailWord_1589210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589210).length < 2 ^ (prefixWord ++ tailWord_1589210).sum := by decide
  have hdescent : baseEnd_1589210 < baseStart_1589210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589219 : List Nat := [1, 1, 1, 6, 1, 12]
def baseStart_1589219 : Nat := 118140960795 + 1589219 * 2 ^ 59
def prefixEnd_1589219 : Nat := 4983230072969 + 3 ^ 40 * 1589219 * 2
def baseEnd_1589219 : Nat := 6716322734631464255587

theorem tailTrace_1589219 : CollatzResearch.WordTrace tailWord_1589219 prefixEnd_1589219 6716322734631464255587 := by
  unfold tailWord_1589219
  simp only [CollatzResearch.WordTrace]
  refine ⟨57963578829538454841698711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38642385886358969894465807 57963578829538454841698711)
  ·
    refine ⟨86945368244307682262548067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57963578829538454841698711 86945368244307682262548067)
    ·
      refine ⟨130418052366461523393822101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86945368244307682262548067 130418052366461523393822101)
      ·
        refine ⟨6113346204677883909085411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 130418052366461523393822101 6113346204677883909085411)
        ·
          refine ⟨9170019307016825863628117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6113346204677883909085411 9170019307016825863628117)
          ·
            refine ⟨6716322734631464255587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 9170019307016825863628117 6716322734631464255587)
            ·
              rfl

theorem cell22_1589219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 12].length) (baseStart_1589219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1589219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1589219 prefixEnd_1589219 := by exact prefixLift 1589219
  have htrace : WordTrace (prefixWord ++ tailWord_1589219) baseStart_1589219 baseEnd_1589219 := by
    simpa [prefixWord, tailWord_1589219, baseEnd_1589219] using wordTrace_append hprefix tailTrace_1589219
  have hstable : (prefixWord ++ tailWord_1589219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589219).length < 2 ^ (prefixWord ++ tailWord_1589219).sum := by decide
  have hdescent : baseEnd_1589219 < baseStart_1589219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589261 : List Nat := [1, 7, 1, 2, 1, 2, 2, 1, 1, 4]
def baseStart_1589261 : Nat := 118140960795 + 1589261 * 2 ^ 59
def prefixEnd_1589261 : Nat := 4983230072969 + 3 ^ 40 * 1589261 * 2
def baseEnd_1589261 : Nat := 544036518963474495152419

theorem tailTrace_1589261 : CollatzResearch.WordTrace tailWord_1589261 prefixEnd_1589261 544036518963474495152419 := by
  unfold tailWord_1589261
  simp only [CollatzResearch.WordTrace]
  refine ⟨57965110695386296014727637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38643407130257530676485091 57965110695386296014727637)
  ·
    refine ⟨1358557281923116312845179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 57965110695386296014727637 1358557281923116312845179)
    ·
      refine ⟨2037835922884674469267769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1358557281923116312845179 2037835922884674469267769)
      ·
        refine ⟨1528376942163505851950827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2037835922884674469267769 1528376942163505851950827)
        ·
          refine ⟨2292565413245258777926241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1528376942163505851950827 2292565413245258777926241)
          ·
            refine ⟨1719424059933944083444681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2292565413245258777926241 1719424059933944083444681)
            ·
              refine ⟨1289568044950458062583511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1719424059933944083444681 1289568044950458062583511)
              ·
                refine ⟨1934352067425687093875267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1289568044950458062583511 1934352067425687093875267)
                ·
                  refine ⟨2901528101138530640812901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1934352067425687093875267 2901528101138530640812901)
                  ·
                    refine ⟨544036518963474495152419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2901528101138530640812901 544036518963474495152419)
                    ·
                      rfl

theorem cell22_1589261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_1589261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1589261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1589261 prefixEnd_1589261 := by exact prefixLift 1589261
  have htrace : WordTrace (prefixWord ++ tailWord_1589261) baseStart_1589261 baseEnd_1589261 := by
    simpa [prefixWord, tailWord_1589261, baseEnd_1589261] using wordTrace_append hprefix tailTrace_1589261
  have hstable : (prefixWord ++ tailWord_1589261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589261).length < 2 ^ (prefixWord ++ tailWord_1589261).sum := by decide
  have hdescent : baseEnd_1589261 < baseStart_1589261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589264 : List Nat := [2, 1, 1, 1, 1, 1, 1, 5, 9]
def baseStart_1589264 : Nat := 118140960795 + 1589264 * 2 ^ 59
def prefixEnd_1589264 : Nat := 4983230072969 + 3 ^ 40 * 1589264 * 2
def baseEnd_1589264 : Nat := 181345848641594495775803

theorem tailTrace_1589264 : CollatzResearch.WordTrace tailWord_1589264 prefixEnd_1589264 181345848641594495775803 := by
  unfold tailWord_1589264
  simp only [CollatzResearch.WordTrace]
  refine ⟨28982610057187713763543423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38643480076250285018057897 28982610057187713763543423)
  ·
    refine ⟨43473915085781570645315135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28982610057187713763543423 43473915085781570645315135)
    ·
      refine ⟨65210872628672355967972703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43473915085781570645315135 65210872628672355967972703)
      ·
        refine ⟨97816308943008533951959055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65210872628672355967972703 97816308943008533951959055)
        ·
          refine ⟨146724463414512800927938583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97816308943008533951959055 146724463414512800927938583)
          ·
            refine ⟨220086695121769201391907875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146724463414512800927938583 220086695121769201391907875)
            ·
              refine ⟨330130042682653802087861813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220086695121769201391907875 330130042682653802087861813)
              ·
                refine ⟨30949691501498793945737045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 330130042682653802087861813 30949691501498793945737045)
                ·
                  refine ⟨181345848641594495775803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 30949691501498793945737045 181345848641594495775803)
                  ·
                    rfl

theorem cell22_1589264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 9].length) (baseStart_1589264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1589264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1589264 prefixEnd_1589264 := by exact prefixLift 1589264
  have htrace : WordTrace (prefixWord ++ tailWord_1589264) baseStart_1589264 baseEnd_1589264 := by
    simpa [prefixWord, tailWord_1589264, baseEnd_1589264] using wordTrace_append hprefix tailTrace_1589264
  have hstable : (prefixWord ++ tailWord_1589264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589264).length < 2 ^ (prefixWord ++ tailWord_1589264).sum := by decide
  have hdescent : baseEnd_1589264 < baseStart_1589264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589285 : List Nat := [1, 3, 1, 2, 2, 3, 2, 4, 1, 3]
def baseStart_1589285 : Nat := 118140960795 + 1589285 * 2 ^ 59
def prefixEnd_1589285 : Nat := 4983230072969 + 3 ^ 40 * 1589285 * 2
def baseEnd_1589285 : Nat := 544044734653946432552345

theorem tailTrace_1589285 : CollatzResearch.WordTrace tailWord_1589285 prefixEnd_1589285 544044734653946432552345 := by
  unfold tailWord_1589285
  simp only [CollatzResearch.WordTrace]
  refine ⟨57965986047299348113601309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38643990698199565409067539 57965986047299348113601309)
  ·
    refine ⟨21737244767737255542600491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57965986047299348113601309 21737244767737255542600491)
    ·
      refine ⟨32605867151605883313900737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21737244767737255542600491 32605867151605883313900737)
      ·
        refine ⟨24454400363704412485425553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32605867151605883313900737 24454400363704412485425553)
        ·
          refine ⟨18340800272778309364069165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24454400363704412485425553 18340800272778309364069165)
          ·
            refine ⟨6877800102291866011525937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18340800272778309364069165 6877800102291866011525937)
            ·
              refine ⟨5158350076718899508644453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6877800102291866011525937 5158350076718899508644453)
              ·
                refine ⟨967190639384793657870835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5158350076718899508644453 967190639384793657870835)
                ·
                  refine ⟨1450785959077190486806253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 967190639384793657870835 1450785959077190486806253)
                  ·
                    refine ⟨544044734653946432552345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1450785959077190486806253 544044734653946432552345)
                    ·
                      rfl

theorem cell22_1589285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 4, 1, 3].length) (baseStart_1589285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1589285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1589285 prefixEnd_1589285 := by exact prefixLift 1589285
  have htrace : WordTrace (prefixWord ++ tailWord_1589285) baseStart_1589285 baseEnd_1589285 := by
    simpa [prefixWord, tailWord_1589285, baseEnd_1589285] using wordTrace_append hprefix tailTrace_1589285
  have hstable : (prefixWord ++ tailWord_1589285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589285).length < 2 ^ (prefixWord ++ tailWord_1589285).sum := by decide
  have hdescent : baseEnd_1589285 < baseStart_1589285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589296 : List Nat := [2, 1, 1, 1, 2, 5, 2, 1, 2, 5]
def baseStart_1589296 : Nat := 118140960795 + 1589296 * 2 ^ 59
def prefixEnd_1589296 : Nat := 4983230072969 + 3 ^ 40 * 1589296 * 2
def baseEnd_1589296 : Nat := 544048500178746070527311

theorem tailTrace_1589296 : CollatzResearch.WordTrace tailWord_1589296 prefixEnd_1589296 544048500178746070527311 := by
  unfold tailWord_1589296
  simp only [CollatzResearch.WordTrace]
  refine ⟨28983193625129748496125871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38644258166839664661501161 28983193625129748496125871)
  ·
    refine ⟨43474790437694622744188807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28983193625129748496125871 43474790437694622744188807)
    ·
      refine ⟨65212185656541934116283211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43474790437694622744188807 65212185656541934116283211)
      ·
        refine ⟨97818278484812901174424817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65212185656541934116283211 97818278484812901174424817)
        ·
          refine ⟨73363708863609675880818613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97818278484812901174424817 73363708863609675880818613)
          ·
            refine ⟨6877847705963407113826745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73363708863609675880818613 6877847705963407113826745)
            ·
              refine ⟨5158385779472555335370059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6877847705963407113826745 5158385779472555335370059)
              ·
                refine ⟨7737578669208833003055089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5158385779472555335370059 7737578669208833003055089)
                ·
                  refine ⟨5803184001906624752291317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7737578669208833003055089 5803184001906624752291317)
                  ·
                    refine ⟨544048500178746070527311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5803184001906624752291317 544048500178746070527311)
                    ·
                      rfl

theorem cell22_1589296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 2, 5].length) (baseStart_1589296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1589296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1589296 prefixEnd_1589296 := by exact prefixLift 1589296
  have htrace : WordTrace (prefixWord ++ tailWord_1589296) baseStart_1589296 baseEnd_1589296 := by
    simpa [prefixWord, tailWord_1589296, baseEnd_1589296] using wordTrace_append hprefix tailTrace_1589296
  have hstable : (prefixWord ++ tailWord_1589296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589296).length < 2 ^ (prefixWord ++ tailWord_1589296).sum := by decide
  have hdescent : baseEnd_1589296 < baseStart_1589296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589311 : List Nat := [1, 1, 2, 2, 3, 1, 2, 3, 3, 4]
def baseStart_1589311 : Nat := 118140960795 + 1589311 * 2 ^ 59
def prefixEnd_1589311 : Nat := 4983230072969 + 3 ^ 40 * 1589311 * 2
def baseEnd_1589311 : Nat := 544053634985291031402265

theorem tailTrace_1589311 : CollatzResearch.WordTrace tailWord_1589311 prefixEnd_1589311 544053634985291031402265 := by
  unfold tailWord_1589311
  simp only [CollatzResearch.WordTrace]
  refine ⟨57966934345205154554047787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38644622896803436369365191 57966934345205154554047787)
  ·
    refine ⟨86950401517807731831071681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57966934345205154554047787 86950401517807731831071681)
    ·
      refine ⟨65212801138355798873303761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86950401517807731831071681 65212801138355798873303761)
      ·
        refine ⟨48909600853766849154977821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65212801138355798873303761 48909600853766849154977821)
        ·
          refine ⟨18341100320162568433116683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48909600853766849154977821 18341100320162568433116683)
          ·
            refine ⟨27511650480243852649675025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18341100320162568433116683 27511650480243852649675025)
            ·
              refine ⟨20633737860182889487256269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27511650480243852649675025 20633737860182889487256269)
              ·
                refine ⟨7737651697568583557721101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20633737860182889487256269 7737651697568583557721101)
                ·
                  refine ⟨2901619386588218834145413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7737651697568583557721101 2901619386588218834145413)
                  ·
                    refine ⟨544053634985291031402265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2901619386588218834145413 544053634985291031402265)
                    ·
                      rfl

theorem cell22_1589311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 3, 4].length) (baseStart_1589311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1589311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1589311 prefixEnd_1589311 := by exact prefixLift 1589311
  have htrace : WordTrace (prefixWord ++ tailWord_1589311) baseStart_1589311 baseEnd_1589311 := by
    simpa [prefixWord, tailWord_1589311, baseEnd_1589311] using wordTrace_append hprefix tailTrace_1589311
  have hstable : (prefixWord ++ tailWord_1589311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589311).length < 2 ^ (prefixWord ++ tailWord_1589311).sum := by decide
  have hdescent : baseEnd_1589311 < baseStart_1589311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589358 : List Nat := [4, 1, 2, 2, 1, 1, 2, 3, 1, 5]
def baseStart_1589358 : Nat := 118140960795 + 1589358 * 2 ^ 59
def prefixEnd_1589358 : Nat := 4983230072969 + 3 ^ 40 * 1589358 * 2
def baseEnd_1589358 : Nat := 544069724045798575477121

theorem tailTrace_1589358 : CollatzResearch.WordTrace tailWord_1589358 prefixEnd_1589358 544069724045798575477121 := by
  unfold tailWord_1589358
  simp only [CollatzResearch.WordTrace]
  refine ⟨7246081072004360197626091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38645765717356587720672485 7246081072004360197626091)
  ·
    refine ⟨10869121608006540296439137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7246081072004360197626091 10869121608006540296439137)
    ·
      refine ⟨8151841206004905222329353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10869121608006540296439137 8151841206004905222329353)
      ·
        refine ⟨6113880904503678916747015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8151841206004905222329353 6113880904503678916747015)
        ·
          refine ⟨9170821356755518375120523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6113880904503678916747015 9170821356755518375120523)
          ·
            refine ⟨13756232035133277562680785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9170821356755518375120523 13756232035133277562680785)
            ·
              refine ⟨10317174026349958172010589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13756232035133277562680785 10317174026349958172010589)
              ·
                refine ⟨3868940259881234314503971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10317174026349958172010589 3868940259881234314503971)
                ·
                  refine ⟨5803410389821851471755957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3868940259881234314503971 5803410389821851471755957)
                  ·
                    refine ⟨544069724045798575477121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5803410389821851471755957 544069724045798575477121)
                    ·
                      rfl

theorem cell22_1589358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_1589358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1589358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1589358 prefixEnd_1589358 := by exact prefixLift 1589358
  have htrace : WordTrace (prefixWord ++ tailWord_1589358) baseStart_1589358 baseEnd_1589358 := by
    simpa [prefixWord, tailWord_1589358, baseEnd_1589358] using wordTrace_append hprefix tailTrace_1589358
  have hstable : (prefixWord ++ tailWord_1589358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589358).length < 2 ^ (prefixWord ++ tailWord_1589358).sum := by decide
  have hdescent : baseEnd_1589358 < baseStart_1589358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589373 : List Nat := [1, 4, 1, 1, 3, 2, 1, 3, 2, 4]
def baseStart_1589373 : Nat := 118140960795 + 1589373 * 2 ^ 59
def prefixEnd_1589373 : Nat := 4983230072969 + 3 ^ 40 * 1589373 * 2
def baseEnd_1589373 : Nat := 544074858852343536352075

theorem tailTrace_1589373 : CollatzResearch.WordTrace tailWord_1589373 prefixEnd_1589373 544074858852343536352075 := by
  unfold tailWord_1589373
  simp only [CollatzResearch.WordTrace]
  refine ⟨57969195670980539142804773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38646130447320359428536515 57969195670980539142804773)
  ·
    refine ⟨10869224188308851089275895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57969195670980539142804773 10869224188308851089275895)
    ·
      refine ⟨16303836282463276633913843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10869224188308851089275895 16303836282463276633913843)
      ·
        refine ⟨24455754423694914950870765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16303836282463276633913843 24455754423694914950870765)
        ·
          refine ⟨9170907908885593106576537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24455754423694914950870765 9170907908885593106576537)
          ·
            refine ⟨6878180931664194829932403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9170907908885593106576537 6878180931664194829932403)
            ·
              refine ⟨10317271397496292244898605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6878180931664194829932403 10317271397496292244898605)
              ·
                refine ⟨3868976774061109591836977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10317271397496292244898605 3868976774061109591836977)
                ·
                  refine ⟨2901732580545832193877733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3868976774061109591836977 2901732580545832193877733)
                  ·
                    refine ⟨544074858852343536352075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2901732580545832193877733 544074858852343536352075)
                    ·
                      rfl

theorem cell22_1589373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_1589373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1589373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1589373 prefixEnd_1589373 := by exact prefixLift 1589373
  have htrace : WordTrace (prefixWord ++ tailWord_1589373) baseStart_1589373 baseEnd_1589373 := by
    simpa [prefixWord, tailWord_1589373, baseEnd_1589373] using wordTrace_append hprefix tailTrace_1589373
  have hstable : (prefixWord ++ tailWord_1589373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589373).length < 2 ^ (prefixWord ++ tailWord_1589373).sum := by decide
  have hdescent : baseEnd_1589373 < baseStart_1589373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589480 : List Nat := [2, 1, 4, 1, 2, 2, 1, 4, 1, 4]
def baseStart_1589480 : Nat := 118140960795 + 1589480 * 2 ^ 59
def prefixEnd_1589480 : Nat := 4983230072969 + 3 ^ 40 * 1589480 * 2
def baseEnd_1589480 : Nat := 544111487139030923926747

theorem tailTrace_1589480 : CollatzResearch.WordTrace tailWord_1589480 prefixEnd_1589480 544111487139030923926747 := by
  unfold tailWord_1589480
  simp only [CollatzResearch.WordTrace]
  refine ⟨28986549140796448208474947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38648732187728597611299929 28986549140796448208474947)
  ·
    refine ⟨43479823711194672312712421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28986549140796448208474947 43479823711194672312712421)
    ·
      refine ⟨8152466945849001058633579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43479823711194672312712421 8152466945849001058633579)
      ·
        refine ⟨12228700418773501587950369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8152466945849001058633579 12228700418773501587950369)
        ·
          refine ⟨9171525314080126190962777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12228700418773501587950369 9171525314080126190962777)
          ·
            refine ⟨6878643985560094643222083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9171525314080126190962777 6878643985560094643222083)
            ·
              refine ⟨10317965978340141964833125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6878643985560094643222083 10317965978340141964833125)
              ·
                refine ⟨1934618620938776618406211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10317965978340141964833125 1934618620938776618406211)
                ·
                  refine ⟨2901927931408164927609317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1934618620938776618406211 2901927931408164927609317)
                  ·
                    refine ⟨544111487139030923926747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2901927931408164927609317 544111487139030923926747)
                    ·
                      rfl

theorem cell22_1589480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_1589480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1589480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1589480 prefixEnd_1589480 := by exact prefixLift 1589480
  have htrace : WordTrace (prefixWord ++ tailWord_1589480) baseStart_1589480 baseEnd_1589480 := by
    simpa [prefixWord, tailWord_1589480, baseEnd_1589480] using wordTrace_append hprefix tailTrace_1589480
  have hstable : (prefixWord ++ tailWord_1589480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589480).length < 2 ^ (prefixWord ++ tailWord_1589480).sum := by decide
  have hdescent : baseEnd_1589480 < baseStart_1589480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589527 : List Nat := [1, 1, 3, 4, 1, 3, 1, 3, 2, 3]
def baseStart_1589527 : Nat := 118140960795 + 1589527 * 2 ^ 59
def prefixEnd_1589527 : Nat := 4983230072969 + 3 ^ 40 * 1589527 * 2
def baseEnd_1589527 : Nat := 544127576199538468001603

theorem tailTrace_1589527 : CollatzResearch.WordTrace tailWord_1589527 prefixEnd_1589527 544127576199538468001603 := by
  unfold tailWord_1589527
  simp only [CollatzResearch.WordTrace]
  refine ⟨57974812512422623443910835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38649875008281748962607223 57974812512422623443910835)
  ·
    refine ⟨86962218768633935165866253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57974812512422623443910835 86962218768633935165866253)
    ·
      refine ⟨32610832038237725687199845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86962218768633935165866253 32610832038237725687199845)
      ·
        refine ⟨6114531007169573566349971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32610832038237725687199845 6114531007169573566349971)
        ·
          refine ⟨9171796510754360349524957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6114531007169573566349971 9171796510754360349524957)
          ·
            refine ⟨3439423691532885131071859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9171796510754360349524957 3439423691532885131071859)
            ·
              refine ⟨5159135537299327696607789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3439423691532885131071859 5159135537299327696607789)
              ·
                refine ⟨1934675826487247886227921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5159135537299327696607789 1934675826487247886227921)
                ·
                  refine ⟨1451006869865435914670941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1934675826487247886227921 1451006869865435914670941)
                  ·
                    refine ⟨544127576199538468001603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1451006869865435914670941 544127576199538468001603)
                    ·
                      rfl

theorem cell22_1589527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 3, 2, 3].length) (baseStart_1589527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1589527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1589527 prefixEnd_1589527 := by exact prefixLift 1589527
  have htrace : WordTrace (prefixWord ++ tailWord_1589527) baseStart_1589527 baseEnd_1589527 := by
    simpa [prefixWord, tailWord_1589527, baseEnd_1589527] using wordTrace_append hprefix tailTrace_1589527
  have hstable : (prefixWord ++ tailWord_1589527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589527).length < 2 ^ (prefixWord ++ tailWord_1589527).sum := by decide
  have hdescent : baseEnd_1589527 < baseStart_1589527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589585 : List Nat := [1, 2, 2, 1, 4, 2, 2, 3, 5]
def baseStart_1589585 : Nat := 118140960795 + 1589585 * 2 ^ 59
def prefixEnd_1589585 : Nat := 4983230072969 + 3 ^ 40 * 1589585 * 2
def baseEnd_1589585 : Nat := 181382476928281883350475

theorem tailTrace_1589585 : CollatzResearch.WordTrace tailWord_1589585 prefixEnd_1589585 181382476928281883350475 := by
  unfold tailWord_1589585
  simp only [CollatzResearch.WordTrace]
  refine ⟨57976927946212499349522209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38651285297474999566348139 57976927946212499349522209)
  ·
    refine ⟨43482695959659374512141657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57976927946212499349522209 43482695959659374512141657)
    ·
      refine ⟨32612021969744530884106243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43482695959659374512141657 32612021969744530884106243)
      ·
        refine ⟨48918032954616796326159365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32612021969744530884106243 48918032954616796326159365)
        ·
          refine ⟨9172131178990649311154881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48918032954616796326159365 9172131178990649311154881)
          ·
            refine ⟨6879098384242986983366161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9172131178990649311154881 6879098384242986983366161)
            ·
              refine ⟨5159323788182240237524621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6879098384242986983366161 5159323788182240237524621)
              ·
                refine ⟨1934746420568340089071733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5159323788182240237524621 1934746420568340089071733)
                ·
                  refine ⟨181382476928281883350475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1934746420568340089071733 181382476928281883350475)
                  ·
                    rfl

theorem cell22_1589585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 3, 5].length) (baseStart_1589585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1589585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1589585 prefixEnd_1589585 := by exact prefixLift 1589585
  have htrace : WordTrace (prefixWord ++ tailWord_1589585) baseStart_1589585 baseEnd_1589585 := by
    simpa [prefixWord, tailWord_1589585, baseEnd_1589585] using wordTrace_append hprefix tailTrace_1589585
  have hstable : (prefixWord ++ tailWord_1589585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589585).length < 2 ^ (prefixWord ++ tailWord_1589585).sum := by decide
  have hdescent : baseEnd_1589585 < baseStart_1589585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589664 : List Nat := [2, 1, 1, 4, 1, 5, 1, 3, 4]
def baseStart_1589664 : Nat := 118140960795 + 1589664 * 2 ^ 59
def prefixEnd_1589664 : Nat := 4983230072969 + 3 ^ 40 * 1589664 * 2
def baseEnd_1589664 : Nat := 181391491366438592442061

theorem tailTrace_1589664 : CollatzResearch.WordTrace tailWord_1589664 prefixEnd_1589664 181391491366438592442061 := by
  unfold tailWord_1589664
  simp only [CollatzResearch.WordTrace]
  refine ⟨28989904656463147920824023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38653206208617530561098697 28989904656463147920824023)
  ·
    refine ⟨43484856984694721881236035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28989904656463147920824023 43484856984694721881236035)
    ·
      refine ⟨65227285477042082821854053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43484856984694721881236035 65227285477042082821854053)
      ·
        refine ⟨12230116026945390529097635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65227285477042082821854053 12230116026945390529097635)
        ·
          refine ⟨18345174040418085793646453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12230116026945390529097635 18345174040418085793646453)
          ·
            refine ⟨1719860066289195543154355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18345174040418085793646453 1719860066289195543154355)
            ·
              refine ⟨2579790099433793314731533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1719860066289195543154355 2579790099433793314731533)
              ·
                refine ⟨967421287287672493024325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2579790099433793314731533 967421287287672493024325)
                ·
                  refine ⟨181391491366438592442061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 967421287287672493024325 181391491366438592442061)
                  ·
                    rfl

theorem cell22_1589664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 3, 4].length) (baseStart_1589664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1589664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1589664 prefixEnd_1589664 := by exact prefixLift 1589664
  have htrace : WordTrace (prefixWord ++ tailWord_1589664) baseStart_1589664 baseEnd_1589664 := by
    simpa [prefixWord, tailWord_1589664, baseEnd_1589664] using wordTrace_append hprefix tailTrace_1589664
  have hstable : (prefixWord ++ tailWord_1589664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589664).length < 2 ^ (prefixWord ++ tailWord_1589664).sum := by decide
  have hdescent : baseEnd_1589664 < baseStart_1589664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589692 : List Nat := [2, 2, 2, 4, 1, 2, 2, 7]
def baseStart_1589692 : Nat := 118140960795 + 1589692 * 2 ^ 59
def prefixEnd_1589692 : Nat := 4983230072969 + 3 ^ 40 * 1589692 * 2
def baseEnd_1589692 : Nat := 60464895452392559736233

theorem tailTrace_1589692 : CollatzResearch.WordTrace tailWord_1589692 prefixEnd_1589692 60464895452392559736233 := by
  unfold tailWord_1589692
  simp only [CollatzResearch.WordTrace]
  refine ⟨28990415278412428311833665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38653887037883237749111553 28990415278412428311833665)
  ·
    refine ⟨21742811458809321233875249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28990415278412428311833665 21742811458809321233875249)
    ·
      refine ⟨16307108594106990925406437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21742811458809321233875249 16307108594106990925406437)
      ·
        refine ⟨3057582861395060798513707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16307108594106990925406437 3057582861395060798513707)
        ·
          refine ⟨4586374292092591197770561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3057582861395060798513707 4586374292092591197770561)
          ·
            refine ⟨3439780719069443398327921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4586374292092591197770561 3439780719069443398327921)
            ·
              refine ⟨2579835539302082548745941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3439780719069443398327921 2579835539302082548745941)
              ·
                refine ⟨60464895452392559736233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2579835539302082548745941 60464895452392559736233)
                ·
                  rfl

theorem cell22_1589692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 7].length) (baseStart_1589692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1589692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1589692 prefixEnd_1589692 := by exact prefixLift 1589692
  have htrace : WordTrace (prefixWord ++ tailWord_1589692) baseStart_1589692 baseEnd_1589692 := by
    simpa [prefixWord, tailWord_1589692, baseEnd_1589692] using wordTrace_append hprefix tailTrace_1589692
  have hstable : (prefixWord ++ tailWord_1589692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589692).length < 2 ^ (prefixWord ++ tailWord_1589692).sum := by decide
  have hdescent : baseEnd_1589692 < baseStart_1589692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589765 : List Nat := [1, 3, 1, 1, 2, 2, 3, 1, 8]
def baseStart_1589765 : Nat := 118140960795 + 1589765 * 2 ^ 59
def prefixEnd_1589765 : Nat := 4983230072969 + 3 ^ 40 * 1589765 * 2
def baseEnd_1589765 : Nat := 181403016154461726850291

theorem tailTrace_1589765 : CollatzResearch.WordTrace tailWord_1589765 prefixEnd_1589765 181403016154461726850291 := by
  unfold tailWord_1589765
  simp only [CollatzResearch.WordTrace]
  refine ⟨57983493085560390091074749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38655662057040260060716499 57983493085560390091074749)
  ·
    refine ⟨21743809907085146284153031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57983493085560390091074749 21743809907085146284153031)
    ·
      refine ⟨32615714860627719426229547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21743809907085146284153031 32615714860627719426229547)
      ·
        refine ⟨48923572290941579139344321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32615714860627719426229547 48923572290941579139344321)
        ·
          refine ⟨36692679218206184354508241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48923572290941579139344321 36692679218206184354508241)
          ·
            refine ⟨27519509413654638265881181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36692679218206184354508241 27519509413654638265881181)
            ·
              refine ⟨10319816030120489349705443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27519509413654638265881181 10319816030120489349705443)
              ·
                refine ⟨15479724045180734024558165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10319816030120489349705443 15479724045180734024558165)
                ·
                  refine ⟨181403016154461726850291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15479724045180734024558165 181403016154461726850291)
                  ·
                    rfl

theorem cell22_1589765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 8].length) (baseStart_1589765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1589765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1589765 prefixEnd_1589765 := by exact prefixLift 1589765
  have htrace : WordTrace (prefixWord ++ tailWord_1589765) baseStart_1589765 baseEnd_1589765 := by
    simpa [prefixWord, tailWord_1589765, baseEnd_1589765] using wordTrace_append hprefix tailTrace_1589765
  have hstable : (prefixWord ++ tailWord_1589765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589765).length < 2 ^ (prefixWord ++ tailWord_1589765).sum := by decide
  have hdescent : baseEnd_1589765 < baseStart_1589765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589784 : List Nat := [2, 1, 2, 3, 3, 2, 1, 3, 1, 4]
def baseStart_1589784 : Nat := 118140960795 + 1589784 * 2 ^ 59
def prefixEnd_1589784 : Nat := 4983230072969 + 3 ^ 40 * 1589784 * 2
def baseEnd_1589784 : Nat := 544215552551675464325815

theorem tailTrace_1589784 : CollatzResearch.WordTrace tailWord_1589784 prefixEnd_1589784 544215552551675464325815 := by
  unfold tailWord_1589784
  simp only [CollatzResearch.WordTrace]
  refine ⟨28992093036245778168008203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38656124048327704224010937 28992093036245778168008203)
  ·
    refine ⟨43488139554368667252012305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28992093036245778168008203 43488139554368667252012305)
    ·
      refine ⟨32616104665776500439009229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43488139554368667252012305 32616104665776500439009229)
      ·
        refine ⟨12231039249666187664628461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32616104665776500439009229 12231039249666187664628461)
        ·
          refine ⟨4586639718624820374235673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12231039249666187664628461 4586639718624820374235673)
          ·
            refine ⟨3439979788968615280676755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4586639718624820374235673 3439979788968615280676755)
            ·
              refine ⟨5159969683452922921015133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3439979788968615280676755 5159969683452922921015133)
              ·
                refine ⟨1934988631294846095380675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5159969683452922921015133 1934988631294846095380675)
                ·
                  refine ⟨2902482946942269143071013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1934988631294846095380675 2902482946942269143071013)
                  ·
                    refine ⟨544215552551675464325815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2902482946942269143071013 544215552551675464325815)
                    ·
                      rfl

theorem cell22_1589784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 3, 1, 4].length) (baseStart_1589784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1589784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1589784 prefixEnd_1589784 := by exact prefixLift 1589784
  have htrace : WordTrace (prefixWord ++ tailWord_1589784) baseStart_1589784 baseEnd_1589784 := by
    simpa [prefixWord, tailWord_1589784, baseEnd_1589784] using wordTrace_append hprefix tailTrace_1589784
  have hstable : (prefixWord ++ tailWord_1589784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589784).length < 2 ^ (prefixWord ++ tailWord_1589784).sum := by decide
  have hdescent : baseEnd_1589784 < baseStart_1589784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589805 : List Nat := [1, 5, 4, 1, 1, 1, 3, 1, 5]
def baseStart_1589805 : Nat := 118140960795 + 1589805 * 2 ^ 59
def prefixEnd_1589805 : Nat := 4983230072969 + 3 ^ 40 * 1589805 * 2
def baseEnd_1589805 : Nat := 181407580426946136516917

theorem tailTrace_1589805 : CollatzResearch.WordTrace tailWord_1589805 prefixEnd_1589805 181407580426946136516917 := by
  unfold tailWord_1589805
  simp only [CollatzResearch.WordTrace]
  refine ⟨57984952005415476922530869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38656634670276984615020579 57984952005415476922530869)
  ·
    refine ⟨5436089250507700961487269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57984952005415476922530869 5436089250507700961487269)
    ·
      refine ⟨1019266734470193930278863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5436089250507700961487269 1019266734470193930278863)
      ·
        refine ⟨1528900101705290895418295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1019266734470193930278863 1528900101705290895418295)
        ·
          refine ⟨2293350152557936343127443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1528900101705290895418295 2293350152557936343127443)
          ·
            refine ⟨3440025228836904514691165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2293350152557936343127443 3440025228836904514691165)
            ·
              refine ⟨1290009460813839193009187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3440025228836904514691165 1290009460813839193009187)
              ·
                refine ⟨1935014191220758789513781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1290009460813839193009187 1935014191220758789513781)
                ·
                  refine ⟨181407580426946136516917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1935014191220758789513781 181407580426946136516917)
                  ·
                    rfl

theorem cell22_1589805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_1589805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1589805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1589805 prefixEnd_1589805 := by exact prefixLift 1589805
  have htrace : WordTrace (prefixWord ++ tailWord_1589805) baseStart_1589805 baseEnd_1589805 := by
    simpa [prefixWord, tailWord_1589805, baseEnd_1589805] using wordTrace_append hprefix tailTrace_1589805
  have hstable : (prefixWord ++ tailWord_1589805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589805).length < 2 ^ (prefixWord ++ tailWord_1589805).sum := by decide
  have hdescent : baseEnd_1589805 < baseStart_1589805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589906 : List Nat := [3, 2, 3, 1, 2, 2, 2, 2, 5]
def baseStart_1589906 : Nat := 118140960795 + 1589906 * 2 ^ 59
def prefixEnd_1589906 : Nat := 4983230072969 + 3 ^ 40 * 1589906 * 2
def baseEnd_1589906 : Nat := 181419105214969270925147

theorem tailTrace_1589906 : CollatzResearch.WordTrace tailWord_1589906 prefixEnd_1589906 181419105214969270925147 := by
  unfold tailWord_1589906
  simp only [CollatzResearch.WordTrace]
  refine ⟨14497158944512392792989393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38659090518699714114638381 14497158944512392792989393)
  ·
    refine ⟨10872869208384294594742045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14497158944512392792989393 10872869208384294594742045)
    ·
      refine ⟨4077325953144110473028267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10872869208384294594742045 4077325953144110473028267)
      ·
        refine ⟨6115988929716165709542401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4077325953144110473028267 6115988929716165709542401)
        ·
          refine ⟨4586991697287124282156801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6115988929716165709542401 4586991697287124282156801)
          ·
            refine ⟨3440243772965343211617601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4586991697287124282156801 3440243772965343211617601)
            ·
              refine ⟨2580182829724007408713201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3440243772965343211617601 2580182829724007408713201)
              ·
                refine ⟨1935137122293005556534901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2580182829724007408713201 1935137122293005556534901)
                ·
                  refine ⟨181419105214969270925147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1935137122293005556534901 181419105214969270925147)
                  ·
                    rfl

theorem cell22_1589906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 2, 5].length) (baseStart_1589906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1589906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1589906 prefixEnd_1589906 := by exact prefixLift 1589906
  have htrace : WordTrace (prefixWord ++ tailWord_1589906) baseStart_1589906 baseEnd_1589906 := by
    simpa [prefixWord, tailWord_1589906, baseEnd_1589906] using wordTrace_append hprefix tailTrace_1589906
  have hstable : (prefixWord ++ tailWord_1589906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589906).length < 2 ^ (prefixWord ++ tailWord_1589906).sum := by decide
  have hdescent : baseEnd_1589906 < baseStart_1589906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589949 : List Nat := [1, 4, 1, 2, 1, 3, 2, 2, 1, 5]
def baseStart_1589949 : Nat := 118140960795 + 1589949 * 2 ^ 59
def prefixEnd_1589949 : Nat := 4983230072969 + 3 ^ 40 * 1589949 * 2
def baseEnd_1589949 : Nat := 544272035423670033950309

theorem tailTrace_1589949 : CollatzResearch.WordTrace tailWord_1589949 prefixEnd_1589949 544272035423670033950309 := by
  unfold tailWord_1589949
  simp only [CollatzResearch.WordTrace]
  refine ⟨57990204116893789515772901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38660136077929193010515267 57990204116893789515772901)
  ·
    refine ⟨10873163271917585534207419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57990204116893789515772901 10873163271917585534207419)
    ·
      refine ⟨16309744907876378301311129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10873163271917585534207419 16309744907876378301311129)
      ·
        refine ⟨12232308680907283725983347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16309744907876378301311129 12232308680907283725983347)
        ·
          refine ⟨18348463021360925588975021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12232308680907283725983347 18348463021360925588975021)
          ·
            refine ⟨6880673633010347095865633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18348463021360925588975021 6880673633010347095865633)
            ·
              refine ⟨5160505224757760321899225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6880673633010347095865633 5160505224757760321899225)
              ·
                refine ⟨3870378918568320241424419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5160505224757760321899225 3870378918568320241424419)
                ·
                  refine ⟨5805568377852480362136629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3870378918568320241424419 5805568377852480362136629)
                  ·
                    refine ⟨544272035423670033950309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5805568377852480362136629 544272035423670033950309)
                    ·
                      rfl

theorem cell22_1589949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_1589949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1589949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1589949 prefixEnd_1589949 := by exact prefixLift 1589949
  have htrace : WordTrace (prefixWord ++ tailWord_1589949) baseStart_1589949 baseEnd_1589949 := by
    simpa [prefixWord, tailWord_1589949, baseEnd_1589949] using wordTrace_append hprefix tailTrace_1589949
  have hstable : (prefixWord ++ tailWord_1589949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589949).length < 2 ^ (prefixWord ++ tailWord_1589949).sum := by decide
  have hdescent : baseEnd_1589949 < baseStart_1589949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589951 : List Nat := [1, 1, 2, 2, 2, 5, 2, 3, 4]
def baseStart_1589951 : Nat := 118140960795 + 1589951 * 2 ^ 59
def prefixEnd_1589951 : Nat := 4983230072969 + 3 ^ 40 * 1589951 * 2
def baseEnd_1589951 : Nat := 181424240021514231800101

theorem tailTrace_1589951 : CollatzResearch.WordTrace tailWord_1589951 prefixEnd_1589951 181424240021514231800101 := by
  unfold tailWord_1589951
  simp only [CollatzResearch.WordTrace]
  refine ⟨57990277062886543857345707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38660184708591029238230471 57990277062886543857345707)
  ·
    refine ⟨86985415594329815786018561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57990277062886543857345707 86985415594329815786018561)
    ·
      refine ⟨65239061695747361839513921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86985415594329815786018561 65239061695747361839513921)
      ·
        refine ⟨48929296271810521379635441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65239061695747361839513921 48929296271810521379635441)
        ·
          refine ⟨36696972203857891034726581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48929296271810521379635441 36696972203857891034726581)
          ·
            refine ⟨3440341144111677284505617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36696972203857891034726581 3440341144111677284505617)
            ·
              refine ⟨2580255858083757963379213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3440341144111677284505617 2580255858083757963379213)
              ·
                refine ⟨967595946781409236267205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2580255858083757963379213 967595946781409236267205)
                ·
                  refine ⟨181424240021514231800101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 967595946781409236267205 181424240021514231800101)
                  ·
                    rfl

theorem cell22_1589951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 3, 4].length) (baseStart_1589951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1589951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1589951 prefixEnd_1589951 := by exact prefixLift 1589951
  have htrace : WordTrace (prefixWord ++ tailWord_1589951) baseStart_1589951 baseEnd_1589951 := by
    simpa [prefixWord, tailWord_1589951, baseEnd_1589951] using wordTrace_append hprefix tailTrace_1589951
  have hstable : (prefixWord ++ tailWord_1589951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589951).length < 2 ^ (prefixWord ++ tailWord_1589951).sum := by decide
  have hdescent : baseEnd_1589951 < baseStart_1589951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589966 : List Nat := [4, 1, 1, 1, 3, 3, 1, 1, 4, 3]
def baseStart_1589966 : Nat := 118140960795 + 1589966 * 2 ^ 59
def prefixEnd_1589966 : Nat := 4983230072969 + 3 ^ 40 * 1589966 * 2
def baseEnd_1589966 : Nat := 544277854871087656275257

theorem tailTrace_1589966 : CollatzResearch.WordTrace tailWord_1589966 prefixEnd_1589966 544277854871087656275257 := by
  unfold tailWord_1589966
  simp only [CollatzResearch.WordTrace]
  refine ⟨7248853019729025177392719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38660549438554800946094501 7248853019729025177392719)
  ·
    refine ⟨10873279529593537766089079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7248853019729025177392719 10873279529593537766089079)
    ·
      refine ⟨16309919294390306649133619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10873279529593537766089079 16309919294390306649133619)
      ·
        refine ⟨24464878941585459973700429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16309919294390306649133619 24464878941585459973700429)
        ·
          refine ⟨9174329603094547490137661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24464878941585459973700429 9174329603094547490137661)
          ·
            refine ⟨3440373601160455308801623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9174329603094547490137661 3440373601160455308801623)
            ·
              refine ⟨5160560401740682963202435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3440373601160455308801623 5160560401740682963202435)
              ·
                refine ⟨7740840602611024444803653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5160560401740682963202435 7740840602611024444803653)
                ·
                  refine ⟨1451407612989567083400685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7740840602611024444803653 1451407612989567083400685)
                  ·
                    refine ⟨544277854871087656275257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1451407612989567083400685 544277854871087656275257)
                    ·
                      rfl

theorem cell22_1589966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 4, 3].length) (baseStart_1589966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1589966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1589966 prefixEnd_1589966 := by exact prefixLift 1589966
  have htrace : WordTrace (prefixWord ++ tailWord_1589966) baseStart_1589966 baseEnd_1589966 := by
    simpa [prefixWord, tailWord_1589966, baseEnd_1589966] using wordTrace_append hprefix tailTrace_1589966
  have hstable : (prefixWord ++ tailWord_1589966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589966).length < 2 ^ (prefixWord ++ tailWord_1589966).sum := by decide
  have hdescent : baseEnd_1589966 < baseStart_1589966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589983 : List Nat := [1, 1, 2, 3, 2, 4, 3, 1, 2, 3]
def baseStart_1589983 : Nat := 118140960795 + 1589983 * 2 ^ 59
def prefixEnd_1589983 : Nat := 4983230072969 + 3 ^ 40 * 1589983 * 2
def baseEnd_1589983 : Nat := 544283674318505278600205

theorem tailTrace_1589983 : CollatzResearch.WordTrace tailWord_1589983 prefixEnd_1589983 544283674318505278600205 := by
  unfold tailWord_1589983
  simp only [CollatzResearch.WordTrace]
  refine ⟨57991444198770613322510603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38660962799180408881673735 57991444198770613322510603)
  ·
    refine ⟨86987166298155919983765905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57991444198770613322510603 86987166298155919983765905)
    ·
      refine ⟨65240374723616939987824429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86987166298155919983765905 65240374723616939987824429)
      ·
        refine ⟨24465140521356352495434161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65240374723616939987824429 24465140521356352495434161)
        ·
          refine ⟨18348855391017264371575621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24465140521356352495434161 18348855391017264371575621)
          ·
            refine ⟨3440410385815737069670429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18348855391017264371575621 3440410385815737069670429)
            ·
              refine ⟨1290153894680901401126411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3440410385815737069670429 1290153894680901401126411)
              ·
                refine ⟨1935230842021352101689617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1290153894680901401126411 1935230842021352101689617)
                ·
                  refine ⟨1451423131516014076267213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1935230842021352101689617 1451423131516014076267213)
                  ·
                    refine ⟨544283674318505278600205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1451423131516014076267213 544283674318505278600205)
                    ·
                      rfl

theorem cell22_1589983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 1, 2, 3].length) (baseStart_1589983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1589983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1589983 prefixEnd_1589983 := by exact prefixLift 1589983
  have htrace : WordTrace (prefixWord ++ tailWord_1589983) baseStart_1589983 baseEnd_1589983 := by
    simpa [prefixWord, tailWord_1589983, baseEnd_1589983] using wordTrace_append hprefix tailTrace_1589983
  have hstable : (prefixWord ++ tailWord_1589983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589983).length < 2 ^ (prefixWord ++ tailWord_1589983).sum := by decide
  have hdescent : baseEnd_1589983 < baseStart_1589983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590024 : List Nat := [2, 1, 3, 2, 2, 2, 2, 1, 7]
def baseStart_1590024 : Nat := 118140960795 + 1590024 * 2 ^ 59
def prefixEnd_1590024 : Nat := 4983230072969 + 3 ^ 40 * 1590024 * 2
def baseEnd_1590024 : Nat := 181432569818798279441693

theorem tailTrace_1590024 : CollatzResearch.WordTrace tailWord_1590024 prefixEnd_1590024 181432569818798279441693 := by
  unfold tailWord_1590024
  simp only [CollatzResearch.WordTrace]
  refine ⟨28996469795811038662376563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38661959727748051549835417 28996469795811038662376563)
  ·
    refine ⟨43494704693716557993564845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28996469795811038662376563 43494704693716557993564845)
    ·
      refine ⟨16310514260143709247586817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43494704693716557993564845 16310514260143709247586817)
      ·
        refine ⟨12232885695107781935690113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16310514260143709247586817 12232885695107781935690113)
        ·
          refine ⟨9174664271330836451767585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12232885695107781935690113 9174664271330836451767585)
          ·
            refine ⟨6880998203498127338825689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9174664271330836451767585 6880998203498127338825689)
            ·
              refine ⟨5160748652623595504119267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6880998203498127338825689 5160748652623595504119267)
              ·
                refine ⟨7741122978935393256178901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5160748652623595504119267 7741122978935393256178901)
                ·
                  refine ⟨181432569818798279441693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7741122978935393256178901 181432569818798279441693)
                  ·
                    rfl

theorem cell22_1590024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 7].length) (baseStart_1590024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1590024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1590024 prefixEnd_1590024 := by exact prefixLift 1590024
  have htrace : WordTrace (prefixWord ++ tailWord_1590024) baseStart_1590024 baseEnd_1590024 := by
    simpa [prefixWord, tailWord_1590024, baseEnd_1590024] using wordTrace_append hprefix tailTrace_1590024
  have hstable : (prefixWord ++ tailWord_1590024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590024).length < 2 ^ (prefixWord ++ tailWord_1590024).sum := by decide
  have hdescent : baseEnd_1590024 < baseStart_1590024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590034 : List Nat := [3, 2, 4, 1, 3, 1, 2, 1, 2, 3]
def baseStart_1590034 : Nat := 118140960795 + 1590034 * 2 ^ 59
def prefixEnd_1590034 : Nat := 4983230072969 + 3 ^ 40 * 1590034 * 2
def baseEnd_1590034 : Nat := 544301132660758145575049

theorem tailTrace_1590034 : CollatzResearch.WordTrace tailWord_1590034 prefixEnd_1590034 544301132660758145575049 := by
  unfold tailWord_1590034
  simp only [CollatzResearch.WordTrace]
  refine ⟨14498326080396462258154289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38662202881057232688411437 14498326080396462258154289)
  ·
    refine ⟨10873744560297346693615717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14498326080396462258154289 10873744560297346693615717)
    ·
      refine ⟨2038827105055752505052947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10873744560297346693615717 2038827105055752505052947)
      ·
        refine ⟨3058240657583628757579421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2038827105055752505052947 3058240657583628757579421)
        ·
          refine ⟨1146840246593860784092283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3058240657583628757579421 1146840246593860784092283)
          ·
            refine ⟨1720260369890791176138425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1146840246593860784092283 1720260369890791176138425)
            ·
              refine ⟨1290195277418093382103819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1720260369890791176138425 1290195277418093382103819)
              ·
                refine ⟨1935292916127140073155729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1290195277418093382103819 1935292916127140073155729)
                ·
                  refine ⟨1451469687095355054866797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1935292916127140073155729 1451469687095355054866797)
                  ·
                    refine ⟨544301132660758145575049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1451469687095355054866797 544301132660758145575049)
                    ·
                      rfl

theorem cell22_1590034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_1590034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1590034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1590034 prefixEnd_1590034 := by exact prefixLift 1590034
  have htrace : WordTrace (prefixWord ++ tailWord_1590034) baseStart_1590034 baseEnd_1590034 := by
    simpa [prefixWord, tailWord_1590034, baseEnd_1590034] using wordTrace_append hprefix tailTrace_1590034
  have hstable : (prefixWord ++ tailWord_1590034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590034).length < 2 ^ (prefixWord ++ tailWord_1590034).sum := by decide
  have hdescent : baseEnd_1590034 < baseStart_1590034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590099 : List Nat := [1, 1, 1, 2, 1, 1, 3, 4, 4, 4]
def baseStart_1590099 : Nat := 118140960795 + 1590099 * 2 ^ 59
def prefixEnd_1590099 : Nat := 4983230072969 + 3 ^ 40 * 1590099 * 2
def baseEnd_1590099 : Nat := 544323383489119642699849

theorem tailTrace_1590099 : CollatzResearch.WordTrace tailWord_1590099 prefixEnd_1590099 544323383489119642699849 := by
  unfold tailWord_1590099
  simp only [CollatzResearch.WordTrace]
  refine ⟨57995675066350365133733351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38663783377566910089155567 57995675066350365133733351)
  ·
    refine ⟨86993512599525547700600027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57995675066350365133733351 86993512599525547700600027)
    ·
      refine ⟨130490268899288321550900041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86993512599525547700600027 130490268899288321550900041)
      ·
        refine ⟨97867701674466241163175031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130490268899288321550900041 97867701674466241163175031)
        ·
          refine ⟨146801552511699361744762547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97867701674466241163175031 146801552511699361744762547)
          ·
            refine ⟨220202328767549042617143821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146801552511699361744762547 220202328767549042617143821)
            ·
              refine ⟨82575873287830890981428933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 220202328767549042617143821 82575873287830890981428933)
              ·
                refine ⟨15482976241468292059017925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82575873287830890981428933 15482976241468292059017925)
                ·
                  refine ⟨2903058045275304761065861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15482976241468292059017925 2903058045275304761065861)
                  ·
                    refine ⟨544323383489119642699849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2903058045275304761065861 544323383489119642699849)
                    ·
                      rfl

theorem cell22_1590099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 4, 4].length) (baseStart_1590099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1590099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1590099 prefixEnd_1590099 := by exact prefixLift 1590099
  have htrace : WordTrace (prefixWord ++ tailWord_1590099) baseStart_1590099 baseEnd_1590099 := by
    simpa [prefixWord, tailWord_1590099, baseEnd_1590099] using wordTrace_append hprefix tailTrace_1590099
  have hstable : (prefixWord ++ tailWord_1590099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590099).length < 2 ^ (prefixWord ++ tailWord_1590099).sum := by decide
  have hdescent : baseEnd_1590099 < baseStart_1590099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590101 : List Nat := [1, 3, 2, 2, 2, 1, 4, 1, 1, 5]
def baseStart_1590101 : Nat := 118140960795 + 1590101 * 2 ^ 59
def prefixEnd_1590101 : Nat := 4983230072969 + 3 ^ 40 * 1590101 * 2
def baseEnd_1590101 : Nat := 544324068129992304149843

theorem tailTrace_1590101 : CollatzResearch.WordTrace tailWord_1590101 prefixEnd_1590101 544324068129992304149843 := by
  unfold tailWord_1590101
  simp only [CollatzResearch.WordTrace]
  refine ⟨57995748012343119475306157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38663832008228746316870771 57995748012343119475306157)
  ·
    refine ⟨21748405504628669803239809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57995748012343119475306157 21748405504628669803239809)
    ·
      refine ⟨16311304128471502352429857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21748405504628669803239809 16311304128471502352429857)
      ·
        refine ⟨12233478096353626764322393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16311304128471502352429857 12233478096353626764322393)
        ·
          refine ⟨9175108572265220073241795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12233478096353626764322393 9175108572265220073241795)
          ·
            refine ⟨13762662858397830109862693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9175108572265220073241795 13762662858397830109862693)
            ·
              refine ⟨2580499285949593145599255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13762662858397830109862693 2580499285949593145599255)
              ·
                refine ⟨3870748928924389718398883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2580499285949593145599255 3870748928924389718398883)
                ·
                  refine ⟨5806123393386584577598325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3870748928924389718398883 5806123393386584577598325)
                  ·
                    refine ⟨544324068129992304149843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5806123393386584577598325 544324068129992304149843)
                    ·
                      rfl

theorem cell22_1590101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_1590101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1590101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1590101 prefixEnd_1590101 := by exact prefixLift 1590101
  have htrace : WordTrace (prefixWord ++ tailWord_1590101) baseStart_1590101 baseEnd_1590101 := by
    simpa [prefixWord, tailWord_1590101, baseEnd_1590101] using wordTrace_append hprefix tailTrace_1590101
  have hstable : (prefixWord ++ tailWord_1590101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590101).length < 2 ^ (prefixWord ++ tailWord_1590101).sum := by decide
  have hdescent : baseEnd_1590101 < baseStart_1590101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590116 : List Nat := [2, 3, 1, 1, 4, 2, 1, 1, 1, 6]
def baseStart_1590116 : Nat := 118140960795 + 1590116 * 2 ^ 59
def prefixEnd_1590116 : Nat := 4983230072969 + 3 ^ 40 * 1590116 * 2
def baseEnd_1590116 : Nat := 544329202936537265024797

theorem tailTrace_1590116 : CollatzResearch.WordTrace tailWord_1590116 prefixEnd_1590116 544329202936537265024797 := by
  unfold tailWord_1590116
  simp only [CollatzResearch.WordTrace]
  refine ⟨28998147553644388518551101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38664196738192518024734801 28998147553644388518551101)
  ·
    refine ⟨10874305332616645694456663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28998147553644388518551101 10874305332616645694456663)
    ·
      refine ⟨16311457998924968541684995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10874305332616645694456663 16311457998924968541684995)
      ·
        refine ⟨24467186998387452812527493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16311457998924968541684995 24467186998387452812527493)
        ·
          refine ⟨4587597562197647402348905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24467186998387452812527493 4587597562197647402348905)
          ·
            refine ⟨3440698171648235551761679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4587597562197647402348905 3440698171648235551761679)
            ·
              refine ⟨5161047257472353327642519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3440698171648235551761679 5161047257472353327642519)
              ·
                refine ⟨7741570886208529991463779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5161047257472353327642519 7741570886208529991463779)
                ·
                  refine ⟨11612356329312794987195669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7741570886208529991463779 11612356329312794987195669)
                  ·
                    refine ⟨544329202936537265024797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11612356329312794987195669 544329202936537265024797)
                    ·
                      rfl

theorem cell22_1590116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_1590116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1590116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1590116 prefixEnd_1590116 := by exact prefixLift 1590116
  have htrace : WordTrace (prefixWord ++ tailWord_1590116) baseStart_1590116 baseEnd_1590116 := by
    simpa [prefixWord, tailWord_1590116, baseEnd_1590116] using wordTrace_append hprefix tailTrace_1590116
  have hstable : (prefixWord ++ tailWord_1590116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590116).length < 2 ^ (prefixWord ++ tailWord_1590116).sum := by decide
  have hdescent : baseEnd_1590116 < baseStart_1590116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590144 : List Nat := [2, 1, 1, 2, 1, 2, 2, 3, 2, 6]
def baseStart_1590144 : Nat := 118140960795 + 1590144 * 2 ^ 59
def prefixEnd_1590144 : Nat := 4983230072969 + 3 ^ 40 * 1590144 * 2
def baseEnd_1590144 : Nat := 544338787908754525324711

theorem tailTrace_1590144 : CollatzResearch.WordTrace tailWord_1590144 prefixEnd_1590144 544338787908754525324711 := by
  unfold tailWord_1590144
  simp only [CollatzResearch.WordTrace]
  refine ⟨28998658175593668909560743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38664877567458225212747657 28998658175593668909560743)
  ·
    refine ⟨43497987263390503364341115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28998658175593668909560743 43497987263390503364341115)
    ·
      refine ⟨65246980895085755046511673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43497987263390503364341115 65246980895085755046511673)
      ·
        refine ⟨48935235671314316284883755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65246980895085755046511673 48935235671314316284883755)
        ·
          refine ⟨73402853506971474427325633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48935235671314316284883755 73402853506971474427325633)
          ·
            refine ⟨55052140130228605820494225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73402853506971474427325633 55052140130228605820494225)
            ·
              refine ⟨41289105097671454365370669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55052140130228605820494225 41289105097671454365370669)
              ·
                refine ⟨15483414411626795387014001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41289105097671454365370669 15483414411626795387014001)
                ·
                  refine ⟨11612560808720096540260501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15483414411626795387014001 11612560808720096540260501)
                  ·
                    refine ⟨544338787908754525324711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11612560808720096540260501 544338787908754525324711)
                    ·
                      rfl

theorem cell22_1590144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 2, 6].length) (baseStart_1590144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1590144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1590144 prefixEnd_1590144 := by exact prefixLift 1590144
  have htrace : WordTrace (prefixWord ++ tailWord_1590144) baseStart_1590144 baseEnd_1590144 := by
    simpa [prefixWord, tailWord_1590144, baseEnd_1590144] using wordTrace_append hprefix tailTrace_1590144
  have hstable : (prefixWord ++ tailWord_1590144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590144).length < 2 ^ (prefixWord ++ tailWord_1590144).sum := by decide
  have hdescent : baseEnd_1590144 < baseStart_1590144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590197 : List Nat := [1, 3, 3, 2, 1, 1, 5, 2, 1, 3]
def baseStart_1590197 : Nat := 118140960795 + 1590197 * 2 ^ 59
def prefixEnd_1590197 : Nat := 4983230072969 + 3 ^ 40 * 1590197 * 2
def baseEnd_1590197 : Nat := 544356930891880053749549

theorem tailTrace_1590197 : CollatzResearch.WordTrace tailWord_1590197 prefixEnd_1590197 544356930891880053749549 := by
  unfold tailWord_1590197
  simp only [CollatzResearch.WordTrace]
  refine ⟨57999249419995327870800845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38666166279996885247200563 57999249419995327870800845)
  ·
    refine ⟨21749718532498247951550317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57999249419995327870800845 21749718532498247951550317)
    ·
      refine ⟨8156144449686842981831369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21749718532498247951550317 8156144449686842981831369)
      ·
        refine ⟨6117108337265132236373527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8156144449686842981831369 6117108337265132236373527)
        ·
          refine ⟨9175662505897698354560291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6117108337265132236373527 9175662505897698354560291)
          ·
            refine ⟨13763493758846547531840437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9175662505897698354560291 13763493758846547531840437)
            ·
              refine ⟨1290327539891863831110041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13763493758846547531840437 1290327539891863831110041)
              ·
                refine ⟨967745654918897873332531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1290327539891863831110041 967745654918897873332531)
                ·
                  refine ⟨1451618482378346809998797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 967745654918897873332531 1451618482378346809998797)
                  ·
                    refine ⟨544356930891880053749549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1451618482378346809998797 544356930891880053749549)
                    ·
                      rfl

theorem cell22_1590197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_1590197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1590197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1590197 prefixEnd_1590197 := by exact prefixLift 1590197
  have htrace : WordTrace (prefixWord ++ tailWord_1590197) baseStart_1590197 baseEnd_1590197 := by
    simpa [prefixWord, tailWord_1590197, baseEnd_1590197] using wordTrace_append hprefix tailTrace_1590197
  have hstable : (prefixWord ++ tailWord_1590197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590197).length < 2 ^ (prefixWord ++ tailWord_1590197).sum := by decide
  have hdescent : baseEnd_1590197 < baseStart_1590197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590223 : List Nat := [1, 1, 2, 1, 1, 6, 3, 2, 1, 4]
def baseStart_1590223 : Nat := 118140960795 + 1590223 * 2 ^ 59
def prefixEnd_1590223 : Nat := 4983230072969 + 3 ^ 40 * 1590223 * 2
def baseEnd_1590223 : Nat := 544365831223224652599469

theorem tailTrace_1590223 : CollatzResearch.WordTrace tailWord_1590223 prefixEnd_1590223 544365831223224652599469 := by
  unfold tailWord_1590223
  simp only [CollatzResearch.WordTrace]
  refine ⟨58000197717901134311247323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38666798478600756207498215 58000197717901134311247323)
  ·
    refine ⟨87000296576851701466870985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58000197717901134311247323 87000296576851701466870985)
    ·
      refine ⟨65250222432638776100153239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87000296576851701466870985 65250222432638776100153239)
      ·
        refine ⟨97875333648958164150229859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65250222432638776100153239 97875333648958164150229859)
        ·
          refine ⟨146813000473437246225344789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97875333648958164150229859 146813000473437246225344789)
          ·
            refine ⟨6881859397192370916813037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 146813000473437246225344789 6881859397192370916813037)
            ·
              refine ⟨2580697273947139093804889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6881859397192370916813037 2580697273947139093804889)
              ·
                refine ⟨1935522955460354320353667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2580697273947139093804889 1935522955460354320353667)
                ·
                  refine ⟨2903284433190531480530501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1935522955460354320353667 2903284433190531480530501)
                  ·
                    refine ⟨544365831223224652599469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2903284433190531480530501 544365831223224652599469)
                    ·
                      rfl

theorem cell22_1590223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 2, 1, 4].length) (baseStart_1590223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1590223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1590223 prefixEnd_1590223 := by exact prefixLift 1590223
  have htrace : WordTrace (prefixWord ++ tailWord_1590223) baseStart_1590223 baseEnd_1590223 := by
    simpa [prefixWord, tailWord_1590223, baseEnd_1590223] using wordTrace_append hprefix tailTrace_1590223
  have hstable : (prefixWord ++ tailWord_1590223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590223).length < 2 ^ (prefixWord ++ tailWord_1590223).sum := by decide
  have hdescent : baseEnd_1590223 < baseStart_1590223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590255 : List Nat := [1, 1, 2, 1, 4, 3, 4, 2, 4]
def baseStart_1590255 : Nat := 118140960795 + 1590255 * 2 ^ 59
def prefixEnd_1590255 : Nat := 4983230072969 + 3 ^ 40 * 1590255 * 2
def baseEnd_1590255 : Nat := 181458928492395745266457

theorem tailTrace_1590255 : CollatzResearch.WordTrace tailWord_1590255 prefixEnd_1590255 181458928492395745266457 := by
  unfold tailWord_1590255
  simp only [CollatzResearch.WordTrace]
  refine ⟨58001364853785203776412219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38667576569190135850941479 58001364853785203776412219)
  ·
    refine ⟨87002047280677805664618329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58001364853785203776412219 87002047280677805664618329)
    ·
      refine ⟨65251535460508354248463747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87002047280677805664618329 65251535460508354248463747)
      ·
        refine ⟨97877303190762531372695621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65251535460508354248463747 97877303190762531372695621)
        ·
          refine ⟨18351994348267974632380429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97877303190762531372695621 18351994348267974632380429)
          ·
            refine ⟨6881997880600490487142661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18351994348267974632380429 6881997880600490487142661)
            ·
              refine ⟨1290374602612591966339249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6881997880600490487142661 1290374602612591966339249)
              ·
                refine ⟨967780951959443974754437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1290374602612591966339249 967780951959443974754437)
                ·
                  refine ⟨181458928492395745266457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 967780951959443974754437 181458928492395745266457)
                  ·
                    rfl

theorem cell22_1590255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 2, 4].length) (baseStart_1590255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1590255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1590255 prefixEnd_1590255 := by exact prefixLift 1590255
  have htrace : WordTrace (prefixWord ++ tailWord_1590255) baseStart_1590255 baseEnd_1590255 := by
    simpa [prefixWord, tailWord_1590255, baseEnd_1590255] using wordTrace_append hprefix tailTrace_1590255
  have hstable : (prefixWord ++ tailWord_1590255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590255).length < 2 ^ (prefixWord ++ tailWord_1590255).sum := by decide
  have hdescent : baseEnd_1590255 < baseStart_1590255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590283 : List Nat := [1, 1, 1, 1, 6, 3, 3, 6]
def baseStart_1590283 : Nat := 118140960795 + 1590283 * 2 ^ 59
def prefixEnd_1590283 : Nat := 4983230072969 + 3 ^ 40 * 1590283 * 2
def baseEnd_1590283 : Nat := 60487374494378277344365

theorem tailTrace_1590283 : CollatzResearch.WordTrace tailWord_1590283 prefixEnd_1590283 60487374494378277344365 := by
  unfold tailWord_1590283
  simp only [CollatzResearch.WordTrace]
  refine ⟨58002386097683764558431503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38668257398455843038954335 58002386097683764558431503)
  ·
    refine ⟨87003579146525646837647255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58002386097683764558431503 87003579146525646837647255)
    ·
      refine ⟨130505368719788470256470883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87003579146525646837647255 130505368719788470256470883)
      ·
        refine ⟨195758053079682705384706325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130505368719788470256470883 195758053079682705384706325)
        ·
          refine ⟨9176158738110126814908109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 195758053079682705384706325 9176158738110126814908109)
          ·
            refine ⟨3441059526791297555590541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9176158738110126814908109 3441059526791297555590541)
            ·
              refine ⟨1290397322546736583346453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3441059526791297555590541 1290397322546736583346453)
              ·
                refine ⟨60487374494378277344365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1290397322546736583346453 60487374494378277344365)
                ·
                  rfl

theorem cell22_1590283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 6].length) (baseStart_1590283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1590283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1590283 prefixEnd_1590283 := by exact prefixLift 1590283
  have htrace : WordTrace (prefixWord ++ tailWord_1590283) baseStart_1590283 baseEnd_1590283 := by
    simpa [prefixWord, tailWord_1590283, baseEnd_1590283] using wordTrace_append hprefix tailTrace_1590283
  have hstable : (prefixWord ++ tailWord_1590283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590283).length < 2 ^ (prefixWord ++ tailWord_1590283).sum := by decide
  have hdescent : baseEnd_1590283 < baseStart_1590283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590298 : List Nat := [3, 1, 1, 3, 1, 2, 1, 2, 5, 3]
def baseStart_1590298 : Nat := 118140960795 + 1590298 * 2 ^ 59
def prefixEnd_1590298 : Nat := 4983230072969 + 3 ^ 40 * 1590298 * 2
def baseEnd_1590298 : Nat := 544391505255949456974239

theorem tailTrace_1590298 : CollatzResearch.WordTrace tailWord_1590298 prefixEnd_1590298 544391505255949456974239 := by
  unfold tailWord_1590298
  simp only [CollatzResearch.WordTrace]
  refine ⟨14500733298157355530056887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38668622128419614746818365 14500733298157355530056887)
  ·
    refine ⟨21751099947236033295085331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14500733298157355530056887 21751099947236033295085331)
    ·
      refine ⟨32626649920854049942627997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21751099947236033295085331 32626649920854049942627997)
      ·
        refine ⟨12234993720320268728485499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32626649920854049942627997 12234993720320268728485499)
        ·
          refine ⟨18352490580480403092728249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12234993720320268728485499 18352490580480403092728249)
          ·
            refine ⟨13764367935360302319546187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18352490580480403092728249 13764367935360302319546187)
            ·
              refine ⟨20646551903040453479319281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13764367935360302319546187 20646551903040453479319281)
              ·
                refine ⟨15484913927280340109489461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20646551903040453479319281 15484913927280340109489461)
                ·
                  refine ⟨1451710680682531885264637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15484913927280340109489461 1451710680682531885264637)
                  ·
                    refine ⟨544391505255949456974239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1451710680682531885264637 544391505255949456974239)
                    ·
                      rfl

theorem cell22_1590298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 5, 3].length) (baseStart_1590298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1590298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1590298 prefixEnd_1590298 := by exact prefixLift 1590298
  have htrace : WordTrace (prefixWord ++ tailWord_1590298) baseStart_1590298 baseEnd_1590298 := by
    simpa [prefixWord, tailWord_1590298, baseEnd_1590298] using wordTrace_append hprefix tailTrace_1590298
  have hstable : (prefixWord ++ tailWord_1590298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590298).length < 2 ^ (prefixWord ++ tailWord_1590298).sum := by decide
  have hdescent : baseEnd_1590298 < baseStart_1590298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590304 : List Nat := [2, 1, 1, 7, 1, 2, 1, 2, 2, 3]
def baseStart_1590304 : Nat := 118140960795 + 1590304 * 2 ^ 59
def prefixEnd_1590304 : Nat := 4983230072969 + 3 ^ 40 * 1590304 * 2
def baseEnd_1590304 : Nat := 544393559178567441324221

theorem tailTrace_1590304 : CollatzResearch.WordTrace tailWord_1590304 prefixEnd_1590304 544393559178567441324221 := by
  unfold tailWord_1590304
  simp only [CollatzResearch.WordTrace]
  refine ⟨29001576015303842572472983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38668768020405123429963977 29001576015303842572472983)
  ·
    refine ⟨43502364022955763858709475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29001576015303842572472983 43502364022955763858709475)
    ·
      refine ⟨65253546034433645788064213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43502364022955763858709475 65253546034433645788064213)
      ·
        refine ⟨1529379985182038573157755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 65253546034433645788064213 1529379985182038573157755)
        ·
          refine ⟨2294069977773057859736633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1529379985182038573157755 2294069977773057859736633)
          ·
            refine ⟨1720552483329793394802475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2294069977773057859736633 1720552483329793394802475)
            ·
              refine ⟨2580828724994690092203713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1720552483329793394802475 2580828724994690092203713)
              ·
                refine ⟨1935621543746017569152785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2580828724994690092203713 1935621543746017569152785)
                ·
                  refine ⟨1451716157809513176864589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1935621543746017569152785 1451716157809513176864589)
                  ·
                    refine ⟨544393559178567441324221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1451716157809513176864589 544393559178567441324221)
                    ·
                      rfl

theorem cell22_1590304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 2, 2, 3].length) (baseStart_1590304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1590304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1590304 prefixEnd_1590304 := by exact prefixLift 1590304
  have htrace : WordTrace (prefixWord ++ tailWord_1590304) baseStart_1590304 baseEnd_1590304 := by
    simpa [prefixWord, tailWord_1590304, baseEnd_1590304] using wordTrace_append hprefix tailTrace_1590304
  have hstable : (prefixWord ++ tailWord_1590304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590304).length < 2 ^ (prefixWord ++ tailWord_1590304).sum := by decide
  have hdescent : baseEnd_1590304 < baseStart_1590304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590315 : List Nat := [1, 1, 1, 1, 2, 1, 5, 6, 1, 3]
def baseStart_1590315 : Nat := 118140960795 + 1590315 * 2 ^ 59
def prefixEnd_1590315 : Nat := 4983230072969 + 3 ^ 40 * 1590315 * 2
def baseEnd_1590315 : Nat := 544397324703367079299187

theorem tailTrace_1590315 : CollatzResearch.WordTrace tailWord_1590315 prefixEnd_1590315 544397324703367079299187 := by
  unfold tailWord_1590315
  simp only [CollatzResearch.WordTrace]
  refine ⟨58003553233567834023596399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38669035489045222682397599 58003553233567834023596399)
  ·
    refine ⟨87005329850351751035394599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58003553233567834023596399 87005329850351751035394599)
    ·
      refine ⟨130507994775527626553091899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87005329850351751035394599 130507994775527626553091899)
      ·
        refine ⟨195761992163291439829637849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130507994775527626553091899 195761992163291439829637849)
        ·
          refine ⟨146821494122468579872228387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195761992163291439829637849 146821494122468579872228387)
          ·
            refine ⟨220232241183702869808342581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146821494122468579872228387 220232241183702869808342581)
            ·
              refine ⟨20646772610972144044532117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 220232241183702869808342581 20646772610972144044532117)
              ·
                refine ⟨967817466139319252087443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20646772610972144044532117 967817466139319252087443)
                ·
                  refine ⟨1451726199208978878131165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 967817466139319252087443 1451726199208978878131165)
                  ·
                    refine ⟨544397324703367079299187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1451726199208978878131165 544397324703367079299187)
                    ·
                      rfl

theorem cell22_1590315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 6, 1, 3].length) (baseStart_1590315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1590315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1590315 prefixEnd_1590315 := by exact prefixLift 1590315
  have htrace : WordTrace (prefixWord ++ tailWord_1590315) baseStart_1590315 baseEnd_1590315 := by
    simpa [prefixWord, tailWord_1590315, baseEnd_1590315] using wordTrace_append hprefix tailTrace_1590315
  have hstable : (prefixWord ++ tailWord_1590315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590315).length < 2 ^ (prefixWord ++ tailWord_1590315).sum := by decide
  have hdescent : baseEnd_1590315 < baseStart_1590315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590349 : List Nat := [1, 6, 1, 1, 1, 2, 3, 3, 1, 3]
def baseStart_1590349 : Nat := 118140960795 + 1590349 * 2 ^ 59
def prefixEnd_1590349 : Nat := 4983230072969 + 3 ^ 40 * 1590349 * 2
def baseEnd_1590349 : Nat := 544408963598202323949083

theorem tailTrace_1590349 : CollatzResearch.WordTrace tailWord_1590349 prefixEnd_1590349 544408963598202323949083 := by
  unfold tailWord_1590349
  simp only [CollatzResearch.WordTrace]
  refine ⟨58004793315444657830334101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38669862210296438553556067 58004793315444657830334101)
  ·
    refine ⟨2718974686661468335796911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 58004793315444657830334101 2718974686661468335796911)
    ·
      refine ⟨4078462029992202503695367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2718974686661468335796911 4078462029992202503695367)
      ·
        refine ⟨6117693044988303755543051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4078462029992202503695367 6117693044988303755543051)
        ·
          refine ⟨9176539567482455633314577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6117693044988303755543051 9176539567482455633314577)
          ·
            refine ⟨6882404675611841724985933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9176539567482455633314577 6882404675611841724985933)
            ·
              refine ⟨2580901753354440646869725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6882404675611841724985933 2580901753354440646869725)
              ·
                refine ⟨967838157507915242576147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2580901753354440646869725 967838157507915242576147)
                ·
                  refine ⟨1451757236261872863864221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 967838157507915242576147 1451757236261872863864221)
                  ·
                    refine ⟨544408963598202323949083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1451757236261872863864221 544408963598202323949083)
                    ·
                      rfl

theorem cell22_1590349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_1590349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1590349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1590349 prefixEnd_1590349 := by exact prefixLift 1590349
  have htrace : WordTrace (prefixWord ++ tailWord_1590349) baseStart_1590349 baseEnd_1590349 := by
    simpa [prefixWord, tailWord_1590349, baseEnd_1590349] using wordTrace_append hprefix tailTrace_1590349
  have hstable : (prefixWord ++ tailWord_1590349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590349).length < 2 ^ (prefixWord ++ tailWord_1590349).sum := by decide
  have hdescent : baseEnd_1590349 < baseStart_1590349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590366 : List Nat := [4, 4, 1, 1, 1, 3, 1, 1, 3, 3]
def baseStart_1590366 : Nat := 118140960795 + 1590366 * 2 ^ 59
def prefixEnd_1590366 : Nat := 4983230072969 + 3 ^ 40 * 1590366 * 2
def baseEnd_1590366 : Nat := 544414783045619946274031

theorem tailTrace_1590366 : CollatzResearch.WordTrace tailWord_1590366 prefixEnd_1590366 544414783045619946274031 := by
  unfold tailWord_1590366
  simp only [CollatzResearch.WordTrace]
  refine ⟨7250676669547883716712869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38670275570922046489135301 7250676669547883716712869)
  ·
    refine ⟨1359501875540228196883663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7250676669547883716712869 1359501875540228196883663)
    ·
      refine ⟨2039252813310342295325495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1359501875540228196883663 2039252813310342295325495)
      ·
        refine ⟨3058879219965513442988243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2039252813310342295325495 3058879219965513442988243)
        ·
          refine ⟨4588318829948270164482365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3058879219965513442988243 4588318829948270164482365)
          ·
            refine ⟨1720619561230601311680887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4588318829948270164482365 1720619561230601311680887)
            ·
              refine ⟨2580929341845901967521331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1720619561230601311680887 2580929341845901967521331)
              ·
                refine ⟨3871394012768852951281997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2580929341845901967521331 3871394012768852951281997)
                ·
                  refine ⟨1451772754788319856730749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3871394012768852951281997 1451772754788319856730749)
                  ·
                    refine ⟨544414783045619946274031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1451772754788319856730749 544414783045619946274031)
                    ·
                      rfl

theorem cell22_1590366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_1590366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1590366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1590366 prefixEnd_1590366 := by exact prefixLift 1590366
  have htrace : WordTrace (prefixWord ++ tailWord_1590366) baseStart_1590366 baseEnd_1590366 := by
    simpa [prefixWord, tailWord_1590366, baseEnd_1590366] using wordTrace_append hprefix tailTrace_1590366
  have hstable : (prefixWord ++ tailWord_1590366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590366).length < 2 ^ (prefixWord ++ tailWord_1590366).sum := by decide
  have hdescent : baseEnd_1590366 < baseStart_1590366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590405 : List Nat := [1, 3, 1, 1, 6, 1, 1, 2, 1, 5]
def baseStart_1590405 : Nat := 118140960795 + 1590405 * 2 ^ 59
def prefixEnd_1590405 : Nat := 4983230072969 + 3 ^ 40 * 1590405 * 2
def baseEnd_1590405 : Nat := 544428133542636844548911

theorem tailTrace_1590405 : CollatzResearch.WordTrace tailWord_1590405 prefixEnd_1590405 544428133542636844548911 := by
  unfold tailWord_1590405
  simp only [CollatzResearch.WordTrace]
  refine ⟨58006835803241779394372669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38671223868827852929581779 58006835803241779394372669)
  ·
    refine ⟨21752563426215667272889751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58006835803241779394372669 21752563426215667272889751)
    ·
      refine ⟨32628845139323500909334627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21752563426215667272889751 32628845139323500909334627)
      ·
        refine ⟨48943267708985251364001941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32628845139323500909334627 48943267708985251364001941)
        ·
          refine ⟨2294215673858683657687591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 48943267708985251364001941 2294215673858683657687591)
          ·
            refine ⟨3441323510788025486531387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2294215673858683657687591 3441323510788025486531387)
            ·
              refine ⟨5161985266182038229797081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3441323510788025486531387 5161985266182038229797081)
              ·
                refine ⟨3871488949636528672347811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5161985266182038229797081 3871488949636528672347811)
                ·
                  refine ⟨5807233424454793008521717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3871488949636528672347811 5807233424454793008521717)
                  ·
                    refine ⟨544428133542636844548911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5807233424454793008521717 544428133542636844548911)
                    ·
                      rfl

theorem cell22_1590405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 5].length) (baseStart_1590405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1590405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1590405 prefixEnd_1590405 := by exact prefixLift 1590405
  have htrace : WordTrace (prefixWord ++ tailWord_1590405) baseStart_1590405 baseEnd_1590405 := by
    simpa [prefixWord, tailWord_1590405, baseEnd_1590405] using wordTrace_append hprefix tailTrace_1590405
  have hstable : (prefixWord ++ tailWord_1590405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590405).length < 2 ^ (prefixWord ++ tailWord_1590405).sum := by decide
  have hdescent : baseEnd_1590405 < baseStart_1590405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590418 : List Nat := [3, 2, 3, 1, 1, 12]
def baseStart_1590418 : Nat := 118140960795 + 1590418 * 2 ^ 59
def prefixEnd_1590418 : Nat := 4983230072969 + 3 ^ 40 * 1590418 * 2
def baseEnd_1590418 : Nat := 6721389922324804246591

theorem tailTrace_1590418 : CollatzResearch.WordTrace tailWord_1590418 prefixEnd_1590418 6721389922324804246591 := by
  unfold tailWord_1590418
  simp only [CollatzResearch.WordTrace]
  refine ⟨14501827488048670653648977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38671539968129788409730605 14501827488048670653648977)
  ·
    refine ⟨10876370616036502990236733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14501827488048670653648977 10876370616036502990236733)
    ·
      refine ⟨4078638981013688621338775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10876370616036502990236733 4078638981013688621338775)
      ·
        refine ⟨6117958471520532932008163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4078638981013688621338775 6117958471520532932008163)
        ·
          refine ⟨9176937707280799398012245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6117958471520532932008163 9176937707280799398012245)
          ·
            refine ⟨6721389922324804246591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 9176937707280799398012245 6721389922324804246591)
            ·
              rfl

theorem cell22_1590418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 12].length) (baseStart_1590418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1590418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1590418 prefixEnd_1590418 := by exact prefixLift 1590418
  have htrace : WordTrace (prefixWord ++ tailWord_1590418) baseStart_1590418 baseEnd_1590418 := by
    simpa [prefixWord, tailWord_1590418, baseEnd_1590418] using wordTrace_append hprefix tailTrace_1590418
  have hstable : (prefixWord ++ tailWord_1590418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590418).length < 2 ^ (prefixWord ++ tailWord_1590418).sum := by decide
  have hdescent : baseEnd_1590418 < baseStart_1590418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590424 : List Nat := [2, 1, 2, 4, 2, 3, 2, 2, 4]
def baseStart_1590424 : Nat := 118140960795 + 1590424 * 2 ^ 59
def prefixEnd_1590424 : Nat := 4983230072969 + 3 ^ 40 * 1590424 * 2
def baseEnd_1590424 : Nat := 181478212543642376107951

theorem tailTrace_1590424 : CollatzResearch.WordTrace tailWord_1590424 prefixEnd_1590424 181478212543642376107951 := by
  unfold tailWord_1590424
  simp only [CollatzResearch.WordTrace]
  refine ⟨29003764395086472819657163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38671685860115297092876217 29003764395086472819657163)
  ·
    refine ⟨43505646592629709229485745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29003764395086472819657163 43505646592629709229485745)
    ·
      refine ⟨32629234944472281922114309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43505646592629709229485745 32629234944472281922114309)
      ·
        refine ⟨6117981552088552860396433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32629234944472281922114309 6117981552088552860396433)
        ·
          refine ⟨4588486164066414645297325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6117981552088552860396433 4588486164066414645297325)
          ·
            refine ⟨1720682311524905491986497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4588486164066414645297325 1720682311524905491986497)
            ·
              refine ⟨1290511733643679118989873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1720682311524905491986497 1290511733643679118989873)
              ·
                refine ⟨967883800232759339242405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1290511733643679118989873 967883800232759339242405)
                ·
                  refine ⟨181478212543642376107951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 967883800232759339242405 181478212543642376107951)
                  ·
                    rfl

theorem cell22_1590424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 2, 4].length) (baseStart_1590424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1590424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1590424 prefixEnd_1590424 := by exact prefixLift 1590424
  have htrace : WordTrace (prefixWord ++ tailWord_1590424) baseStart_1590424 baseEnd_1590424 := by
    simpa [prefixWord, tailWord_1590424, baseEnd_1590424] using wordTrace_append hprefix tailTrace_1590424
  have hstable : (prefixWord ++ tailWord_1590424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590424).length < 2 ^ (prefixWord ++ tailWord_1590424).sum := by decide
  have hdescent : baseEnd_1590424 < baseStart_1590424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590450 : List Nat := [3, 2, 1, 1, 1, 4, 1, 1, 5, 3]
def baseStart_1590450 : Nat := 118140960795 + 1590450 * 2 ^ 59
def prefixEnd_1590450 : Nat := 4983230072969 + 3 ^ 40 * 1590450 * 2
def baseEnd_1590450 : Nat := 544443537962271727173773

theorem tailTrace_1590450 : CollatzResearch.WordTrace tailWord_1590450 prefixEnd_1590450 544443537962271727173773 := by
  unfold tailWord_1590450
  simp only [CollatzResearch.WordTrace]
  refine ⟨14502119272019688019940201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38672318058719168053173869 14502119272019688019940201)
  ·
    refine ⟨10876589454014766014955151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14502119272019688019940201 10876589454014766014955151)
    ·
      refine ⟨16314884181022149022432727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10876589454014766014955151 16314884181022149022432727)
      ·
        refine ⟨24472326271533223533649091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16314884181022149022432727 24472326271533223533649091)
        ·
          refine ⟨36708489407299835300473637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24472326271533223533649091 36708489407299835300473637)
          ·
            refine ⟨6882841763868719118838807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36708489407299835300473637 6882841763868719118838807)
            ·
              refine ⟨10324262645803078678258211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6882841763868719118838807 10324262645803078678258211)
              ·
                refine ⟨15486393968704618017387317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10324262645803078678258211 15486393968704618017387317)
                ·
                  refine ⟨1451849434566057939130061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15486393968704618017387317 1451849434566057939130061)
                  ·
                    refine ⟨544443537962271727173773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1451849434566057939130061 544443537962271727173773)
                    ·
                      rfl

theorem cell22_1590450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 5, 3].length) (baseStart_1590450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1590450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1590450 prefixEnd_1590450 := by exact prefixLift 1590450
  have htrace : WordTrace (prefixWord ++ tailWord_1590450) baseStart_1590450 baseEnd_1590450 := by
    simpa [prefixWord, tailWord_1590450, baseEnd_1590450] using wordTrace_append hprefix tailTrace_1590450
  have hstable : (prefixWord ++ tailWord_1590450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590450).length < 2 ^ (prefixWord ++ tailWord_1590450).sum := by decide
  have hdescent : baseEnd_1590450 < baseStart_1590450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590454 : List Nat := [5, 1, 3, 2, 1, 1, 1, 1, 1, 6]
def baseStart_1590454 : Nat := 118140960795 + 1590454 * 2 ^ 59
def prefixEnd_1590454 : Nat := 4983230072969 + 3 ^ 40 * 1590454 * 2
def baseEnd_1590454 : Nat := 544444907244017050073761

theorem tailTrace_1590454 : CollatzResearch.WordTrace tailWord_1590454 prefixEnd_1590454 544444907244017050073761 := by
  unfold tailWord_1590454
  simp only [CollatzResearch.WordTrace]
  refine ⟨3625538936254016297681651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38672415320042840508604277 3625538936254016297681651)
  ·
    refine ⟨5438308404381024446522477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3625538936254016297681651 5438308404381024446522477)
    ·
      refine ⟨2039365651642884167445929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5438308404381024446522477 2039365651642884167445929)
      ·
        refine ⟨1529524238732163125584447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2039365651642884167445929 1529524238732163125584447)
        ·
          refine ⟨2294286358098244688376671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1529524238732163125584447 2294286358098244688376671)
          ·
            refine ⟨3441429537147367032565007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2294286358098244688376671 3441429537147367032565007)
            ·
              refine ⟨5162144305721050548847511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3441429537147367032565007 5162144305721050548847511)
              ·
                refine ⟨7743216458581575823271267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5162144305721050548847511 7743216458581575823271267)
                ·
                  refine ⟨11614824687872363734906901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7743216458581575823271267 11614824687872363734906901)
                  ·
                    refine ⟨544444907244017050073761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11614824687872363734906901 544444907244017050073761)
                    ·
                      rfl

theorem cell22_1590454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_1590454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1590454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1590454 prefixEnd_1590454 := by exact prefixLift 1590454
  have htrace : WordTrace (prefixWord ++ tailWord_1590454) baseStart_1590454 baseEnd_1590454 := by
    simpa [prefixWord, tailWord_1590454, baseEnd_1590454] using wordTrace_append hprefix tailTrace_1590454
  have hstable : (prefixWord ++ tailWord_1590454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590454).length < 2 ^ (prefixWord ++ tailWord_1590454).sum := by decide
  have hdescent : baseEnd_1590454 < baseStart_1590454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590497 : List Nat := [1, 2, 3, 1, 3, 3, 3, 1, 5]
def baseStart_1590497 : Nat := 118140960795 + 1590497 * 2 ^ 59
def prefixEnd_1590497 : Nat := 4983230072969 + 3 ^ 40 * 1590497 * 2
def baseEnd_1590497 : Nat := 181486542340926423749543

theorem tailTrace_1590497 : CollatzResearch.WordTrace tailWord_1590497 prefixEnd_1590497 181486542340926423749543 := by
  unfold tailWord_1590497
  simp only [CollatzResearch.WordTrace]
  refine ⟨58010191318908479106721745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38673460879272319404481163 58010191318908479106721745)
  ·
    refine ⟨43507643489181359330041309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58010191318908479106721745 43507643489181359330041309)
    ·
      refine ⟨16315366308443009748765491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43507643489181359330041309 16315366308443009748765491)
      ·
        refine ⟨24473049462664514623148237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16315366308443009748765491 24473049462664514623148237)
        ·
          refine ⟨9177393548499192983680589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24473049462664514623148237 9177393548499192983680589)
          ·
            refine ⟨3441522580687197368880221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9177393548499192983680589 3441522580687197368880221)
            ·
              refine ⟨1290570967757699013330083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3441522580687197368880221 1290570967757699013330083)
              ·
                refine ⟨1935856451636548519995125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1290570967757699013330083 1935856451636548519995125)
                ·
                  refine ⟨181486542340926423749543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1935856451636548519995125 181486542340926423749543)
                  ·
                    rfl

theorem cell22_1590497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 1, 5].length) (baseStart_1590497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1590497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1590497 prefixEnd_1590497 := by exact prefixLift 1590497
  have htrace : WordTrace (prefixWord ++ tailWord_1590497) baseStart_1590497 baseEnd_1590497 := by
    simpa [prefixWord, tailWord_1590497, baseEnd_1590497] using wordTrace_append hprefix tailTrace_1590497
  have hstable : (prefixWord ++ tailWord_1590497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590497).length < 2 ^ (prefixWord ++ tailWord_1590497).sum := by decide
  have hdescent : baseEnd_1590497 < baseStart_1590497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590510 : List Nat := [4, 1, 2, 1, 1, 1, 2, 3, 3, 4]
def baseStart_1590510 : Nat := 118140960795 + 1590510 * 2 ^ 59
def prefixEnd_1590510 : Nat := 4983230072969 + 3 ^ 40 * 1590510 * 2
def baseEnd_1590510 : Nat := 544464077188451570673589

theorem tailTrace_1590510 : CollatzResearch.WordTrace tailWord_1590510 prefixEnd_1590510 544464077188451570673589 := by
  unfold tailWord_1590510
  simp only [CollatzResearch.WordTrace]
  refine ⟨7251333183482672790868123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38673776978574254884629989 7251333183482672790868123)
  ·
    refine ⟨10876999775224009186302185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7251333183482672790868123 10876999775224009186302185)
    ·
      refine ⟨8157749831418006889726639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10876999775224009186302185 8157749831418006889726639)
      ·
        refine ⟨12236624747127010334589959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8157749831418006889726639 12236624747127010334589959)
        ·
          refine ⟨18354937120690515501884939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12236624747127010334589959 18354937120690515501884939)
          ·
            refine ⟨27532405681035773252827409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18354937120690515501884939 27532405681035773252827409)
            ·
              refine ⟨20649304260776829939620557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27532405681035773252827409 20649304260776829939620557)
              ·
                refine ⟨7743489097791311227357709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20649304260776829939620557 7743489097791311227357709)
                ·
                  refine ⟨2903808411671741710259141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7743489097791311227357709 2903808411671741710259141)
                  ·
                    refine ⟨544464077188451570673589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2903808411671741710259141 544464077188451570673589)
                    ·
                      rfl

theorem cell22_1590510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_1590510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1590510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1590510 prefixEnd_1590510 := by exact prefixLift 1590510
  have htrace : WordTrace (prefixWord ++ tailWord_1590510) baseStart_1590510 baseEnd_1590510 := by
    simpa [prefixWord, tailWord_1590510, baseEnd_1590510] using wordTrace_append hprefix tailTrace_1590510
  have hstable : (prefixWord ++ tailWord_1590510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590510).length < 2 ^ (prefixWord ++ tailWord_1590510).sum := by decide
  have hdescent : baseEnd_1590510 < baseStart_1590510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590542 : List Nat := [4, 1, 1, 2, 1, 5, 1, 1, 6]
def baseStart_1590542 : Nat := 118140960795 + 1590542 * 2 ^ 59
def prefixEnd_1590542 : Nat := 4983230072969 + 3 ^ 40 * 1590542 * 2
def baseEnd_1590542 : Nat := 181491677147471384624497

theorem tailTrace_1590542 : CollatzResearch.WordTrace tailWord_1590542 prefixEnd_1590542 181491677147471384624497 := by
  unfold tailWord_1590542
  simp only [CollatzResearch.WordTrace]
  refine ⟨7251479075468181474013735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38674555069163634528073253 7251479075468181474013735)
  ·
    refine ⟨10877218613202272211020603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7251479075468181474013735 10877218613202272211020603)
    ·
      refine ⟨16315827919803408316530905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10877218613202272211020603 16315827919803408316530905)
      ·
        refine ⟨12236870939852556237398179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16315827919803408316530905 12236870939852556237398179)
        ·
          refine ⟨18355306409778834356097269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12236870939852556237398179 18355306409778834356097269)
          ·
            refine ⟨1720809975916765720884119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18355306409778834356097269 1720809975916765720884119)
            ·
              refine ⟨2581214963875148581326179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1720809975916765720884119 2581214963875148581326179)
              ·
                refine ⟨3871822445812722871989269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2581214963875148581326179 3871822445812722871989269)
                ·
                  refine ⟨181491677147471384624497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3871822445812722871989269 181491677147471384624497)
                  ·
                    rfl

theorem cell22_1590542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 6].length) (baseStart_1590542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1590542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1590542 prefixEnd_1590542 := by exact prefixLift 1590542
  have htrace : WordTrace (prefixWord ++ tailWord_1590542) baseStart_1590542 baseEnd_1590542 := by
    simpa [prefixWord, tailWord_1590542, baseEnd_1590542] using wordTrace_append hprefix tailTrace_1590542
  have hstable : (prefixWord ++ tailWord_1590542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590542).length < 2 ^ (prefixWord ++ tailWord_1590542).sum := by decide
  have hdescent : baseEnd_1590542 < baseStart_1590542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590636 : List Nat := [2, 2, 1, 1, 5, 2, 2, 3, 1, 3]
def baseStart_1590636 : Nat := 118140960795 + 1590636 * 2 ^ 59
def prefixEnd_1590636 : Nat := 4983230072969 + 3 ^ 40 * 1590636 * 2
def baseEnd_1590636 : Nat := 544507209563429242023203

theorem tailTrace_1590636 : CollatzResearch.WordTrace tailWord_1590636 prefixEnd_1590636 544507209563429242023203 := by
  unfold tailWord_1590636
  simp only [CollatzResearch.WordTrace]
  refine ⟨29007630532702452923015881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38676840710269937230687841 29007630532702452923015881)
  ·
    refine ⟨21755722899526839692261911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29007630532702452923015881 21755722899526839692261911)
    ·
      refine ⟨32633584349290259538392867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21755722899526839692261911 32633584349290259538392867)
      ·
        refine ⟨48950376523935389307589301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32633584349290259538392867 48950376523935389307589301)
        ·
          refine ⟨4589097799118942747586497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48950376523935389307589301 4589097799118942747586497)
          ·
            refine ⟨3441823349339207060689873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4589097799118942747586497 3441823349339207060689873)
            ·
              refine ⟨2581367512004405295517405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3441823349339207060689873 2581367512004405295517405)
              ·
                refine ⟨968012817001651985819027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2581367512004405295517405 968012817001651985819027)
                ·
                  refine ⟨1452019225502477978728541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 968012817001651985819027 1452019225502477978728541)
                  ·
                    refine ⟨544507209563429242023203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1452019225502477978728541 544507209563429242023203)
                    ·
                      rfl

theorem cell22_1590636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 3, 1, 3].length) (baseStart_1590636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1590636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1590636 prefixEnd_1590636 := by exact prefixLift 1590636
  have htrace : WordTrace (prefixWord ++ tailWord_1590636) baseStart_1590636 baseEnd_1590636 := by
    simpa [prefixWord, tailWord_1590636, baseEnd_1590636] using wordTrace_append hprefix tailTrace_1590636
  have hstable : (prefixWord ++ tailWord_1590636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590636).length < 2 ^ (prefixWord ++ tailWord_1590636).sum := by decide
  have hdescent : baseEnd_1590636 < baseStart_1590636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590709 : List Nat := [1, 3, 3, 2, 2, 1, 2, 1, 4, 3]
def baseStart_1590709 : Nat := 118140960795 + 1590709 * 2 ^ 59
def prefixEnd_1590709 : Nat := 4983230072969 + 3 ^ 40 * 1590709 * 2
def baseEnd_1590709 : Nat := 544532198955281384947979

theorem tailTrace_1590709 : CollatzResearch.WordTrace tailWord_1590709 prefixEnd_1590709 544532198955281384947979 := by
  unfold tailWord_1590709
  simp only [CollatzResearch.WordTrace]
  refine ⟨58017923594140439313439181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38678615729426959542292787 58017923594140439313439181)
  ·
    refine ⟨21756721347802664742539693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58017923594140439313439181 21756721347802664742539693)
    ·
      refine ⟨8158770505425999278452385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21756721347802664742539693 8158770505425999278452385)
      ·
        refine ⟨6119077879069499458839289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8158770505425999278452385 6119077879069499458839289)
        ·
          refine ⟨4589308409302124594129467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6119077879069499458839289 4589308409302124594129467)
          ·
            refine ⟨6883962613953186891194201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4589308409302124594129467 6883962613953186891194201)
            ·
              refine ⟨5162971960464890168395651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6883962613953186891194201 5162971960464890168395651)
              ·
                refine ⟨7744457940697335252593477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5162971960464890168395651 7744457940697335252593477)
                ·
                  refine ⟨1452085863880750359861277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7744457940697335252593477 1452085863880750359861277)
                  ·
                    refine ⟨544532198955281384947979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1452085863880750359861277 544532198955281384947979)
                    ·
                      rfl

theorem cell22_1590709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_1590709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1590709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1590709 prefixEnd_1590709 := by exact prefixLift 1590709
  have htrace : WordTrace (prefixWord ++ tailWord_1590709) baseStart_1590709 baseEnd_1590709 := by
    simpa [prefixWord, tailWord_1590709, baseEnd_1590709] using wordTrace_append hprefix tailTrace_1590709
  have hstable : (prefixWord ++ tailWord_1590709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590709).length < 2 ^ (prefixWord ++ tailWord_1590709).sum := by decide
  have hdescent : baseEnd_1590709 < baseStart_1590709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590767 : List Nat := [1, 1, 2, 1, 4, 1, 3, 4, 5]
def baseStart_1590767 : Nat := 118140960795 + 1590767 * 2 ^ 59
def prefixEnd_1590767 : Nat := 4983230072969 + 3 ^ 40 * 1590767 * 2
def baseEnd_1590767 : Nat := 181517351180196188999267

theorem tailTrace_1590767 : CollatzResearch.WordTrace tailWord_1590767 prefixEnd_1590767 181517351180196188999267 := by
  unfold tailWord_1590767
  simp only [CollatzResearch.WordTrace]
  refine ⟨58020039027930315219050555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38680026018620210146033703 58020039027930315219050555)
  ·
    refine ⟨87030058541895472828575833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58020039027930315219050555 87030058541895472828575833)
    ·
      refine ⟨65272543906421604621431875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87030058541895472828575833 65272543906421604621431875)
      ·
        refine ⟨97908815859632406932147813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65272543906421604621431875 97908815859632406932147813)
        ·
          refine ⟨18357902973681076299777715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97908815859632406932147813 18357902973681076299777715)
          ·
            refine ⟨27536854460521614449666573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18357902973681076299777715 27536854460521614449666573)
            ·
              refine ⟨10326320422695605418624965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27536854460521614449666573 10326320422695605418624965)
              ·
                refine ⟨1936185079255426015992181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10326320422695605418624965 1936185079255426015992181)
                ·
                  refine ⟨181517351180196188999267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1936185079255426015992181 181517351180196188999267)
                  ·
                    rfl

theorem cell22_1590767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 4, 5].length) (baseStart_1590767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1590767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1590767 prefixEnd_1590767 := by exact prefixLift 1590767
  have htrace : WordTrace (prefixWord ++ tailWord_1590767) baseStart_1590767 baseEnd_1590767 := by
    simpa [prefixWord, tailWord_1590767, baseEnd_1590767] using wordTrace_append hprefix tailTrace_1590767
  have hstable : (prefixWord ++ tailWord_1590767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590767).length < 2 ^ (prefixWord ++ tailWord_1590767).sum := by decide
  have hdescent : baseEnd_1590767 < baseStart_1590767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590790 : List Nat := [6, 2, 1, 1, 2, 1, 3, 6]
def baseStart_1590790 : Nat := 118140960795 + 1590790 * 2 ^ 59
def prefixEnd_1590790 : Nat := 4983230072969 + 3 ^ 40 * 1590790 * 2
def baseEnd_1590790 : Nat := 60506658545624908185859

theorem tailTrace_1590790 : CollatzResearch.WordTrace tailWord_1590790 prefixEnd_1590790 60506658545624908185859 := by
  unfold tailWord_1590790
  simp only [CollatzResearch.WordTrace]
  refine ⟨1813152434588968442098057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 38680585271231326764758549 1813152434588968442098057)
  ·
    refine ⟨1359864325941726331573543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1813152434588968442098057 1359864325941726331573543)
    ·
      refine ⟨2039796488912589497360315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1359864325941726331573543 2039796488912589497360315)
      ·
        refine ⟨3059694733368884246040473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2039796488912589497360315 3059694733368884246040473)
        ·
          refine ⟨2294771050026663184530355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3059694733368884246040473 2294771050026663184530355)
          ·
            refine ⟨3442156575039994776795533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2294771050026663184530355 3442156575039994776795533)
            ·
              refine ⟨1290808715639998041298325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3442156575039994776795533 1290808715639998041298325)
              ·
                refine ⟨60506658545624908185859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1290808715639998041298325 60506658545624908185859)
                ·
                  rfl

theorem cell22_1590790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_1590790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1590790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1590790 prefixEnd_1590790 := by exact prefixLift 1590790
  have htrace : WordTrace (prefixWord ++ tailWord_1590790) baseStart_1590790 baseEnd_1590790 := by
    simpa [prefixWord, tailWord_1590790, baseEnd_1590790] using wordTrace_append hprefix tailTrace_1590790
  have hstable : (prefixWord ++ tailWord_1590790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590790).length < 2 ^ (prefixWord ++ tailWord_1590790).sum := by decide
  have hdescent : baseEnd_1590790 < baseStart_1590790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590812 : List Nat := [2, 2, 3, 1, 2, 1, 1, 2, 8]
def baseStart_1590812 : Nat := 118140960795 + 1590812 * 2 ^ 59
def prefixEnd_1590812 : Nat := 4983230072969 + 3 ^ 40 * 1590812 * 2
def baseEnd_1590812 : Nat := 181522485986741149874221

theorem tailTrace_1590812 : CollatzResearch.WordTrace tailWord_1590812 prefixEnd_1590812 181522485986741149874221 := by
  unfold tailWord_1590812
  simp only [CollatzResearch.WordTrace]
  refine ⟨29010840156383643952219345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38681120208511525269625793 29010840156383643952219345)
  ·
    refine ⟨21758130117287732964164509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29010840156383643952219345 21758130117287732964164509)
    ·
      refine ⟨8159298793982899861561691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21758130117287732964164509 8159298793982899861561691)
      ·
        refine ⟨12238948190974349792342537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8159298793982899861561691 12238948190974349792342537)
        ·
          refine ⟨9179211143230762344256903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12238948190974349792342537 9179211143230762344256903)
          ·
            refine ⟨13768816714846143516385355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9179211143230762344256903 13768816714846143516385355)
            ·
              refine ⟨20653225072269215274578033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13768816714846143516385355 20653225072269215274578033)
              ·
                refine ⟨15489918804201911455933525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20653225072269215274578033 15489918804201911455933525)
                ·
                  refine ⟨181522485986741149874221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15489918804201911455933525 181522485986741149874221)
                  ·
                    rfl

theorem cell22_1590812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 8].length) (baseStart_1590812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1590812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1590812 prefixEnd_1590812 := by exact prefixLift 1590812
  have htrace : WordTrace (prefixWord ++ tailWord_1590812) baseStart_1590812 baseEnd_1590812 := by
    simpa [prefixWord, tailWord_1590812, baseEnd_1590812] using wordTrace_append hprefix tailTrace_1590812
  have hstable : (prefixWord ++ tailWord_1590812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590812).length < 2 ^ (prefixWord ++ tailWord_1590812).sum := by decide
  have hdescent : baseEnd_1590812 < baseStart_1590812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590842 : List Nat := [3, 1, 1, 1, 3, 2, 1, 1, 3, 6]
def baseStart_1590842 : Nat := 118140960795 + 1590842 * 2 ^ 59
def prefixEnd_1590842 : Nat := 4983230072969 + 3 ^ 40 * 1590842 * 2
def baseEnd_1590842 : Nat := 544577727573313371372571

theorem tailTrace_1590842 : CollatzResearch.WordTrace tailWord_1590842 prefixEnd_1590842 544577727573313371372571 := by
  unfold tailWord_1590842
  simp only [CollatzResearch.WordTrace]
  refine ⟨14505693625664650757007695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38681849668439068685353853 14505693625664650757007695)
  ·
    refine ⟨21758540438496976135511543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14505693625664650757007695 21758540438496976135511543)
    ·
      refine ⟨32637810657745464203267315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21758540438496976135511543 32637810657745464203267315)
      ·
        refine ⟨48956715986618196304900973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32637810657745464203267315 48956715986618196304900973)
        ·
          refine ⟨18358768494981823614337865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48956715986618196304900973 18358768494981823614337865)
          ·
            refine ⟨13769076371236367710753399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18358768494981823614337865 13769076371236367710753399)
            ·
              refine ⟨20653614556854551566130099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13769076371236367710753399 20653614556854551566130099)
              ·
                refine ⟨30980421835281827349195149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20653614556854551566130099 30980421835281827349195149)
                ·
                  refine ⟨11617658188230685255948181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30980421835281827349195149 11617658188230685255948181)
                  ·
                    refine ⟨544577727573313371372571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11617658188230685255948181 544577727573313371372571)
                    ·
                      rfl

theorem cell22_1590842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 3, 6].length) (baseStart_1590842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1590842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1590842 prefixEnd_1590842 := by exact prefixLift 1590842
  have htrace : WordTrace (prefixWord ++ tailWord_1590842) baseStart_1590842 baseEnd_1590842 := by
    simpa [prefixWord, tailWord_1590842, baseEnd_1590842] using wordTrace_append hprefix tailTrace_1590842
  have hstable : (prefixWord ++ tailWord_1590842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590842).length < 2 ^ (prefixWord ++ tailWord_1590842).sum := by decide
  have hdescent : baseEnd_1590842 < baseStart_1590842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590876 : List Nat := [2, 2, 4, 1, 2, 2, 1, 2, 2, 4]
def baseStart_1590876 : Nat := 118140960795 + 1590876 * 2 ^ 59
def prefixEnd_1590876 : Nat := 4983230072969 + 3 ^ 40 * 1590876 * 2
def baseEnd_1590876 : Nat := 544589366468148616022467

theorem tailTrace_1590876 : CollatzResearch.WordTrace tailWord_1590876 prefixEnd_1590876 544589366468148616022467 := by
  unfold tailWord_1590876
  simp only [CollatzResearch.WordTrace]
  refine ⟨29012007292267713417384241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38682676389690284556512321 29012007292267713417384241)
  ·
    refine ⟨21759005469200785063038181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29012007292267713417384241 21759005469200785063038181)
    ·
      refine ⟨4079813525475147199319659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21759005469200785063038181 4079813525475147199319659)
      ·
        refine ⟨6119720288212720798979489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4079813525475147199319659 6119720288212720798979489)
        ·
          refine ⟨4589790216159540599234617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6119720288212720798979489 4589790216159540599234617)
          ·
            refine ⟨3442342662119655449425963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4589790216159540599234617 3442342662119655449425963)
            ·
              refine ⟨5163513993179483174138945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3442342662119655449425963 5163513993179483174138945)
              ·
                refine ⟨3872635494884612380604209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5163513993179483174138945 3872635494884612380604209)
                ·
                  refine ⟨2904476621163459285453157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3872635494884612380604209 2904476621163459285453157)
                  ·
                    refine ⟨544589366468148616022467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2904476621163459285453157 544589366468148616022467)
                    ·
                      rfl

theorem cell22_1590876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_1590876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1590876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1590876 prefixEnd_1590876 := by exact prefixLift 1590876
  have htrace : WordTrace (prefixWord ++ tailWord_1590876) baseStart_1590876 baseEnd_1590876 := by
    simpa [prefixWord, tailWord_1590876, baseEnd_1590876] using wordTrace_append hprefix tailTrace_1590876
  have hstable : (prefixWord ++ tailWord_1590876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590876).length < 2 ^ (prefixWord ++ tailWord_1590876).sum := by decide
  have hdescent : baseEnd_1590876 < baseStart_1590876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590936 : List Nat := [2, 1, 2, 4, 1, 3, 2, 2, 5]
def baseStart_1590936 : Nat := 118140960795 + 1590936 * 2 ^ 59
def prefixEnd_1590936 : Nat := 4983230072969 + 3 ^ 40 * 1590936 * 2
def baseEnd_1590936 : Nat := 181536635231442819840761

theorem tailTrace_1590936 : CollatzResearch.WordTrace tailWord_1590936 prefixEnd_1590936 181536635231442819840761 := by
  unfold tailWord_1590936
  simp only [CollatzResearch.WordTrace]
  refine ⟨29013101482159028540976331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38684135309545371387968441 29013101482159028540976331)
  ·
    refine ⟨43519652223238542811464497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29013101482159028540976331 43519652223238542811464497)
    ·
      refine ⟨32639739167428907108598373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43519652223238542811464497 32639739167428907108598373)
      ·
        refine ⟨6119951093892920082862195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32639739167428907108598373 6119951093892920082862195)
        ·
          refine ⟨9179926640839380124293293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6119951093892920082862195 9179926640839380124293293)
          ·
            refine ⟨3442472490314767546609985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9179926640839380124293293 3442472490314767546609985)
            ·
              refine ⟨2581854367736075659957489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3442472490314767546609985 2581854367736075659957489)
              ·
                refine ⟨1936390775802056744968117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2581854367736075659957489 1936390775802056744968117)
                ·
                  refine ⟨181536635231442819840761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1936390775802056744968117 181536635231442819840761)
                  ·
                    rfl

theorem cell22_1590936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 2, 5].length) (baseStart_1590936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1590936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1590936 prefixEnd_1590936 := by exact prefixLift 1590936
  have htrace : WordTrace (prefixWord ++ tailWord_1590936) baseStart_1590936 baseEnd_1590936 := by
    simpa [prefixWord, tailWord_1590936, baseEnd_1590936] using wordTrace_append hprefix tailTrace_1590936
  have hstable : (prefixWord ++ tailWord_1590936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590936).length < 2 ^ (prefixWord ++ tailWord_1590936).sum := by decide
  have hdescent : baseEnd_1590936 < baseStart_1590936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590940 : List Nat := [2, 2, 3, 2, 3, 1, 1, 4, 1, 3]
def baseStart_1590940 : Nat := 118140960795 + 1590940 * 2 ^ 59
def prefixEnd_1590940 : Nat := 4983230072969 + 3 ^ 40 * 1590940 * 2
def baseEnd_1590940 : Nat := 544611274976073782422271

theorem tailTrace_1590940 : CollatzResearch.WordTrace tailWord_1590940 prefixEnd_1590940 544611274976073782422271 := by
  unfold tailWord_1590940
  simp only [CollatzResearch.WordTrace]
  refine ⟨29013174428151782882549137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38684232570869043843398849 29013174428151782882549137)
  ·
    refine ⟨21759880821113837161911853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29013174428151782882549137 21759880821113837161911853)
    ·
      refine ⟨8159955307917688935716945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21759880821113837161911853 8159955307917688935716945)
      ·
        refine ⟨6119966480938266701787709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8159955307917688935716945 6119966480938266701787709)
        ·
          refine ⟨2294987430351850013170391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6119966480938266701787709 2294987430351850013170391)
          ·
            refine ⟨3442481145527775019755587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2294987430351850013170391 3442481145527775019755587)
            ·
              refine ⟨5163721718291662529633381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3442481145527775019755587 5163721718291662529633381)
              ·
                refine ⟨968197822179686724306259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5163721718291662529633381 968197822179686724306259)
                ·
                  refine ⟨1452296733269530086459389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 968197822179686724306259 1452296733269530086459389)
                  ·
                    refine ⟨544611274976073782422271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1452296733269530086459389 544611274976073782422271)
                    ·
                      rfl

theorem cell22_1590940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_1590940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1590940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1590940 prefixEnd_1590940 := by exact prefixLift 1590940
  have htrace : WordTrace (prefixWord ++ tailWord_1590940) baseStart_1590940 baseEnd_1590940 := by
    simpa [prefixWord, tailWord_1590940, baseEnd_1590940] using wordTrace_append hprefix tailTrace_1590940
  have hstable : (prefixWord ++ tailWord_1590940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590940).length < 2 ^ (prefixWord ++ tailWord_1590940).sum := by decide
  have hdescent : baseEnd_1590940 < baseStart_1590940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590949 : List Nat := [1, 3, 1, 2, 1, 2, 3, 2, 3, 4]
def baseStart_1590949 : Nat := 118140960795 + 1590949 * 2 ^ 59
def prefixEnd_1590949 : Nat := 4983230072969 + 3 ^ 40 * 1590949 * 2
def baseEnd_1590949 : Nat := 544614355860000758947243

theorem tailTrace_1590949 : CollatzResearch.WordTrace tailWord_1590949 prefixEnd_1590949 544614355860000758947243 := by
  unfold tailWord_1590949
  simp only [CollatzResearch.WordTrace]
  refine ⟨58026677113270960302175901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38684451408847306868117267 58026677113270960302175901)
  ·
    refine ⟨21760003917476610113315963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58026677113270960302175901 21760003917476610113315963)
    ·
      refine ⟨32640005876214915169973945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21760003917476610113315963 32640005876214915169973945)
      ·
        refine ⟨24480004407161186377480459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32640005876214915169973945 24480004407161186377480459)
        ·
          refine ⟨36720006610741779566220689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24480004407161186377480459 36720006610741779566220689)
          ·
            refine ⟨27540004958056334674665517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36720006610741779566220689 27540004958056334674665517)
            ·
              refine ⟨10327501859271125502999569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27540004958056334674665517 10327501859271125502999569)
              ·
                refine ⟨7745626394453344127249677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10327501859271125502999569 7745626394453344127249677)
                ·
                  refine ⟨2904609897920004047718629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7745626394453344127249677 2904609897920004047718629)
                  ·
                    refine ⟨544614355860000758947243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2904609897920004047718629 544614355860000758947243)
                    ·
                      rfl

theorem cell22_1590949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 3, 4].length) (baseStart_1590949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1590949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1590949 prefixEnd_1590949 := by exact prefixLift 1590949
  have htrace : WordTrace (prefixWord ++ tailWord_1590949) baseStart_1590949 baseEnd_1590949 := by
    simpa [prefixWord, tailWord_1590949, baseEnd_1590949] using wordTrace_append hprefix tailTrace_1590949
  have hstable : (prefixWord ++ tailWord_1590949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590949).length < 2 ^ (prefixWord ++ tailWord_1590949).sum := by decide
  have hdescent : baseEnd_1590949 < baseStart_1590949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591041 : List Nat := [1, 2, 4, 1, 1, 1, 2, 2, 5, 3]
def baseStart_1591041 : Nat := 118140960795 + 1591041 * 2 ^ 59
def prefixEnd_1591041 : Nat := 4983230072969 + 3 ^ 40 * 1591041 * 2
def baseEnd_1591041 : Nat := 544645849340143185646961

theorem tailTrace_1591041 : CollatzResearch.WordTrace tailWord_1591041 prefixEnd_1591041 544645849340143185646961 := by
  unfold tailWord_1591041
  simp only [CollatzResearch.WordTrace]
  refine ⟨58030032628937660014524977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38686688419291773343016651 58030032628937660014524977)
  ·
    refine ⟨43522524471703245010893733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58030032628937660014524977 43522524471703245010893733)
    ·
      refine ⟨8160473338444358439542575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43522524471703245010893733 8160473338444358439542575)
      ·
        refine ⟨12240710007666537659313863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8160473338444358439542575 12240710007666537659313863)
        ·
          refine ⟨18361065011499806488970795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12240710007666537659313863 18361065011499806488970795)
          ·
            refine ⟨27541597517249709733456193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18361065011499806488970795 27541597517249709733456193)
            ·
              refine ⟨20656198137937282300092145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27541597517249709733456193 20656198137937282300092145)
              ·
                refine ⟨15492148603452961725069109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20656198137937282300092145 15492148603452961725069109)
                ·
                  refine ⟨1452388931573715161725229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15492148603452961725069109 1452388931573715161725229)
                  ·
                    refine ⟨544645849340143185646961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1452388931573715161725229 544645849340143185646961)
                    ·
                      rfl

theorem cell22_1591041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_1591041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1591041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1591041 prefixEnd_1591041 := by exact prefixLift 1591041
  have htrace : WordTrace (prefixWord ++ tailWord_1591041) baseStart_1591041 baseEnd_1591041 := by
    simpa [prefixWord, tailWord_1591041, baseEnd_1591041] using wordTrace_append hprefix tailTrace_1591041
  have hstable : (prefixWord ++ tailWord_1591041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591041).length < 2 ^ (prefixWord ++ tailWord_1591041).sum := by decide
  have hdescent : baseEnd_1591041 < baseStart_1591041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591071 : List Nat := [1, 1, 2, 4, 2, 1, 3, 3, 5]
def baseStart_1591071 : Nat := 118140960795 + 1591071 * 2 ^ 59
def prefixEnd_1591071 : Nat := 4983230072969 + 3 ^ 40 * 1591071 * 2
def baseEnd_1591071 : Nat := 181552039651077702465623

theorem tailTrace_1591071 : CollatzResearch.WordTrace tailWord_1591071 prefixEnd_1591071 181552039651077702465623 := by
  unfold tailWord_1591071
  simp only [CollatzResearch.WordTrace]
  refine ⟨58031126818828975138117067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38687417879219316758744711 58031126818828975138117067)
  ·
    refine ⟨87046690228243462707175601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58031126818828975138117067 87046690228243462707175601)
    ·
      refine ⟨65285017671182597030381701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87046690228243462707175601 65285017671182597030381701)
      ·
        refine ⟨12240940813346736943196569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65285017671182597030381701 12240940813346736943196569)
        ·
          refine ⟨9180705610010052707397427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12240940813346736943196569 9180705610010052707397427)
          ·
            refine ⟨13771058415015079061096141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9180705610010052707397427 13771058415015079061096141)
            ·
              refine ⟨5164146905630654647911053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13771058415015079061096141 5164146905630654647911053)
              ·
                refine ⟨1936555089611495492966645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5164146905630654647911053 1936555089611495492966645)
                ·
                  refine ⟨181552039651077702465623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1936555089611495492966645 181552039651077702465623)
                  ·
                    rfl

theorem cell22_1591071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 3, 5].length) (baseStart_1591071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1591071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1591071 prefixEnd_1591071 := by exact prefixLift 1591071
  have htrace : WordTrace (prefixWord ++ tailWord_1591071) baseStart_1591071 baseEnd_1591071 := by
    simpa [prefixWord, tailWord_1591071, baseEnd_1591071] using wordTrace_append hprefix tailTrace_1591071
  have hstable : (prefixWord ++ tailWord_1591071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591071).length < 2 ^ (prefixWord ++ tailWord_1591071).sum := by decide
  have hdescent : baseEnd_1591071 < baseStart_1591071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591150 : List Nat := [4, 1, 2, 3, 1, 1, 1, 5, 4]
def baseStart_1591150 : Nat := 118140960795 + 1591150 * 2 ^ 59
def prefixEnd_1591150 : Nat := 4983230072969 + 3 ^ 40 * 1591150 * 2
def baseEnd_1591150 : Nat := 181561054089234411557209

theorem tailTrace_1591150 : CollatzResearch.WordTrace tailWord_1591150 prefixEnd_1591150 181561054089234411557209 := by
  unfold tailWord_1591150
  simp only [CollatzResearch.WordTrace]
  refine ⟨7254251023192846453780363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38689338790361847753495269 7254251023192846453780363)
  ·
    refine ⟨10881376534789269680670545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7254251023192846453780363 10881376534789269680670545)
    ·
      refine ⟨8161032401091952260502909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10881376534789269680670545 8161032401091952260502909)
      ·
        refine ⟨3060387150409482097688591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8161032401091952260502909 3060387150409482097688591)
        ·
          refine ⟨4590580725614223146532887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3060387150409482097688591 4590580725614223146532887)
          ·
            refine ⟨6885871088421334719799331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4590580725614223146532887 6885871088421334719799331)
            ·
              refine ⟨10328806632632002079698997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6885871088421334719799331 10328806632632002079698997)
              ·
                refine ⟨968325621809250194971781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10328806632632002079698997 968325621809250194971781)
                ·
                  refine ⟨181561054089234411557209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 968325621809250194971781 181561054089234411557209)
                  ·
                    rfl

theorem cell22_1591150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 5, 4].length) (baseStart_1591150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1591150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1591150 prefixEnd_1591150 := by exact prefixLift 1591150
  have htrace : WordTrace (prefixWord ++ tailWord_1591150) baseStart_1591150 baseEnd_1591150 := by
    simpa [prefixWord, tailWord_1591150, baseEnd_1591150] using wordTrace_append hprefix tailTrace_1591150
  have hstable : (prefixWord ++ tailWord_1591150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591150).length < 2 ^ (prefixWord ++ tailWord_1591150).sum := by decide
  have hdescent : baseEnd_1591150 < baseStart_1591150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591182 : List Nat := [4, 1, 1, 5, 1, 2, 1, 1, 1, 5]
def baseStart_1591182 : Nat := 118140960795 + 1591182 * 2 ^ 59
def prefixEnd_1591182 : Nat := 4983230072969 + 3 ^ 40 * 1591182 * 2
def baseEnd_1591182 : Nat := 544694116521665817871529

theorem tailTrace_1591182 : CollatzResearch.WordTrace tailWord_1591182 prefixEnd_1591182 544694116521665817871529 := by
  unfold tailWord_1591182
  simp only [CollatzResearch.WordTrace]
  refine ⟨7254396915178355136925975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38690116880951227396938533 7254396915178355136925975)
  ·
    refine ⟨10881595372767532705388963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7254396915178355136925975 10881595372767532705388963)
    ·
      refine ⟨16322393059151299058083445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10881595372767532705388963 16322393059151299058083445)
      ·
        refine ⟨1530224349295434286695323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16322393059151299058083445 1530224349295434286695323)
        ·
          refine ⟨2295336523943151430042985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1530224349295434286695323 2295336523943151430042985)
          ·
            refine ⟨1721502392957363572532239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2295336523943151430042985 1721502392957363572532239)
            ·
              refine ⟨2582253589436045358798359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1721502392957363572532239 2582253589436045358798359)
              ·
                refine ⟨3873380384154068038197539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2582253589436045358798359 3873380384154068038197539)
                ·
                  refine ⟨5810070576231102057296309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3873380384154068038197539 5810070576231102057296309)
                  ·
                    refine ⟨544694116521665817871529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5810070576231102057296309 544694116521665817871529)
                    ·
                      rfl

theorem cell22_1591182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 1, 5].length) (baseStart_1591182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1591182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1591182 prefixEnd_1591182 := by exact prefixLift 1591182
  have htrace : WordTrace (prefixWord ++ tailWord_1591182) baseStart_1591182 baseEnd_1591182 := by
    simpa [prefixWord, tailWord_1591182, baseEnd_1591182] using wordTrace_append hprefix tailTrace_1591182
  have hstable : (prefixWord ++ tailWord_1591182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591182).length < 2 ^ (prefixWord ++ tailWord_1591182).sum := by decide
  have hdescent : baseEnd_1591182 < baseStart_1591182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591193 : List Nat := [1, 2, 1, 2, 1, 3, 4, 2, 3, 3]
def baseStart_1591193 : Nat := 118140960795 + 1591193 * 2 ^ 59
def prefixEnd_1591193 : Nat := 4983230072969 + 3 ^ 40 * 1591193 * 2
def baseEnd_1591193 : Nat := 544697882046465455846495

theorem tailTrace_1591193 : CollatzResearch.WordTrace tailWord_1591193 prefixEnd_1591193 544697882046465455846495 := by
  unfold tailWord_1591193
  simp only [CollatzResearch.WordTrace]
  refine ⟨58035576524386989974058233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38690384349591326649372155 58035576524386989974058233)
  ·
    refine ⟨43526682393290242480543675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58035576524386989974058233 43526682393290242480543675)
    ·
      refine ⟨65290023589935363720815513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43526682393290242480543675 65290023589935363720815513)
      ·
        refine ⟨48967517692451522790611635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65290023589935363720815513 48967517692451522790611635)
        ·
          refine ⟨73451276538677284185917453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48967517692451522790611635 73451276538677284185917453)
          ·
            refine ⟨27544228702003981569719045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73451276538677284185917453 27544228702003981569719045)
            ·
              refine ⟨5164542881625746544322321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27544228702003981569719045 5164542881625746544322321)
              ·
                refine ⟨3873407161219309908241741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5164542881625746544322321 3873407161219309908241741)
                ·
                  refine ⟨1452527685457241215590653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3873407161219309908241741 1452527685457241215590653)
                  ·
                    refine ⟨544697882046465455846495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1452527685457241215590653 544697882046465455846495)
                    ·
                      rfl

theorem cell22_1591193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 3, 3].length) (baseStart_1591193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1591193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1591193 prefixEnd_1591193 := by exact prefixLift 1591193
  have htrace : WordTrace (prefixWord ++ tailWord_1591193) baseStart_1591193 baseEnd_1591193 := by
    simpa [prefixWord, tailWord_1591193, baseEnd_1591193] using wordTrace_append hprefix tailTrace_1591193
  have hstable : (prefixWord ++ tailWord_1591193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591193).length < 2 ^ (prefixWord ++ tailWord_1591193).sum := by decide
  have hdescent : baseEnd_1591193 < baseStart_1591193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591214 : List Nat := [4, 1, 5, 1, 1, 1, 1, 2, 2, 4]
def baseStart_1591214 : Nat := 118140960795 + 1591214 * 2 ^ 59
def prefixEnd_1591214 : Nat := 4983230072969 + 3 ^ 40 * 1591214 * 2
def baseEnd_1591214 : Nat := 544705070775628401071431

theorem tailTrace_1591214 : CollatzResearch.WordTrace tailWord_1591214 prefixEnd_1591214 544705070775628401071431 := by
  unfold tailWord_1591214
  simp only [CollatzResearch.WordTrace]
  refine ⟨7254542807163863820071587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38690894971540607040381797 7254542807163863820071587)
  ·
    refine ⟨10881814210745795730107381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7254542807163863820071587 10881814210745795730107381)
    ·
      refine ⟨1020170082257418349697567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10881814210745795730107381 1020170082257418349697567)
      ·
        refine ⟨1530255123386127524546351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1020170082257418349697567 1530255123386127524546351)
        ·
          refine ⟨2295382685079191286819527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1530255123386127524546351 2295382685079191286819527)
          ·
            refine ⟨3443074027618786930229291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2295382685079191286819527 3443074027618786930229291)
            ·
              refine ⟨5164611041428180395343937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3443074027618786930229291 5164611041428180395343937)
              ·
                refine ⟨3873458281071135296507953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5164611041428180395343937 3873458281071135296507953)
                ·
                  refine ⟨2905093710803351472380965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3873458281071135296507953 2905093710803351472380965)
                  ·
                    refine ⟨544705070775628401071431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2905093710803351472380965 544705070775628401071431)
                    ·
                      rfl

theorem cell22_1591214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_1591214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1591214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1591214 prefixEnd_1591214 := by exact prefixLift 1591214
  have htrace : WordTrace (prefixWord ++ tailWord_1591214) baseStart_1591214 baseEnd_1591214 := by
    simpa [prefixWord, tailWord_1591214, baseEnd_1591214] using wordTrace_append hprefix tailTrace_1591214
  have hstable : (prefixWord ++ tailWord_1591214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591214).length < 2 ^ (prefixWord ++ tailWord_1591214).sum := by decide
  have hdescent : baseEnd_1591214 < baseStart_1591214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591240 : List Nat := [2, 1, 3, 1, 4, 1, 4, 1, 5]
def baseStart_1591240 : Nat := 118140960795 + 1591240 * 2 ^ 59
def prefixEnd_1591240 : Nat := 4983230072969 + 3 ^ 40 * 1591240 * 2
def baseEnd_1591240 : Nat := 181571323702324333307117

theorem tailTrace_1591240 : CollatzResearch.WordTrace tailWord_1591240 prefixEnd_1591240 181571323702324333307117 := by
  unfold tailWord_1591240
  simp only [CollatzResearch.WordTrace]
  refine ⟨29018645377608358500509587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38691527170144478000679449 29018645377608358500509587)
  ·
    refine ⟨43527968066412537750764381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29018645377608358500509587 43527968066412537750764381)
    ·
      refine ⟨16322988024904701656536643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43527968066412537750764381 16322988024904701656536643)
      ·
        refine ⟨24484482037357052484804965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16322988024904701656536643 24484482037357052484804965)
        ·
          refine ⟨4590840382004447340900931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24484482037357052484804965 4590840382004447340900931)
          ·
            refine ⟨6886260573006671011351397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4590840382004447340900931 6886260573006671011351397)
            ·
              refine ⟨1291173857438750814628387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6886260573006671011351397 1291173857438750814628387)
              ·
                refine ⟨1936760786158126221942581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1291173857438750814628387 1936760786158126221942581)
                ·
                  refine ⟨181571323702324333307117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1936760786158126221942581 181571323702324333307117)
                  ·
                    rfl

theorem cell22_1591240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 1, 5].length) (baseStart_1591240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1591240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1591240 prefixEnd_1591240 := by exact prefixLift 1591240
  have htrace : WordTrace (prefixWord ++ tailWord_1591240) baseStart_1591240 baseEnd_1591240 := by
    simpa [prefixWord, tailWord_1591240, baseEnd_1591240] using wordTrace_append hprefix tailTrace_1591240
  have hstable : (prefixWord ++ tailWord_1591240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591240).length < 2 ^ (prefixWord ++ tailWord_1591240).sum := by decide
  have hdescent : baseEnd_1591240 < baseStart_1591240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591283 : List Nat := [1, 1, 1, 2, 2, 2, 1, 5, 4, 3]
def baseStart_1591283 : Nat := 118140960795 + 1591283 * 2 ^ 59
def prefixEnd_1591283 : Nat := 4983230072969 + 3 ^ 40 * 1591283 * 2
def baseEnd_1591283 : Nat := 544728690885735221096219

theorem tailTrace_1591283 : CollatzResearch.WordTrace tailWord_1591283 prefixEnd_1591283 544728690885735221096219 := by
  unfold tailWord_1591283
  simp only [CollatzResearch.WordTrace]
  refine ⟨58038859094060935344834503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38692572729373956896556335 58038859094060935344834503)
  ·
    refine ⟨87058288641091403017251755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58038859094060935344834503 87058288641091403017251755)
    ·
      refine ⟨130587432961637104525877633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87058288641091403017251755 130587432961637104525877633)
      ·
        refine ⟨97940574721227828394408225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130587432961637104525877633 97940574721227828394408225)
        ·
          refine ⟨73455431040920871295806169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97940574721227828394408225 73455431040920871295806169)
          ·
            refine ⟨55091573280690653471854627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73455431040920871295806169 55091573280690653471854627)
            ·
              refine ⟨82637359921035980207781941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55091573280690653471854627 82637359921035980207781941)
              ·
                refine ⟨7747252492597123144479557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82637359921035980207781941 7747252492597123144479557)
                ·
                  refine ⟨1452609842361960589589917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7747252492597123144479557 1452609842361960589589917)
                  ·
                    refine ⟨544728690885735221096219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1452609842361960589589917 544728690885735221096219)
                    ·
                      rfl

theorem cell22_1591283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 4, 3].length) (baseStart_1591283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1591283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1591283 prefixEnd_1591283 := by exact prefixLift 1591283
  have htrace : WordTrace (prefixWord ++ tailWord_1591283) baseStart_1591283 baseEnd_1591283 := by
    simpa [prefixWord, tailWord_1591283, baseEnd_1591283] using wordTrace_append hprefix tailTrace_1591283
  have hstable : (prefixWord ++ tailWord_1591283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591283).length < 2 ^ (prefixWord ++ tailWord_1591283).sum := by decide
  have hdescent : baseEnd_1591283 < baseStart_1591283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591296 : List Nat := [2, 1, 1, 2, 1, 1, 1, 13]
def baseStart_1591296 : Nat := 118140960795 + 1591296 * 2 ^ 59
def prefixEnd_1591296 : Nat := 4983230072969 + 3 ^ 40 * 1591296 * 2
def baseEnd_1591296 : Nat := 60525904561267502280131

theorem tailTrace_1591296 : CollatzResearch.WordTrace tailWord_1591296 prefixEnd_1591296 60525904561267502280131 := by
  unfold tailWord_1591296
  simp only [CollatzResearch.WordTrace]
  refine ⟨29019666621506919282528871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38692888828675892376705161 29019666621506919282528871)
  ·
    refine ⟨43529499932260378923793307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29019666621506919282528871 43529499932260378923793307)
    ·
      refine ⟨65294249898390568385689961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43529499932260378923793307 65294249898390568385689961)
      ·
        refine ⟨48970687423792926289267471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65294249898390568385689961 48970687423792926289267471)
        ·
          refine ⟨73456031135689389433901207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48970687423792926289267471 73456031135689389433901207)
          ·
            refine ⟨110184046703534084150851811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73456031135689389433901207 110184046703534084150851811)
            ·
              refine ⟨165276070055301126226277717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110184046703534084150851811 165276070055301126226277717)
              ·
                refine ⟨60525904561267502280131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 165276070055301126226277717 60525904561267502280131)
                ·
                  rfl

theorem cell22_1591296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 13].length) (baseStart_1591296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1591296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1591296 prefixEnd_1591296 := by exact prefixLift 1591296
  have htrace : WordTrace (prefixWord ++ tailWord_1591296) baseStart_1591296 baseEnd_1591296 := by
    simpa [prefixWord, tailWord_1591296, baseEnd_1591296] using wordTrace_append hprefix tailTrace_1591296
  have hstable : (prefixWord ++ tailWord_1591296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591296).length < 2 ^ (prefixWord ++ tailWord_1591296).sum := by decide
  have hdescent : baseEnd_1591296 < baseStart_1591296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591345 : List Nat := [1, 2, 2, 3, 1, 3, 1, 3, 3, 3]
def baseStart_1591345 : Nat := 118140960795 + 1591345 * 2 ^ 59
def prefixEnd_1591345 : Nat := 4983230072969 + 3 ^ 40 * 1591345 * 2
def baseEnd_1591345 : Nat := 544749914752787726046029

theorem tailTrace_1591345 : CollatzResearch.WordTrace tailWord_1591345 prefixEnd_1591345 544749914752787726046029 := by
  unfold tailWord_1591345
  simp only [CollatzResearch.WordTrace]
  refine ⟨58041120419836319933591489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38694080279890879955727659 58041120419836319933591489)
  ·
    refine ⟨43530840314877239950193617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58041120419836319933591489 43530840314877239950193617)
    ·
      refine ⟨32648130236157929962645213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43530840314877239950193617 32648130236157929962645213)
      ·
        refine ⟨12243048838559223735991955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32648130236157929962645213 12243048838559223735991955)
        ·
          refine ⟨18364573257838835603987933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12243048838559223735991955 18364573257838835603987933)
          ·
            refine ⟨6886714971689563351495475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18364573257838835603987933 6886714971689563351495475)
            ·
              refine ⟨10330072457534345027243213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6886714971689563351495475 10330072457534345027243213)
              ·
                refine ⟨3873777171575379385216205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10330072457534345027243213 3873777171575379385216205)
                ·
                  refine ⟨1452666439340767269456077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3873777171575379385216205 1452666439340767269456077)
                  ·
                    refine ⟨544749914752787726046029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1452666439340767269456077 544749914752787726046029)
                    ·
                      rfl

theorem cell22_1591345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 3, 3].length) (baseStart_1591345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1591345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1591345 prefixEnd_1591345 := by exact prefixLift 1591345
  have htrace : WordTrace (prefixWord ++ tailWord_1591345) baseStart_1591345 baseEnd_1591345 := by
    simpa [prefixWord, tailWord_1591345, baseEnd_1591345] using wordTrace_append hprefix tailTrace_1591345
  have hstable : (prefixWord ++ tailWord_1591345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591345).length < 2 ^ (prefixWord ++ tailWord_1591345).sum := by decide
  have hdescent : baseEnd_1591345 < baseStart_1591345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591405 : List Nat := [1, 5, 1, 1, 2, 1, 2, 2, 3, 4]
def baseStart_1591405 : Nat := 118140960795 + 1591405 * 2 ^ 59
def prefixEnd_1591405 : Nat := 4983230072969 + 3 ^ 40 * 1591405 * 2
def baseEnd_1591405 : Nat := 544770453978967569545845

theorem tailTrace_1591405 : CollatzResearch.WordTrace tailWord_1591405 prefixEnd_1591405 544770453978967569545845 := by
  unfold tailWord_1591405
  simp only [CollatzResearch.WordTrace]
  refine ⟨58043308799618950180775669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38695539199745966787183779 58043308799618950180775669)
  ·
    refine ⟨5441560199964276579447719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58043308799618950180775669 5441560199964276579447719)
    ·
      refine ⟨8162340299946414869171579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5441560199964276579447719 8162340299946414869171579)
      ·
        refine ⟨12243510449919622303757369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8162340299946414869171579 12243510449919622303757369)
        ·
          refine ⟨9182632837439716727818027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12243510449919622303757369 9182632837439716727818027)
          ·
            refine ⟨13773949256159575091727041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9182632837439716727818027 13773949256159575091727041)
            ·
              refine ⟨10330461942119681318795281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13773949256159575091727041 10330461942119681318795281)
              ·
                refine ⟨7747846456589760989096461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10330461942119681318795281 7747846456589760989096461)
                ·
                  refine ⟨2905442421221160370911173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7747846456589760989096461 2905442421221160370911173)
                  ·
                    refine ⟨544770453978967569545845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2905442421221160370911173 544770453978967569545845)
                    ·
                      rfl

theorem cell22_1591405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_1591405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1591405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1591405 prefixEnd_1591405 := by exact prefixLift 1591405
  have htrace : WordTrace (prefixWord ++ tailWord_1591405) baseStart_1591405 baseEnd_1591405 := by
    simpa [prefixWord, tailWord_1591405, baseEnd_1591405] using wordTrace_append hprefix tailTrace_1591405
  have hstable : (prefixWord ++ tailWord_1591405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591405).length < 2 ^ (prefixWord ++ tailWord_1591405).sum := by decide
  have hdescent : baseEnd_1591405 < baseStart_1591405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591418 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 7, 5]
def baseStart_1591418 : Nat := 118140960795 + 1591418 * 2 ^ 59
def prefixEnd_1591418 : Nat := 4983230072969 + 3 ^ 40 * 1591418 * 2
def baseEnd_1591418 : Nat := 544774904144639868970805

theorem tailTrace_1591418 : CollatzResearch.WordTrace tailWord_1591418 prefixEnd_1591418 544774904144639868970805 := by
  unfold tailWord_1591418
  simp only [CollatzResearch.WordTrace]
  refine ⟨14510945737142963350249727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38695855299047902267332605 14510945737142963350249727)
  ·
    refine ⟨21766418605714445025374591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14510945737142963350249727 21766418605714445025374591)
    ·
      refine ⟨32649627908571667538061887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21766418605714445025374591 32649627908571667538061887)
      ·
        refine ⟨48974441862857501307092831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32649627908571667538061887 48974441862857501307092831)
        ·
          refine ⟨73461662794286251960639247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48974441862857501307092831 73461662794286251960639247)
          ·
            refine ⟨110192494191429377940958871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73461662794286251960639247 110192494191429377940958871)
            ·
              refine ⟨165288741287144066911438307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110192494191429377940958871 165288741287144066911438307)
              ·
                refine ⟨247933111930716100367157461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165288741287144066911438307 247933111930716100367157461)
                ·
                  refine ⟨5810932310876158602355253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 247933111930716100367157461 5810932310876158602355253)
                  ·
                    refine ⟨544774904144639868970805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5810932310876158602355253 544774904144639868970805)
                    ·
                      rfl

theorem cell22_1591418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 7, 5].length) (baseStart_1591418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1591418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1591418 prefixEnd_1591418 := by exact prefixLift 1591418
  have htrace : WordTrace (prefixWord ++ tailWord_1591418) baseStart_1591418 baseEnd_1591418 := by
    simpa [prefixWord, tailWord_1591418, baseEnd_1591418] using wordTrace_append hprefix tailTrace_1591418
  have hstable : (prefixWord ++ tailWord_1591418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591418).length < 2 ^ (prefixWord ++ tailWord_1591418).sum := by decide
  have hdescent : baseEnd_1591418 < baseStart_1591418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591448 : List Nat := [2, 1, 2, 4, 13]
def baseStart_1591448 : Nat := 118140960795 + 1591448 * 2 ^ 59
def prefixEnd_1591448 : Nat := 4983230072969 + 3 ^ 40 * 1591448 * 2
def baseEnd_1591448 : Nat := 2241914295299299550291

theorem tailTrace_1591448 : CollatzResearch.WordTrace tailWord_1591448 prefixEnd_1591448 2241914295299299550291 := by
  unfold tailWord_1591448
  simp only [CollatzResearch.WordTrace]
  refine ⟨29022438569231584262295499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38696584758975445683060665 29022438569231584262295499)
  ·
    refine ⟨43533657853847376393443249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29022438569231584262295499 43533657853847376393443249)
    ·
      refine ⟨32650243390385532295082437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43533657853847376393443249 32650243390385532295082437)
      ·
        refine ⟨6121920635697287305327957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32650243390385532295082437 6121920635697287305327957)
        ·
          refine ⟨2241914295299299550291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 6121920635697287305327957 2241914295299299550291)
          ·
            rfl

theorem cell22_1591448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 13].length) (baseStart_1591448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1591448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1591448 prefixEnd_1591448 := by exact prefixLift 1591448
  have htrace : WordTrace (prefixWord ++ tailWord_1591448) baseStart_1591448 baseEnd_1591448 := by
    simpa [prefixWord, tailWord_1591448, baseEnd_1591448] using wordTrace_append hprefix tailTrace_1591448
  have hstable : (prefixWord ++ tailWord_1591448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591448).length < 2 ^ (prefixWord ++ tailWord_1591448).sum := by decide
  have hdescent : baseEnd_1591448 < baseStart_1591448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591469 : List Nat := [1, 5, 2, 1, 2, 1, 2, 3, 2, 3]
def baseStart_1591469 : Nat := 118140960795 + 1591469 * 2 ^ 59
def prefixEnd_1591469 : Nat := 4983230072969 + 3 ^ 40 * 1591469 * 2
def baseEnd_1591469 : Nat := 544792362486892735945649

theorem tailTrace_1591469 : CollatzResearch.WordTrace tailWord_1591469 prefixEnd_1591469 544792362486892735945649 := by
  unfold tailWord_1591469
  simp only [CollatzResearch.WordTrace]
  refine ⟨58045643071387089111105461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38697095380924726074070307 58045643071387089111105461)
  ·
    refine ⟨5441779037942539604166137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58045643071387089111105461 5441779037942539604166137)
    ·
      refine ⟨4081334278456904703124603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5441779037942539604166137 4081334278456904703124603)
      ·
        refine ⟨6122001417685357054686905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4081334278456904703124603 6122001417685357054686905)
        ·
          refine ⟨4591501063264017791015179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6122001417685357054686905 4591501063264017791015179)
          ·
            refine ⟨6887251594896026686522769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4591501063264017791015179 6887251594896026686522769)
            ·
              refine ⟨5165438696172020014892077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6887251594896026686522769 5165438696172020014892077)
              ·
                refine ⟨1937039511064507505584529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5165438696172020014892077 1937039511064507505584529)
                ·
                  refine ⟨1452779633298380629188397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1937039511064507505584529 1452779633298380629188397)
                  ·
                    refine ⟨544792362486892735945649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1452779633298380629188397 544792362486892735945649)
                    ·
                      rfl

theorem cell22_1591469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_1591469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1591469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1591469 prefixEnd_1591469 := by exact prefixLift 1591469
  have htrace : WordTrace (prefixWord ++ tailWord_1591469) baseStart_1591469 baseEnd_1591469 := by
    simpa [prefixWord, tailWord_1591469, baseEnd_1591469] using wordTrace_append hprefix tailTrace_1591469
  have hstable : (prefixWord ++ tailWord_1591469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591469).length < 2 ^ (prefixWord ++ tailWord_1591469).sum := by decide
  have hdescent : baseEnd_1591469 < baseStart_1591469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591484 : List Nat := [2, 2, 2, 3, 3, 2, 1, 1, 2, 4]
def baseStart_1591484 : Nat := 118140960795 + 1591484 * 2 ^ 59
def prefixEnd_1591484 : Nat := 4983230072969 + 3 ^ 40 * 1591484 * 2
def baseEnd_1591484 : Nat := 544797497293437696820603

theorem tailTrace_1591484 : CollatzResearch.WordTrace tailWord_1591484 prefixEnd_1591484 544797497293437696820603 := by
  unfold tailWord_1591484
  simp only [CollatzResearch.WordTrace]
  refine ⟨29023095083166373336450753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38697460110888497781934337 29023095083166373336450753)
  ·
    refine ⟨21767321312374780002338065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29023095083166373336450753 21767321312374780002338065)
    ·
      refine ⟨16325490984281085001753549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21767321312374780002338065 16325490984281085001753549)
      ·
        refine ⟨6122059119105406875657581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16325490984281085001753549 6122059119105406875657581)
        ·
          refine ⟨2295772169664527578371593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6122059119105406875657581 2295772169664527578371593)
          ·
            refine ⟨1721829127248395683778695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2295772169664527578371593 1721829127248395683778695)
            ·
              refine ⟨2582743690872593525668043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1721829127248395683778695 2582743690872593525668043)
              ·
                refine ⟨3874115536308890288502065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2582743690872593525668043 3874115536308890288502065)
                ·
                  refine ⟨2905586652231667716376549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3874115536308890288502065 2905586652231667716376549)
                  ·
                    refine ⟨544797497293437696820603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2905586652231667716376549 544797497293437696820603)
                    ·
                      rfl

theorem cell22_1591484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 2, 4].length) (baseStart_1591484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1591484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1591484 prefixEnd_1591484 := by exact prefixLift 1591484
  have htrace : WordTrace (prefixWord ++ tailWord_1591484) baseStart_1591484 baseEnd_1591484 := by
    simpa [prefixWord, tailWord_1591484, baseEnd_1591484] using wordTrace_append hprefix tailTrace_1591484
  have hstable : (prefixWord ++ tailWord_1591484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591484).length < 2 ^ (prefixWord ++ tailWord_1591484).sum := by decide
  have hdescent : baseEnd_1591484 < baseStart_1591484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591514 : List Nat := [3, 1, 1, 2, 2, 1, 4, 4, 1, 3]
def baseStart_1591514 : Nat := 118140960795 + 1591514 * 2 ^ 59
def prefixEnd_1591514 : Nat := 4983230072969 + 3 ^ 40 * 1591514 * 2
def baseEnd_1591514 : Nat := 544807766906527618570511

theorem tailTrace_1591514 : CollatzResearch.WordTrace tailWord_1591514 prefixEnd_1591514 544807766906527618570511 := by
  unfold tailWord_1591514
  simp only [CollatzResearch.WordTrace]
  refine ⟨14511821089056015449123399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38698189570816041197662397 14511821089056015449123399)
  ·
    refine ⟨21767731633584023173685099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14511821089056015449123399 21767731633584023173685099)
    ·
      refine ⟨32651597450376034760527649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21767731633584023173685099 32651597450376034760527649)
      ·
        refine ⟨24488698087782026070395737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32651597450376034760527649 24488698087782026070395737)
        ·
          refine ⟨18366523565836519552796803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24488698087782026070395737 18366523565836519552796803)
          ·
            refine ⟨27549785348754779329195205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18366523565836519552796803 27549785348754779329195205)
            ·
              refine ⟨5165584752891521124224101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27549785348754779329195205 5165584752891521124224101)
              ·
                refine ⟨968547141167160210792019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5165584752891521124224101 968547141167160210792019)
                ·
                  refine ⟨1452820711750740316188029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 968547141167160210792019 1452820711750740316188029)
                  ·
                    refine ⟨544807766906527618570511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1452820711750740316188029 544807766906527618570511)
                    ·
                      rfl

theorem cell22_1591514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 4, 1, 3].length) (baseStart_1591514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1591514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1591514 prefixEnd_1591514 := by exact prefixLift 1591514
  have htrace : WordTrace (prefixWord ++ tailWord_1591514) baseStart_1591514 baseEnd_1591514 := by
    simpa [prefixWord, tailWord_1591514, baseEnd_1591514] using wordTrace_append hprefix tailTrace_1591514
  have hstable : (prefixWord ++ tailWord_1591514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591514).length < 2 ^ (prefixWord ++ tailWord_1591514).sum := by decide
  have hdescent : baseEnd_1591514 < baseStart_1591514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591585 : List Nat := [1, 2, 3, 2, 1, 1, 2, 1, 3, 6]
def baseStart_1591585 : Nat := 118140960795 + 1591585 * 2 ^ 59
def prefixEnd_1591585 : Nat := 4983230072969 + 3 ^ 40 * 1591585 * 2
def baseEnd_1591585 : Nat := 544832071657507100045293

theorem tailTrace_1591585 : CollatzResearch.WordTrace tailWord_1591585 prefixEnd_1591585 544832071657507100045293 := by
  unfold tailWord_1591585
  simp only [CollatzResearch.WordTrace]
  refine ⟨58049873938966840922328209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38699915959311227281552139 58049873938966840922328209)
  ·
    refine ⟨43537405454225130691746157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58049873938966840922328209 43537405454225130691746157)
    ·
      refine ⟨16326527045334424009404809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43537405454225130691746157 16326527045334424009404809)
      ·
        refine ⟨12244895284000818007053607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16326527045334424009404809 12244895284000818007053607)
        ·
          refine ⟨18367342926001227010580411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12244895284000818007053607 18367342926001227010580411)
          ·
            refine ⟨27551014389001840515870617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18367342926001227010580411 27551014389001840515870617)
            ·
              refine ⟨20663260791751380386902963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27551014389001840515870617 20663260791751380386902963)
              ·
                refine ⟨30994891187627070580354445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20663260791751380386902963 30994891187627070580354445)
                ·
                  refine ⟨11623084195360151467632917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30994891187627070580354445 11623084195360151467632917)
                  ·
                    refine ⟨544832071657507100045293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11623084195360151467632917 544832071657507100045293)
                    ·
                      rfl

theorem cell22_1591585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_1591585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1591585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1591585 prefixEnd_1591585 := by exact prefixLift 1591585
  have htrace : WordTrace (prefixWord ++ tailWord_1591585) baseStart_1591585 baseEnd_1591585 := by
    simpa [prefixWord, tailWord_1591585, baseEnd_1591585] using wordTrace_append hprefix tailTrace_1591585
  have hstable : (prefixWord ++ tailWord_1591585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591585).length < 2 ^ (prefixWord ++ tailWord_1591585).sum := by decide
  have hdescent : baseEnd_1591585 < baseStart_1591585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591604 : List Nat := [2, 5, 1, 1, 1, 3, 1, 2, 1, 5]
def baseStart_1591604 : Nat := 118140960795 + 1591604 * 2 ^ 59
def prefixEnd_1591604 : Nat := 4983230072969 + 3 ^ 40 * 1591604 * 2
def baseEnd_1591604 : Nat := 544838575745797383820235

theorem tailTrace_1591604 : CollatzResearch.WordTrace tailWord_1591604 prefixEnd_1591604 544838575745797383820235 := by
  unfold tailWord_1591604
  simp only [CollatzResearch.WordTrace]
  refine ⟨29025283462949003583634933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38700377950598671444846577 29025283462949003583634933)
  ·
    refine ⟨2721120324651469085965775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29025283462949003583634933 2721120324651469085965775)
    ·
      refine ⟨4081680486977203628948663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2721120324651469085965775 4081680486977203628948663)
      ·
        refine ⟨6122520730465805443422995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4081680486977203628948663 6122520730465805443422995)
        ·
          refine ⟨9183781095698708165134493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6122520730465805443422995 9183781095698708165134493)
          ·
            refine ⟨3443917910887015561925435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9183781095698708165134493 3443917910887015561925435)
            ·
              refine ⟨5165876866330523342888153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3443917910887015561925435 5165876866330523342888153)
              ·
                refine ⟨3874407649747892507166115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5165876866330523342888153 3874407649747892507166115)
                ·
                  refine ⟨5811611474621838760749173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3874407649747892507166115 5811611474621838760749173)
                  ·
                    refine ⟨544838575745797383820235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5811611474621838760749173 544838575745797383820235)
                    ·
                      rfl

theorem cell22_1591604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_1591604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1591604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1591604 prefixEnd_1591604 := by exact prefixLift 1591604
  have htrace : WordTrace (prefixWord ++ tailWord_1591604) baseStart_1591604 baseEnd_1591604 := by
    simpa [prefixWord, tailWord_1591604, baseEnd_1591604] using wordTrace_append hprefix tailTrace_1591604
  have hstable : (prefixWord ++ tailWord_1591604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591604).length < 2 ^ (prefixWord ++ tailWord_1591604).sum := by decide
  have hdescent : baseEnd_1591604 < baseStart_1591604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591617 : List Nat := [1, 2, 5, 2, 2, 10]
def baseStart_1591617 : Nat := 118140960795 + 1591617 * 2 ^ 59
def prefixEnd_1591617 : Nat := 4983230072969 + 3 ^ 40 * 1591617 * 2
def baseEnd_1591617 : Nat := 6726457110018144237595

theorem tailTrace_1591617 : CollatzResearch.WordTrace tailWord_1591617 prefixEnd_1591617 6726457110018144237595 := by
  unfold tailWord_1591617
  simp only [CollatzResearch.WordTrace]
  refine ⟨58051041074850910387493105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38700694049900606924995403 58051041074850910387493105)
  ·
    refine ⟨43538280806138182790619829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58051041074850910387493105 43538280806138182790619829)
    ·
      refine ⟨4081713825575454636620609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43538280806138182790619829 4081713825575454636620609)
      ·
        refine ⟨3061285369181590977465457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4081713825575454636620609 3061285369181590977465457)
        ·
          refine ⟨2295964026886193233099093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3061285369181590977465457 2295964026886193233099093)
          ·
            refine ⟨6726457110018144237595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2295964026886193233099093 6726457110018144237595)
            ·
              rfl

theorem cell22_1591617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 10].length) (baseStart_1591617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1591617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1591617 prefixEnd_1591617 := by exact prefixLift 1591617
  have htrace : WordTrace (prefixWord ++ tailWord_1591617) baseStart_1591617 baseEnd_1591617 := by
    simpa [prefixWord, tailWord_1591617, baseEnd_1591617] using wordTrace_append hprefix tailTrace_1591617
  have hstable : (prefixWord ++ tailWord_1591617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591617).length < 2 ^ (prefixWord ++ tailWord_1591617).sum := by decide
  have hdescent : baseEnd_1591617 < baseStart_1591617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591666 : List Nat := [3, 2, 1, 2, 1, 3, 1, 5, 1, 3]
def baseStart_1591666 : Nat := 118140960795 + 1591666 * 2 ^ 59
def prefixEnd_1591666 : Nat := 4983230072969 + 3 ^ 40 * 1591666 * 2
def baseEnd_1591666 : Nat := 544859799612849888770045

theorem tailTrace_1591666 : CollatzResearch.WordTrace tailWord_1591666 prefixEnd_1591666 544859799612849888770045 := by
  unfold tailWord_1591666
  simp only [CollatzResearch.WordTrace]
  refine ⟨14513207062918347939006713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38701885501115594504017901 14513207062918347939006713)
  ·
    refine ⟨10884905297188760954255035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14513207062918347939006713 10884905297188760954255035)
    ·
      refine ⟨16327357945783141431382553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10884905297188760954255035 16327357945783141431382553)
      ·
        refine ⟨12245518459337356073536915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16327357945783141431382553 12245518459337356073536915)
        ·
          refine ⟨18368277689006034110305373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12245518459337356073536915 18368277689006034110305373)
          ·
            refine ⟨6888104133377262791364515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18368277689006034110305373 6888104133377262791364515)
            ·
              refine ⟨10332156200065894187046773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6888104133377262791364515 10332156200065894187046773)
              ·
                refine ⟨968639643756177580035635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10332156200065894187046773 968639643756177580035635)
                ·
                  refine ⟨1452959465634266370053453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 968639643756177580035635 1452959465634266370053453)
                  ·
                    refine ⟨544859799612849888770045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1452959465634266370053453 544859799612849888770045)
                    ·
                      rfl

theorem cell22_1591666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 5, 1, 3].length) (baseStart_1591666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1591666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1591666 prefixEnd_1591666 := by exact prefixLift 1591666
  have htrace : WordTrace (prefixWord ++ tailWord_1591666) baseStart_1591666 baseEnd_1591666 := by
    simpa [prefixWord, tailWord_1591666, baseEnd_1591666] using wordTrace_append hprefix tailTrace_1591666
  have hstable : (prefixWord ++ tailWord_1591666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591666).length < 2 ^ (prefixWord ++ tailWord_1591666).sum := by decide
  have hdescent : baseEnd_1591666 < baseStart_1591666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591677 : List Nat := [1, 4, 1, 1, 2, 3, 1, 2, 2, 5]
def baseStart_1591677 : Nat := 118140960795 + 1591677 * 2 ^ 59
def prefixEnd_1591677 : Nat := 4983230072969 + 3 ^ 40 * 1591677 * 2
def baseEnd_1591677 : Nat := 544863565137649526745011

theorem tailTrace_1591677 : CollatzResearch.WordTrace tailWord_1591677 prefixEnd_1591677 544863565137649526745011 := by
  unfold tailWord_1591677
  simp only [CollatzResearch.WordTrace]
  refine ⟨58053229454633540634677285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38702152969755693756451523 58053229454633540634677285)
  ·
    refine ⟨10884980522743788869001991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58053229454633540634677285 10884980522743788869001991)
    ·
      refine ⟨16327470784115683303502987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10884980522743788869001991 16327470784115683303502987)
      ·
        refine ⟨24491206176173524955254481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16327470784115683303502987 24491206176173524955254481)
        ·
          refine ⟨18368404632130143716440861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24491206176173524955254481 18368404632130143716440861)
          ·
            refine ⟨6888151737048803893665323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18368404632130143716440861 6888151737048803893665323)
            ·
              refine ⟨10332227605573205840497985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6888151737048803893665323 10332227605573205840497985)
              ·
                refine ⟨7749170704179904380373489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10332227605573205840497985 7749170704179904380373489)
                ·
                  refine ⟨5811878028134928285280117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7749170704179904380373489 5811878028134928285280117)
                  ·
                    refine ⟨544863565137649526745011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5811878028134928285280117 544863565137649526745011)
                    ·
                      rfl

theorem cell22_1591677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_1591677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1591677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1591677 prefixEnd_1591677 := by exact prefixLift 1591677
  have htrace : WordTrace (prefixWord ++ tailWord_1591677) baseStart_1591677 baseEnd_1591677 := by
    simpa [prefixWord, tailWord_1591677, baseEnd_1591677] using wordTrace_append hprefix tailTrace_1591677
  have hstable : (prefixWord ++ tailWord_1591677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591677).length < 2 ^ (prefixWord ++ tailWord_1591677).sum := by decide
  have hdescent : baseEnd_1591677 < baseStart_1591677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591694 : List Nat := [4, 1, 1, 4, 1, 1, 2, 1, 2, 5]
def baseStart_1591694 : Nat := 118140960795 + 1591694 * 2 ^ 59
def prefixEnd_1591694 : Nat := 4983230072969 + 3 ^ 40 * 1591694 * 2
def baseEnd_1591694 : Nat := 544869384585067149069959

theorem tailTrace_1591694 : CollatzResearch.WordTrace tailWord_1591694 prefixEnd_1591694 544869384585067149069959 := by
  unfold tailWord_1591694
  simp only [CollatzResearch.WordTrace]
  refine ⟨7256731186946494067255767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38702566330381301692030757 7256731186946494067255767)
  ·
    refine ⟨10885096780419741100883651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7256731186946494067255767 10885096780419741100883651)
    ·
      refine ⟨16327645170629611651325477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10885096780419741100883651 16327645170629611651325477)
      ·
        refine ⟨3061433469493052184623527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16327645170629611651325477 3061433469493052184623527)
        ·
          refine ⟨4592150204239578276935291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3061433469493052184623527 4592150204239578276935291)
          ·
            refine ⟨6888225306359367415402937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4592150204239578276935291 6888225306359367415402937)
            ·
              refine ⟨5166168979769525561552203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6888225306359367415402937 5166168979769525561552203)
              ·
                refine ⟨7749253469654288342328305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5166168979769525561552203 7749253469654288342328305)
                ·
                  refine ⟨5811940102240716256746229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7749253469654288342328305 5811940102240716256746229)
                  ·
                    refine ⟨544869384585067149069959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5811940102240716256746229 544869384585067149069959)
                    ·
                      rfl

theorem cell22_1591694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_1591694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1591694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1591694 prefixEnd_1591694 := by exact prefixLift 1591694
  have htrace : WordTrace (prefixWord ++ tailWord_1591694) baseStart_1591694 baseEnd_1591694 := by
    simpa [prefixWord, tailWord_1591694, baseEnd_1591694] using wordTrace_append hprefix tailTrace_1591694
  have hstable : (prefixWord ++ tailWord_1591694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591694).length < 2 ^ (prefixWord ++ tailWord_1591694).sum := by decide
  have hdescent : baseEnd_1591694 < baseStart_1591694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591702 : List Nat := [5, 3, 1, 2, 2, 1, 2, 6]
def baseStart_1591702 : Nat := 118140960795 + 1591702 * 2 ^ 59
def prefixEnd_1591702 : Nat := 4983230072969 + 3 ^ 40 * 1591702 * 2
def baseEnd_1591702 : Nat := 60541347016506421652215

theorem tailTrace_1591702 : CollatzResearch.WordTrace tailWord_1591702 prefixEnd_1591702 60541347016506421652215 := by
  unfold tailWord_1591702
  simp only [CollatzResearch.WordTrace]
  refine ⟨3628383829971435619021085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38702760853028646602891573 3628383829971435619021085)
  ·
    refine ⟨1360643936239288357132907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3628383829971435619021085 1360643936239288357132907)
    ·
      refine ⟨2040965904358932535699361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1360643936239288357132907 2040965904358932535699361)
      ·
        refine ⟨1530724428269199401774521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2040965904358932535699361 1530724428269199401774521)
        ·
          refine ⟨1148043321201899551330891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1530724428269199401774521 1148043321201899551330891)
          ·
            refine ⟨1722064981802849326996337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1148043321201899551330891 1722064981802849326996337)
            ·
              refine ⟨1291548736352136995247253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1722064981802849326996337 1291548736352136995247253)
              ·
                refine ⟨60541347016506421652215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1291548736352136995247253 60541347016506421652215)
                ·
                  rfl

theorem cell22_1591702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 6].length) (baseStart_1591702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1591702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1591702 prefixEnd_1591702 := by exact prefixLift 1591702
  have htrace : WordTrace (prefixWord ++ tailWord_1591702) baseStart_1591702 baseEnd_1591702 := by
    simpa [prefixWord, tailWord_1591702, baseEnd_1591702] using wordTrace_append hprefix tailTrace_1591702
  have hstable : (prefixWord ++ tailWord_1591702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591702).length < 2 ^ (prefixWord ++ tailWord_1591702).sum := by decide
  have hdescent : baseEnd_1591702 < baseStart_1591702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591752 : List Nat := [2, 1, 3, 1, 3, 2, 1, 9]
def baseStart_1591752 : Nat := 118140960795 + 1591752 * 2 ^ 59
def prefixEnd_1591752 : Nat := 4983230072969 + 3 ^ 40 * 1591752 * 2
def baseEnd_1591752 : Nat := 60543248796708259013309

theorem tailTrace_1591752 : CollatzResearch.WordTrace tailWord_1591752 prefixEnd_1591752 60543248796708259013309 := by
  unfold tailWord_1591752
  simp only [CollatzResearch.WordTrace]
  refine ⟨29027982464680914221828755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38703976619574552295771673 29027982464680914221828755)
  ·
    refine ⟨43541973697021371332743133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29027982464680914221828755 43541973697021371332743133)
    ·
      refine ⟨16328240136383014249778675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43541973697021371332743133 16328240136383014249778675)
      ·
        refine ⟨24492360204574521374668013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16328240136383014249778675 24492360204574521374668013)
        ·
          refine ⟨9184635076715445515500505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24492360204574521374668013 9184635076715445515500505)
          ·
            refine ⟨6888476307536584136625379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9184635076715445515500505 6888476307536584136625379)
            ·
              refine ⟨10332714461304876204938069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6888476307536584136625379 10332714461304876204938069)
              ·
                refine ⟨60543248796708259013309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10332714461304876204938069 60543248796708259013309)
                ·
                  rfl

theorem cell22_1591752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 9].length) (baseStart_1591752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1591752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1591752 prefixEnd_1591752 := by exact prefixLift 1591752
  have htrace : WordTrace (prefixWord ++ tailWord_1591752) baseStart_1591752 baseEnd_1591752 := by
    simpa [prefixWord, tailWord_1591752, baseEnd_1591752] using wordTrace_append hprefix tailTrace_1591752
  have hstable : (prefixWord ++ tailWord_1591752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591752).length < 2 ^ (prefixWord ++ tailWord_1591752).sum := by decide
  have hdescent : baseEnd_1591752 < baseStart_1591752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591848 : List Nat := [2, 1, 5, 2, 1, 3, 1, 2, 5]
def baseStart_1591848 : Nat := 118140960795 + 1591848 * 2 ^ 59
def prefixEnd_1591848 : Nat := 4983230072969 + 3 ^ 40 * 1591848 * 2
def baseEnd_1591848 : Nat := 181640700644087360239829

theorem tailTrace_1591848 : CollatzResearch.WordTrace tailWord_1591848 prefixEnd_1591848 181640700644087360239829 := by
  unfold tailWord_1591848
  simp only [CollatzResearch.WordTrace]
  refine ⟨29029733168507018419576099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38706310891342691226101465 29029733168507018419576099)
  ·
    refine ⟨43544599752760527629364149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29029733168507018419576099 43544599752760527629364149)
    ·
      refine ⟨4082306226821299465252889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43544599752760527629364149 4082306226821299465252889)
      ·
        refine ⟨3061729670115974598939667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4082306226821299465252889 3061729670115974598939667)
        ·
          refine ⟨4592594505173961898409501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3061729670115974598939667 4592594505173961898409501)
          ·
            refine ⟨1722222939440235711903563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4592594505173961898409501 1722222939440235711903563)
            ·
              refine ⟨2583334409160353567855345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1722222939440235711903563 2583334409160353567855345)
              ·
                refine ⟨1937500806870265175891509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2583334409160353567855345 1937500806870265175891509)
                ·
                  refine ⟨181640700644087360239829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1937500806870265175891509 181640700644087360239829)
                  ·
                    rfl

theorem cell22_1591848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 2, 5].length) (baseStart_1591848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1591848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1591848 prefixEnd_1591848 := by exact prefixLift 1591848
  have htrace : WordTrace (prefixWord ++ tailWord_1591848) baseStart_1591848 baseEnd_1591848 := by
    simpa [prefixWord, tailWord_1591848, baseEnd_1591848] using wordTrace_append hprefix tailTrace_1591848
  have hstable : (prefixWord ++ tailWord_1591848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591848).length < 2 ^ (prefixWord ++ tailWord_1591848).sum := by decide
  have hdescent : baseEnd_1591848 < baseStart_1591848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591859 : List Nat := [1, 1, 1, 2, 4, 2, 4, 1, 6]
def baseStart_1591859 : Nat := 118140960795 + 1591859 * 2 ^ 59
def prefixEnd_1591859 : Nat := 4983230072969 + 3 ^ 40 * 1591859 * 2
def baseEnd_1591859 : Nat := 181641955819020572898151

theorem tailTrace_1591859 : CollatzResearch.WordTrace tailWord_1591859 prefixEnd_1591859 181641955819020572898151 := by
  unfold tailWord_1591859
  simp only [CollatzResearch.WordTrace]
  refine ⟨58059867539974185717802631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38706578359982790478535087 58059867539974185717802631)
  ·
    refine ⟨87089801309961278576703947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58059867539974185717802631 87089801309961278576703947)
    ·
      refine ⟨130634701964941917865055921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87089801309961278576703947 130634701964941917865055921)
      ·
        refine ⟨97976026473706438398791941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130634701964941917865055921 97976026473706438398791941)
        ·
          refine ⟨18370504963819957199773489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97976026473706438398791941 18370504963819957199773489)
          ·
            refine ⟨13777878722864967899830117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18370504963819957199773489 13777878722864967899830117)
            ·
              refine ⟨2583352260537181481218147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13777878722864967899830117 2583352260537181481218147)
              ·
                refine ⟨3875028390805772221827221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2583352260537181481218147 3875028390805772221827221)
                ·
                  refine ⟨181641955819020572898151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3875028390805772221827221 181641955819020572898151)
                  ·
                    rfl

theorem cell22_1591859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 6].length) (baseStart_1591859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1591859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1591859 prefixEnd_1591859 := by exact prefixLift 1591859
  have htrace : WordTrace (prefixWord ++ tailWord_1591859) baseStart_1591859 baseEnd_1591859 := by
    simpa [prefixWord, tailWord_1591859, baseEnd_1591859] using wordTrace_append hprefix tailTrace_1591859
  have hstable : (prefixWord ++ tailWord_1591859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591859).length < 2 ^ (prefixWord ++ tailWord_1591859).sum := by decide
  have hdescent : baseEnd_1591859 < baseStart_1591859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591889 : List Nat := [1, 2, 2, 1, 3, 3, 2, 1, 1, 6]
def baseStart_1591889 : Nat := 118140960795 + 1591889 * 2 ^ 59
def prefixEnd_1591889 : Nat := 4983230072969 + 3 ^ 40 * 1591889 * 2
def baseEnd_1591889 : Nat := 544936137070151640444361

theorem tailTrace_1591889 : CollatzResearch.WordTrace tailWord_1591889 prefixEnd_1591889 544936137070151640444361 := by
  unfold tailWord_1591889
  simp only [CollatzResearch.WordTrace]
  refine ⟨58060961729865500841394721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38707307819910333894263147 58060961729865500841394721)
  ·
    refine ⟨43545721297399125631046041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58060961729865500841394721 43545721297399125631046041)
    ·
      refine ⟨32659290973049344223284531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43545721297399125631046041 32659290973049344223284531)
      ·
        refine ⟨48988936459574016334926797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32659290973049344223284531 48988936459574016334926797)
        ·
          refine ⟨18370851172340256125597549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48988936459574016334926797 18370851172340256125597549)
          ·
            refine ⟨6889069189627596047099081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18370851172340256125597549 6889069189627596047099081)
            ·
              refine ⟨5166801892220697035324311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6889069189627596047099081 5166801892220697035324311)
              ·
                refine ⟨7750202838331045552986467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5166801892220697035324311 7750202838331045552986467)
                ·
                  refine ⟨11625304257496568329479701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7750202838331045552986467 11625304257496568329479701)
                  ·
                    refine ⟨544936137070151640444361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11625304257496568329479701 544936137070151640444361)
                    ·
                      rfl

theorem cell22_1591889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 6].length) (baseStart_1591889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1591889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1591889 prefixEnd_1591889 := by exact prefixLift 1591889
  have htrace : WordTrace (prefixWord ++ tailWord_1591889) baseStart_1591889 baseEnd_1591889 := by
    simpa [prefixWord, tailWord_1591889, baseEnd_1591889] using wordTrace_append hprefix tailTrace_1591889
  have hstable : (prefixWord ++ tailWord_1591889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591889).length < 2 ^ (prefixWord ++ tailWord_1591889).sum := by decide
  have hdescent : baseEnd_1591889 < baseStart_1591889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591925 : List Nat := [1, 3, 4, 2, 2, 1, 1, 3, 2, 3]
def baseStart_1591925 : Nat := 118140960795 + 1591925 * 2 ^ 59
def prefixEnd_1591925 : Nat := 4983230072969 + 3 ^ 40 * 1591925 * 2
def baseEnd_1591925 : Nat := 544948460605859546544251

theorem tailTrace_1591925 : CollatzResearch.WordTrace tailWord_1591925 prefixEnd_1591925 544948460605859546544251 := by
  unfold tailWord_1591925
  simp only [CollatzResearch.WordTrace]
  refine ⟨58062274757735078989705229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38708183171823385993136819 58062274757735078989705229)
  ·
    refine ⟨21773353034150654621139461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58062274757735078989705229 21773353034150654621139461)
    ·
      refine ⟨4082503693903247741463649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21773353034150654621139461 4082503693903247741463649)
      ·
        refine ⟨3061877770427435806097737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4082503693903247741463649 3061877770427435806097737)
        ·
          refine ⟨2296408327820576854573303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3061877770427435806097737 2296408327820576854573303)
          ·
            refine ⟨3444612491730865281859955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2296408327820576854573303 3444612491730865281859955)
            ·
              refine ⟨5166918737596297922789933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3444612491730865281859955 5166918737596297922789933)
              ·
                refine ⟨1937594526598611721046225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5166918737596297922789933 1937594526598611721046225)
                ·
                  refine ⟨1453195894948958790784669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1937594526598611721046225 1453195894948958790784669)
                  ·
                    refine ⟨544948460605859546544251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1453195894948958790784669 544948460605859546544251)
                    ·
                      rfl

theorem cell22_1591925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_1591925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1591925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1591925 prefixEnd_1591925 := by exact prefixLift 1591925
  have htrace : WordTrace (prefixWord ++ tailWord_1591925) baseStart_1591925 baseEnd_1591925 := by
    simpa [prefixWord, tailWord_1591925, baseEnd_1591925] using wordTrace_append hprefix tailTrace_1591925
  have hstable : (prefixWord ++ tailWord_1591925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591925).length < 2 ^ (prefixWord ++ tailWord_1591925).sum := by decide
  have hdescent : baseEnd_1591925 < baseStart_1591925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591981 : List Nat := [1, 5, 2, 1, 1, 2, 1, 1, 1, 7]
def baseStart_1591981 : Nat := 118140960795 + 1591981 * 2 ^ 59
def prefixEnd_1591981 : Nat := 4983230072969 + 3 ^ 40 * 1591981 * 2
def baseEnd_1591981 : Nat := 544967630550294067144079

theorem tailTrace_1591981 : CollatzResearch.WordTrace tailWord_1591981 prefixEnd_1591981 544967630550294067144079 := by
  unfold tailWord_1591981
  simp only [CollatzResearch.WordTrace]
  refine ⟨58064317245532200553743797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38709544830354800369162531 58064317245532200553743797)
  ·
    refine ⟨5443529741768643801913481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58064317245532200553743797 5443529741768643801913481)
    ·
      refine ⟨4082647306326482851435111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5443529741768643801913481 4082647306326482851435111)
      ·
        refine ⟨6123970959489724277152667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4082647306326482851435111 6123970959489724277152667)
        ·
          refine ⟨9185956439234586415729001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6123970959489724277152667 9185956439234586415729001)
          ·
            refine ⟨6889467329425939811796751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9185956439234586415729001 6889467329425939811796751)
            ·
              refine ⟨10334200994138909717695127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6889467329425939811796751 10334200994138909717695127)
              ·
                refine ⟨15501301491208364576542691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10334200994138909717695127 15501301491208364576542691)
                ·
                  refine ⟨23251952236812546864814037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15501301491208364576542691 23251952236812546864814037)
                  ·
                    refine ⟨544967630550294067144079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23251952236812546864814037 544967630550294067144079)
                    ·
                      rfl

theorem cell22_1591981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_1591981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1591981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1591981 prefixEnd_1591981 := by exact prefixLift 1591981
  have htrace : WordTrace (prefixWord ++ tailWord_1591981) baseStart_1591981 baseEnd_1591981 := by
    simpa [prefixWord, tailWord_1591981, baseEnd_1591981] using wordTrace_append hprefix tailTrace_1591981
  have hstable : (prefixWord ++ tailWord_1591981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591981).length < 2 ^ (prefixWord ++ tailWord_1591981).sum := by decide
  have hdescent : baseEnd_1591981 < baseStart_1591981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591996 : List Nat := [2, 2, 2, 3, 1, 1, 1, 3, 3, 4]
def baseStart_1591996 : Nat := 118140960795 + 1591996 * 2 ^ 59
def prefixEnd_1591996 : Nat := 4983230072969 + 3 ^ 40 * 1591996 * 2
def baseEnd_1591996 : Nat := 544972765356839028019033

theorem tailTrace_1591996 : CollatzResearch.WordTrace tailWord_1591996 prefixEnd_1591996 544972765356839028019033 := by
  unfold tailWord_1591996
  simp only [CollatzResearch.WordTrace]
  refine ⟨29032432170238929057769921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38709909560318572077026561 29032432170238929057769921)
  ·
    refine ⟨21774324127679196793327441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29032432170238929057769921 21774324127679196793327441)
    ·
      refine ⟨16330743095759397594995581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21774324127679196793327441 16330743095759397594995581)
      ·
        refine ⟨6124028660909774098123343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16330743095759397594995581 6124028660909774098123343)
        ·
          refine ⟨9186042991364661147185015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6124028660909774098123343 9186042991364661147185015)
          ·
            refine ⟨13779064487046991720777523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9186042991364661147185015 13779064487046991720777523)
            ·
              refine ⟨20668596730570487581166285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13779064487046991720777523 20668596730570487581166285)
              ·
                refine ⟨7750723773963932842937357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20668596730570487581166285 7750723773963932842937357)
                ·
                  refine ⟨2906521415236474816101509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7750723773963932842937357 2906521415236474816101509)
                  ·
                    refine ⟨544972765356839028019033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2906521415236474816101509 544972765356839028019033)
                    ·
                      rfl

theorem cell22_1591996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_1591996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1591996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1591996 prefixEnd_1591996 := by exact prefixLift 1591996
  have htrace : WordTrace (prefixWord ++ tailWord_1591996) baseStart_1591996 baseEnd_1591996 := by
    simpa [prefixWord, tailWord_1591996, baseEnd_1591996] using wordTrace_append hprefix tailTrace_1591996
  have hstable : (prefixWord ++ tailWord_1591996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591996).length < 2 ^ (prefixWord ++ tailWord_1591996).sum := by decide
  have hdescent : baseEnd_1591996 < baseStart_1591996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592028 : List Nat := [2, 2, 5, 1, 1, 1, 1, 3, 6]
def baseStart_1592028 : Nat := 118140960795 + 1592028 * 2 ^ 59
def prefixEnd_1592028 : Nat := 4983230072969 + 3 ^ 40 * 1592028 * 2
def baseEnd_1592028 : Nat := 181661239870267203739645

theorem tailTrace_1592028 : CollatzResearch.WordTrace tailWord_1592028 prefixEnd_1592028 181661239870267203739645 := by
  unfold tailWord_1592028
  simp only [CollatzResearch.WordTrace]
  refine ⟨29033015738180963790352369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38710687650907951720469825 29033015738180963790352369)
  ·
    refine ⟨21774761803635722842764277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29033015738180963790352369 21774761803635722842764277)
    ·
      refine ⟨2041383919090849016509151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21774761803635722842764277 2041383919090849016509151)
      ·
        refine ⟨3062075878636273524763727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2041383919090849016509151 3062075878636273524763727)
        ·
          refine ⟨4593113817954410287145591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3062075878636273524763727 4593113817954410287145591)
          ·
            refine ⟨6889670726931615430718387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4593113817954410287145591 6889670726931615430718387)
            ·
              refine ⟨10334506090397423146077581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6889670726931615430718387 10334506090397423146077581)
              ·
                refine ⟨3875439783899033679779093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10334506090397423146077581 3875439783899033679779093)
                ·
                  refine ⟨181661239870267203739645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3875439783899033679779093 181661239870267203739645)
                  ·
                    rfl

theorem cell22_1592028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 6].length) (baseStart_1592028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1592028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1592028 prefixEnd_1592028 := by exact prefixLift 1592028
  have htrace : WordTrace (prefixWord ++ tailWord_1592028) baseStart_1592028 baseEnd_1592028 := by
    simpa [prefixWord, tailWord_1592028, baseEnd_1592028] using wordTrace_append hprefix tailTrace_1592028
  have hstable : (prefixWord ++ tailWord_1592028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592028).length < 2 ^ (prefixWord ++ tailWord_1592028).sum := by decide
  have hdescent : baseEnd_1592028 < baseStart_1592028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592062 : List Nat := [4, 2, 2, 1, 2, 3, 1, 3, 4]
def baseStart_1592062 : Nat := 118140960795 + 1592062 * 2 ^ 59
def prefixEnd_1592062 : Nat := 4983230072969 + 3 ^ 40 * 1592062 * 2
def baseEnd_1592062 : Nat := 181665119501878951956277

theorem tailTrace_1592062 : CollatzResearch.WordTrace tailWord_1592062 prefixEnd_1592062 181665119501878951956277 := by
  unfold tailWord_1592062
  simp only [CollatzResearch.WordTrace]
  refine ⟨7258408944779843923430305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38711514372159167591628293 7258408944779843923430305)
  ·
    refine ⟨5443806708584882942572729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7258408944779843923430305 5443806708584882942572729)
    ·
      refine ⟨4082855031438662206929547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5443806708584882942572729 4082855031438662206929547)
      ·
        refine ⟨6124282547157993310394321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4082855031438662206929547 6124282547157993310394321)
        ·
          refine ⟨4593211910368494982795741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6124282547157993310394321 4593211910368494982795741)
          ·
            refine ⟨1722454466388185618548403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4593211910368494982795741 1722454466388185618548403)
            ·
              refine ⟨2583681699582278427822605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1722454466388185618548403 2583681699582278427822605)
              ·
                refine ⟨968880637343354410433477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2583681699582278427822605 968880637343354410433477)
                ·
                  refine ⟨181665119501878951956277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 968880637343354410433477 181665119501878951956277)
                  ·
                    rfl

theorem cell22_1592062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_1592062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1592062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1592062 prefixEnd_1592062 := by exact prefixLift 1592062
  have htrace : WordTrace (prefixWord ++ tailWord_1592062) baseStart_1592062 baseEnd_1592062 := by
    simpa [prefixWord, tailWord_1592062, baseEnd_1592062] using wordTrace_append hprefix tailTrace_1592062
  have hstable : (prefixWord ++ tailWord_1592062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592062).length < 2 ^ (prefixWord ++ tailWord_1592062).sum := by decide
  have hdescent : baseEnd_1592062 < baseStart_1592062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592163 : List Nat := [1, 1, 1, 5, 3, 2, 1, 2, 6]
def baseStart_1592163 : Nat := 118140960795 + 1592163 * 2 ^ 59
def prefixEnd_1592163 : Nat := 4983230072969 + 3 ^ 40 * 1592163 * 2
def baseEnd_1592163 : Nat := 181676644289902086364507

theorem tailTrace_1592163 : CollatzResearch.WordTrace tailWord_1592163 prefixEnd_1592163 181676644289902086364507 := by
  unfold tailWord_1592163
  simp only [CollatzResearch.WordTrace]
  refine ⟨58070955330872845636869143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38713970220581897091246095 58070955330872845636869143)
  ·
    refine ⟨87106432996309268455303715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58070955330872845636869143 87106432996309268455303715)
    ·
      refine ⟨130659649494463902682955573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87106432996309268455303715 130659649494463902682955573)
      ·
        refine ⟨12249342140105990876527085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 130659649494463902682955573 12249342140105990876527085)
        ·
          refine ⟨4593503302539746578697657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12249342140105990876527085 4593503302539746578697657)
          ·
            refine ⟨3445127476904809934023243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4593503302539746578697657 3445127476904809934023243)
            ·
              refine ⟨5167691215357214901034865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3445127476904809934023243 5167691215357214901034865)
              ·
                refine ⟨3875768411517911175776149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5167691215357214901034865 3875768411517911175776149)
                ·
                  refine ⟨181676644289902086364507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3875768411517911175776149 181676644289902086364507)
                  ·
                    rfl

theorem cell22_1592163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 6].length) (baseStart_1592163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1592163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1592163 prefixEnd_1592163 := by exact prefixLift 1592163
  have htrace : WordTrace (prefixWord ++ tailWord_1592163) baseStart_1592163 baseEnd_1592163 := by
    simpa [prefixWord, tailWord_1592163, baseEnd_1592163] using wordTrace_append hprefix tailTrace_1592163
  have hstable : (prefixWord ++ tailWord_1592163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592163).length < 2 ^ (prefixWord ++ tailWord_1592163).sum := by decide
  have hdescent : baseEnd_1592163 < baseStart_1592163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592178 : List Nat := [3, 2, 1, 2, 1, 1, 4, 2, 1, 5]
def baseStart_1592178 : Nat := 118140960795 + 1592178 * 2 ^ 59
def prefixEnd_1592178 : Nat := 4983230072969 + 3 ^ 40 * 1592178 * 2
def baseEnd_1592178 : Nat := 545035067676251219968475

theorem tailTrace_1592178 : CollatzResearch.WordTrace tailWord_1592178 prefixEnd_1592178 545035067676251219968475 := by
  unfold tailWord_1592178
  simp only [CollatzResearch.WordTrace]
  refine ⟨14517875606454625799666297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38714334950545668799110125 14517875606454625799666297)
  ·
    refine ⟨10888406704840969349749723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14517875606454625799666297 10888406704840969349749723)
    ·
      refine ⟨16332610057261454024624585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10888406704840969349749723 16332610057261454024624585)
      ·
        refine ⟨12249457542946090518468439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16332610057261454024624585 12249457542946090518468439)
        ·
          refine ⟨18374186314419135777702659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12249457542946090518468439 18374186314419135777702659)
          ·
            refine ⟨27561279471628703666553989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18374186314419135777702659 27561279471628703666553989)
            ·
              refine ⟨5167739900930381937478873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27561279471628703666553989 5167739900930381937478873)
              ·
                refine ⟨3875804925697786453109155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5167739900930381937478873 3875804925697786453109155)
                ·
                  refine ⟨5813707388546679679663733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3875804925697786453109155 5813707388546679679663733)
                  ·
                    refine ⟨545035067676251219968475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5813707388546679679663733 545035067676251219968475)
                    ·
                      rfl

theorem cell22_1592178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_1592178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1592178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1592178 prefixEnd_1592178 := by exact prefixLift 1592178
  have htrace : WordTrace (prefixWord ++ tailWord_1592178) baseStart_1592178 baseEnd_1592178 := by
    simpa [prefixWord, tailWord_1592178, baseEnd_1592178] using wordTrace_append hprefix tailTrace_1592178
  have hstable : (prefixWord ++ tailWord_1592178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592178).length < 2 ^ (prefixWord ++ tailWord_1592178).sum := by decide
  have hdescent : baseEnd_1592178 < baseStart_1592178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592182 : List Nat := [5, 1, 1, 3, 1, 2, 1, 3, 1, 4]
def baseStart_1592182 : Nat := 118140960795 + 1592182 * 2 ^ 59
def prefixEnd_1592182 : Nat := 4983230072969 + 3 ^ 40 * 1592182 * 2
def baseEnd_1592182 : Nat := 545036436957996542868463

theorem tailTrace_1592182 : CollatzResearch.WordTrace tailWord_1592182 prefixEnd_1592182 545036436957996542868463 := by
  unfold tailWord_1592182
  simp only [CollatzResearch.WordTrace]
  refine ⟨3629478019862750742613175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38714432211869341254540533 3629478019862750742613175)
  ·
    refine ⟨5444217029794126113919763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3629478019862750742613175 5444217029794126113919763)
    ·
      refine ⟨8166325544691189170879645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5444217029794126113919763 8166325544691189170879645)
      ·
        refine ⟨3062372079259195939079867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8166325544691189170879645 3062372079259195939079867)
        ·
          refine ⟨4593558118888793908619801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3062372079259195939079867 4593558118888793908619801)
          ·
            refine ⟨3445168589166595431464851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4593558118888793908619801 3445168589166595431464851)
            ·
              refine ⟨5167752883749893147197277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3445168589166595431464851 5167752883749893147197277)
              ·
                refine ⟨1937907331406209930198979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5167752883749893147197277 1937907331406209930198979)
                ·
                  refine ⟨2906860997109314895298469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1937907331406209930198979 2906860997109314895298469)
                  ·
                    refine ⟨545036436957996542868463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2906860997109314895298469 545036436957996542868463)
                    ·
                      rfl

theorem cell22_1592182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_1592182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1592182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1592182 prefixEnd_1592182 := by exact prefixLift 1592182
  have htrace : WordTrace (prefixWord ++ tailWord_1592182) baseStart_1592182 baseEnd_1592182 := by
    simpa [prefixWord, tailWord_1592182, baseEnd_1592182] using wordTrace_append hprefix tailTrace_1592182
  have hstable : (prefixWord ++ tailWord_1592182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592182).length < 2 ^ (prefixWord ++ tailWord_1592182).sum := by decide
  have hdescent : baseEnd_1592182 < baseStart_1592182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592225 : List Nat := [1, 2, 3, 4, 1, 1, 4, 6]
def baseStart_1592225 : Nat := 118140960795 + 1592225 * 2 ^ 59
def prefixEnd_1592225 : Nat := 4983230072969 + 3 ^ 40 * 1592225 * 2
def baseEnd_1592225 : Nat := 60561239637417640449259

theorem tailTrace_1592225 : CollatzResearch.WordTrace tailWord_1592225 prefixEnd_1592225 60561239637417640449259 := by
  unfold tailWord_1592225
  simp only [CollatzResearch.WordTrace]
  refine ⟨58073216656648230225626129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38715477771098820150417419 58073216656648230225626129)
  ·
    refine ⟨43554912492486172669219597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58073216656648230225626129 43554912492486172669219597)
    ·
      refine ⟨16333092184682314750957349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43554912492486172669219597 16333092184682314750957349)
      ·
        refine ⟨3062454784627934015804503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16333092184682314750957349 3062454784627934015804503)
        ·
          refine ⟨4593682176941901023706755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3062454784627934015804503 4593682176941901023706755)
          ·
            refine ⟨6890523265412851535560133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4593682176941901023706755 6890523265412851535560133)
            ·
              refine ⟨1291973112264909662917525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6890523265412851535560133 1291973112264909662917525)
              ·
                refine ⟨60561239637417640449259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1291973112264909662917525 60561239637417640449259)
                ·
                  rfl

theorem cell22_1592225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 6].length) (baseStart_1592225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1592225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1592225 prefixEnd_1592225 := by exact prefixLift 1592225
  have htrace : WordTrace (prefixWord ++ tailWord_1592225) baseStart_1592225 baseEnd_1592225 := by
    simpa [prefixWord, tailWord_1592225, baseEnd_1592225] using wordTrace_append hprefix tailTrace_1592225
  have hstable : (prefixWord ++ tailWord_1592225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592225).length < 2 ^ (prefixWord ++ tailWord_1592225).sum := by decide
  have hdescent : baseEnd_1592225 < baseStart_1592225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592268 : List Nat := [2, 2, 1, 4, 1, 1, 2, 1, 1, 7]
def baseStart_1592268 : Nat := 118140960795 + 1592268 * 2 ^ 59
def prefixEnd_1592268 : Nat := 4983230072969 + 3 ^ 40 * 1592268 * 2
def baseEnd_1592268 : Nat := 545065876515520985218199

theorem tailTrace_1592268 : CollatzResearch.WordTrace tailWord_1592268 prefixEnd_1592268 545065876515520985218199 := by
  unfold tailWord_1592268
  simp only [CollatzResearch.WordTrace]
  refine ⟨29037392497746224284720729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38716523330328299046294305 29037392497746224284720729)
  ·
    refine ⟨21778044373309668213540547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29037392497746224284720729 21778044373309668213540547)
    ·
      refine ⟨32667066559964502320310821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21778044373309668213540547 32667066559964502320310821)
      ·
        refine ⟨6125074979993344185058279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32667066559964502320310821 6125074979993344185058279)
        ·
          refine ⟨9187612469990016277587419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6125074979993344185058279 9187612469990016277587419)
          ·
            refine ⟨13781418704985024416381129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9187612469990016277587419 13781418704985024416381129)
            ·
              refine ⟨10336064028738768312285847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13781418704985024416381129 10336064028738768312285847)
              ·
                refine ⟨15504096043108152468428771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10336064028738768312285847 15504096043108152468428771)
                ·
                  refine ⟨23256144064662228702643157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15504096043108152468428771 23256144064662228702643157)
                  ·
                    refine ⟨545065876515520985218199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23256144064662228702643157 545065876515520985218199)
                    ·
                      rfl

theorem cell22_1592268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 1, 7].length) (baseStart_1592268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1592268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1592268 prefixEnd_1592268 := by exact prefixLift 1592268
  have htrace : WordTrace (prefixWord ++ tailWord_1592268) baseStart_1592268 baseEnd_1592268 := by
    simpa [prefixWord, tailWord_1592268, baseEnd_1592268] using wordTrace_append hprefix tailTrace_1592268
  have hstable : (prefixWord ++ tailWord_1592268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592268).length < 2 ^ (prefixWord ++ tailWord_1592268).sum := by decide
  have hdescent : baseEnd_1592268 < baseStart_1592268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592270 : List Nat := [4, 1, 1, 1, 2, 4, 1, 3, 5]
def baseStart_1592270 : Nat := 118140960795 + 1592270 * 2 ^ 59
def prefixEnd_1592270 : Nat := 4983230072969 + 3 ^ 40 * 1592270 * 2
def baseEnd_1592270 : Nat := 181688853718797882222731

theorem tailTrace_1592270 : CollatzResearch.WordTrace tailWord_1592270 prefixEnd_1592270 181688853718797882222731 := by
  unfold tailWord_1592270
  simp only [CollatzResearch.WordTrace]
  refine ⟨7259357242685650363876783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38716571960990135274009509 7259357242685650363876783)
  ·
    refine ⟨10889035864028475545815175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7259357242685650363876783 10889035864028475545815175)
    ·
      refine ⟨16333553796042713318722763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10889035864028475545815175 16333553796042713318722763)
      ·
        refine ⟨24500330694064069978084145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16333553796042713318722763 24500330694064069978084145)
        ·
          refine ⟨18375248020548052483563109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24500330694064069978084145 18375248020548052483563109)
          ·
            refine ⟨3445359003852759840668083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18375248020548052483563109 3445359003852759840668083)
            ·
              refine ⟨5168038505779139761002125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3445359003852759840668083 5168038505779139761002125)
              ·
                refine ⟨1938014439667177410375797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5168038505779139761002125 1938014439667177410375797)
                ·
                  refine ⟨181688853718797882222731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1938014439667177410375797 181688853718797882222731)
                  ·
                    rfl

theorem cell22_1592270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 3, 5].length) (baseStart_1592270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1592270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1592270 prefixEnd_1592270 := by exact prefixLift 1592270
  have htrace : WordTrace (prefixWord ++ tailWord_1592270) baseStart_1592270 baseEnd_1592270 := by
    simpa [prefixWord, tailWord_1592270, baseEnd_1592270] using wordTrace_append hprefix tailTrace_1592270
  have hstable : (prefixWord ++ tailWord_1592270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592270).length < 2 ^ (prefixWord ++ tailWord_1592270).sum := by decide
  have hdescent : baseEnd_1592270 < baseStart_1592270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592313 : List Nat := [1, 2, 1, 3, 1, 3, 1, 2, 3, 5]
def baseStart_1592313 : Nat := 118140960795 + 1592313 * 2 ^ 59
def prefixEnd_1592313 : Nat := 4983230072969 + 3 ^ 40 * 1592313 * 2
def baseEnd_1592313 : Nat := 545081280935155867843061

theorem tailTrace_1592313 : CollatzResearch.WordTrace tailWord_1592313 prefixEnd_1592313 545081280935155867843061 := by
  unfold tailWord_1592313
  simp only [CollatzResearch.WordTrace]
  refine ⟨58076426280329421254829593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38717617520219614169886395 58076426280329421254829593)
  ·
    refine ⟨43557319710247065941122195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58076426280329421254829593 43557319710247065941122195)
    ·
      refine ⟨65335979565370598911683293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43557319710247065941122195 65335979565370598911683293)
      ·
        refine ⟨24500992337013974591881235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65335979565370598911683293 24500992337013974591881235)
        ·
          refine ⟨36751488505520961887821853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24500992337013974591881235 36751488505520961887821853)
          ·
            refine ⟨13781808189570360707933195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36751488505520961887821853 13781808189570360707933195)
            ·
              refine ⟨20672712284355541061899793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13781808189570360707933195 20672712284355541061899793)
              ·
                refine ⟨15504534213266655796424845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20672712284355541061899793 15504534213266655796424845)
                ·
                  refine ⟨5814200329974995923659317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15504534213266655796424845 5814200329974995923659317)
                  ·
                    refine ⟨545081280935155867843061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5814200329974995923659317 545081280935155867843061)
                    ·
                      rfl

theorem cell22_1592313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 5].length) (baseStart_1592313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1592313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1592313 prefixEnd_1592313 := by exact prefixLift 1592313
  have htrace : WordTrace (prefixWord ++ tailWord_1592313) baseStart_1592313 baseEnd_1592313 := by
    simpa [prefixWord, tailWord_1592313, baseEnd_1592313] using wordTrace_append hprefix tailTrace_1592313
  have hstable : (prefixWord ++ tailWord_1592313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592313).length < 2 ^ (prefixWord ++ tailWord_1592313).sum := by decide
  have hdescent : baseEnd_1592313 < baseStart_1592313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592330 : List Nat := [3, 1, 2, 2, 3, 1, 1, 3, 1, 5]
def baseStart_1592330 : Nat := 118140960795 + 1592330 * 2 ^ 59
def prefixEnd_1592330 : Nat := 4983230072969 + 3 ^ 40 * 1592330 * 2
def baseEnd_1592330 : Nat := 545087100382573490168009

theorem tailTrace_1592330 : CollatzResearch.WordTrace tailWord_1592330 prefixEnd_1592330 545087100382573490168009 := by
  unfold tailWord_1592330
  simp only [CollatzResearch.WordTrace]
  refine ⟨14519261580316958289549611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38718030880845222105465629 14519261580316958289549611)
  ·
    refine ⟨21778892370475437434324417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14519261580316958289549611 21778892370475437434324417)
    ·
      refine ⟨16334169277856578075743313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21778892370475437434324417 16334169277856578075743313)
      ·
        refine ⟨12250626958392433556807485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16334169277856578075743313 12250626958392433556807485)
        ·
          refine ⟨4593985109397162583802807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12250626958392433556807485 4593985109397162583802807)
          ·
            refine ⟨6890977664095743875704211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4593985109397162583802807 6890977664095743875704211)
            ·
              refine ⟨10336466496143615813556317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6890977664095743875704211 10336466496143615813556317)
              ·
                refine ⟨3876174936053855930083619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10336466496143615813556317 3876174936053855930083619)
                ·
                  refine ⟨5814262404080783895125429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3876174936053855930083619 5814262404080783895125429)
                  ·
                    refine ⟨545087100382573490168009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5814262404080783895125429 545087100382573490168009)
                    ·
                      rfl

theorem cell22_1592330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_1592330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1592330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1592330 prefixEnd_1592330 := by exact prefixLift 1592330
  have htrace : WordTrace (prefixWord ++ tailWord_1592330) baseStart_1592330 baseEnd_1592330 := by
    simpa [prefixWord, tailWord_1592330, baseEnd_1592330] using wordTrace_append hprefix tailTrace_1592330
  have hstable : (prefixWord ++ tailWord_1592330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592330).length < 2 ^ (prefixWord ++ tailWord_1592330).sum := by decide
  have hdescent : baseEnd_1592330 < baseStart_1592330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592345 : List Nat := [1, 2, 1, 2, 1, 1, 7, 1, 2, 4]
def baseStart_1592345 : Nat := 118140960795 + 1592345 * 2 ^ 59
def prefixEnd_1592345 : Nat := 4983230072969 + 3 ^ 40 * 1592345 * 2
def baseEnd_1592345 : Nat := 545092235189118451042963

theorem tailTrace_1592345 : CollatzResearch.WordTrace tailWord_1592345 prefixEnd_1592345 545092235189118451042963 := by
  unfold tailWord_1592345
  simp only [CollatzResearch.WordTrace]
  refine ⟨58077593416213490719994489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38718395610808993813329659 58077593416213490719994489)
  ·
    refine ⟨43558195062160118039995867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58077593416213490719994489 43558195062160118039995867)
    ·
      refine ⟨65337292593240177059993801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43558195062160118039995867 65337292593240177059993801)
      ·
        refine ⟨49002969444930132794995351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65337292593240177059993801 49002969444930132794995351)
        ·
          refine ⟨73504454167395199192493027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49002969444930132794995351 73504454167395199192493027)
          ·
            refine ⟨110256681251092798788739541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73504454167395199192493027 110256681251092798788739541)
            ·
              refine ⟨2584140966822487471611083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 110256681251092798788739541 2584140966822487471611083)
              ·
                refine ⟨3876211450233731207416625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2584140966822487471611083 3876211450233731207416625)
                ·
                  refine ⟨2907158587675298405562469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3876211450233731207416625 2907158587675298405562469)
                  ·
                    refine ⟨545092235189118451042963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2907158587675298405562469 545092235189118451042963)
                    ·
                      rfl

theorem cell22_1592345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 2, 4].length) (baseStart_1592345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1592345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1592345 prefixEnd_1592345 := by exact prefixLift 1592345
  have htrace : WordTrace (prefixWord ++ tailWord_1592345) baseStart_1592345 baseEnd_1592345 := by
    simpa [prefixWord, tailWord_1592345, baseEnd_1592345] using wordTrace_append hprefix tailTrace_1592345
  have hstable : (prefixWord ++ tailWord_1592345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592345).length < 2 ^ (prefixWord ++ tailWord_1592345).sum := by decide
  have hdescent : baseEnd_1592345 < baseStart_1592345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592349 : List Nat := [1, 4, 2, 2, 3, 1, 2, 3, 4]
def baseStart_1592349 : Nat := 118140960795 + 1592349 * 2 ^ 59
def prefixEnd_1592349 : Nat := 4983230072969 + 3 ^ 40 * 1592349 * 2
def baseEnd_1592349 : Nat := 181697868156954591314317

theorem tailTrace_1592349 : CollatzResearch.WordTrace tailWord_1592349 prefixEnd_1592349 181697868156954591314317 := by
  unfold tailWord_1592349
  simp only [CollatzResearch.WordTrace]
  refine ⟨58077739308198999403140101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38718492872132666268760067 58077739308198999403140101)
  ·
    refine ⟨10889576120287312388088769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58077739308198999403140101 10889576120287312388088769)
    ·
      refine ⟨8167182090215484291066577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10889576120287312388088769 8167182090215484291066577)
      ·
        refine ⟨6125386567661613218299933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8167182090215484291066577 6125386567661613218299933)
        ·
          refine ⟨2297019962873104956862475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6125386567661613218299933 2297019962873104956862475)
          ·
            refine ⟨3445529944309657435293713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2297019962873104956862475 3445529944309657435293713)
            ·
              refine ⟨2584147458232243076470285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3445529944309657435293713 2584147458232243076470285)
              ·
                refine ⟨969055296837091153676357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2584147458232243076470285 969055296837091153676357)
                ·
                  refine ⟨181697868156954591314317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 969055296837091153676357 181697868156954591314317)
                  ·
                    rfl

theorem cell22_1592349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 3, 4].length) (baseStart_1592349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1592349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1592349 prefixEnd_1592349 := by exact prefixLift 1592349
  have htrace : WordTrace (prefixWord ++ tailWord_1592349) baseStart_1592349 baseEnd_1592349 := by
    simpa [prefixWord, tailWord_1592349, baseEnd_1592349] using wordTrace_append hprefix tailTrace_1592349
  have hstable : (prefixWord ++ tailWord_1592349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592349).length < 2 ^ (prefixWord ++ tailWord_1592349).sum := by decide
  have hdescent : baseEnd_1592349 < baseStart_1592349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592403 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 3, 7]
def baseStart_1592403 : Nat := 118140960795 + 1592403 * 2 ^ 59
def prefixEnd_1592403 : Nat := 4983230072969 + 3 ^ 40 * 1592403 * 2
def baseEnd_1592403 : Nat := 545112089774425633092785

theorem tailTrace_1592403 : CollatzResearch.WordTrace tailWord_1592403 prefixEnd_1592403 545112089774425633092785 := by
  unfold tailWord_1592403
  simp only [CollatzResearch.WordTrace]
  refine ⟨58079708850003366625605863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38719805900002244417070575 58079708850003366625605863)
  ·
    refine ⟨87119563275005049938408795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58079708850003366625605863 87119563275005049938408795)
    ·
      refine ⟨130679344912507574907613193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87119563275005049938408795 130679344912507574907613193)
      ·
        refine ⟨98009508684380681180709895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130679344912507574907613193 98009508684380681180709895)
        ·
          refine ⟨147014263026571021771064843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98009508684380681180709895 147014263026571021771064843)
          ·
            refine ⟨220521394539856532656597265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147014263026571021771064843 220521394539856532656597265)
            ·
              refine ⟨165391045904892399492447949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220521394539856532656597265 165391045904892399492447949)
              ·
                refine ⟨62021642214334649809667981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 165391045904892399492447949 62021642214334649809667981)
                ·
                  refine ⟨23258115830375493678625493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62021642214334649809667981 23258115830375493678625493)
                  ·
                    refine ⟨545112089774425633092785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23258115830375493678625493 545112089774425633092785)
                    ·
                      rfl

theorem cell22_1592403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 7].length) (baseStart_1592403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1592403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1592403 prefixEnd_1592403 := by exact prefixLift 1592403
  have htrace : WordTrace (prefixWord ++ tailWord_1592403) baseStart_1592403 baseEnd_1592403 := by
    simpa [prefixWord, tailWord_1592403, baseEnd_1592403] using wordTrace_append hprefix tailTrace_1592403
  have hstable : (prefixWord ++ tailWord_1592403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592403).length < 2 ^ (prefixWord ++ tailWord_1592403).sum := by decide
  have hdescent : baseEnd_1592403 < baseStart_1592403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592452 : List Nat := [2, 3, 2, 1, 2, 3, 1, 1, 3, 4]
def baseStart_1592452 : Nat := 118140960795 + 1592452 * 2 ^ 59
def prefixEnd_1592452 : Nat := 4983230072969 + 3 ^ 40 * 1592452 * 2
def baseEnd_1592452 : Nat := 545128863475805838617635

theorem tailTrace_1592452 : CollatzResearch.WordTrace tailWord_1592452 prefixEnd_1592452 545128863475805838617635 := by
  unfold tailWord_1592452
  simp only [CollatzResearch.WordTrace]
  refine ⟨29040748013412923997069805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38720997351217231996093073 29040748013412923997069805)
  ·
    refine ⟨10890280505029846498901177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29040748013412923997069805 10890280505029846498901177)
    ·
      refine ⟨8167710378772384874175883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10890280505029846498901177 8167710378772384874175883)
      ·
        refine ⟨12251565568158577311263825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8167710378772384874175883 12251565568158577311263825)
        ·
          refine ⟨9188674176118932983447869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12251565568158577311263825 9188674176118932983447869)
          ·
            refine ⟨3445752816044599868792951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9188674176118932983447869 3445752816044599868792951)
            ·
              refine ⟨5168629224066899803189427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3445752816044599868792951 5168629224066899803189427)
              ·
                refine ⟨7752943836100349704784141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5168629224066899803189427 7752943836100349704784141)
                ·
                  refine ⟨2907353938537631139294053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7752943836100349704784141 2907353938537631139294053)
                  ·
                    refine ⟨545128863475805838617635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2907353938537631139294053 545128863475805838617635)
                    ·
                      rfl

theorem cell22_1592452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_1592452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1592452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1592452 prefixEnd_1592452 := by exact prefixLift 1592452
  have htrace : WordTrace (prefixWord ++ tailWord_1592452) baseStart_1592452 baseEnd_1592452 := by
    simpa [prefixWord, tailWord_1592452, baseEnd_1592452] using wordTrace_append hprefix tailTrace_1592452
  have hstable : (prefixWord ++ tailWord_1592452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592452).length < 2 ^ (prefixWord ++ tailWord_1592452).sum := by decide
  have hdescent : baseEnd_1592452 < baseStart_1592452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592484 : List Nat := [2, 3, 1, 2, 3, 2, 1, 4, 4]
def baseStart_1592484 : Nat := 118140960795 + 1592484 * 2 ^ 59
def prefixEnd_1592484 : Nat := 4983230072969 + 3 ^ 40 * 1592484 * 2
def baseEnd_1592484 : Nat := 181713272576589473939179

theorem tailTrace_1592484 : CollatzResearch.WordTrace tailWord_1592484 prefixEnd_1592484 181713272576589473939179 := by
  unfold tailWord_1592484
  simp only [CollatzResearch.WordTrace]
  refine ⟨29041331581354958729652253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38721775441806611639536337 29041331581354958729652253)
  ·
    refine ⟨10890499343008109523619595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29041331581354958729652253 10890499343008109523619595)
    ·
      refine ⟨16335749014512164285429393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10890499343008109523619595 16335749014512164285429393)
      ·
        refine ⟨12251811760884123214072045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16335749014512164285429393 12251811760884123214072045)
        ·
          refine ⟨4594429410331546205277017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12251811760884123214072045 4594429410331546205277017)
          ·
            refine ⟨3445822057748659653957763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4594429410331546205277017 3445822057748659653957763)
            ·
              refine ⟨5168733086622989480936645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3445822057748659653957763 5168733086622989480936645)
              ·
                refine ⟨969137453741810527675621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5168733086622989480936645 969137453741810527675621)
                ·
                  refine ⟨181713272576589473939179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 969137453741810527675621 181713272576589473939179)
                  ·
                    rfl

theorem cell22_1592484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 4, 4].length) (baseStart_1592484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1592484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1592484 prefixEnd_1592484 := by exact prefixLift 1592484
  have htrace : WordTrace (prefixWord ++ tailWord_1592484) baseStart_1592484 baseEnd_1592484 := by
    simpa [prefixWord, tailWord_1592484, baseEnd_1592484] using wordTrace_append hprefix tailTrace_1592484
  have hstable : (prefixWord ++ tailWord_1592484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592484).length < 2 ^ (prefixWord ++ tailWord_1592484).sum := by decide
  have hdescent : baseEnd_1592484 < baseStart_1592484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592495 : List Nat := [1, 1, 2, 1, 2, 3, 5, 7]
def baseStart_1592495 : Nat := 118140960795 + 1592495 * 2 ^ 59
def prefixEnd_1592495 : Nat := 4983230072969 + 3 ^ 40 * 1592495 * 2
def baseEnd_1592495 : Nat := 60571509250507562199167

theorem tailTrace_1592495 : CollatzResearch.WordTrace tailWord_1592495 prefixEnd_1592495 60571509250507562199167 := by
  unfold tailWord_1592495
  simp only [CollatzResearch.WordTrace]
  refine ⟨58083064365670066337954939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38722042910446710891969959 58083064365670066337954939)
  ·
    refine ⟨87124596548505099506932409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58083064365670066337954939 87124596548505099506932409)
    ·
      refine ⟨65343447411378824630199307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87124596548505099506932409 65343447411378824630199307)
      ·
        refine ⟨98015171117068236945298961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65343447411378824630199307 98015171117068236945298961)
        ·
          refine ⟨73511378337801177708974221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98015171117068236945298961 73511378337801177708974221)
          ·
            refine ⟨27566766876675441640865333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73511378337801177708974221 27566766876675441640865333)
            ·
              refine ⟨2584384394688322653831125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27566766876675441640865333 2584384394688322653831125)
              ·
                refine ⟨60571509250507562199167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2584384394688322653831125 60571509250507562199167)
                ·
                  rfl

theorem cell22_1592495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 7].length) (baseStart_1592495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1592495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1592495 prefixEnd_1592495 := by exact prefixLift 1592495
  have htrace : WordTrace (prefixWord ++ tailWord_1592495) baseStart_1592495 baseEnd_1592495 := by
    simpa [prefixWord, tailWord_1592495, baseEnd_1592495] using wordTrace_append hprefix tailTrace_1592495
  have hstable : (prefixWord ++ tailWord_1592495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592495).length < 2 ^ (prefixWord ++ tailWord_1592495).sum := by decide
  have hdescent : baseEnd_1592495 < baseStart_1592495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592544 : List Nat := [2, 1, 1, 3, 1, 5, 2, 1, 3, 3]
def baseStart_1592544 : Nat := 118140960795 + 1592544 * 2 ^ 59
def prefixEnd_1592544 : Nat := 4983230072969 + 3 ^ 40 * 1592544 * 2
def baseEnd_1592544 : Nat := 545160356955948265317353

theorem tailTrace_1592544 : CollatzResearch.WordTrace tailWord_1592544 prefixEnd_1592544 545160356955948265317353 := by
  unfold tailWord_1592544
  simp only [CollatzResearch.WordTrace]
  refine ⟨29042425771246273853244343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38723234361661698470992457 29042425771246273853244343)
  ·
    refine ⟨43563638656869410779866515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29042425771246273853244343 43563638656869410779866515)
    ·
      refine ⟨65345457985304116169799773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43563638656869410779866515 65345457985304116169799773)
      ·
        refine ⟨24504546744489043563674915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65345457985304116169799773 24504546744489043563674915)
        ·
          refine ⟨36756820116733565345512373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24504546744489043563674915 36756820116733565345512373)
          ·
            refine ⟨3445951885943771751141785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36756820116733565345512373 3445951885943771751141785)
            ·
              refine ⟨2584463914457828813356339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3445951885943771751141785 2584463914457828813356339)
              ·
                refine ⟨3876695871686743220034509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2584463914457828813356339 3876695871686743220034509)
                ·
                  refine ⟨1453760951882528707512941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3876695871686743220034509 1453760951882528707512941)
                  ·
                    refine ⟨545160356955948265317353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1453760951882528707512941 545160356955948265317353)
                    ·
                      rfl

theorem cell22_1592544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 3, 3].length) (baseStart_1592544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1592544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1592544 prefixEnd_1592544 := by exact prefixLift 1592544
  have htrace : WordTrace (prefixWord ++ tailWord_1592544) baseStart_1592544 baseEnd_1592544 := by
    simpa [prefixWord, tailWord_1592544, baseEnd_1592544] using wordTrace_append hprefix tailTrace_1592544
  have hstable : (prefixWord ++ tailWord_1592544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592544).length < 2 ^ (prefixWord ++ tailWord_1592544).sum := by decide
  have hdescent : baseEnd_1592544 < baseStart_1592544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592608 : List Nat := [2, 1, 1, 5, 4, 1, 2, 1, 5]
def baseStart_1592608 : Nat := 118140960795 + 1592608 * 2 ^ 59
def prefixEnd_1592608 : Nat := 4983230072969 + 3 ^ 40 * 1592608 * 2
def baseEnd_1592608 : Nat := 181727421821291143905719

theorem tailTrace_1592608 : CollatzResearch.WordTrace tailWord_1592608 prefixEnd_1592608 181727421821291143905719 := by
  unfold tailWord_1592608
  simp only [CollatzResearch.WordTrace]
  refine ⟨29043592907130343318409239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38724790542840457757878985 29043592907130343318409239)
  ·
    refine ⟨43565389360695514977613859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29043592907130343318409239 43565389360695514977613859)
    ·
      refine ⟨65348084041043272466420789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43565389360695514977613859 65348084041043272466420789)
      ·
        refine ⟨6126382878847806793726949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65348084041043272466420789 6126382878847806793726949)
        ·
          refine ⟨1148696789783963773823803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6126382878847806793726949 1148696789783963773823803)
          ·
            refine ⟨1723045184675945660735705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1148696789783963773823803 1723045184675945660735705)
            ·
              refine ⟨1292283888506959245551779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1723045184675945660735705 1292283888506959245551779)
              ·
                refine ⟨1938425832760438868327669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1292283888506959245551779 1938425832760438868327669)
                ·
                  refine ⟨181727421821291143905719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1938425832760438868327669 181727421821291143905719)
                  ·
                    rfl

theorem cell22_1592608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 1, 5].length) (baseStart_1592608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1592608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1592608 prefixEnd_1592608 := by exact prefixLift 1592608
  have htrace : WordTrace (prefixWord ++ tailWord_1592608) baseStart_1592608 baseEnd_1592608 := by
    simpa [prefixWord, tailWord_1592608, baseEnd_1592608] using wordTrace_append hprefix tailTrace_1592608
  have hstable : (prefixWord ++ tailWord_1592608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592608).length < 2 ^ (prefixWord ++ tailWord_1592608).sum := by decide
  have hdescent : baseEnd_1592608 < baseStart_1592608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592621 : List Nat := [1, 5, 3, 1, 1, 2, 1, 1, 3, 4]
def baseStart_1592621 : Nat := 118140960795 + 1592621 * 2 ^ 59
def prefixEnd_1592621 : Nat := 4983230072969 + 3 ^ 40 * 1592621 * 2
def baseEnd_1592621 : Nat := 545186715629545731142117

theorem tailTrace_1592621 : CollatzResearch.WordTrace tailWord_1592621 prefixEnd_1592621 545186715629545731142117 := by
  unfold tailWord_1592621
  simp only [CollatzResearch.WordTrace]
  refine ⟨58087659963213589857041717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38725106642142393238027811 58087659963213589857041717)
  ·
    refine ⟨5445718121551274049097661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58087659963213589857041717 5445718121551274049097661)
    ·
      refine ⟨2042144295581727768411623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5445718121551274049097661 2042144295581727768411623)
      ·
        refine ⟨3063216443372591652617435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2042144295581727768411623 3063216443372591652617435)
        ·
          refine ⟨4594824665058887478926153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3063216443372591652617435 4594824665058887478926153)
          ·
            refine ⟨3446118498794165609194615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4594824665058887478926153 3446118498794165609194615)
            ·
              refine ⟨5169177748191248413791923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3446118498794165609194615 5169177748191248413791923)
              ·
                refine ⟨7753766622286872620687885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5169177748191248413791923 7753766622286872620687885)
                ·
                  refine ⟨2907662483357577232757957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7753766622286872620687885 2907662483357577232757957)
                  ·
                    refine ⟨545186715629545731142117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2907662483357577232757957 545186715629545731142117)
                    ·
                      rfl

theorem cell22_1592621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_1592621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1592621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1592621 prefixEnd_1592621 := by exact prefixLift 1592621
  have htrace : WordTrace (prefixWord ++ tailWord_1592621) baseStart_1592621 baseEnd_1592621 := by
    simpa [prefixWord, tailWord_1592621, baseEnd_1592621] using wordTrace_append hprefix tailTrace_1592621
  have hstable : (prefixWord ++ tailWord_1592621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592621).length < 2 ^ (prefixWord ++ tailWord_1592621).sum := by decide
  have hdescent : baseEnd_1592621 < baseStart_1592621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592646 : List Nat := [6, 1, 1, 3, 2, 1, 2, 2, 1, 3]
def baseStart_1592646 : Nat := 118140960795 + 1592646 * 2 ^ 59
def prefixEnd_1592646 : Nat := 4983230072969 + 3 ^ 40 * 1592646 * 2
def baseEnd_1592646 : Nat := 545195273640453999267041

theorem tailTrace_1592646 : CollatzResearch.WordTrace tailWord_1592646 prefixEnd_1592646 545195273640453999267041 := by
  unfold tailWord_1592646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1815267868378844347709431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 38725714525415346084467861 1815267868378844347709431)
  ·
    refine ⟨2722901802568266521564147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1815267868378844347709431 2722901802568266521564147)
    ·
      refine ⟨4084352703852399782346221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2722901802568266521564147 4084352703852399782346221)
      ·
        refine ⟨1531632263944649918379833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4084352703852399782346221 1531632263944649918379833)
        ·
          refine ⟨1148724197958487438784875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1531632263944649918379833 1148724197958487438784875)
          ·
            refine ⟨1723086296937731158177313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1148724197958487438784875 1723086296937731158177313)
            ·
              refine ⟨1292314722703298368632985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1723086296937731158177313 1292314722703298368632985)
              ·
                refine ⟨969236042027473776474739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1292314722703298368632985 969236042027473776474739)
                ·
                  refine ⟨1453854063041210664712109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 969236042027473776474739 1453854063041210664712109)
                  ·
                    refine ⟨545195273640453999267041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1453854063041210664712109 545195273640453999267041)
                    ·
                      rfl

theorem cell22_1592646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_1592646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1592646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1592646 prefixEnd_1592646 := by exact prefixLift 1592646
  have htrace : WordTrace (prefixWord ++ tailWord_1592646) baseStart_1592646 baseEnd_1592646 := by
    simpa [prefixWord, tailWord_1592646, baseEnd_1592646] using wordTrace_append hprefix tailTrace_1592646
  have hstable : (prefixWord ++ tailWord_1592646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592646).length < 2 ^ (prefixWord ++ tailWord_1592646).sum := by decide
  have hdescent : baseEnd_1592646 < baseStart_1592646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592677 : List Nat := [1, 3, 1, 3, 1, 2, 1, 2, 2, 6]
def baseStart_1592677 : Nat := 118140960795 + 1592677 * 2 ^ 59
def prefixEnd_1592677 : Nat := 4983230072969 + 3 ^ 40 * 1592677 * 2
def baseEnd_1592677 : Nat := 545205885573980251741945

theorem tailTrace_1592677 : CollatzResearch.WordTrace tailWord_1592677 prefixEnd_1592677 545205885573980251741945 := by
  unfold tailWord_1592677
  simp only [CollatzResearch.WordTrace]
  refine ⟨58089702451010711421080285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38726468300673807614053523 58089702451010711421080285)
  ·
    refine ⟨21783638419129016782905107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58089702451010711421080285 21783638419129016782905107)
    ·
      refine ⟨32675457628693525174357661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21783638419129016782905107 32675457628693525174357661)
      ·
        refine ⟨12253296610760071940384123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32675457628693525174357661 12253296610760071940384123)
        ·
          refine ⟨18379944916140107910576185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12253296610760071940384123 18379944916140107910576185)
          ·
            refine ⟨13784958687105080932932139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18379944916140107910576185 13784958687105080932932139)
            ·
              refine ⟨20677438030657621399398209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13784958687105080932932139 20677438030657621399398209)
              ·
                refine ⟨15508078522993216049548657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20677438030657621399398209 15508078522993216049548657)
                ·
                  refine ⟨11631058892244912037161493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15508078522993216049548657 11631058892244912037161493)
                  ·
                    refine ⟨545205885573980251741945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11631058892244912037161493 545205885573980251741945)
                    ·
                      rfl

theorem cell22_1592677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 6].length) (baseStart_1592677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1592677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1592677 prefixEnd_1592677 := by exact prefixLift 1592677
  have htrace : WordTrace (prefixWord ++ tailWord_1592677) baseStart_1592677 baseEnd_1592677 := by
    simpa [prefixWord, tailWord_1592677, baseEnd_1592677] using wordTrace_append hprefix tailTrace_1592677
  have hstable : (prefixWord ++ tailWord_1592677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592677).length < 2 ^ (prefixWord ++ tailWord_1592677).sum := by decide
  have hdescent : baseEnd_1592677 < baseStart_1592677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592702 : List Nat := [4, 2, 3, 2, 1, 2, 1, 2, 2, 3]
def baseStart_1592702 : Nat := 118140960795 + 1592702 * 2 ^ 59
def prefixEnd_1592702 : Nat := 4983230072969 + 3 ^ 40 * 1592702 * 2
def baseEnd_1592702 : Nat := 545214443584888519866869

theorem tailTrace_1592702 : CollatzResearch.WordTrace tailWord_1592702 prefixEnd_1592702 545214443584888519866869 := by
  unfold tailWord_1592702
  simp only [CollatzResearch.WordTrace]
  refine ⟨7261326784490017586342545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38727076183946760460493573 7261326784490017586342545)
  ·
    refine ⟨5445995088367513189756909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7261326784490017586342545 5445995088367513189756909)
    ·
      refine ⟨2042248158137817446158841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5445995088367513189756909 2042248158137817446158841)
      ·
        refine ⟨1531686118603363084619131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2042248158137817446158841 1531686118603363084619131)
        ·
          refine ⟨2297529177905044626928697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1531686118603363084619131 2297529177905044626928697)
          ·
            refine ⟨1723146883428783470196523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2297529177905044626928697 1723146883428783470196523)
            ·
              refine ⟨2584720325143175205294785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1723146883428783470196523 2584720325143175205294785)
              ·
                refine ⟨1938540243857381403971089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2584720325143175205294785 1938540243857381403971089)
                ·
                  refine ⟨1453905182893036052978317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1938540243857381403971089 1453905182893036052978317)
                  ·
                    refine ⟨545214443584888519866869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1453905182893036052978317 545214443584888519866869)
                    ·
                      rfl

theorem cell22_1592702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_1592702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1592702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1592702 prefixEnd_1592702 := by exact prefixLift 1592702
  have htrace : WordTrace (prefixWord ++ tailWord_1592702) baseStart_1592702 baseEnd_1592702 := by
    simpa [prefixWord, tailWord_1592702, baseEnd_1592702] using wordTrace_append hprefix tailTrace_1592702
  have hstable : (prefixWord ++ tailWord_1592702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592702).length < 2 ^ (prefixWord ++ tailWord_1592702).sum := by decide
  have hdescent : baseEnd_1592702 < baseStart_1592702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592709 : List Nat := [1, 3, 1, 1, 3, 1, 5, 2, 5]
def baseStart_1592709 : Nat := 118140960795 + 1592709 * 2 ^ 59
def prefixEnd_1592709 : Nat := 4983230072969 + 3 ^ 40 * 1592709 * 2
def baseEnd_1592709 : Nat := 181738946609314278313949

theorem tailTrace_1592709 : CollatzResearch.WordTrace tailWord_1592709 prefixEnd_1592709 181738946609314278313949 := by
  unfold tailWord_1592709
  simp only [CollatzResearch.WordTrace]
  refine ⟨58090869586894780886245181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38727246391263187257496787 58090869586894780886245181)
  ·
    refine ⟨21784076095085542832341943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58090869586894780886245181 21784076095085542832341943)
    ·
      refine ⟨32676114142628314248512915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21784076095085542832341943 32676114142628314248512915)
      ·
        refine ⟨49014171213942471372769373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32676114142628314248512915 49014171213942471372769373)
        ·
          refine ⟨18380314205228426764788515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49014171213942471372769373 18380314205228426764788515)
          ·
            refine ⟨27570471307842640147182773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18380314205228426764788515 27570471307842640147182773)
            ·
              refine ⟨2584731685110247513798385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27570471307842640147182773 2584731685110247513798385)
              ·
                refine ⟨1938548763832685635348789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2584731685110247513798385 1938548763832685635348789)
                ·
                  refine ⟨181738946609314278313949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1938548763832685635348789 181738946609314278313949)
                  ·
                    rfl

theorem cell22_1592709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 2, 5].length) (baseStart_1592709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1592709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1592709 prefixEnd_1592709 := by exact prefixLift 1592709
  have htrace : WordTrace (prefixWord ++ tailWord_1592709) baseStart_1592709 baseEnd_1592709 := by
    simpa [prefixWord, tailWord_1592709, baseEnd_1592709] using wordTrace_append hprefix tailTrace_1592709
  have hstable : (prefixWord ++ tailWord_1592709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592709).length < 2 ^ (prefixWord ++ tailWord_1592709).sum := by decide
  have hdescent : baseEnd_1592709 < baseStart_1592709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592790 : List Nat := [5, 2, 1, 1, 1, 4, 1, 2, 1, 4]
def baseStart_1592790 : Nat := 118140960795 + 1592790 * 2 ^ 59
def prefixEnd_1592790 : Nat := 4983230072969 + 3 ^ 40 * 1592790 * 2
def baseEnd_1592790 : Nat := 545244567783285623666599

theorem tailTrace_1592790 : CollatzResearch.WordTrace tailWord_1592790 prefixEnd_1592790 545244567783285623666599 := by
  unfold tailWord_1592790
  simp only [CollatzResearch.WordTrace]
  refine ⟨3630863993725083232496489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38729215933067554479962549 3630863993725083232496489)
  ·
    refine ⟨2723147995293812424372367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3630863993725083232496489 2723147995293812424372367)
    ·
      refine ⟨4084721992940718636558551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2723147995293812424372367 4084721992940718636558551)
      ·
        refine ⟨6127082989411077954837827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4084721992940718636558551 6127082989411077954837827)
        ·
          refine ⟨9190624484116616932256741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6127082989411077954837827 9190624484116616932256741)
          ·
            refine ⟨1723242090771865674798139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9190624484116616932256741 1723242090771865674798139)
            ·
              refine ⟨2584863136157798512197209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1723242090771865674798139 2584863136157798512197209)
              ·
                refine ⟨1938647352118348884147907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2584863136157798512197209 1938647352118348884147907)
                ·
                  refine ⟨2907971028177523326221861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1938647352118348884147907 2907971028177523326221861)
                  ·
                    refine ⟨545244567783285623666599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2907971028177523326221861 545244567783285623666599)
                    ·
                      rfl

theorem cell22_1592790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_1592790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1592790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1592790 prefixEnd_1592790 := by exact prefixLift 1592790
  have htrace : WordTrace (prefixWord ++ tailWord_1592790) baseStart_1592790 baseEnd_1592790 := by
    simpa [prefixWord, tailWord_1592790, baseEnd_1592790] using wordTrace_append hprefix tailTrace_1592790
  have hstable : (prefixWord ++ tailWord_1592790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592790).length < 2 ^ (prefixWord ++ tailWord_1592790).sum := by decide
  have hdescent : baseEnd_1592790 < baseStart_1592790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592801 : List Nat := [1, 2, 3, 1, 2, 4, 2, 1, 2, 4]
def baseStart_1592801 : Nat := 118140960795 + 1592801 * 2 ^ 59
def prefixEnd_1592801 : Nat := 4983230072969 + 3 ^ 40 * 1592801 * 2
def baseEnd_1592801 : Nat := 545248333308085261641565

theorem tailTrace_1592801 : CollatzResearch.WordTrace tailWord_1592801 prefixEnd_1592801 545248333308085261641565 := by
  unfold tailWord_1592801
  simp only [CollatzResearch.WordTrace]
  refine ⟨58094225102561480598594257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38729483401707653732396171 58094225102561480598594257)
  ·
    refine ⟨43570668826921110448945693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58094225102561480598594257 43570668826921110448945693)
    ·
      refine ⟨16339000810095416418354635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43570668826921110448945693 16339000810095416418354635)
      ·
        refine ⟨24508501215143124627531953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16339000810095416418354635 24508501215143124627531953)
        ·
          refine ⟨18381375911357343470648965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24508501215143124627531953 18381375911357343470648965)
          ·
            refine ⟨3446507983379501900746681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18381375911357343470648965 3446507983379501900746681)
            ·
              refine ⟨2584880987534626425560011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3446507983379501900746681 2584880987534626425560011)
              ·
                refine ⟨3877321481301939638340017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2584880987534626425560011 3877321481301939638340017)
                ·
                  refine ⟨2907991110976454728755013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3877321481301939638340017 2907991110976454728755013)
                  ·
                    refine ⟨545248333308085261641565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2907991110976454728755013 545248333308085261641565)
                    ·
                      rfl

theorem cell22_1592801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_1592801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1592801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1592801 prefixEnd_1592801 := by exact prefixLift 1592801
  have htrace : WordTrace (prefixWord ++ tailWord_1592801) baseStart_1592801 baseEnd_1592801 := by
    simpa [prefixWord, tailWord_1592801, baseEnd_1592801] using wordTrace_append hprefix tailTrace_1592801
  have hstable : (prefixWord ++ tailWord_1592801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592801).length < 2 ^ (prefixWord ++ tailWord_1592801).sum := by decide
  have hdescent : baseEnd_1592801 < baseStart_1592801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592829 : List Nat := [1, 4, 1, 1, 1, 4, 1, 1, 2, 6]
def baseStart_1592829 : Nat := 118140960795 + 1592829 * 2 ^ 59
def prefixEnd_1592829 : Nat := 4983230072969 + 3 ^ 40 * 1592829 * 2
def baseEnd_1592829 : Nat := 545257918280302521941479

theorem tailTrace_1592829 : CollatzResearch.WordTrace tailWord_1592829 prefixEnd_1592829 545257918280302521941479 := by
  unfold tailWord_1592829
  simp only [CollatzResearch.WordTrace]
  refine ⟨58095246346460041380613541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38730164230973360920409027 58095246346460041380613541)
  ·
    refine ⟨10892858689961257758865039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58095246346460041380613541 10892858689961257758865039)
    ·
      refine ⟨16339288034941886638297559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10892858689961257758865039 16339288034941886638297559)
      ·
        refine ⟨24508932052412829957446339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16339288034941886638297559 24508932052412829957446339)
        ·
          refine ⟨36763398078619244936169509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24508932052412829957446339 36763398078619244936169509)
          ·
            refine ⟨6893137139741108425531783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36763398078619244936169509 6893137139741108425531783)
            ·
              refine ⟨10339705709611662638297675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6893137139741108425531783 10339705709611662638297675)
              ·
                refine ⟨15509558564417493957446513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10339705709611662638297675 15509558564417493957446513)
                ·
                  refine ⟨11632168923313120468084885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15509558564417493957446513 11632168923313120468084885)
                  ·
                    refine ⟨545257918280302521941479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11632168923313120468084885 545257918280302521941479)
                    ·
                      rfl

theorem cell22_1592829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_1592829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1592829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1592829 prefixEnd_1592829 := by exact prefixLift 1592829
  have htrace : WordTrace (prefixWord ++ tailWord_1592829) baseStart_1592829 baseEnd_1592829 := by
    simpa [prefixWord, tailWord_1592829, baseEnd_1592829] using wordTrace_append hprefix tailTrace_1592829
  have hstable : (prefixWord ++ tailWord_1592829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592829).length < 2 ^ (prefixWord ++ tailWord_1592829).sum := by decide
  have hdescent : baseEnd_1592829 < baseStart_1592829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592833 : List Nat := [1, 2, 4, 1, 5, 1, 1, 7]
def baseStart_1592833 : Nat := 118140960795 + 1592833 * 2 ^ 59
def prefixEnd_1592833 : Nat := 4983230072969 + 3 ^ 40 * 1592833 * 2
def baseEnd_1592833 : Nat := 60584365284671982760163

theorem tailTrace_1592833 : CollatzResearch.WordTrace tailWord_1592833 prefixEnd_1592833 60584365284671982760163 := by
  unfold tailWord_1592833
  simp only [CollatzResearch.WordTrace]
  refine ⟨58095392238445550063759153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38730261492297033375839435 58095392238445550063759153)
  ·
    refine ⟨43571544178834162547819365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58095392238445550063759153 43571544178834162547819365)
    ·
      refine ⟨8169664533531405477716131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43571544178834162547819365 8169664533531405477716131)
      ·
        refine ⟨12254496800297108216574197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8169664533531405477716131 12254496800297108216574197)
        ·
          refine ⟨1148859075027853895303831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12254496800297108216574197 1148859075027853895303831)
          ·
            refine ⟨1723288612541780842955747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1148859075027853895303831 1723288612541780842955747)
            ·
              refine ⟨2584932918812671264433621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1723288612541780842955747 2584932918812671264433621)
              ·
                refine ⟨60584365284671982760163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2584932918812671264433621 60584365284671982760163)
                ·
                  rfl

theorem cell22_1592833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 7].length) (baseStart_1592833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1592833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1592833 prefixEnd_1592833 := by exact prefixLift 1592833
  have htrace : WordTrace (prefixWord ++ tailWord_1592833) baseStart_1592833 baseEnd_1592833 := by
    simpa [prefixWord, tailWord_1592833, baseEnd_1592833] using wordTrace_append hprefix tailTrace_1592833
  have hstable : (prefixWord ++ tailWord_1592833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592833).length < 2 ^ (prefixWord ++ tailWord_1592833).sum := by decide
  have hdescent : baseEnd_1592833 < baseStart_1592833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592852 : List Nat := [2, 4, 3, 1, 3, 1, 1, 1, 2, 4]
def baseStart_1592852 : Nat := 118140960795 + 1592852 * 2 ^ 59
def prefixEnd_1592852 : Nat := 4983230072969 + 3 ^ 40 * 1592852 * 2
def baseEnd_1592852 : Nat := 545265791650338128616409

theorem tailTrace_1592852 : CollatzResearch.WordTrace tailWord_1592852 prefixEnd_1592852 545265791650338128616409 := by
  unfold tailWord_1592852
  simp only [CollatzResearch.WordTrace]
  refine ⟨29048042612688358154350405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38730723483584477539133873 29048042612688358154350405)
  ·
    refine ⟨5446507989879067153940701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29048042612688358154350405 5446507989879067153940701)
    ·
      refine ⟨2042440496204650182727763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5446507989879067153940701 2042440496204650182727763)
      ·
        refine ⟨3063660744306975274091645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2042440496204650182727763 3063660744306975274091645)
        ·
          refine ⟨1148872779115115727784367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3063660744306975274091645 1148872779115115727784367)
          ·
            refine ⟨1723309168672673591676551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1148872779115115727784367 1723309168672673591676551)
            ·
              refine ⟨2584963753009010387514827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1723309168672673591676551 2584963753009010387514827)
              ·
                refine ⟨3877445629513515581272241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2584963753009010387514827 3877445629513515581272241)
                ·
                  refine ⟨2908084222135136685954181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3877445629513515581272241 2908084222135136685954181)
                  ·
                    refine ⟨545265791650338128616409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2908084222135136685954181 545265791650338128616409)
                    ·
                      rfl

theorem cell22_1592852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_1592852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1592852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1592852 prefixEnd_1592852 := by exact prefixLift 1592852
  have htrace : WordTrace (prefixWord ++ tailWord_1592852) baseStart_1592852 baseEnd_1592852 := by
    simpa [prefixWord, tailWord_1592852, baseEnd_1592852] using wordTrace_append hprefix tailTrace_1592852
  have hstable : (prefixWord ++ tailWord_1592852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592852).length < 2 ^ (prefixWord ++ tailWord_1592852).sum := by decide
  have hdescent : baseEnd_1592852 < baseStart_1592852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592865 : List Nat := [1, 2, 3, 2, 2, 3, 2, 3, 1, 3]
def baseStart_1592865 : Nat := 118140960795 + 1592865 * 2 ^ 59
def prefixEnd_1592865 : Nat := 4983230072969 + 3 ^ 40 * 1592865 * 2
def baseEnd_1592865 : Nat := 545270241816010428041369

theorem tailTrace_1592865 : CollatzResearch.WordTrace tailWord_1592865 prefixEnd_1592865 545270241816010428041369 := by
  unfold tailWord_1592865
  simp only [CollatzResearch.WordTrace]
  refine ⟨58096559374329619528924049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38731039582886413019282699 58096559374329619528924049)
  ·
    refine ⟨43572419530747214646693037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58096559374329619528924049 43572419530747214646693037)
    ·
      refine ⟨16339657324030205492509889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43572419530747214646693037 16339657324030205492509889)
      ·
        refine ⟨12254742993022654119382417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16339657324030205492509889 12254742993022654119382417)
        ·
          refine ⟨9191057244766990589536813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12254742993022654119382417 9191057244766990589536813)
          ·
            refine ⟨3446646466787621471076305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9191057244766990589536813 3446646466787621471076305)
            ·
              refine ⟨2584984850090716103307229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3446646466787621471076305 2584984850090716103307229)
              ·
                refine ⟨969369318784018538740211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2584984850090716103307229 969369318784018538740211)
                ·
                  refine ⟨1454053978176027808110317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 969369318784018538740211 1454053978176027808110317)
                  ·
                    refine ⟨545270241816010428041369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1454053978176027808110317 545270241816010428041369)
                    ·
                      rfl

theorem cell22_1592865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 3, 1, 3].length) (baseStart_1592865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1592865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1592865 prefixEnd_1592865 := by exact prefixLift 1592865
  have htrace : WordTrace (prefixWord ++ tailWord_1592865) baseStart_1592865 baseEnd_1592865 := by
    simpa [prefixWord, tailWord_1592865, baseEnd_1592865] using wordTrace_append hprefix tailTrace_1592865
  have hstable : (prefixWord ++ tailWord_1592865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592865).length < 2 ^ (prefixWord ++ tailWord_1592865).sum := by decide
  have hdescent : baseEnd_1592865 < baseStart_1592865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592878 : List Nat := [4, 1, 3, 1, 2, 1, 3, 2, 5]
def baseStart_1592878 : Nat := 118140960795 + 1592878 * 2 ^ 59
def prefixEnd_1592878 : Nat := 4983230072969 + 3 ^ 40 * 1592878 * 2
def baseEnd_1592878 : Nat := 181758230660560909155443

theorem tailTrace_1592878 : CollatzResearch.WordTrace tailWord_1592878 prefixEnd_1592878 181758230660560909155443 := by
  unfold tailWord_1592878
  simp only [CollatzResearch.WordTrace]
  refine ⟨7262129190410315343643411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38731355682188348499431525 7262129190410315343643411)
  ·
    refine ⟨10893193785615473015465117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7262129190410315343643411 10893193785615473015465117)
    ·
      refine ⟨4084947669605802380799419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10893193785615473015465117 4084947669605802380799419)
      ·
        refine ⟨6127421504408703571199129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4084947669605802380799419 6127421504408703571199129)
        ·
          refine ⟨4595566128306527678399347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6127421504408703571199129 4595566128306527678399347)
          ·
            refine ⟨6893349192459791517599021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4595566128306527678399347 6893349192459791517599021)
            ·
              refine ⟨2585005947172421819099633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6893349192459791517599021 2585005947172421819099633)
              ·
                refine ⟨1938754460379316364324725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2585005947172421819099633 1938754460379316364324725)
                ·
                  refine ⟨181758230660560909155443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1938754460379316364324725 181758230660560909155443)
                  ·
                    rfl

theorem cell22_1592878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 2, 5].length) (baseStart_1592878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1592878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1592878 prefixEnd_1592878 := by exact prefixLift 1592878
  have htrace : WordTrace (prefixWord ++ tailWord_1592878) baseStart_1592878 baseEnd_1592878 := by
    simpa [prefixWord, tailWord_1592878, baseEnd_1592878] using wordTrace_append hprefix tailTrace_1592878
  have hstable : (prefixWord ++ tailWord_1592878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592878).length < 2 ^ (prefixWord ++ tailWord_1592878).sum := by decide
  have hdescent : baseEnd_1592878 < baseStart_1592878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592908 : List Nat := [2, 2, 1, 3, 1, 4, 2, 2, 1, 4]
def baseStart_1592908 : Nat := 118140960795 + 1592908 * 2 ^ 59
def prefixEnd_1592908 : Nat := 4983230072969 + 3 ^ 40 * 1592908 * 2
def baseEnd_1592908 : Nat := 545284961594772649216237

theorem tailTrace_1592908 : CollatzResearch.WordTrace tailWord_1592908 prefixEnd_1592908 545284961594772649216237 := by
  unfold tailWord_1592908
  simp only [CollatzResearch.WordTrace]
  refine ⟨29049063856586918936369689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38732085142115891915159585 29049063856586918936369689)
  ·
    refine ⟨21786797892440189202277267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29049063856586918936369689 21786797892440189202277267)
    ·
      refine ⟨32680196838660283803415901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21786797892440189202277267 32680196838660283803415901)
      ·
        refine ⟨12255073814497606426280963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32680196838660283803415901 12255073814497606426280963)
        ·
          refine ⟨18382610721746409639421445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12255073814497606426280963 18382610721746409639421445)
          ·
            refine ⟨3446739510327451807391521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18382610721746409639421445 3446739510327451807391521)
            ·
              refine ⟨2585054632745588855543641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3446739510327451807391521 2585054632745588855543641)
              ·
                refine ⟨1938790974559191641657731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2585054632745588855543641 1938790974559191641657731)
                ·
                  refine ⟨2908186461838787462486597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1938790974559191641657731 2908186461838787462486597)
                  ·
                    refine ⟨545284961594772649216237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2908186461838787462486597 545284961594772649216237)
                    ·
                      rfl

theorem cell22_1592908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 2, 1, 4].length) (baseStart_1592908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1592908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1592908 prefixEnd_1592908 := by exact prefixLift 1592908
  have htrace : WordTrace (prefixWord ++ tailWord_1592908) baseStart_1592908 baseEnd_1592908 := by
    simpa [prefixWord, tailWord_1592908, baseEnd_1592908] using wordTrace_append hprefix tailTrace_1592908
  have hstable : (prefixWord ++ tailWord_1592908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592908).length < 2 ^ (prefixWord ++ tailWord_1592908).sum := by decide
  have hdescent : baseEnd_1592908 < baseStart_1592908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592938 : List Nat := [3, 1, 3, 2, 1, 2, 2, 1, 4, 3]
def baseStart_1592938 : Nat := 118140960795 + 1592938 * 2 ^ 59
def prefixEnd_1592938 : Nat := 4983230072969 + 3 ^ 40 * 1592938 * 2
def baseEnd_1592938 : Nat := 545295231207862570966145

theorem tailTrace_1592938 : CollatzResearch.WordTrace tailWord_1592938 prefixEnd_1592938 545295231207862570966145 := by
  unfold tailWord_1592938
  simp only [CollatzResearch.WordTrace]
  refine ⟨14524805475766288249082867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38732814602043435330887645 14524805475766288249082867)
  ·
    refine ⟨21787208213649432373624301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14524805475766288249082867 21787208213649432373624301)
    ·
      refine ⟨8170203080118537140109113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21787208213649432373624301 8170203080118537140109113)
      ·
        refine ⟨6127652310088902855081835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8170203080118537140109113 6127652310088902855081835)
        ·
          refine ⟨9191478465133354282622753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6127652310088902855081835 9191478465133354282622753)
          ·
            refine ⟨6893608848850015711967065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9191478465133354282622753 6893608848850015711967065)
            ·
              refine ⟨5170206636637511783975299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6893608848850015711967065 5170206636637511783975299)
              ·
                refine ⟨7755309954956267675962949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5170206636637511783975299 7755309954956267675962949)
                ·
                  refine ⟨1454120616554300189243053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7755309954956267675962949 1454120616554300189243053)
                  ·
                    refine ⟨545295231207862570966145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1454120616554300189243053 545295231207862570966145)
                    ·
                      rfl

theorem cell22_1592938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_1592938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1592938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1592938 prefixEnd_1592938 := by exact prefixLift 1592938
  have htrace : WordTrace (prefixWord ++ tailWord_1592938) baseStart_1592938 baseEnd_1592938 := by
    simpa [prefixWord, tailWord_1592938, baseEnd_1592938] using wordTrace_append hprefix tailTrace_1592938
  have hstable : (prefixWord ++ tailWord_1592938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592938).length < 2 ^ (prefixWord ++ tailWord_1592938).sum := by decide
  have hdescent : baseEnd_1592938 < baseStart_1592938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593011 : List Nat := [1, 1, 1, 2, 3, 3, 3, 1, 2, 5]
def baseStart_1593011 : Nat := 118140960795 + 1593011 * 2 ^ 59
def prefixEnd_1593011 : Nat := 4983230072969 + 3 ^ 40 * 1593011 * 2
def baseEnd_1593011 : Nat := 545320220599714713890921

theorem tailTrace_1593011 : CollatzResearch.WordTrace tailWord_1593011 prefixEnd_1593011 545320220599714713890921 := by
  unfold tailWord_1593011
  simp only [CollatzResearch.WordTrace]
  refine ⟨58101884431800686463738887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38734589621200457642492591 58101884431800686463738887)
  ·
    refine ⟨87152826647701029695608331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58101884431800686463738887 87152826647701029695608331)
    ·
      refine ⟨130729239971551544543412497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87152826647701029695608331 130729239971551544543412497)
      ·
        refine ⟨98046929978663658407559373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130729239971551544543412497 98046929978663658407559373)
        ·
          refine ⟨36767598741998871902834765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98046929978663658407559373 36767598741998871902834765)
          ·
            refine ⟨13787849528249576963563037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36767598741998871902834765 13787849528249576963563037)
            ·
              refine ⟨5170443573093591361336139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13787849528249576963563037 5170443573093591361336139)
              ·
                refine ⟨7755665359640387042004209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5170443573093591361336139 7755665359640387042004209)
                ·
                  refine ⟨5816749019730290281503157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7755665359640387042004209 5816749019730290281503157)
                  ·
                    refine ⟨545320220599714713890921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5816749019730290281503157 545320220599714713890921)
                    ·
                      rfl

theorem cell22_1593011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 5].length) (baseStart_1593011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1593011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1593011 prefixEnd_1593011 := by exact prefixLift 1593011
  have htrace : WordTrace (prefixWord ++ tailWord_1593011) baseStart_1593011 baseEnd_1593011 := by
    simpa [prefixWord, tailWord_1593011, baseEnd_1593011] using wordTrace_append hprefix tailTrace_1593011
  have hstable : (prefixWord ++ tailWord_1593011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593011).length < 2 ^ (prefixWord ++ tailWord_1593011).sum := by decide
  have hdescent : baseEnd_1593011 < baseStart_1593011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593056 : List Nat := [2, 1, 1, 3, 1, 2, 2, 2, 3, 5]
def baseStart_1593056 : Nat := 118140960795 + 1593056 * 2 ^ 59
def prefixEnd_1593056 : Nat := 4983230072969 + 3 ^ 40 * 1593056 * 2
def baseEnd_1593056 : Nat := 545335625019349596515783

theorem tailTrace_1593056 : CollatzResearch.WordTrace tailWord_1593056 prefixEnd_1593056 545335625019349596515783 := by
  unfold tailWord_1593056
  simp only [CollatzResearch.WordTrace]
  refine ⟨29051762858318829574563511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38735683811091772766084681 29051762858318829574563511)
  ·
    refine ⟨43577644287478244361845267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29051762858318829574563511 43577644287478244361845267)
    ·
      refine ⟨65366466431217366542767901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43577644287478244361845267 65366466431217366542767901)
      ·
        refine ⟨24512424911706512453537963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65366466431217366542767901 24512424911706512453537963)
        ·
          refine ⟨36768637367559768680306945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24512424911706512453537963 36768637367559768680306945)
          ·
            refine ⟨27576478025669826510230209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36768637367559768680306945 27576478025669826510230209)
            ·
              refine ⟨20682358519252369882672657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27576478025669826510230209 20682358519252369882672657)
              ·
                refine ⟨15511768889439277412004493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20682358519252369882672657 15511768889439277412004493)
                ·
                  refine ⟨5816913333539729029501685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15511768889439277412004493 5816913333539729029501685)
                  ·
                    refine ⟨545335625019349596515783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5816913333539729029501685 545335625019349596515783)
                    ·
                      rfl

theorem cell22_1593056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 3, 5].length) (baseStart_1593056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1593056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1593056 prefixEnd_1593056 := by exact prefixLift 1593056
  have htrace : WordTrace (prefixWord ++ tailWord_1593056) baseStart_1593056 baseEnd_1593056 := by
    simpa [prefixWord, tailWord_1593056, baseEnd_1593056] using wordTrace_append hprefix tailTrace_1593056
  have hstable : (prefixWord ++ tailWord_1593056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593056).length < 2 ^ (prefixWord ++ tailWord_1593056).sum := by decide
  have hdescent : baseEnd_1593056 < baseStart_1593056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593071 : List Nat := [1, 1, 2, 1, 5, 1, 1, 1, 3, 6]
def baseStart_1593071 : Nat := 118140960795 + 1593071 * 2 ^ 59
def prefixEnd_1593071 : Nat := 4983230072969 + 3 ^ 40 * 1593071 * 2
def baseEnd_1593071 : Nat := 545340759825894557390737

theorem tailTrace_1593071 : CollatzResearch.WordTrace tailWord_1593071 prefixEnd_1593071 545340759825894557390737 := by
  unfold tailWord_1593071
  simp only [CollatzResearch.WordTrace]
  refine ⟨58104072811583316710923067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38736048541055544473948711 58104072811583316710923067)
  ·
    refine ⟨87156109217374975066384601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58104072811583316710923067 87156109217374975066384601)
    ·
      refine ⟨65367081913031231299788451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87156109217374975066384601 65367081913031231299788451)
      ·
        refine ⟨98050622869546846949682677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65367081913031231299788451 98050622869546846949682677)
        ·
          refine ⟨9192245894020016901532751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 98050622869546846949682677 9192245894020016901532751)
          ·
            refine ⟨13788368841030025352299127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9192245894020016901532751 13788368841030025352299127)
            ·
              refine ⟨20682553261545038028448691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13788368841030025352299127 20682553261545038028448691)
              ·
                refine ⟨31023829892317557042673037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20682553261545038028448691 31023829892317557042673037)
                ·
                  refine ⟨11633936209619083891002389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31023829892317557042673037 11633936209619083891002389)
                  ·
                    refine ⟨545340759825894557390737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11633936209619083891002389 545340759825894557390737)
                    ·
                      rfl

theorem cell22_1593071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 6].length) (baseStart_1593071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1593071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1593071 prefixEnd_1593071 := by exact prefixLift 1593071
  have htrace : WordTrace (prefixWord ++ tailWord_1593071) baseStart_1593071 baseEnd_1593071 := by
    simpa [prefixWord, tailWord_1593071, baseEnd_1593071] using wordTrace_append hprefix tailTrace_1593071
  have hstable : (prefixWord ++ tailWord_1593071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593071).length < 2 ^ (prefixWord ++ tailWord_1593071).sum := by decide
  have hdescent : baseEnd_1593071 < baseStart_1593071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593073 : List Nat := [1, 2, 2, 2, 2, 3, 3, 1, 1, 5]
def baseStart_1593073 : Nat := 118140960795 + 1593073 * 2 ^ 59
def prefixEnd_1593073 : Nat := 4983230072969 + 3 ^ 40 * 1593073 * 2
def baseEnd_1593073 : Nat := 545341444466767218840731

theorem tailTrace_1593073 : CollatzResearch.WordTrace tailWord_1593073 prefixEnd_1593073 545341444466767218840731 := by
  unfold tailWord_1593073
  simp only [CollatzResearch.WordTrace]
  refine ⟨58104145757576071052495873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38736097171717380701663915 58104145757576071052495873)
  ·
    refine ⟨43578109318182053289371905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58104145757576071052495873 43578109318182053289371905)
    ·
      refine ⟨32683581988636539967028929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43578109318182053289371905 32683581988636539967028929)
      ·
        refine ⟨24512686491477404975271697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32683581988636539967028929 24512686491477404975271697)
        ·
          refine ⟨18384514868608053731453773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24512686491477404975271697 18384514868608053731453773)
          ·
            refine ⟨6894193075728020149295165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18384514868608053731453773 6894193075728020149295165)
            ·
              refine ⟨2585322403398007555985687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6894193075728020149295165 2585322403398007555985687)
              ·
                refine ⟨3877983605097011333978531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2585322403398007555985687 3877983605097011333978531)
                ·
                  refine ⟨5816975407645517000967797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3877983605097011333978531 5816975407645517000967797)
                  ·
                    refine ⟨545341444466767218840731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5816975407645517000967797 545341444466767218840731)
                    ·
                      rfl

theorem cell22_1593073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 5].length) (baseStart_1593073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1593073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1593073 prefixEnd_1593073 := by exact prefixLift 1593073
  have htrace : WordTrace (prefixWord ++ tailWord_1593073) baseStart_1593073 baseEnd_1593073 := by
    simpa [prefixWord, tailWord_1593073, baseEnd_1593073] using wordTrace_append hprefix tailTrace_1593073
  have hstable : (prefixWord ++ tailWord_1593073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593073).length < 2 ^ (prefixWord ++ tailWord_1593073).sum := by decide
  have hdescent : baseEnd_1593073 < baseStart_1593073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593090 : List Nat := [3, 4, 1, 1, 1, 1, 1, 1, 6, 3]
def baseStart_1593090 : Nat := 118140960795 + 1593090 * 2 ^ 59
def prefixEnd_1593090 : Nat := 4983230072969 + 3 ^ 40 * 1593090 * 2
def baseEnd_1593090 : Nat := 545347263914184841165679

theorem tailTrace_1593090 : CollatzResearch.WordTrace tailWord_1593090 prefixEnd_1593090 545347263914184841165679 := by
  unfold tailWord_1593090
  simp only [CollatzResearch.WordTrace]
  refine ⟨14526191449628620738966181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38736510532342988637243149 14526191449628620738966181)
  ·
    refine ⟨2723660896805366388556159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14526191449628620738966181 2723660896805366388556159)
    ·
      refine ⟨4085491345208049582834239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2723660896805366388556159 4085491345208049582834239)
      ·
        refine ⟨6128237017812074374251359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4085491345208049582834239 6128237017812074374251359)
        ·
          refine ⟨9192355526718111561377039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6128237017812074374251359 9192355526718111561377039)
          ·
            refine ⟨13788533290077167342065559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9192355526718111561377039 13788533290077167342065559)
            ·
              refine ⟨20682799935115751013098339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13788533290077167342065559 20682799935115751013098339)
              ·
                refine ⟨31024199902673626519647509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20682799935115751013098339 31024199902673626519647509)
                ·
                  refine ⟨1454259370437826243108477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 31024199902673626519647509 1454259370437826243108477)
                  ·
                    refine ⟨545347263914184841165679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1454259370437826243108477 545347263914184841165679)
                    ·
                      rfl

theorem cell22_1593090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_1593090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1593090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1593090 prefixEnd_1593090 := by exact prefixLift 1593090
  have htrace : WordTrace (prefixWord ++ tailWord_1593090) baseStart_1593090 baseEnd_1593090 := by
    simpa [prefixWord, tailWord_1593090, baseEnd_1593090] using wordTrace_append hprefix tailTrace_1593090
  have hstable : (prefixWord ++ tailWord_1593090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593090).length < 2 ^ (prefixWord ++ tailWord_1593090).sum := by decide
  have hdescent : baseEnd_1593090 < baseStart_1593090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593092 : List Nat := [2, 3, 2, 2, 1, 4, 1, 3, 4]
def baseStart_1593092 : Nat := 118140960795 + 1593092 * 2 ^ 59
def prefixEnd_1593092 : Nat := 4983230072969 + 3 ^ 40 * 1593092 * 2
def baseEnd_1593092 : Nat := 181782649518352500871891

theorem tailTrace_1593092 : CollatzResearch.WordTrace tailWord_1593092 prefixEnd_1593092 181782649518352500871891 := by
  unfold tailWord_1593092
  simp only [CollatzResearch.WordTrace]
  refine ⟨29052419372253618648718765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38736559163004824864958353 29052419372253618648718765)
  ·
    refine ⟨10894657264595106993269537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29052419372253618648718765 10894657264595106993269537)
    ·
      refine ⟨8170992948446330244952153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10894657264595106993269537 8170992948446330244952153)
      ·
        refine ⟨6128244711334747683714115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8170992948446330244952153 6128244711334747683714115)
        ·
          refine ⟨9192367067002121525571173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6128244711334747683714115 9192367067002121525571173)
          ·
            refine ⟨1723568825062897786044595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9192367067002121525571173 1723568825062897786044595)
            ·
              refine ⟨2585353237594346679066893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1723568825062897786044595 2585353237594346679066893)
              ·
                refine ⟨969507464097880004650085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2585353237594346679066893 969507464097880004650085)
                ·
                  refine ⟨181782649518352500871891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 969507464097880004650085 181782649518352500871891)
                  ·
                    rfl

theorem cell22_1593092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 3, 4].length) (baseStart_1593092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1593092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1593092 prefixEnd_1593092 := by exact prefixLift 1593092
  have htrace : WordTrace (prefixWord ++ tailWord_1593092) baseStart_1593092 baseEnd_1593092 := by
    simpa [prefixWord, tailWord_1593092, baseEnd_1593092] using wordTrace_append hprefix tailTrace_1593092
  have hstable : (prefixWord ++ tailWord_1593092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593092).length < 2 ^ (prefixWord ++ tailWord_1593092).sum := by decide
  have hdescent : baseEnd_1593092 < baseStart_1593092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593124 : List Nat := [2, 3, 1, 3, 2, 3, 2, 1, 2, 3]
def baseStart_1593124 : Nat := 118140960795 + 1593124 * 2 ^ 59
def prefixEnd_1593124 : Nat := 4983230072969 + 3 ^ 40 * 1593124 * 2
def baseEnd_1593124 : Nat := 545358902809020085815575

theorem tailTrace_1593124 : CollatzResearch.WordTrace tailWord_1593124 prefixEnd_1593124 545358902809020085815575 := by
  unfold tailWord_1593124
  simp only [CollatzResearch.WordTrace]
  refine ⟨29053002940195653381301213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38737337253594204508401617 29053002940195653381301213)
  ·
    refine ⟨10894876102573370017987955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29053002940195653381301213 10894876102573370017987955)
    ·
      refine ⟨16342314153860055026981933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10894876102573370017987955 16342314153860055026981933)
      ·
        refine ⟨6128367807697520635118225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16342314153860055026981933 6128367807697520635118225)
        ·
          refine ⟨4596275855773140476338669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6128367807697520635118225 4596275855773140476338669)
          ·
            refine ⟨1723603445914927678627001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4596275855773140476338669 1723603445914927678627001)
            ·
              refine ⟨1292702584436195758970251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1723603445914927678627001 1292702584436195758970251)
              ·
                refine ⟨1939053876654293638455377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1292702584436195758970251 1939053876654293638455377)
                ·
                  refine ⟨1454290407490720228841533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1939053876654293638455377 1454290407490720228841533)
                  ·
                    refine ⟨545358902809020085815575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1454290407490720228841533 545358902809020085815575)
                    ·
                      rfl

theorem cell22_1593124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 1, 2, 3].length) (baseStart_1593124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1593124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1593124 prefixEnd_1593124 := by exact prefixLift 1593124
  have htrace : WordTrace (prefixWord ++ tailWord_1593124) baseStart_1593124 baseEnd_1593124 := by
    simpa [prefixWord, tailWord_1593124, baseEnd_1593124] using wordTrace_append hprefix tailTrace_1593124
  have hstable : (prefixWord ++ tailWord_1593124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593124).length < 2 ^ (prefixWord ++ tailWord_1593124).sum := by decide
  have hdescent : baseEnd_1593124 < baseStart_1593124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593169 : List Nat := [1, 2, 2, 1, 5, 1, 4, 2, 1, 3]
def baseStart_1593169 : Nat := 118140960795 + 1593169 * 2 ^ 59
def prefixEnd_1593169 : Nat := 4983230072969 + 3 ^ 40 * 1593169 * 2
def baseEnd_1593169 : Nat := 545374307228654968440437

theorem tailTrace_1593169 : CollatzResearch.WordTrace tailWord_1593169 prefixEnd_1593169 545374307228654968440437 := by
  unfold tailWord_1593169
  simp only [CollatzResearch.WordTrace]
  refine ⟨58107647165228279447990561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38738431443485519631993707 58107647165228279447990561)
  ·
    refine ⟨43580735373921209585992921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58107647165228279447990561 43580735373921209585992921)
    ·
      refine ⟨32685551530440907189494691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43580735373921209585992921 32685551530440907189494691)
      ·
        refine ⟨49028327295661360784242037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32685551530440907189494691 49028327295661360784242037)
        ·
          refine ⟨4596405683968252573522691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49028327295661360784242037 4596405683968252573522691)
          ·
            refine ⟨6894608525952378860284037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4596405683968252573522691 6894608525952378860284037)
            ·
              refine ⟨1292739098616071036303257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6894608525952378860284037 1292739098616071036303257)
              ·
                refine ⟨969554323962053277227443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1292739098616071036303257 969554323962053277227443)
                ·
                  refine ⟨1454331485943079915841165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 969554323962053277227443 1454331485943079915841165)
                  ·
                    refine ⟨545374307228654968440437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1454331485943079915841165 545374307228654968440437)
                    ·
                      rfl

theorem cell22_1593169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 2, 1, 3].length) (baseStart_1593169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1593169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1593169 prefixEnd_1593169 := by exact prefixLift 1593169
  have htrace : WordTrace (prefixWord ++ tailWord_1593169) baseStart_1593169 baseEnd_1593169 := by
    simpa [prefixWord, tailWord_1593169, baseEnd_1593169] using wordTrace_append hprefix tailTrace_1593169
  have hstable : (prefixWord ++ tailWord_1593169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593169).length < 2 ^ (prefixWord ++ tailWord_1593169).sum := by decide
  have hdescent : baseEnd_1593169 < baseStart_1593169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593178 : List Nat := [3, 1, 1, 2, 1, 3, 1, 1, 5, 4]
def baseStart_1593178 : Nat := 118140960795 + 1593178 * 2 ^ 59
def prefixEnd_1593178 : Nat := 4983230072969 + 3 ^ 40 * 1593178 * 2
def baseEnd_1593178 : Nat := 545377388112581944965409

theorem tailTrace_1593178 : CollatzResearch.WordTrace tailWord_1593178 prefixEnd_1593178 545377388112581944965409 := by
  unfold tailWord_1593178
  simp only [CollatzResearch.WordTrace]
  refine ⟨14526993855548918496267047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38738650281463782656712125 14526993855548918496267047)
  ·
    refine ⟨21790490783323377744400571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14526993855548918496267047 21790490783323377744400571)
    ·
      refine ⟨32685736174985066616600857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21790490783323377744400571 32685736174985066616600857)
      ·
        refine ⟨24514302131238799962450643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32685736174985066616600857 24514302131238799962450643)
        ·
          refine ⟨36771453196858199943675965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24514302131238799962450643 36771453196858199943675965)
          ·
            refine ⟨13789294948821824978878487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36771453196858199943675965 13789294948821824978878487)
            ·
              refine ⟨20683942423232737468317731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13789294948821824978878487 20683942423232737468317731)
              ·
                refine ⟨31025913634849106202476597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20683942423232737468317731 31025913634849106202476597)
                ·
                  refine ⟨2908679403267103706482181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31025913634849106202476597 2908679403267103706482181)
                  ·
                    refine ⟨545377388112581944965409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2908679403267103706482181 545377388112581944965409)
                    ·
                      rfl

theorem cell22_1593178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 5, 4].length) (baseStart_1593178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1593178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1593178 prefixEnd_1593178 := by exact prefixLift 1593178
  have htrace : WordTrace (prefixWord ++ tailWord_1593178) baseStart_1593178 baseEnd_1593178 := by
    simpa [prefixWord, tailWord_1593178, baseEnd_1593178] using wordTrace_append hprefix tailTrace_1593178
  have hstable : (prefixWord ++ tailWord_1593178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593178).length < 2 ^ (prefixWord ++ tailWord_1593178).sum := by decide
  have hdescent : baseEnd_1593178 < baseStart_1593178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593210 : List Nat := [3, 1, 1, 1, 1, 1, 5, 5, 4]
def baseStart_1593210 : Nat := 118140960795 + 1593210 * 2 ^ 59
def prefixEnd_1593210 : Nat := 4983230072969 + 3 ^ 40 * 1593210 * 2
def baseEnd_1593210 : Nat := 181796114122181509388437

theorem tailTrace_1593210 : CollatzResearch.WordTrace tailWord_1593210 prefixEnd_1593210 181796114122181509388437 := by
  unfold tailWord_1593210
  simp only [CollatzResearch.WordTrace]
  refine ⟨14527285639519935862558271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38739428372053162300155389 14527285639519935862558271)
  ·
    refine ⟨21790928459279903793837407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14527285639519935862558271 21790928459279903793837407)
    ·
      refine ⟨32686392688919855690756111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21790928459279903793837407 32686392688919855690756111)
      ·
        refine ⟨49029589033379783536134167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32686392688919855690756111 49029589033379783536134167)
        ·
          refine ⟨73544383550069675304201251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49029589033379783536134167 73544383550069675304201251)
          ·
            refine ⟨110316575325104512956301877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73544383550069675304201251 110316575325104512956301877)
            ·
              refine ⟨10342178936728548089653301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 110316575325104512956301877 10342178936728548089653301)
              ·
                refine ⟨969579275318301383404997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10342178936728548089653301 969579275318301383404997)
                ·
                  refine ⟨181796114122181509388437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 969579275318301383404997 181796114122181509388437)
                  ·
                    rfl

theorem cell22_1593210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 5, 4].length) (baseStart_1593210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1593210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1593210 prefixEnd_1593210 := by exact prefixLift 1593210
  have htrace : WordTrace (prefixWord ++ tailWord_1593210) baseStart_1593210 baseEnd_1593210 := by
    simpa [prefixWord, tailWord_1593210, baseEnd_1593210] using wordTrace_append hprefix tailTrace_1593210
  have hstable : (prefixWord ++ tailWord_1593210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593210).length < 2 ^ (prefixWord ++ tailWord_1593210).sum := by decide
  have hdescent : baseEnd_1593210 < baseStart_1593210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593225 : List Nat := [1, 2, 1, 1, 5, 1, 3, 1, 4, 3]
def baseStart_1593225 : Nat := 118140960795 + 1593225 * 2 ^ 59
def prefixEnd_1593225 : Nat := 4983230072969 + 3 ^ 40 * 1593225 * 2
def baseEnd_1593225 : Nat := 545393477173089489040265

theorem tailTrace_1593225 : CollatzResearch.WordTrace tailWord_1593225 prefixEnd_1593225 545393477173089489040265 := by
  unfold tailWord_1593225
  simp only [CollatzResearch.WordTrace]
  refine ⟨58109689653025401012029129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38739793102016934008019419 58109689653025401012029129)
  ·
    refine ⟨43582267239769050759021847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58109689653025401012029129 43582267239769050759021847)
    ·
      refine ⟨65373400859653576138532771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43582267239769050759021847 65373400859653576138532771)
      ·
        refine ⟨98060101289480364207799157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65373400859653576138532771 98060101289480364207799157)
        ·
          refine ⟨9193134495888784144481171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 98060101289480364207799157 9193134495888784144481171)
          ·
            refine ⟨13789701743833176216721757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9193134495888784144481171 13789701743833176216721757)
            ·
              refine ⟨5171138153937441081270659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13789701743833176216721757 5171138153937441081270659)
              ·
                refine ⟨7756707230906161621905989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5171138153937441081270659 7756707230906161621905989)
                ·
                  refine ⟨1454382605794905304107373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7756707230906161621905989 1454382605794905304107373)
                  ·
                    refine ⟨545393477173089489040265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1454382605794905304107373 545393477173089489040265)
                    ·
                      rfl

theorem cell22_1593225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 4, 3].length) (baseStart_1593225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1593225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1593225 prefixEnd_1593225 := by exact prefixLift 1593225
  have htrace : WordTrace (prefixWord ++ tailWord_1593225) baseStart_1593225 baseEnd_1593225 := by
    simpa [prefixWord, tailWord_1593225, baseEnd_1593225] using wordTrace_append hprefix tailTrace_1593225
  have hstable : (prefixWord ++ tailWord_1593225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593225).length < 2 ^ (prefixWord ++ tailWord_1593225).sum := by decide
  have hdescent : baseEnd_1593225 < baseStart_1593225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593242 : List Nat := [3, 1, 1, 4, 2, 3, 1, 1, 1, 5]
def baseStart_1593242 : Nat := 118140960795 + 1593242 * 2 ^ 59
def prefixEnd_1593242 : Nat := 4983230072969 + 3 ^ 40 * 1593242 * 2
def baseEnd_1593242 : Nat := 545399296620507111365213

theorem tailTrace_1593242 : CollatzResearch.WordTrace tailWord_1593242 prefixEnd_1593242 545399296620507111365213 := by
  unfold tailWord_1593242
  simp only [CollatzResearch.WordTrace]
  refine ⟨14527577423490953228849495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38740206462642541943598653 14527577423490953228849495)
  ·
    refine ⟨21791366135236429843274243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14527577423490953228849495 21791366135236429843274243)
    ·
      refine ⟨32687049202854644764911365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21791366135236429843274243 32687049202854644764911365)
      ·
        refine ⟨6128821725535245893420881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32687049202854644764911365 6128821725535245893420881)
        ·
          refine ⟨4596616294151434420065661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6128821725535245893420881 4596616294151434420065661)
          ·
            refine ⟨1723731110306787907524623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4596616294151434420065661 1723731110306787907524623)
            ·
              refine ⟨2585596665460181861286935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1723731110306787907524623 2585596665460181861286935)
              ·
                refine ⟨3878394998190272791930403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2585596665460181861286935 3878394998190272791930403)
                ·
                  refine ⟨5817592497285409187895605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3878394998190272791930403 5817592497285409187895605)
                  ·
                    refine ⟨545399296620507111365213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5817592497285409187895605 545399296620507111365213)
                    ·
                      rfl

theorem cell22_1593242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 1, 5].length) (baseStart_1593242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1593242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1593242 prefixEnd_1593242 := by exact prefixLift 1593242
  have htrace : WordTrace (prefixWord ++ tailWord_1593242) baseStart_1593242 baseEnd_1593242 := by
    simpa [prefixWord, tailWord_1593242, baseEnd_1593242] using wordTrace_append hprefix tailTrace_1593242
  have hstable : (prefixWord ++ tailWord_1593242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593242).length < 2 ^ (prefixWord ++ tailWord_1593242).sum := by decide
  have hdescent : baseEnd_1593242 < baseStart_1593242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593246 : List Nat := [4, 3, 1, 3, 1, 1, 2, 2, 1, 4]
def baseStart_1593246 : Nat := 118140960795 + 1593246 * 2 ^ 59
def prefixEnd_1593246 : Nat := 4983230072969 + 3 ^ 40 * 1593246 * 2
def baseEnd_1593246 : Nat := 545400665902252434265201

theorem tailTrace_1593246 : CollatzResearch.WordTrace tailWord_1593246 prefixEnd_1593246 545400665902252434265201 := by
  unfold tailWord_1593246
  simp only [CollatzResearch.WordTrace]
  refine ⟨7263806948243665199817949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38740303723966214399029061 7263806948243665199817949)
  ·
    refine ⟨2723927605591374449931731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7263806948243665199817949 2723927605591374449931731)
    ·
      refine ⟨4085891408387061674897597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2723927605591374449931731 4085891408387061674897597)
      ·
        refine ⟨1532209278145148128086599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4085891408387061674897597 1532209278145148128086599)
        ·
          refine ⟨2298313917217722192129899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1532209278145148128086599 2298313917217722192129899)
          ·
            refine ⟨3447470875826583288194849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2298313917217722192129899 3447470875826583288194849)
            ·
              refine ⟨2585603156869937466146137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3447470875826583288194849 2585603156869937466146137)
              ·
                refine ⟨1939202367652453099609603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2585603156869937466146137 1939202367652453099609603)
                ·
                  refine ⟨2908803551478679649414405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1939202367652453099609603 2908803551478679649414405)
                  ·
                    refine ⟨545400665902252434265201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2908803551478679649414405 545400665902252434265201)
                    ·
                      rfl

theorem cell22_1593246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_1593246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1593246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1593246 prefixEnd_1593246 := by exact prefixLift 1593246
  have htrace : WordTrace (prefixWord ++ tailWord_1593246) baseStart_1593246 baseEnd_1593246 := by
    simpa [prefixWord, tailWord_1593246, baseEnd_1593246] using wordTrace_append hprefix tailTrace_1593246
  have hstable : (prefixWord ++ tailWord_1593246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593246).length < 2 ^ (prefixWord ++ tailWord_1593246).sum := by decide
  have hdescent : baseEnd_1593246 < baseStart_1593246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593255 : List Nat := [1, 1, 6, 1, 2, 2, 1, 8]
def baseStart_1593255 : Nat := 118140960795 + 1593255 * 2 ^ 59
def prefixEnd_1593255 : Nat := 4983230072969 + 3 ^ 40 * 1593255 * 2
def baseEnd_1593255 : Nat := 60600416309575490087797

theorem tailTrace_1593255 : CollatzResearch.WordTrace tailWord_1593255 prefixEnd_1593255 60600416309575490087797 := by
  unfold tailWord_1593255
  simp only [CollatzResearch.WordTrace]
  refine ⟨58110783842916716135621219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38740522561944477423747479 58110783842916716135621219)
  ·
    refine ⟨87166175764375074203431829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58110783842916716135621219 87166175764375074203431829)
    ·
      refine ⟨4085914488955081603285867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 87166175764375074203431829 4085914488955081603285867)
      ·
        refine ⟨6128871733432622404928801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4085914488955081603285867 6128871733432622404928801)
        ·
          refine ⟨4596653800074466803696601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6128871733432622404928801 4596653800074466803696601)
          ·
            refine ⟨3447490350055850102772451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4596653800074466803696601 3447490350055850102772451)
            ·
              refine ⟨5171235525083775154158677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3447490350055850102772451 5171235525083775154158677)
              ·
                refine ⟨60600416309575490087797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5171235525083775154158677 60600416309575490087797)
                ·
                  rfl

theorem cell22_1593255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 8].length) (baseStart_1593255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1593255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1593255 prefixEnd_1593255 := by exact prefixLift 1593255
  have htrace : WordTrace (prefixWord ++ tailWord_1593255) baseStart_1593255 baseEnd_1593255 := by
    simpa [prefixWord, tailWord_1593255, baseEnd_1593255] using wordTrace_append hprefix tailTrace_1593255
  have hstable : (prefixWord ++ tailWord_1593255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593255).length < 2 ^ (prefixWord ++ tailWord_1593255).sum := by decide
  have hdescent : baseEnd_1593255 < baseStart_1593255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593334 : List Nat := [5, 1, 1, 1, 4, 1, 2, 2, 5]
def baseStart_1593334 : Nat := 118140960795 + 1593334 * 2 ^ 59
def prefixEnd_1593334 : Nat := 4983230072969 + 3 ^ 40 * 1593334 * 2
def baseEnd_1593334 : Nat := 181810263366883179354977

theorem tailTrace_1593334 : CollatzResearch.WordTrace tailWord_1593334 prefixEnd_1593334 181810263366883179354977 := by
  unfold tailWord_1593334
  simp only [CollatzResearch.WordTrace]
  refine ⟨3632104075601907039234191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38742443473087008418498037 3632104075601907039234191)
  ·
    refine ⟨5448156113402860558851287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3632104075601907039234191 5448156113402860558851287)
    ·
      refine ⟨8172234170104290838276931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5448156113402860558851287 8172234170104290838276931)
      ·
        refine ⟨12258351255156436257415397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8172234170104290838276931 12258351255156436257415397)
        ·
          refine ⟨2298440860341831798265387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12258351255156436257415397 2298440860341831798265387)
          ·
            refine ⟨3447661290512747697398081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2298440860341831798265387 3447661290512747697398081)
            ·
              refine ⟨2585745967884560773048561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3447661290512747697398081 2585745967884560773048561)
              ·
                refine ⟨1939309475913420579786421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2585745967884560773048561 1939309475913420579786421)
                ·
                  refine ⟨181810263366883179354977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1939309475913420579786421 181810263366883179354977)
                  ·
                    rfl

theorem cell22_1593334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_1593334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1593334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1593334 prefixEnd_1593334 := by exact prefixLift 1593334
  have htrace : WordTrace (prefixWord ++ tailWord_1593334) baseStart_1593334 baseEnd_1593334 := by
    simpa [prefixWord, tailWord_1593334, baseEnd_1593334] using wordTrace_append hprefix tailTrace_1593334
  have hstable : (prefixWord ++ tailWord_1593334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593334).length < 2 ^ (prefixWord ++ tailWord_1593334).sum := by decide
  have hdescent : baseEnd_1593334 < baseStart_1593334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593345 : List Nat := [1, 2, 4, 1, 2, 1, 2, 3, 6]
def baseStart_1593345 : Nat := 118140960795 + 1593345 * 2 ^ 59
def prefixEnd_1593345 : Nat := 4983230072969 + 3 ^ 40 * 1593345 * 2
def baseEnd_1593345 : Nat := 181811518541816392013299

theorem tailTrace_1593345 : CollatzResearch.WordTrace tailWord_1593345 prefixEnd_1593345 181811518541816392013299 := by
  unfold tailWord_1593345
  simp only [CollatzResearch.WordTrace]
  refine ⟨58114066412590661506397489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38742710941727107670931659 58114066412590661506397489)
  ·
    refine ⟨43585549809442996129798117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58114066412590661506397489 43585549809442996129798117)
    ·
      refine ⟨8172290589270561774337147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43585549809442996129798117 8172290589270561774337147)
      ·
        refine ⟨12258435883905842661505721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8172290589270561774337147 12258435883905842661505721)
        ·
          refine ⟨9193826912929381996129291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12258435883905842661505721 9193826912929381996129291)
          ·
            refine ⟨13790740369394072994193937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9193826912929381996129291 13790740369394072994193937)
            ·
              refine ⟨10343055277045554745645453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13790740369394072994193937 10343055277045554745645453)
              ·
                refine ⟨3878645728892083029617045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10343055277045554745645453 3878645728892083029617045)
                ·
                  refine ⟨181811518541816392013299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3878645728892083029617045 181811518541816392013299)
                  ·
                    rfl

theorem cell22_1593345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 6].length) (baseStart_1593345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1593345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1593345 prefixEnd_1593345 := by exact prefixLift 1593345
  have htrace : WordTrace (prefixWord ++ tailWord_1593345) baseStart_1593345 baseEnd_1593345 := by
    simpa [prefixWord, tailWord_1593345, baseEnd_1593345] using wordTrace_append hprefix tailTrace_1593345
  have hstable : (prefixWord ++ tailWord_1593345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593345).length < 2 ^ (prefixWord ++ tailWord_1593345).sum := by decide
  have hdescent : baseEnd_1593345 < baseStart_1593345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593375 : List Nat := [1, 1, 2, 4, 1, 2, 3, 1, 1, 6]
def baseStart_1593375 : Nat := 118140960795 + 1593375 * 2 ^ 59
def prefixEnd_1593375 : Nat := 4983230072969 + 3 ^ 40 * 1593375 * 2
def baseEnd_1593375 : Nat := 545444825238539097789805

theorem tailTrace_1593375 : CollatzResearch.WordTrace tailWord_1593375 prefixEnd_1593375 545444825238539097789805 := by
  unfold tailWord_1593375
  simp only [CollatzResearch.WordTrace]
  refine ⟨58115160602481976629989579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38743440401654651086659719 58115160602481976629989579)
  ·
    refine ⟨87172740903722964944984369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58115160602481976629989579 87172740903722964944984369)
    ·
      refine ⟨65379555677792223708738277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87172740903722964944984369 65379555677792223708738277)
      ·
        refine ⟨12258666689586041945388427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65379555677792223708738277 12258666689586041945388427)
        ·
          refine ⟨18388000034379062918082641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12258666689586041945388427 18388000034379062918082641)
          ·
            refine ⟨13791000025784297188561981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18388000034379062918082641 13791000025784297188561981)
            ·
              refine ⟨5171625009669111445710743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13791000025784297188561981 5171625009669111445710743)
              ·
                refine ⟨7757437514503667168566115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5171625009669111445710743 7757437514503667168566115)
                ·
                  refine ⟨11636156271755500752849173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7757437514503667168566115 11636156271755500752849173)
                  ·
                    refine ⟨545444825238539097789805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11636156271755500752849173 545444825238539097789805)
                    ·
                      rfl

theorem cell22_1593375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 6].length) (baseStart_1593375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1593375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1593375 prefixEnd_1593375 := by exact prefixLift 1593375
  have htrace : WordTrace (prefixWord ++ tailWord_1593375) baseStart_1593375 baseEnd_1593375 := by
    simpa [prefixWord, tailWord_1593375, baseEnd_1593375] using wordTrace_append hprefix tailTrace_1593375
  have hstable : (prefixWord ++ tailWord_1593375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593375).length < 2 ^ (prefixWord ++ tailWord_1593375).sum := by decide
  have hdescent : baseEnd_1593375 < baseStart_1593375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593394 : List Nat := [3, 2, 1, 1, 2, 3, 3, 2, 2, 3]
def baseStart_1593394 : Nat := 118140960795 + 1593394 * 2 ^ 59
def prefixEnd_1593394 : Nat := 4983230072969 + 3 ^ 40 * 1593394 * 2
def baseEnd_1593394 : Nat := 545451329326829381564747

theorem tailTrace_1593394 : CollatzResearch.WordTrace tailWord_1593394 prefixEnd_1593394 545451329326829381564747 := by
  unfold tailWord_1593394
  simp only [CollatzResearch.WordTrace]
  refine ⟨14528963397353285718732809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38743902392942095249954157 14528963397353285718732809)
  ·
    refine ⟨10896722548014964289049607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14528963397353285718732809 10896722548014964289049607)
    ·
      refine ⟨16345083822022446433574411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10896722548014964289049607 16345083822022446433574411)
      ·
        refine ⟨24517625733033669650361617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16345083822022446433574411 24517625733033669650361617)
        ·
          refine ⟨18388219299775252237771213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24517625733033669650361617 18388219299775252237771213)
          ·
            refine ⟨6895582237415719589164205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18388219299775252237771213 6895582237415719589164205)
            ·
              refine ⟨2585843339030894845936577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6895582237415719589164205 2585843339030894845936577)
              ·
                refine ⟨1939382504273171134452433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2585843339030894845936577 1939382504273171134452433)
                ·
                  refine ⟨1454536878204878350839325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1939382504273171134452433 1454536878204878350839325)
                  ·
                    refine ⟨545451329326829381564747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1454536878204878350839325 545451329326829381564747)
                    ·
                      rfl

theorem cell22_1593394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 2, 2, 3].length) (baseStart_1593394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1593394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1593394 prefixEnd_1593394 := by exact prefixLift 1593394
  have htrace : WordTrace (prefixWord ++ tailWord_1593394) baseStart_1593394 baseEnd_1593394 := by
    simpa [prefixWord, tailWord_1593394, baseEnd_1593394] using wordTrace_append hprefix tailTrace_1593394
  have hstable : (prefixWord ++ tailWord_1593394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593394).length < 2 ^ (prefixWord ++ tailWord_1593394).sum := by decide
  have hdescent : baseEnd_1593394 < baseStart_1593394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593420 : List Nat := [2, 2, 1, 3, 1, 1, 2, 2, 2, 6]
def baseStart_1593420 : Nat := 118140960795 + 1593420 * 2 ^ 59
def prefixEnd_1593420 : Nat := 4983230072969 + 3 ^ 40 * 1593420 * 2
def baseEnd_1593420 : Nat := 545460229658173980414667

theorem tailTrace_1593420 : CollatzResearch.WordTrace tailWord_1593420 prefixEnd_1593420 545460229658173980414667 := by
  unfold tailWord_1593420
  simp only [CollatzResearch.WordTrace]
  refine ⟨29058400943659474657688857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38744534591545966210251809 29058400943659474657688857)
  ·
    refine ⟨21793800707744605993266643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29058400943659474657688857 21793800707744605993266643)
    ·
      refine ⟨32690701061616908989899965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21793800707744605993266643 32690701061616908989899965)
      ·
        refine ⟨12259012898106340871212487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32690701061616908989899965 12259012898106340871212487)
        ·
          refine ⟨18388519347159511306818731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12259012898106340871212487 18388519347159511306818731)
          ·
            refine ⟨27582779020739266960228097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18388519347159511306818731 27582779020739266960228097)
            ·
              refine ⟨20687084265554450220171073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27582779020739266960228097 20687084265554450220171073)
              ·
                refine ⟨15515313199165837665128305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20687084265554450220171073 15515313199165837665128305)
                ·
                  refine ⟨11636484899374378248846229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15515313199165837665128305 11636484899374378248846229)
                  ·
                    refine ⟨545460229658173980414667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11636484899374378248846229 545460229658173980414667)
                    ·
                      rfl

theorem cell22_1593420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 2, 6].length) (baseStart_1593420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1593420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1593420 prefixEnd_1593420 := by exact prefixLift 1593420
  have htrace : WordTrace (prefixWord ++ tailWord_1593420) baseStart_1593420 baseEnd_1593420 := by
    simpa [prefixWord, tailWord_1593420, baseEnd_1593420] using wordTrace_append hprefix tailTrace_1593420
  have hstable : (prefixWord ++ tailWord_1593420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593420).length < 2 ^ (prefixWord ++ tailWord_1593420).sum := by decide
  have hdescent : baseEnd_1593420 < baseStart_1593420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593439 : List Nat := [1, 1, 2, 3, 1, 1, 2, 7, 1, 3]
def baseStart_1593439 : Nat := 118140960795 + 1593439 * 2 ^ 59
def prefixEnd_1593439 : Nat := 4983230072969 + 3 ^ 40 * 1593439 * 2
def baseEnd_1593439 : Nat := 545466733746464264189609

theorem tailTrace_1593439 : CollatzResearch.WordTrace tailWord_1593439 prefixEnd_1593439 545466733746464264189609 := by
  unfold tailWord_1593439
  simp only [CollatzResearch.WordTrace]
  refine ⟨58117494874250115560319371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38744996582833410373546247 58117494874250115560319371)
  ·
    refine ⟨87176242311375173340479057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58117494874250115560319371 87176242311375173340479057)
    ·
      refine ⟨65382181733531380005359293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87176242311375173340479057 65382181733531380005359293)
      ·
        refine ⟨24518318150074267502009735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65382181733531380005359293 24518318150074267502009735)
        ·
          refine ⟨36777477225111401253014603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24518318150074267502009735 36777477225111401253014603)
          ·
            refine ⟨55166215837667101879521905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36777477225111401253014603 55166215837667101879521905)
            ·
              refine ⟨41374661878250326409641429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55166215837667101879521905 41374661878250326409641429)
              ·
                refine ⟨969718637771492025225971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 41374661878250326409641429 969718637771492025225971)
                ·
                  refine ⟨1454577956657238037838957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 969718637771492025225971 1454577956657238037838957)
                  ·
                    refine ⟨545466733746464264189609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1454577956657238037838957 545466733746464264189609)
                    ·
                      rfl

theorem cell22_1593439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 7, 1, 3].length) (baseStart_1593439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1593439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1593439 prefixEnd_1593439 := by exact prefixLift 1593439
  have htrace : WordTrace (prefixWord ++ tailWord_1593439) baseStart_1593439 baseEnd_1593439 := by
    simpa [prefixWord, tailWord_1593439, baseEnd_1593439] using wordTrace_append hprefix tailTrace_1593439
  have hstable : (prefixWord ++ tailWord_1593439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593439).length < 2 ^ (prefixWord ++ tailWord_1593439).sum := by decide
  have hdescent : baseEnd_1593439 < baseStart_1593439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593469 : List Nat := [1, 4, 1, 1, 3, 2, 4, 1, 5]
def baseStart_1593469 : Nat := 118140960795 + 1593469 * 2 ^ 59
def prefixEnd_1593469 : Nat := 4983230072969 + 3 ^ 40 * 1593469 * 2
def baseEnd_1593469 : Nat := 181825667786518061979839

theorem tailTrace_1593469 : CollatzResearch.WordTrace tailWord_1593469 prefixEnd_1593469 181825667786518061979839 := by
  unfold tailWord_1593469
  simp only [CollatzResearch.WordTrace]
  refine ⟨58118589064141430683911461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38745726042760953789274307 58118589064141430683911461)
  ·
    refine ⟨10897235449526518253233399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58118589064141430683911461 10897235449526518253233399)
    ·
      refine ⟨16345853174289777379850099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10897235449526518253233399 16345853174289777379850099)
      ·
        refine ⟨24518779761434666069775149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16345853174289777379850099 24518779761434666069775149)
        ·
          refine ⟨9194542410537999776165681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24518779761434666069775149 9194542410537999776165681)
          ·
            refine ⟨6895906807903499832124261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9194542410537999776165681 6895906807903499832124261)
            ·
              refine ⟨1292982526481906218523299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6895906807903499832124261 1292982526481906218523299)
              ·
                refine ⟨1939473789722859327784949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1292982526481906218523299 1939473789722859327784949)
                ·
                  refine ⟨181825667786518061979839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1939473789722859327784949 181825667786518061979839)
                  ·
                    rfl

theorem cell22_1593469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 1, 5].length) (baseStart_1593469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1593469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1593469 prefixEnd_1593469 := by exact prefixLift 1593469
  have htrace : WordTrace (prefixWord ++ tailWord_1593469) baseStart_1593469 baseEnd_1593469 := by
    simpa [prefixWord, tailWord_1593469, baseEnd_1593469] using wordTrace_append hprefix tailTrace_1593469
  have hstable : (prefixWord ++ tailWord_1593469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593469).length < 2 ^ (prefixWord ++ tailWord_1593469).sum := by decide
  have hdescent : baseEnd_1593469 < baseStart_1593469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593529 : List Nat := [1, 2, 1, 4, 1, 2, 1, 5, 2, 3]
def baseStart_1593529 : Nat := 118140960795 + 1593529 * 2 ^ 59
def prefixEnd_1593529 : Nat := 4983230072969 + 3 ^ 40 * 1593529 * 2
def baseEnd_1593529 : Nat := 545497542585734029439333

theorem tailTrace_1593529 : CollatzResearch.WordTrace tailWord_1593529 prefixEnd_1593529 545497542585734029439333 := by
  unfold tailWord_1593529
  simp only [CollatzResearch.WordTrace]
  refine ⟨58120777443924060931095641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38747184962616040620730427 58120777443924060931095641)
  ·
    refine ⟨43590583082943045698321731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58120777443924060931095641 43590583082943045698321731)
    ·
      refine ⟨65385874624414568547482597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43590583082943045698321731 65385874624414568547482597)
      ·
        refine ⟨12259851492077731602652987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65385874624414568547482597 12259851492077731602652987)
        ·
          refine ⟨18389777238116597403979481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12259851492077731602652987 18389777238116597403979481)
          ·
            refine ⟨13792332928587448052984611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18389777238116597403979481 13792332928587448052984611)
            ·
              refine ⟨20688499392881172079476917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13792332928587448052984611 20688499392881172079476917)
              ·
                refine ⟨1939546818082609882450961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20688499392881172079476917 1939546818082609882450961)
                ·
                  refine ⟨1454660113561957411838221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1939546818082609882450961 1454660113561957411838221)
                  ·
                    refine ⟨545497542585734029439333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1454660113561957411838221 545497542585734029439333)
                    ·
                      rfl

theorem cell22_1593529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 5, 2, 3].length) (baseStart_1593529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1593529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1593529 prefixEnd_1593529 := by exact prefixLift 1593529
  have htrace : WordTrace (prefixWord ++ tailWord_1593529) baseStart_1593529 baseEnd_1593529 := by
    simpa [prefixWord, tailWord_1593529, baseEnd_1593529] using wordTrace_append hprefix tailTrace_1593529
  have hstable : (prefixWord ++ tailWord_1593529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593529).length < 2 ^ (prefixWord ++ tailWord_1593529).sum := by decide
  have hdescent : baseEnd_1593529 < baseStart_1593529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593548 : List Nat := [2, 2, 1, 6, 1, 1, 2, 3, 4]
def baseStart_1593548 : Nat := 118140960795 + 1593548 * 2 ^ 59
def prefixEnd_1593548 : Nat := 4983230072969 + 3 ^ 40 * 1593548 * 2
def baseEnd_1593548 : Nat := 181834682224674771071425

theorem tailTrace_1593548 : CollatzResearch.WordTrace tailWord_1593548 prefixEnd_1593548 181834682224674771071425 := by
  unfold tailWord_1593548
  simp only [CollatzResearch.WordTrace]
  refine ⟨29060735215427613588018649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38747646953903484784024865 29060735215427613588018649)
  ·
    refine ⟨21795551411570710191013987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29060735215427613588018649 21795551411570710191013987)
    ·
      refine ⟨32693327117356065286520981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21795551411570710191013987 32693327117356065286520981)
      ·
        refine ⟨1532499708626065560305671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 32693327117356065286520981 1532499708626065560305671)
        ·
          refine ⟨2298749562939098340458507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1532499708626065560305671 2298749562939098340458507)
          ·
            refine ⟨3448124344408647510687761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2298749562939098340458507 3448124344408647510687761)
            ·
              refine ⟨2586093258306485633015821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3448124344408647510687761 2586093258306485633015821)
              ·
                refine ⟨969784971864932112380933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2586093258306485633015821 969784971864932112380933)
                ·
                  refine ⟨181834682224674771071425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 969784971864932112380933 181834682224674771071425)
                  ·
                    rfl

theorem cell22_1593548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 3, 4].length) (baseStart_1593548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1593548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1593548 prefixEnd_1593548 := by exact prefixLift 1593548
  have htrace : WordTrace (prefixWord ++ tailWord_1593548) baseStart_1593548 baseEnd_1593548 := by
    simpa [prefixWord, tailWord_1593548, baseEnd_1593548] using wordTrace_append hprefix tailTrace_1593548
  have hstable : (prefixWord ++ tailWord_1593548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593548).length < 2 ^ (prefixWord ++ tailWord_1593548).sum := by decide
  have hdescent : baseEnd_1593548 < baseStart_1593548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593608 : List Nat := [2, 1, 3, 2, 3, 1, 3, 3, 1, 3]
def baseStart_1593608 : Nat := 118140960795 + 1593608 * 2 ^ 59
def prefixEnd_1593608 : Nat := 4983230072969 + 3 ^ 40 * 1593608 * 2
def baseEnd_1593608 : Nat := 545524585900204156714091

theorem tailTrace_1593608 : CollatzResearch.WordTrace tailWord_1593608 prefixEnd_1593608 545524585900204156714091 := by
  unfold tailWord_1593608
  simp only [CollatzResearch.WordTrace]
  refine ⟨29061829405318928711610739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38749105873758571615480985 29061829405318928711610739)
  ·
    refine ⟨43592744107978393067416109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29061829405318928711610739 43592744107978393067416109)
    ·
      refine ⟨16347279040491897400281041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43592744107978393067416109 16347279040491897400281041)
      ·
        refine ⟨12260459280368923050210781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16347279040491897400281041 12260459280368923050210781)
        ·
          refine ⟨4597672230138346143829043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12260459280368923050210781 4597672230138346143829043)
          ·
            refine ⟨6896508345207519215743565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4597672230138346143829043 6896508345207519215743565)
            ·
              refine ⟨2586190629452819705903837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6896508345207519215743565 2586190629452819705903837)
              ·
                refine ⟨969821486044807389713939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2586190629452819705903837 969821486044807389713939)
                ·
                  refine ⟨1454732229067211084570909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 969821486044807389713939 1454732229067211084570909)
                  ·
                    refine ⟨545524585900204156714091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1454732229067211084570909 545524585900204156714091)
                    ·
                      rfl

theorem cell22_1593608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 3, 1, 3].length) (baseStart_1593608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1593608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1593608 prefixEnd_1593608 := by exact prefixLift 1593608
  have htrace : WordTrace (prefixWord ++ tailWord_1593608) baseStart_1593608 baseEnd_1593608 := by
    simpa [prefixWord, tailWord_1593608, baseEnd_1593608] using wordTrace_append hprefix tailTrace_1593608
  have hstable : (prefixWord ++ tailWord_1593608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593608).length < 2 ^ (prefixWord ++ tailWord_1593608).sum := by decide
  have hdescent : baseEnd_1593608 < baseStart_1593608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593664 : List Nat := [2, 1, 1, 2, 2, 1, 2, 4, 4, 3]
def baseStart_1593664 : Nat := 118140960795 + 1593664 * 2 ^ 59
def prefixEnd_1593664 : Nat := 4983230072969 + 3 ^ 40 * 1593664 * 2
def baseEnd_1593664 : Nat := 545543755844638677313919

theorem tailTrace_1593664 : CollatzResearch.WordTrace tailWord_1593664 prefixEnd_1593664 545543755844638677313919 := by
  unfold tailWord_1593664
  simp only [CollatzResearch.WordTrace]
  refine ⟨29062850649217489493630023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38750467532289985991506697 29062850649217489493630023)
  ·
    refine ⟨43594275973826234240445035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29062850649217489493630023 43594275973826234240445035)
    ·
      refine ⟨65391413960739351360667553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43594275973826234240445035 65391413960739351360667553)
      ·
        refine ⟨49043560470554513520500665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65391413960739351360667553 49043560470554513520500665)
        ·
          refine ⟨36782670352915885140375499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49043560470554513520500665 36782670352915885140375499)
          ·
            refine ⟨55174005529373827710563249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36782670352915885140375499 55174005529373827710563249)
            ·
              refine ⟨41380504147030370782922437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55174005529373827710563249 41380504147030370782922437)
              ·
                refine ⟨7758844527568194521797957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41380504147030370782922437 7758844527568194521797957)
                ·
                  refine ⟨1454783348919036472837117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7758844527568194521797957 1454783348919036472837117)
                  ·
                    refine ⟨545543755844638677313919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1454783348919036472837117 545543755844638677313919)
                    ·
                      rfl

theorem cell22_1593664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 4, 3].length) (baseStart_1593664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1593664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1593664 prefixEnd_1593664 := by exact prefixLift 1593664
  have htrace : WordTrace (prefixWord ++ tailWord_1593664) baseStart_1593664 baseEnd_1593664 := by
    simpa [prefixWord, tailWord_1593664, baseEnd_1593664] using wordTrace_append hprefix tailTrace_1593664
  have hstable : (prefixWord ++ tailWord_1593664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593664).length < 2 ^ (prefixWord ++ tailWord_1593664).sum := by decide
  have hdescent : baseEnd_1593664 < baseStart_1593664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593681 : List Nat := [1, 2, 2, 1, 4, 2, 1, 4, 2, 3]
def baseStart_1593681 : Nat := 118140960795 + 1593681 * 2 ^ 59
def prefixEnd_1593681 : Nat := 4983230072969 + 3 ^ 40 * 1593681 * 2
def baseEnd_1593681 : Nat := 545549575292056299638867

theorem tailTrace_1593681 : CollatzResearch.WordTrace tailWord_1593681 prefixEnd_1593681 545549575292056299638867 := by
  unfold tailWord_1593681
  simp only [CollatzResearch.WordTrace]
  refine ⟨58126321339373390890628897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38750880892915593927085931 58126321339373390890628897)
  ·
    refine ⟨43594741004530043167971673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58126321339373390890628897 43594741004530043167971673)
    ·
      refine ⟨32696055753397532375978755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43594741004530043167971673 32696055753397532375978755)
      ·
        refine ⟨49044083630096298563968133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32696055753397532375978755 49044083630096298563968133)
        ·
          refine ⟨9195765680643055980744025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49044083630096298563968133 9195765680643055980744025)
          ·
            refine ⟨6896824260482291985558019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9195765680643055980744025 6896824260482291985558019)
            ·
              refine ⟨10345236390723437978337029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6896824260482291985558019 10345236390723437978337029)
              ·
                refine ⟨1939731823260644620938193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10345236390723437978337029 1939731823260644620938193)
                ·
                  refine ⟨1454798867445483465703645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1939731823260644620938193 1454798867445483465703645)
                  ·
                    refine ⟨545549575292056299638867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1454798867445483465703645 545549575292056299638867)
                    ·
                      rfl

theorem cell22_1593681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 4, 2, 3].length) (baseStart_1593681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1593681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1593681 prefixEnd_1593681 := by exact prefixLift 1593681
  have htrace : WordTrace (prefixWord ++ tailWord_1593681) baseStart_1593681 baseEnd_1593681 := by
    simpa [prefixWord, tailWord_1593681, baseEnd_1593681] using wordTrace_append hprefix tailTrace_1593681
  have hstable : (prefixWord ++ tailWord_1593681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593681).length < 2 ^ (prefixWord ++ tailWord_1593681).sum := by decide
  have hdescent : baseEnd_1593681 < baseStart_1593681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593698 : List Nat := [3, 3, 2, 1, 1, 2, 2, 3, 2, 3]
def baseStart_1593698 : Nat := 118140960795 + 1593698 * 2 ^ 59
def prefixEnd_1593698 : Nat := 4983230072969 + 3 ^ 40 * 1593698 * 2
def baseEnd_1593698 : Nat := 545555394739473921963815

theorem tailTrace_1593698 : CollatzResearch.WordTrace tailWord_1593698 prefixEnd_1593698 545555394739473921963815 := by
  unfold tailWord_1593698
  simp only [CollatzResearch.WordTrace]
  refine ⟨14531735345077950698499437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38751294253541201862665165 14531735345077950698499437)
  ·
    refine ⟨5449400754404231511937289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14531735345077950698499437 5449400754404231511937289)
    ·
      refine ⟨4087050565803173633952967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5449400754404231511937289 4087050565803173633952967)
      ·
        refine ⟨6130575848704760450929451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4087050565803173633952967 6130575848704760450929451)
        ·
          refine ⟨9195863773057140676394177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6130575848704760450929451 9195863773057140676394177)
          ·
            refine ⟨6896897829792855507295633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9195863773057140676394177 6896897829792855507295633)
            ·
              refine ⟨5172673372344641630471725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6896897829792855507295633 5172673372344641630471725)
              ·
                refine ⟨1939752514629240611426897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5172673372344641630471725 1939752514629240611426897)
                ·
                  refine ⟨1454814385971930458570173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1939752514629240611426897 1454814385971930458570173)
                  ·
                    refine ⟨545555394739473921963815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1454814385971930458570173 545555394739473921963815)
                    ·
                      rfl

theorem cell22_1593698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_1593698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1593698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1593698 prefixEnd_1593698 := by exact prefixLift 1593698
  have htrace : WordTrace (prefixWord ++ tailWord_1593698) baseStart_1593698 baseEnd_1593698 := by
    simpa [prefixWord, tailWord_1593698, baseEnd_1593698] using wordTrace_append hprefix tailTrace_1593698
  have hstable : (prefixWord ++ tailWord_1593698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593698).length < 2 ^ (prefixWord ++ tailWord_1593698).sum := by decide
  have hdescent : baseEnd_1593698 < baseStart_1593698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593739 : List Nat := [1, 1, 1, 1, 4, 5, 1, 1, 7]
def baseStart_1593739 : Nat := 118140960795 + 1593739 * 2 ^ 59
def prefixEnd_1593739 : Nat := 4983230072969 + 3 ^ 40 * 1593739 * 2
def baseEnd_1593739 : Nat := 181856476625787827229563

theorem tailTrace_1593739 : CollatzResearch.WordTrace tailWord_1593739 prefixEnd_1593739 181856476625787827229563 := by
  unfold tailWord_1593739
  simp only [CollatzResearch.WordTrace]
  refine ⟨58128436773163266796240271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38752291182108844530826847 58128436773163266796240271)
  ·
    refine ⟨87192655159744900194360407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58128436773163266796240271 87192655159744900194360407)
    ·
      refine ⟨130788982739617350291540611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87192655159744900194360407 130788982739617350291540611)
      ·
        refine ⟨196183474109426025437310917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130788982739617350291540611 196183474109426025437310917)
        ·
          refine ⟨36784401395517379769495797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 196183474109426025437310917 36784401395517379769495797)
          ·
            refine ⟨3448537630829754353390231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36784401395517379769495797 3448537630829754353390231)
            ·
              refine ⟨5172806446244631530085347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3448537630829754353390231 5172806446244631530085347)
              ·
                refine ⟨7759209669366947295128021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5172806446244631530085347 7759209669366947295128021)
                ·
                  refine ⟨181856476625787827229563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7759209669366947295128021 181856476625787827229563)
                  ·
                    rfl

theorem cell22_1593739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 7].length) (baseStart_1593739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1593739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1593739 prefixEnd_1593739 := by exact prefixLift 1593739
  have htrace : WordTrace (prefixWord ++ tailWord_1593739) baseStart_1593739 baseEnd_1593739 := by
    simpa [prefixWord, tailWord_1593739, baseEnd_1593739] using wordTrace_append hprefix tailTrace_1593739
  have hstable : (prefixWord ++ tailWord_1593739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593739).length < 2 ^ (prefixWord ++ tailWord_1593739).sum := by decide
  have hdescent : baseEnd_1593739 < baseStart_1593739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593769 : List Nat := [1, 2, 1, 1, 1, 1, 3, 5, 3, 4]
def baseStart_1593769 : Nat := 118140960795 + 1593769 * 2 ^ 59
def prefixEnd_1593769 : Nat := 4983230072969 + 3 ^ 40 * 1593769 * 2
def baseEnd_1593769 : Nat := 545579699490453403438597

theorem tailTrace_1593769 : CollatzResearch.WordTrace tailWord_1593769 prefixEnd_1593769 545579699490453403438597 := by
  unfold tailWord_1593769
  simp only [CollatzResearch.WordTrace]
  refine ⟨58129530963054581919832361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38753020642036387946554907 58129530963054581919832361)
  ·
    refine ⟨43597148222290936439874271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58129530963054581919832361 43597148222290936439874271)
    ·
      refine ⟨65395722333436404659811407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43597148222290936439874271 65395722333436404659811407)
      ·
        refine ⟨98093583500154606989717111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65395722333436404659811407 98093583500154606989717111)
        ·
          refine ⟨147140375250231910484575667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98093583500154606989717111 147140375250231910484575667)
          ·
            refine ⟨220710562875347865726863501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147140375250231910484575667 220710562875347865726863501)
            ·
              refine ⟨82766461078255449647573813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 220710562875347865726863501 82766461078255449647573813)
              ·
                refine ⟨7759355726086448404460045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82766461078255449647573813 7759355726086448404460045)
                ·
                  refine ⟨2909758397282418151672517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7759355726086448404460045 2909758397282418151672517)
                  ·
                    refine ⟨545579699490453403438597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2909758397282418151672517 545579699490453403438597)
                    ·
                      rfl

theorem cell22_1593769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 3, 4].length) (baseStart_1593769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1593769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1593769 prefixEnd_1593769 := by exact prefixLift 1593769
  have htrace : WordTrace (prefixWord ++ tailWord_1593769) baseStart_1593769 baseEnd_1593769 := by
    simpa [prefixWord, tailWord_1593769, baseEnd_1593769] using wordTrace_append hprefix tailTrace_1593769
  have hstable : (prefixWord ++ tailWord_1593769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593769).length < 2 ^ (prefixWord ++ tailWord_1593769).sum := by decide
  have hdescent : baseEnd_1593769 < baseStart_1593769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593801 : List Nat := [1, 2, 1, 1, 2, 1, 4, 6, 4]
def baseStart_1593801 : Nat := 118140960795 + 1593801 * 2 ^ 59
def prefixEnd_1593801 : Nat := 4983230072969 + 3 ^ 40 * 1593801 * 2
def baseEnd_1593801 : Nat := 181863551248138662212833

theorem tailTrace_1593801 : CollatzResearch.WordTrace tailWord_1593801 prefixEnd_1593801 181863551248138662212833 := by
  unfold tailWord_1593801
  simp only [CollatzResearch.WordTrace]
  refine ⟨58130698098938651384997257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38753798732625767589998171 58130698098938651384997257)
  ·
    refine ⟨43598023574203988538747943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58130698098938651384997257 43598023574203988538747943)
    ·
      refine ⟨65397035361305982808121915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43598023574203988538747943 65397035361305982808121915)
      ·
        refine ⟨98095553041958974212182873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65397035361305982808121915 98095553041958974212182873)
        ·
          refine ⟨73571664781469230659137155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98095553041958974212182873 73571664781469230659137155)
          ·
            refine ⟨110357497172203845988705733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73571664781469230659137155 110357497172203845988705733)
            ·
              refine ⟨20692030719788221122882325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110357497172203845988705733 20692030719788221122882325)
              ·
                refine ⟨969938939990072865135109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20692030719788221122882325 969938939990072865135109)
                ·
                  refine ⟨181863551248138662212833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 969938939990072865135109 181863551248138662212833)
                  ·
                    rfl

theorem cell22_1593801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 6, 4].length) (baseStart_1593801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1593801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1593801 prefixEnd_1593801 := by exact prefixLift 1593801
  have htrace : WordTrace (prefixWord ++ tailWord_1593801) baseStart_1593801 baseEnd_1593801 := by
    simpa [prefixWord, tailWord_1593801, baseEnd_1593801] using wordTrace_append hprefix tailTrace_1593801
  have hstable : (prefixWord ++ tailWord_1593801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593801).length < 2 ^ (prefixWord ++ tailWord_1593801).sum := by decide
  have hdescent : baseEnd_1593801 < baseStart_1593801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593859 : List Nat := [1, 1, 1, 3, 2, 1, 3, 1, 1, 8]
def baseStart_1593859 : Nat := 118140960795 + 1593859 * 2 ^ 59
def prefixEnd_1593859 : Nat := 4983230072969 + 3 ^ 40 * 1593859 * 2
def baseEnd_1593859 : Nat := 545610508329723168688321

theorem tailTrace_1593859 : CollatzResearch.WordTrace tailWord_1593859 prefixEnd_1593859 545610508329723168688321 := by
  unfold tailWord_1593859
  simp only [CollatzResearch.WordTrace]
  refine ⟨58132813532728527290608631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38755209021819018193739087 58132813532728527290608631)
  ·
    refine ⟨87199220299092790935912947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58132813532728527290608631 87199220299092790935912947)
    ·
      refine ⟨130798830448639186403869421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87199220299092790935912947 130798830448639186403869421)
      ·
        refine ⟨49049561418239694901451033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130798830448639186403869421 49049561418239694901451033)
        ·
          refine ⟨36787171063679771176088275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49049561418239694901451033 36787171063679771176088275)
          ·
            refine ⟨55180756595519656764132413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36787171063679771176088275 55180756595519656764132413)
            ·
              refine ⟨20692783723319871286549655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55180756595519656764132413 20692783723319871286549655)
              ·
                refine ⟨31039175584979806929824483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20692783723319871286549655 31039175584979806929824483)
                ·
                  refine ⟨46558763377469710394736725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31039175584979806929824483 46558763377469710394736725)
                  ·
                    refine ⟨545610508329723168688321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 46558763377469710394736725 545610508329723168688321)
                    ·
                      rfl

theorem cell22_1593859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 8].length) (baseStart_1593859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1593859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1593859 prefixEnd_1593859 := by exact prefixLift 1593859
  have htrace : WordTrace (prefixWord ++ tailWord_1593859) baseStart_1593859 baseEnd_1593859 := by
    simpa [prefixWord, tailWord_1593859, baseEnd_1593859] using wordTrace_append hprefix tailTrace_1593859
  have hstable : (prefixWord ++ tailWord_1593859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593859).length < 2 ^ (prefixWord ++ tailWord_1593859).sum := by decide
  have hdescent : baseEnd_1593859 < baseStart_1593859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593863 : List Nat := [1, 1, 4, 3, 3, 2, 1, 7]
def baseStart_1593863 : Nat := 118140960795 + 1593863 * 2 ^ 59
def prefixEnd_1593863 : Nat := 4983230072969 + 3 ^ 40 * 1593863 * 2
def baseEnd_1593863 : Nat := 60623541956829832398701

theorem tailTrace_1593863 : CollatzResearch.WordTrace tailWord_1593863 prefixEnd_1593863 60623541956829832398701 := by
  unfold tailWord_1593863
  simp only [CollatzResearch.WordTrace]
  refine ⟨58132959424714035973754243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38755306283142690649169495 58132959424714035973754243)
  ·
    refine ⟨87199439137071053960631365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58132959424714035973754243 87199439137071053960631365)
    ·
      refine ⟨16349894838200822617618381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87199439137071053960631365 16349894838200822617618381)
      ·
        refine ⟨6131210564325308481606893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16349894838200822617618381 6131210564325308481606893)
        ·
          refine ⟨2299203961621990680602585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6131210564325308481606893 2299203961621990680602585)
          ·
            refine ⟨1724402971216493010451939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2299203961621990680602585 1724402971216493010451939)
            ·
              refine ⟨2586604456824739515677909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1724402971216493010451939 2586604456824739515677909)
              ·
                refine ⟨60623541956829832398701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2586604456824739515677909 60623541956829832398701)
                ·
                  rfl

theorem cell22_1593863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 7].length) (baseStart_1593863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1593863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1593863 prefixEnd_1593863 := by exact prefixLift 1593863
  have htrace : WordTrace (prefixWord ++ tailWord_1593863) baseStart_1593863 baseEnd_1593863 := by
    simpa [prefixWord, tailWord_1593863, baseEnd_1593863] using wordTrace_append hprefix tailTrace_1593863
  have hstable : (prefixWord ++ tailWord_1593863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593863).length < 2 ^ (prefixWord ++ tailWord_1593863).sum := by decide
  have hdescent : baseEnd_1593863 < baseStart_1593863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593901 : List Nat := [1, 5, 4, 1, 1, 2, 1, 2, 2, 3]
def baseStart_1593901 : Nat := 118140960795 + 1593901 * 2 ^ 59
def prefixEnd_1593901 : Nat := 4983230072969 + 3 ^ 40 * 1593901 * 2
def baseEnd_1593901 : Nat := 545624885788049059138193

theorem tailTrace_1593901 : CollatzResearch.WordTrace tailWord_1593901 prefixEnd_1593901 545624885788049059138193 := by
  unfold tailWord_1593901
  simp only [CollatzResearch.WordTrace]
  refine ⟨58134345398576368463637557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38756230265717578975758371 58134345398576368463637557)
  ·
    refine ⟨5450094881116534543466021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58134345398576368463637557 5450094881116534543466021)
    ·
      refine ⟨1021892790209350226899879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5450094881116534543466021 1021892790209350226899879)
      ·
        refine ⟨1532839185314025340349819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1021892790209350226899879 1532839185314025340349819)
        ·
          refine ⟨2299258777971038010524729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1532839185314025340349819 2299258777971038010524729)
          ·
            refine ⟨1724444083478278507893547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2299258777971038010524729 1724444083478278507893547)
            ·
              refine ⟨2586666125217417761840321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1724444083478278507893547 2586666125217417761840321)
              ·
                refine ⟨1939999593913063321380241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2586666125217417761840321 1939999593913063321380241)
                ·
                  refine ⟨1454999695434797491035181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1939999593913063321380241 1454999695434797491035181)
                  ·
                    refine ⟨545624885788049059138193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1454999695434797491035181 545624885788049059138193)
                    ·
                      rfl

theorem cell22_1593901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_1593901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1593901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1593901 prefixEnd_1593901 := by exact prefixLift 1593901
  have htrace : WordTrace (prefixWord ++ tailWord_1593901) baseStart_1593901 baseEnd_1593901 := by
    simpa [prefixWord, tailWord_1593901, baseEnd_1593901] using wordTrace_append hprefix tailTrace_1593901
  have hstable : (prefixWord ++ tailWord_1593901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593901).length < 2 ^ (prefixWord ++ tailWord_1593901).sum := by decide
  have hdescent : baseEnd_1593901 < baseStart_1593901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593906 : List Nat := [3, 2, 1, 1, 2, 1, 3, 2, 2, 5]
def baseStart_1593906 : Nat := 118140960795 + 1593906 * 2 ^ 59
def prefixEnd_1593906 : Nat := 4983230072969 + 3 ^ 40 * 1593906 * 2
def baseEnd_1593906 : Nat := 545626597390230712763177

theorem tailTrace_1593906 : CollatzResearch.WordTrace tailWord_1593906 prefixEnd_1593906 545626597390230712763177 := by
  unfold tailWord_1593906
  simp only [CollatzResearch.WordTrace]
  refine ⟨14533631940889563579392393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38756351842372169545046381 14533631940889563579392393)
  ·
    refine ⟨10900223955667172684544295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14533631940889563579392393 10900223955667172684544295)
    ·
      refine ⟨16350335933500759026816443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10900223955667172684544295 16350335933500759026816443)
      ·
        refine ⟨24525503900251138540224665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16350335933500759026816443 24525503900251138540224665)
        ·
          refine ⟨18394127925188353905168499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24525503900251138540224665 18394127925188353905168499)
          ·
            refine ⟨27591191887782530857752749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18394127925188353905168499 27591191887782530857752749)
            ·
              refine ⟨10346696957918449071657281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27591191887782530857752749 10346696957918449071657281)
              ·
                refine ⟨7760022718438836803742961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10346696957918449071657281 7760022718438836803742961)
                ·
                  refine ⟨5820017038829127602807221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7760022718438836803742961 5820017038829127602807221)
                  ·
                    refine ⟨545626597390230712763177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5820017038829127602807221 545626597390230712763177)
                    ·
                      rfl

theorem cell22_1593906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_1593906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1593906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1593906 prefixEnd_1593906 := by exact prefixLift 1593906
  have htrace : WordTrace (prefixWord ++ tailWord_1593906) baseStart_1593906 baseEnd_1593906 := by
    simpa [prefixWord, tailWord_1593906, baseEnd_1593906] using wordTrace_append hprefix tailTrace_1593906
  have hstable : (prefixWord ++ tailWord_1593906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593906).length < 2 ^ (prefixWord ++ tailWord_1593906).sum := by decide
  have hdescent : baseEnd_1593906 < baseStart_1593906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593951 : List Nat := [1, 1, 2, 3, 1, 1, 1, 6, 1, 5]
def baseStart_1593951 : Nat := 118140960795 + 1593951 * 2 ^ 59
def prefixEnd_1593951 : Nat := 4983230072969 + 3 ^ 40 * 1593951 * 2
def baseEnd_1593951 : Nat := 545642001809865595388039

theorem tailTrace_1593951 : CollatzResearch.WordTrace tailWord_1593951 prefixEnd_1593951 545642001809865595388039 := by
  unfold tailWord_1593951
  simp only [CollatzResearch.WordTrace]
  refine ⟨58136169048395227002957707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38757446032263484668638471 58136169048395227002957707)
  ·
    refine ⟨87204253572592840504436561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58136169048395227002957707 87204253572592840504436561)
    ·
      refine ⟨65403190179444630378327421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87204253572592840504436561 65403190179444630378327421)
      ·
        refine ⟨24526196317291736391872783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65403190179444630378327421 24526196317291736391872783)
        ·
          refine ⟨36789294475937604587809175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24526196317291736391872783 36789294475937604587809175)
          ·
            refine ⟨55183941713906406881713763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36789294475937604587809175 55183941713906406881713763)
            ·
              refine ⟨82775912570859610322570645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55183941713906406881713763 82775912570859610322570645)
              ·
                refine ⟨3880120901759044233870499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 82775912570859610322570645 3880120901759044233870499)
                ·
                  refine ⟨5820181352638566350805749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3880120901759044233870499 5820181352638566350805749)
                  ·
                    refine ⟨545642001809865595388039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5820181352638566350805749 545642001809865595388039)
                    ·
                      rfl

theorem cell22_1593951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 5].length) (baseStart_1593951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1593951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1593951 prefixEnd_1593951 := by exact prefixLift 1593951
  have htrace : WordTrace (prefixWord ++ tailWord_1593951) baseStart_1593951 baseEnd_1593951 := by
    simpa [prefixWord, tailWord_1593951, baseEnd_1593951] using wordTrace_append hprefix tailTrace_1593951
  have hstable : (prefixWord ++ tailWord_1593951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593951).length < 2 ^ (prefixWord ++ tailWord_1593951).sum := by decide
  have hdescent : baseEnd_1593951 < baseStart_1593951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593970 : List Nat := [3, 2, 1, 2, 4, 2, 1, 1, 6]
def baseStart_1593970 : Nat := 118140960795 + 1593970 * 2 ^ 59
def prefixEnd_1593970 : Nat := 4983230072969 + 3 ^ 40 * 1593970 * 2
def baseEnd_1593970 : Nat := 181882835299385293054327

theorem tailTrace_1593970 : CollatzResearch.WordTrace tailWord_1593970 prefixEnd_1593970 181882835299385293054327 := by
  unfold tailWord_1593970
  simp only [CollatzResearch.WordTrace]
  refine ⟨14534215508831598311974841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38757908023550928831932909 14534215508831598311974841)
  ·
    refine ⟨10900661631623698733981131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14534215508831598311974841 10900661631623698733981131)
    ·
      refine ⟨16350992447435548100971697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10900661631623698733981131 16350992447435548100971697)
      ·
        refine ⟨12263244335576661075728773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16350992447435548100971697 12263244335576661075728773)
        ·
          refine ⟨2299358312920623951699145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12263244335576661075728773 2299358312920623951699145)
          ·
            refine ⟨1724518734690467963774359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2299358312920623951699145 1724518734690467963774359)
            ·
              refine ⟨2586778102035701945661539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1724518734690467963774359 2586778102035701945661539)
              ·
                refine ⟨3880167153053552918492309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2586778102035701945661539 3880167153053552918492309)
                ·
                  refine ⟨181882835299385293054327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3880167153053552918492309 181882835299385293054327)
                  ·
                    rfl

theorem cell22_1593970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 6].length) (baseStart_1593970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1593970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1593970 prefixEnd_1593970 := by exact prefixLift 1593970
  have htrace : WordTrace (prefixWord ++ tailWord_1593970) baseStart_1593970 baseEnd_1593970 := by
    simpa [prefixWord, tailWord_1593970, baseEnd_1593970] using wordTrace_append hprefix tailTrace_1593970
  have hstable : (prefixWord ++ tailWord_1593970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593970).length < 2 ^ (prefixWord ++ tailWord_1593970).sum := by decide
  have hdescent : baseEnd_1593970 < baseStart_1593970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593985 : List Nat := [1, 2, 4, 2, 1, 1, 3, 3, 2, 3]
def baseStart_1593985 : Nat := 118140960795 + 1593985 * 2 ^ 59
def prefixEnd_1593985 : Nat := 4983230072969 + 3 ^ 40 * 1593985 * 2
def baseEnd_1593985 : Nat := 545653640704700840037935

theorem tailTrace_1593985 : CollatzResearch.WordTrace tailWord_1593985 prefixEnd_1593985 545653640704700840037935 := by
  unfold tailWord_1593985
  simp only [CollatzResearch.WordTrace]
  refine ⟨58137409130272050809695409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38758272753514700539796939 58137409130272050809695409)
  ·
    refine ⟨43603056847704038107271557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58137409130272050809695409 43603056847704038107271557)
    ·
      refine ⟨8175573158944507145113417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43603056847704038107271557 8175573158944507145113417)
      ·
        refine ⟨6131679869208380358835063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8175573158944507145113417 6131679869208380358835063)
        ·
          refine ⟨9197519803812570538252595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6131679869208380358835063 9197519803812570538252595)
          ·
            refine ⟨13796279705718855807378893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9197519803812570538252595 13796279705718855807378893)
            ·
              refine ⟨5173604889644570927767085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13796279705718855807378893 5173604889644570927767085)
              ·
                refine ⟨1940101833616714097912657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5173604889644570927767085 1940101833616714097912657)
                ·
                  refine ⟨1455076375212535573434493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1940101833616714097912657 1455076375212535573434493)
                  ·
                    refine ⟨545653640704700840037935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1455076375212535573434493 545653640704700840037935)
                    ·
                      rfl

theorem cell22_1593985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_1593985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1593985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1593985 prefixEnd_1593985 := by exact prefixLift 1593985
  have htrace : WordTrace (prefixWord ++ tailWord_1593985) baseStart_1593985 baseEnd_1593985 := by
    simpa [prefixWord, tailWord_1593985, baseEnd_1593985] using wordTrace_append hprefix tailTrace_1593985
  have hstable : (prefixWord ++ tailWord_1593985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593985).length < 2 ^ (prefixWord ++ tailWord_1593985).sum := by decide
  have hdescent : baseEnd_1593985 < baseStart_1593985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594120 : List Nat := [2, 1, 3, 2, 2, 2, 1, 2, 4, 3]
def baseStart_1594120 : Nat := 118140960795 + 1594120 * 2 ^ 59
def prefixEnd_1594120 : Nat := 4983230072969 + 3 ^ 40 * 1594120 * 2
def baseEnd_1594120 : Nat := 545699853963605487912521

theorem tailTrace_1594120 : CollatzResearch.WordTrace tailWord_1594120 prefixEnd_1594120 545699853963605487912521 := by
  unfold tailWord_1594120
  simp only [CollatzResearch.WordTrace]
  refine ⟨29071166492391484432929907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38761555323188645910573209 29071166492391484432929907)
  ·
    refine ⟨43606749738587226649394861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29071166492391484432929907 43606749738587226649394861)
    ·
      refine ⟨16352531151970209993523073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43606749738587226649394861 16352531151970209993523073)
      ·
        refine ⟨12264398363977657495142305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16352531151970209993523073 12264398363977657495142305)
        ·
          refine ⟨9198298772983243121356729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12264398363977657495142305 9198298772983243121356729)
          ·
            refine ⟨6898724079737432341017547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9198298772983243121356729 6898724079737432341017547)
            ·
              refine ⟨10348086119606148511526321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6898724079737432341017547 10348086119606148511526321)
              ·
                refine ⟨7761064589704611383644741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10348086119606148511526321 7761064589704611383644741)
                ·
                  refine ⟨1455199610569614634433389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7761064589704611383644741 1455199610569614634433389)
                  ·
                    refine ⟨545699853963605487912521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1455199610569614634433389 545699853963605487912521)
                    ·
                      rfl

theorem cell22_1594120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 4, 3].length) (baseStart_1594120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1594120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1594120 prefixEnd_1594120 := by exact prefixLift 1594120
  have htrace : WordTrace (prefixWord ++ tailWord_1594120) baseStart_1594120 baseEnd_1594120 := by
    simpa [prefixWord, tailWord_1594120, baseEnd_1594120] using wordTrace_append hprefix tailTrace_1594120
  have hstable : (prefixWord ++ tailWord_1594120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594120).length < 2 ^ (prefixWord ++ tailWord_1594120).sum := by decide
  have hdescent : baseEnd_1594120 < baseStart_1594120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594199 : List Nat := [1, 1, 3, 2, 4, 2, 1, 4, 1, 3]
def baseStart_1594199 : Nat := 118140960795 + 1594199 * 2 ^ 59
def prefixEnd_1594199 : Nat := 4983230072969 + 3 ^ 40 * 1594199 * 2
def baseEnd_1594199 : Nat := 545726897278075615187279

theorem tailTrace_1594199 : CollatzResearch.WordTrace tailWord_1594199 prefixEnd_1594199 545726897278075615187279 := by
  unfold tailWord_1594199
  simp only [CollatzResearch.WordTrace]
  refine ⟨58145214351496765357985651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38763476234331176905323767 58145214351496765357985651)
  ·
    refine ⟨87217821527245148036978477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58145214351496765357985651 87217821527245148036978477)
    ·
      refine ⟨32706683072716930513866929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87217821527245148036978477 32706683072716930513866929)
      ·
        refine ⟨24530012304537697885400197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32706683072716930513866929 24530012304537697885400197)
        ·
          refine ⟨4599377307100818353512537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24530012304537697885400197 4599377307100818353512537)
          ·
            refine ⟨3449532980325613765134403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4599377307100818353512537 3449532980325613765134403)
            ·
              refine ⟨5174299470488420647701605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3449532980325613765134403 5174299470488420647701605)
              ·
                refine ⟨970181150716578871444051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5174299470488420647701605 970181150716578871444051)
                ·
                  refine ⟨1455271726074868307166077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 970181150716578871444051 1455271726074868307166077)
                  ·
                    refine ⟨545726897278075615187279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1455271726074868307166077 545726897278075615187279)
                    ·
                      rfl

theorem cell22_1594199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 4, 1, 3].length) (baseStart_1594199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1594199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1594199 prefixEnd_1594199 := by exact prefixLift 1594199
  have htrace : WordTrace (prefixWord ++ tailWord_1594199) baseStart_1594199 baseEnd_1594199 := by
    simpa [prefixWord, tailWord_1594199, baseEnd_1594199] using wordTrace_append hprefix tailTrace_1594199
  have hstable : (prefixWord ++ tailWord_1594199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594199).length < 2 ^ (prefixWord ++ tailWord_1594199).sum := by decide
  have hdescent : baseEnd_1594199 < baseStart_1594199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594225 : List Nat := [1, 2, 2, 2, 1, 4, 2, 1, 3, 4]
def baseStart_1594225 : Nat := 118140960795 + 1594225 * 2 ^ 59
def prefixEnd_1594225 : Nat := 4983230072969 + 3 ^ 40 * 1594225 * 2
def baseEnd_1594225 : Nat := 545735797609420214037199

theorem tailTrace_1594225 : CollatzResearch.WordTrace tailWord_1594225 prefixEnd_1594225 545735797609420214037199 := by
  unfold tailWord_1594225
  simp only [CollatzResearch.WordTrace]
  refine ⟨58146162649402571798432129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38764108432935047865621419 58146162649402571798432129)
  ·
    refine ⟨43609621987051928848824097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58146162649402571798432129 43609621987051928848824097)
    ·
      refine ⟨32707216490288946636618073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43609621987051928848824097 32707216490288946636618073)
      ·
        refine ⟨24530412367716709977463555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32707216490288946636618073 24530412367716709977463555)
        ·
          refine ⟨36795618551575064966195333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24530412367716709977463555 36795618551575064966195333)
          ·
            refine ⟨6899178478420324681161625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36795618551575064966195333 6899178478420324681161625)
            ·
              refine ⟨5174383858815243510871219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6899178478420324681161625 5174383858815243510871219)
              ·
                refine ⟨7761575788222865266306829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5174383858815243510871219 7761575788222865266306829)
                ·
                  refine ⟨2910590920583574474865061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7761575788222865266306829 2910590920583574474865061)
                  ·
                    refine ⟨545735797609420214037199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2910590920583574474865061 545735797609420214037199)
                    ·
                      rfl

theorem cell22_1594225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 3, 4].length) (baseStart_1594225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1594225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1594225 prefixEnd_1594225 := by exact prefixLift 1594225
  have htrace : WordTrace (prefixWord ++ tailWord_1594225) baseStart_1594225 baseEnd_1594225 := by
    simpa [prefixWord, tailWord_1594225, baseEnd_1594225] using wordTrace_append hprefix tailTrace_1594225
  have hstable : (prefixWord ++ tailWord_1594225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594225).length < 2 ^ (prefixWord ++ tailWord_1594225).sum := by decide
  have hdescent : baseEnd_1594225 < baseStart_1594225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594272 : List Nat := [2, 1, 1, 4, 1, 1, 2, 5, 2, 3]
def baseStart_1594272 : Nat := 118140960795 + 1594272 * 2 ^ 59
def prefixEnd_1594272 : Nat := 4983230072969 + 3 ^ 40 * 1594272 * 2
def baseEnd_1594272 : Nat := 545751886669927758112055

theorem tailTrace_1594272 : CollatzResearch.WordTrace tailWord_1594272 prefixEnd_1594272 545751886669927758112055 := by
  unfold tailWord_1594272
  simp only [CollatzResearch.WordTrace]
  refine ⟨29073938440116149412696535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38765251253488199216928713 29073938440116149412696535)
  ·
    refine ⟨43610907660174224119044803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29073938440116149412696535 43610907660174224119044803)
    ·
      refine ⟨65416361490261336178567205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43610907660174224119044803 65416361490261336178567205)
      ·
        refine ⟨12265567779424000533481351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65416361490261336178567205 12265567779424000533481351)
        ·
          refine ⟨18398351669136000800222027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12265567779424000533481351 18398351669136000800222027)
          ·
            refine ⟨27597527503704001200333041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18398351669136000800222027 27597527503704001200333041)
            ·
              refine ⟨20698145627778000900249781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27597527503704001200333041 20698145627778000900249781)
              ·
                refine ⟨1940451152604187584398417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20698145627778000900249781 1940451152604187584398417)
                ·
                  refine ⟨1455338364453140688298813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1940451152604187584398417 1455338364453140688298813)
                  ·
                    refine ⟨545751886669927758112055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1455338364453140688298813 545751886669927758112055)
                    ·
                      rfl

theorem cell22_1594272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 5, 2, 3].length) (baseStart_1594272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1594272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1594272 prefixEnd_1594272 := by exact prefixLift 1594272
  have htrace : WordTrace (prefixWord ++ tailWord_1594272) baseStart_1594272 baseEnd_1594272 := by
    simpa [prefixWord, tailWord_1594272, baseEnd_1594272] using wordTrace_append hprefix tailTrace_1594272
  have hstable : (prefixWord ++ tailWord_1594272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594272).length < 2 ^ (prefixWord ++ tailWord_1594272).sum := by decide
  have hdescent : baseEnd_1594272 < baseStart_1594272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594308 : List Nat := [2, 3, 3, 3, 1, 1, 3, 2, 4]
def baseStart_1594308 : Nat := 118140960795 + 1594308 * 2 ^ 59
def prefixEnd_1594308 : Nat := 4983230072969 + 3 ^ 40 * 1594308 * 2
def baseEnd_1594308 : Nat := 181921403401878554737315

theorem tailTrace_1594308 : CollatzResearch.WordTrace tailWord_1594308 prefixEnd_1594308 181921403401878554737315 := by
  unfold tailWord_1594308
  simp only [CollatzResearch.WordTrace]
  refine ⟨29074594954050938486851789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38766126605401251315802385 29074594954050938486851789)
  ·
    refine ⟨10902973107769101932569421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29074594954050938486851789 10902973107769101932569421)
    ·
      refine ⟨4088614915413413224713533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10902973107769101932569421 4088614915413413224713533)
      ·
        refine ⟨1533230593280029959267575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4088614915413413224713533 1533230593280029959267575)
        ·
          refine ⟨2299845889920044938901363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1533230593280029959267575 2299845889920044938901363)
          ·
            refine ⟨3449768834880067408352045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2299845889920044938901363 3449768834880067408352045)
            ·
              refine ⟨1293663313080025278132017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3449768834880067408352045 1293663313080025278132017)
              ·
                refine ⟨970247484810018958599013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1293663313080025278132017 970247484810018958599013)
                ·
                  refine ⟨181921403401878554737315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 970247484810018958599013 181921403401878554737315)
                  ·
                    rfl

theorem cell22_1594308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 2, 4].length) (baseStart_1594308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1594308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1594308 prefixEnd_1594308 := by exact prefixLift 1594308
  have htrace : WordTrace (prefixWord ++ tailWord_1594308) baseStart_1594308 baseEnd_1594308 := by
    simpa [prefixWord, tailWord_1594308, baseEnd_1594308] using wordTrace_append hprefix tailTrace_1594308
  have hstable : (prefixWord ++ tailWord_1594308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594308).length < 2 ^ (prefixWord ++ tailWord_1594308).sum := by decide
  have hdescent : baseEnd_1594308 < baseStart_1594308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594392 : List Nat := [2, 1, 2, 3, 2, 3, 1, 2, 6]
def baseStart_1594392 : Nat := 118140960795 + 1594392 * 2 ^ 59
def prefixEnd_1594392 : Nat := 4983230072969 + 3 ^ 40 * 1594392 * 2
def baseEnd_1594392 : Nat := 181930988374095815037229

theorem tailTrace_1594392 : CollatzResearch.WordTrace tailWord_1594392 prefixEnd_1594392 181930988374095815037229 := by
  unfold tailWord_1594392
  simp only [CollatzResearch.WordTrace]
  refine ⟨29076126819898779659880715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38768169093198372879840953 29076126819898779659880715)
  ·
    refine ⟨43614190229848169489821073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29076126819898779659880715 43614190229848169489821073)
    ·
      refine ⟨32710642672386127117365805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43614190229848169489821073 32710642672386127117365805)
      ·
        refine ⟨12266491002144797669012177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32710642672386127117365805 12266491002144797669012177)
        ·
          refine ⟨9199868251608598251759133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12266491002144797669012177 9199868251608598251759133)
          ·
            refine ⟨3449950594353224344409675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9199868251608598251759133 3449950594353224344409675)
            ·
              refine ⟨5174925891529836516614513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3449950594353224344409675 5174925891529836516614513)
              ·
                refine ⟨3881194418647377387460885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5174925891529836516614513 3881194418647377387460885)
                ·
                  refine ⟨181930988374095815037229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3881194418647377387460885 181930988374095815037229)
                  ·
                    rfl

theorem cell22_1594392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 6].length) (baseStart_1594392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1594392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1594392 prefixEnd_1594392 := by exact prefixLift 1594392
  have htrace : WordTrace (prefixWord ++ tailWord_1594392) baseStart_1594392 baseEnd_1594392 := by
    simpa [prefixWord, tailWord_1594392, baseEnd_1594392] using wordTrace_append hprefix tailTrace_1594392
  have hstable : (prefixWord ++ tailWord_1594392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594392).length < 2 ^ (prefixWord ++ tailWord_1594392).sum := by decide
  have hdescent : baseEnd_1594392 < baseStart_1594392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594424 : List Nat := [2, 1, 2, 1, 5, 2, 1, 1, 4, 3]
def baseStart_1594424 : Nat := 118140960795 + 1594424 * 2 ^ 59
def prefixEnd_1594424 : Nat := 4983230072969 + 3 ^ 40 * 1594424 * 2
def baseEnd_1594424 : Nat := 545803919376250028311589

theorem tailTrace_1594424 : CollatzResearch.WordTrace tailWord_1594424 prefixEnd_1594424 545803919376250028311589 := by
  unfold tailWord_1594424
  simp only [CollatzResearch.WordTrace]
  refine ⟨29076710387840814392463163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38768947183787752523284217 29076710387840814392463163)
  ·
    refine ⟨43615065581761221588694745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29076710387840814392463163 43615065581761221588694745)
    ·
      refine ⟨32711299186320916191521059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43615065581761221588694745 32711299186320916191521059)
      ·
        refine ⟨49066948779481374287281589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32711299186320916191521059 49066948779481374287281589)
        ·
          refine ⟨4600026448076378839432649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49066948779481374287281589 4600026448076378839432649)
          ·
            refine ⟨3450019836057284129574487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4600026448076378839432649 3450019836057284129574487)
            ·
              refine ⟨5175029754085926194361731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3450019836057284129574487 5175029754085926194361731)
              ·
                refine ⟨7762544631128889291542597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5175029754085926194361731 7762544631128889291542597)
                ·
                  refine ⟨1455477118336666742164237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7762544631128889291542597 1455477118336666742164237)
                  ·
                    refine ⟨545803919376250028311589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1455477118336666742164237 545803919376250028311589)
                    ·
                      rfl

theorem cell22_1594424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 4, 3].length) (baseStart_1594424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1594424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1594424 prefixEnd_1594424 := by exact prefixLift 1594424
  have htrace : WordTrace (prefixWord ++ tailWord_1594424) baseStart_1594424 baseEnd_1594424 := by
    simpa [prefixWord, tailWord_1594424, baseEnd_1594424] using wordTrace_append hprefix tailTrace_1594424
  have hstable : (prefixWord ++ tailWord_1594424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594424).length < 2 ^ (prefixWord ++ tailWord_1594424).sum := by decide
  have hdescent : baseEnd_1594424 < baseStart_1594424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594482 : List Nat := [3, 2, 1, 2, 2, 1, 1, 3, 7]
def baseStart_1594482 : Nat := 118140960795 + 1594482 * 2 ^ 59
def prefixEnd_1594482 : Nat := 4983230072969 + 3 ^ 40 * 1594482 * 2
def baseEnd_1594482 : Nat := 181941257987185736787137

theorem tailTrace_1594482 : CollatzResearch.WordTrace tailWord_1594482 prefixEnd_1594482 181941257987185736787137 := by
  unfold tailWord_1594482
  simp only [CollatzResearch.WordTrace]
  refine ⟨14538884052367876172634425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38770357472981003127025133 14538884052367876172634425)
  ·
    refine ⟨10904163039275907129475819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14538884052367876172634425 10904163039275907129475819)
    ·
      refine ⟨16356244558913860694213729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10904163039275907129475819 16356244558913860694213729)
      ·
        refine ⟨12267183419185395520660297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16356244558913860694213729 12267183419185395520660297)
        ·
          refine ⟨9200387564389046640495223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12267183419185395520660297 9200387564389046640495223)
          ·
            refine ⟨13800581346583569960742835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9200387564389046640495223 13800581346583569960742835)
            ·
              refine ⟨20700872019875354941114253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13800581346583569960742835 20700872019875354941114253)
              ·
                refine ⟨7762827007453258102917845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20700872019875354941114253 7762827007453258102917845)
                ·
                  refine ⟨181941257987185736787137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7762827007453258102917845 181941257987185736787137)
                  ·
                    rfl

theorem cell22_1594482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 7].length) (baseStart_1594482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1594482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1594482 prefixEnd_1594482 := by exact prefixLift 1594482
  have htrace : WordTrace (prefixWord ++ tailWord_1594482) baseStart_1594482 baseEnd_1594482 := by
    simpa [prefixWord, tailWord_1594482, baseEnd_1594482] using wordTrace_append hprefix tailTrace_1594482
  have hstable : (prefixWord ++ tailWord_1594482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594482).length < 2 ^ (prefixWord ++ tailWord_1594482).sum := by decide
  have hdescent : baseEnd_1594482 < baseStart_1594482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594544 : List Nat := [2, 1, 1, 1, 2, 1, 2, 8, 4]
def baseStart_1594544 : Nat := 118140960795 + 1594544 * 2 ^ 59
def prefixEnd_1594544 : Nat := 4983230072969 + 3 ^ 40 * 1594544 * 2
def baseEnd_1594544 : Nat := 181948332609536571770407

theorem tailTrace_1594544 : CollatzResearch.WordTrace tailWord_1594544 prefixEnd_1594544 181948332609536571770407 := by
  unfold tailWord_1594544
  simp only [CollatzResearch.WordTrace]
  refine ⟨29078898767623444639647343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38771865023497926186196457 29078898767623444639647343)
  ·
    refine ⟨43618348151435166959471015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29078898767623444639647343 43618348151435166959471015)
    ·
      refine ⟨65427522227152750439206523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43618348151435166959471015 65427522227152750439206523)
      ·
        refine ⟨98141283340729125658809785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65427522227152750439206523 98141283340729125658809785)
        ·
          refine ⟨73605962505546844244107339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98141283340729125658809785 73605962505546844244107339)
          ·
            refine ⟨110408943758320266366161009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73605962505546844244107339 110408943758320266366161009)
            ·
              refine ⟨82806707818740199774620757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110408943758320266366161009 82806707818740199774620757)
              ·
                refine ⟨970391107250861716108837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 82806707818740199774620757 970391107250861716108837)
                ·
                  refine ⟨181948332609536571770407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 970391107250861716108837 181948332609536571770407)
                  ·
                    rfl

theorem cell22_1594544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 8, 4].length) (baseStart_1594544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1594544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1594544 prefixEnd_1594544 := by exact prefixLift 1594544
  have htrace : WordTrace (prefixWord ++ tailWord_1594544) baseStart_1594544 baseEnd_1594544 := by
    simpa [prefixWord, tailWord_1594544, baseEnd_1594544] using wordTrace_append hprefix tailTrace_1594544
  have hstable : (prefixWord ++ tailWord_1594544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594544).length < 2 ^ (prefixWord ++ tailWord_1594544).sum := by decide
  have hdescent : baseEnd_1594544 < baseStart_1594544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594561 : List Nat := [1, 2, 6, 1, 1, 2, 1, 2, 6]
def baseStart_1594561 : Nat := 118140960795 + 1594561 * 2 ^ 59
def prefixEnd_1594561 : Nat := 4983230072969 + 3 ^ 40 * 1594561 * 2
def baseEnd_1594561 : Nat := 181950272425342445878723

theorem tailTrace_1594561 : CollatzResearch.WordTrace tailWord_1594561 prefixEnd_1594561 181950272425342445878723 := by
  unfold tailWord_1594561
  simp only [CollatzResearch.WordTrace]
  refine ⟨58158417576185301182663537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38772278384123534121775691 58158417576185301182663537)
  ·
    refine ⟨43618813182138975886997653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58158417576185301182663537 43618813182138975886997653)
    ·
      refine ⟨2044631867912764494703015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 43618813182138975886997653 2044631867912764494703015)
      ·
        refine ⟨3066947801869146742054523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2044631867912764494703015 3066947801869146742054523)
        ·
          refine ⟨4600421702803720113081785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3066947801869146742054523 4600421702803720113081785)
          ·
            refine ⟨3450316277102790084811339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4600421702803720113081785 3450316277102790084811339)
            ·
              refine ⟨5175474415654185127217009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3450316277102790084811339 5175474415654185127217009)
              ·
                refine ⟨3881605811740638845412757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5175474415654185127217009 3881605811740638845412757)
                ·
                  refine ⟨181950272425342445878723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3881605811740638845412757 181950272425342445878723)
                  ·
                    rfl

theorem cell22_1594561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 6].length) (baseStart_1594561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1594561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1594561 prefixEnd_1594561 := by exact prefixLift 1594561
  have htrace : WordTrace (prefixWord ++ tailWord_1594561) baseStart_1594561 baseEnd_1594561 := by
    simpa [prefixWord, tailWord_1594561, baseEnd_1594561] using wordTrace_append hprefix tailTrace_1594561
  have hstable : (prefixWord ++ tailWord_1594561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594561).length < 2 ^ (prefixWord ++ tailWord_1594561).sum := by decide
  have hdescent : baseEnd_1594561 < baseStart_1594561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594593 : List Nat := [1, 2, 3, 1, 3, 4, 1, 2, 2, 3]
def baseStart_1594593 : Nat := 118140960795 + 1594593 * 2 ^ 59
def prefixEnd_1594593 : Nat := 4983230072969 + 3 ^ 40 * 1594593 * 2
def baseEnd_1594593 : Nat := 545861771529989920836071

theorem tailTrace_1594593 : CollatzResearch.WordTrace tailWord_1594593 prefixEnd_1594593 545861771529989920836071 := by
  unfold tailWord_1594593
  simp only [CollatzResearch.WordTrace]
  refine ⟨58159584712069370647828433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38773056474712913765218955 58159584712069370647828433)
  ·
    refine ⟨43619688534052027985871325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58159584712069370647828433 43619688534052027985871325)
    ·
      refine ⟨16357383200269510494701747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43619688534052027985871325 16357383200269510494701747)
      ·
        refine ⟨24536074800404265742052621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16357383200269510494701747 24536074800404265742052621)
        ·
          refine ⟨9201028050151599653269733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24536074800404265742052621 9201028050151599653269733)
          ·
            refine ⟨1725192759403424934988075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9201028050151599653269733 1725192759403424934988075)
            ·
              refine ⟨2587789139105137402482113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1725192759403424934988075 2587789139105137402482113)
              ·
                refine ⟨1940841854328853051861585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2587789139105137402482113 1940841854328853051861585)
                ·
                  refine ⟨1455631390746639788896189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1940841854328853051861585 1455631390746639788896189)
                  ·
                    refine ⟨545861771529989920836071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1455631390746639788896189 545861771529989920836071)
                    ·
                      rfl

theorem cell22_1594593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 2, 2, 3].length) (baseStart_1594593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1594593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1594593 prefixEnd_1594593 := by exact prefixLift 1594593
  have htrace : WordTrace (prefixWord ++ tailWord_1594593) baseStart_1594593 baseEnd_1594593 := by
    simpa [prefixWord, tailWord_1594593, baseEnd_1594593] using wordTrace_append hprefix tailTrace_1594593
  have hstable : (prefixWord ++ tailWord_1594593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594593).length < 2 ^ (prefixWord ++ tailWord_1594593).sum := by decide
  have hdescent : baseEnd_1594593 < baseStart_1594593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594610 : List Nat := [3, 2, 1, 3, 3, 1, 3, 1, 2, 3]
def baseStart_1594610 : Nat := 118140960795 + 1594610 * 2 ^ 59
def prefixEnd_1594610 : Nat := 4983230072969 + 3 ^ 40 * 1594610 * 2
def baseEnd_1594610 : Nat := 545867590977407543161019

theorem tailTrace_1594610 : CollatzResearch.WordTrace tailWord_1594610 prefixEnd_1594610 545867590977407543161019 := by
  unfold tailWord_1594610
  simp only [CollatzResearch.WordTrace]
  refine ⟨14540051188251945637799321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38773469835338521700798189 14540051188251945637799321)
  ·
    refine ⟨10905038391188959228349491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14540051188251945637799321 10905038391188959228349491)
    ·
      refine ⟨16357557586783438842524237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10905038391188959228349491 16357557586783438842524237)
      ·
        refine ⟨6134084095043789565946589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16357557586783438842524237 6134084095043789565946589)
        ·
          refine ⟨2300281535641421087229971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6134084095043789565946589 2300281535641421087229971)
          ·
            refine ⟨3450422303462131630844957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2300281535641421087229971 3450422303462131630844957)
            ·
              refine ⟨1293908363798299361566859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3450422303462131630844957 1293908363798299361566859)
              ·
                refine ⟨1940862545697449042350289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1293908363798299361566859 1940862545697449042350289)
                ·
                  refine ⟨1455646909273086781762717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1940862545697449042350289 1455646909273086781762717)
                  ·
                    refine ⟨545867590977407543161019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1455646909273086781762717 545867590977407543161019)
                    ·
                      rfl

theorem cell22_1594610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 1, 2, 3].length) (baseStart_1594610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1594610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1594610 prefixEnd_1594610 := by exact prefixLift 1594610
  have htrace : WordTrace (prefixWord ++ tailWord_1594610) baseStart_1594610 baseEnd_1594610 := by
    simpa [prefixWord, tailWord_1594610, baseEnd_1594610] using wordTrace_append hprefix tailTrace_1594610
  have hstable : (prefixWord ++ tailWord_1594610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594610).length < 2 ^ (prefixWord ++ tailWord_1594610).sum := by decide
  have hdescent : baseEnd_1594610 < baseStart_1594610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594655 : List Nat := [1, 1, 2, 4, 5, 1, 1, 1, 3, 3]
def baseStart_1594655 : Nat := 118140960795 + 1594655 * 2 ^ 59
def prefixEnd_1594655 : Nat := 4983230072969 + 3 ^ 40 * 1594655 * 2
def baseEnd_1594655 : Nat := 545882995397042425785881

theorem tailTrace_1594655 : CollatzResearch.WordTrace tailWord_1594655 prefixEnd_1594655 545882995397042425785881 := by
  unfold tailWord_1594655
  simp only [CollatzResearch.WordTrace]
  refine ⟨58161846037844755236585419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38774564025229836824390279 58161846037844755236585419)
  ·
    refine ⟨87242769056767132854878129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58161846037844755236585419 87242769056767132854878129)
    ·
      refine ⟨65432076792575349641158597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87242769056767132854878129 65432076792575349641158597)
      ·
        refine ⟨12268514398607878057717237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65432076792575349641158597 12268514398607878057717237)
        ·
          refine ⟨1150173224869488567910991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12268514398607878057717237 1150173224869488567910991)
          ·
            refine ⟨1725259837304232851866487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1150173224869488567910991 1725259837304232851866487)
            ·
              refine ⟨2587889755956349277799731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1725259837304232851866487 2587889755956349277799731)
              ·
                refine ⟨3881834633934523916699597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2587889755956349277799731 3881834633934523916699597)
                ·
                  refine ⟨1455687987725446468762349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3881834633934523916699597 1455687987725446468762349)
                  ·
                    refine ⟨545882995397042425785881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1455687987725446468762349 545882995397042425785881)
                    ·
                      rfl

theorem cell22_1594655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 3, 3].length) (baseStart_1594655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1594655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1594655 prefixEnd_1594655 := by exact prefixLift 1594655
  have htrace : WordTrace (prefixWord ++ tailWord_1594655) baseStart_1594655 baseEnd_1594655 := by
    simpa [prefixWord, tailWord_1594655, baseEnd_1594655] using wordTrace_append hprefix tailTrace_1594655
  have hstable : (prefixWord ++ tailWord_1594655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594655).length < 2 ^ (prefixWord ++ tailWord_1594655).sum := by decide
  have hdescent : baseEnd_1594655 < baseStart_1594655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594696 : List Nat := [2, 1, 3, 1, 1, 2, 1, 7, 4]
def baseStart_1594696 : Nat := 118140960795 + 1594696 * 2 ^ 59
def prefixEnd_1594696 : Nat := 4983230072969 + 3 ^ 40 * 1594696 * 2
def baseEnd_1594696 : Nat := 181965676844977328503585

theorem tailTrace_1594696 : CollatzResearch.WordTrace tailWord_1594696 prefixEnd_1594696 181965676844977328503585 := by
  unfold tailWord_1594696
  simp only [CollatzResearch.WordTrace]
  refine ⟨29081670715348109619413971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38775560953797479492551961 29081670715348109619413971)
  ·
    refine ⟨43622506073022164429120957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29081670715348109619413971 43622506073022164429120957)
    ·
      refine ⟨16358439777383311660920359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43622506073022164429120957 16358439777383311660920359)
      ·
        refine ⟨24537659666074967491380539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16358439777383311660920359 24537659666074967491380539)
        ·
          refine ⟨36806489499112451237070809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24537659666074967491380539 36806489499112451237070809)
          ·
            refine ⟨27604867124334338427803107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36806489499112451237070809 27604867124334338427803107)
            ·
              refine ⟨41407300686501507641704661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27604867124334338427803107 41407300686501507641704661)
              ·
                refine ⟨970483609839879085352453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 41407300686501507641704661 970483609839879085352453)
                ·
                  refine ⟨181965676844977328503585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 970483609839879085352453 181965676844977328503585)
                  ·
                    rfl

theorem cell22_1594696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 7, 4].length) (baseStart_1594696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1594696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1594696 prefixEnd_1594696 := by exact prefixLift 1594696
  have htrace : WordTrace (prefixWord ++ tailWord_1594696) baseStart_1594696 baseEnd_1594696 := by
    simpa [prefixWord, tailWord_1594696, baseEnd_1594696] using wordTrace_append hprefix tailTrace_1594696
  have hstable : (prefixWord ++ tailWord_1594696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594696).length < 2 ^ (prefixWord ++ tailWord_1594696).sum := by decide
  have hdescent : baseEnd_1594696 < baseStart_1594696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594713 : List Nat := [1, 2, 1, 2, 2, 2, 6, 2, 4]
def baseStart_1594713 : Nat := 118140960795 + 1594713 * 2 ^ 59
def prefixEnd_1594713 : Nat := 4983230072969 + 3 ^ 40 * 1594713 * 2
def baseEnd_1594713 : Nat := 181967616660783202611901

theorem tailTrace_1594713 : CollatzResearch.WordTrace tailWord_1594713 prefixEnd_1594713 181967616660783202611901 := by
  unfold tailWord_1594713
  simp only [CollatzResearch.WordTrace]
  refine ⟨58163961471634631142196793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38775974314423087428131195 58163961471634631142196793)
  ·
    refine ⟨43622971103725973356647595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58163961471634631142196793 43622971103725973356647595)
    ·
      refine ⟨65434456655588960034971393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43622971103725973356647595 65434456655588960034971393)
      ·
        refine ⟨49075842491691720026228545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65434456655588960034971393 49075842491691720026228545)
        ·
          refine ⟨36806881868768790019671409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49075842491691720026228545 36806881868768790019671409)
          ·
            refine ⟨27605161401576592514753557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36806881868768790019671409 27605161401576592514753557)
            ·
              refine ⟨1293991940698902774129073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27605161401576592514753557 1293991940698902774129073)
              ·
                refine ⟨970493955524177080596805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1293991940698902774129073 970493955524177080596805)
                ·
                  refine ⟨181967616660783202611901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 970493955524177080596805 181967616660783202611901)
                  ·
                    rfl

theorem cell22_1594713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 2, 4].length) (baseStart_1594713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1594713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1594713 prefixEnd_1594713 := by exact prefixLift 1594713
  have htrace : WordTrace (prefixWord ++ tailWord_1594713) baseStart_1594713 baseEnd_1594713 := by
    simpa [prefixWord, tailWord_1594713, baseEnd_1594713] using wordTrace_append hprefix tailTrace_1594713
  have hstable : (prefixWord ++ tailWord_1594713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594713).length < 2 ^ (prefixWord ++ tailWord_1594713).sum := by decide
  have hdescent : baseEnd_1594713 < baseStart_1594713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594728 : List Nat := [2, 1, 4, 2, 3, 1, 2, 1, 1, 5]
def baseStart_1594728 : Nat := 118140960795 + 1594728 * 2 ^ 59
def prefixEnd_1594728 : Nat := 4983230072969 + 3 ^ 40 * 1594728 * 2
def baseEnd_1594728 : Nat := 545907984788894568710657

theorem tailTrace_1594728 : CollatzResearch.WordTrace tailWord_1594728 prefixEnd_1594728 545907984788894568710657 := by
  unfold tailWord_1594728
  simp only [CollatzResearch.WordTrace]
  refine ⟨29082254283290144351996419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38776339044386859135995225 29082254283290144351996419)
  ·
    refine ⟨43623381424935216527994629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29082254283290144351996419 43623381424935216527994629)
    ·
      refine ⟨8179384017175353098998993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43623381424935216527994629 8179384017175353098998993)
      ·
        refine ⟨6134538012881514824249245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8179384017175353098998993 6134538012881514824249245)
        ·
          refine ⟨2300451754830568059093467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6134538012881514824249245 2300451754830568059093467)
          ·
            refine ⟨3450677632245852088640201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2300451754830568059093467 3450677632245852088640201)
            ·
              refine ⟨2588008224184389066480151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3450677632245852088640201 2588008224184389066480151)
              ·
                refine ⟨3882012336276583599720227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2588008224184389066480151 3882012336276583599720227)
                ·
                  refine ⟨5823018504414875399580341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3882012336276583599720227 5823018504414875399580341)
                  ·
                    refine ⟨545907984788894568710657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5823018504414875399580341 545907984788894568710657)
                    ·
                      rfl

theorem cell22_1594728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_1594728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1594728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1594728 prefixEnd_1594728 := by exact prefixLift 1594728
  have htrace : WordTrace (prefixWord ++ tailWord_1594728) baseStart_1594728 baseEnd_1594728 := by
    simpa [prefixWord, tailWord_1594728, baseEnd_1594728] using wordTrace_append hprefix tailTrace_1594728
  have hstable : (prefixWord ++ tailWord_1594728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594728).length < 2 ^ (prefixWord ++ tailWord_1594728).sum := by decide
  have hdescent : baseEnd_1594728 < baseStart_1594728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594769 : List Nat := [1, 2, 2, 1, 1, 1, 2, 5, 7]
def baseStart_1594769 : Nat := 118140960795 + 1594769 * 2 ^ 59
def prefixEnd_1594769 : Nat := 4983230072969 + 3 ^ 40 * 1594769 * 2
def baseEnd_1594769 : Nat := 181974006642261376145177

theorem tailTrace_1594769 : CollatzResearch.WordTrace tailWord_1594769 prefixEnd_1594769 181974006642261376145177 := by
  unfold tailWord_1594769
  simp only [CollatzResearch.WordTrace]
  refine ⟨58166003959431752706235361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38777335972954501804156907 58166003959431752706235361)
  ·
    refine ⟨43624502969573814529676521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58166003959431752706235361 43624502969573814529676521)
    ·
      refine ⟨32718377227180360897257391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43624502969573814529676521 32718377227180360897257391)
      ·
        refine ⟨49077565840770541345886087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32718377227180360897257391 49077565840770541345886087)
        ·
          refine ⟨73616348761155812018829131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49077565840770541345886087 73616348761155812018829131)
          ·
            refine ⟨110424523141733718028243697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73616348761155812018829131 110424523141733718028243697)
            ·
              refine ⟨82818392356300288521182773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110424523141733718028243697 82818392356300288521182773)
              ·
                refine ⟨7764224283403152048860885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82818392356300288521182773 7764224283403152048860885)
                ·
                  refine ⟨181974006642261376145177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7764224283403152048860885 181974006642261376145177)
                  ·
                    rfl

theorem cell22_1594769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 7].length) (baseStart_1594769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1594769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1594769 prefixEnd_1594769 := by exact prefixLift 1594769
  have htrace : WordTrace (prefixWord ++ tailWord_1594769) baseStart_1594769 baseEnd_1594769 := by
    simpa [prefixWord, tailWord_1594769, baseEnd_1594769] using wordTrace_append hprefix tailTrace_1594769
  have hstable : (prefixWord ++ tailWord_1594769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594769).length < 2 ^ (prefixWord ++ tailWord_1594769).sum := by decide
  have hdescent : baseEnd_1594769 < baseStart_1594769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594792 : List Nat := [2, 1, 6, 1, 3, 1, 2, 6]
def baseStart_1594792 : Nat := 118140960795 + 1594792 * 2 ^ 59
def prefixEnd_1594792 : Nat := 4983230072969 + 3 ^ 40 * 1594792 * 2
def baseEnd_1594792 : Nat := 60658877032979970567829

theorem tailTrace_1594792 : CollatzResearch.WordTrace tailWord_1594792 prefixEnd_1594792 60658877032979970567829 := by
  unfold tailWord_1594792
  simp only [CollatzResearch.WordTrace]
  refine ⟨29083421419174213817161315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38777895225565618422881753 29083421419174213817161315)
  ·
    refine ⟨43625132128761320725741973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29083421419174213817161315 43625132128761320725741973)
    ·
      refine ⟨2044928068535686909019155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 43625132128761320725741973 2044928068535686909019155)
      ·
        refine ⟨3067392102803530363528733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2044928068535686909019155 3067392102803530363528733)
        ·
          refine ⟨1150272038551323886323275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3067392102803530363528733 1150272038551323886323275)
          ·
            refine ⟨1725408057826985829484913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1150272038551323886323275 1725408057826985829484913)
            ·
              refine ⟨1294056043370239372113685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1725408057826985829484913 1294056043370239372113685)
              ·
                refine ⟨60658877032979970567829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1294056043370239372113685 60658877032979970567829)
                ·
                  rfl

theorem cell22_1594792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 6].length) (baseStart_1594792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1594792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1594792 prefixEnd_1594792 := by exact prefixLift 1594792
  have htrace : WordTrace (prefixWord ++ tailWord_1594792) baseStart_1594792 baseEnd_1594792 := by
    simpa [prefixWord, tailWord_1594792, baseEnd_1594792] using wordTrace_append hprefix tailTrace_1594792
  have hstable : (prefixWord ++ tailWord_1594792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594792).length < 2 ^ (prefixWord ++ tailWord_1594792).sum := by decide
  have hdescent : baseEnd_1594792 < baseStart_1594792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594799 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 2, 8]
def baseStart_1594799 : Nat := 118140960795 + 1594799 * 2 ^ 59
def prefixEnd_1594799 : Nat := 4983230072969 + 3 ^ 40 * 1594799 * 2
def baseEnd_1594799 : Nat := 545932289539874050185439

theorem tailTrace_1594799 : CollatzResearch.WordTrace tailWord_1594799 prefixEnd_1594799 545932289539874050185439 := by
  unfold tailWord_1594799
  simp only [CollatzResearch.WordTrace]
  refine ⟨58167098149323067829827451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38778065432882045219884967 58167098149323067829827451)
  ·
    refine ⟨87250647223984601744741177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58167098149323067829827451 87250647223984601744741177)
    ·
      refine ⟨65437985417988451308555883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87250647223984601744741177 65437985417988451308555883)
      ·
        refine ⟨98156978126982676962833825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65437985417988451308555883 98156978126982676962833825)
        ·
          refine ⟨73617733595237007722125369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98156978126982676962833825 73617733595237007722125369)
          ·
            refine ⟨55213300196427755791594027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73617733595237007722125369 55213300196427755791594027)
            ·
              refine ⟨82819950294641633687391041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55213300196427755791594027 82819950294641633687391041)
              ·
                refine ⟨62114962720981225265543281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82819950294641633687391041 62114962720981225265543281)
                ·
                  refine ⟨46586222040735918949157461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62114962720981225265543281 46586222040735918949157461)
                  ·
                    refine ⟨545932289539874050185439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 46586222040735918949157461 545932289539874050185439)
                    ·
                      rfl

theorem cell22_1594799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 8].length) (baseStart_1594799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1594799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1594799 prefixEnd_1594799 := by exact prefixLift 1594799
  have htrace : WordTrace (prefixWord ++ tailWord_1594799) baseStart_1594799 baseEnd_1594799 := by
    simpa [prefixWord, tailWord_1594799, baseEnd_1594799] using wordTrace_append hprefix tailTrace_1594799
  have hstable : (prefixWord ++ tailWord_1594799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594799).length < 2 ^ (prefixWord ++ tailWord_1594799).sum := by decide
  have hdescent : baseEnd_1594799 < baseStart_1594799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594831 : List Nat := [1, 1, 2, 1, 1, 4, 5, 1, 6]
def baseStart_1594831 : Nat := 118140960795 + 1594831 * 2 ^ 59
def prefixEnd_1594831 : Nat := 4983230072969 + 3 ^ 40 * 1594831 * 2
def baseEnd_1594831 : Nat := 181981081264612211128447

theorem tailTrace_1594831 : CollatzResearch.WordTrace tailWord_1594831 prefixEnd_1594831 181981081264612211128447 := by
  unfold tailWord_1594831
  simp only [CollatzResearch.WordTrace]
  refine ⟨58168265285207137294992347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38778843523471424863328231 58168265285207137294992347)
  ·
    refine ⟨87252397927810705942488521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58168265285207137294992347 87252397927810705942488521)
    ·
      refine ⟨65439298445858029456866391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87252397927810705942488521 65439298445858029456866391)
      ·
        refine ⟨98158947668787044185299587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65439298445858029456866391 98158947668787044185299587)
        ·
          refine ⟨147238421503180566277949381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98158947668787044185299587 147238421503180566277949381)
          ·
            refine ⟨27607204031846356177115509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 147238421503180566277949381 27607204031846356177115509)
            ·
              refine ⟨2588175377985595891604579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27607204031846356177115509 2588175377985595891604579)
              ·
                refine ⟨3882263066978393837406869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2588175377985595891604579 3882263066978393837406869)
                ·
                  refine ⟨181981081264612211128447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3882263066978393837406869 181981081264612211128447)
                  ·
                    rfl

theorem cell22_1594831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 6].length) (baseStart_1594831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1594831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1594831 prefixEnd_1594831 := by exact prefixLift 1594831
  have htrace : WordTrace (prefixWord ++ tailWord_1594831) baseStart_1594831 baseEnd_1594831 := by
    simpa [prefixWord, tailWord_1594831, baseEnd_1594831] using wordTrace_append hprefix tailTrace_1594831
  have hstable : (prefixWord ++ tailWord_1594831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594831).length < 2 ^ (prefixWord ++ tailWord_1594831).sum := by decide
  have hdescent : baseEnd_1594831 < baseStart_1594831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594882 : List Nat := [3, 4, 1, 2, 1, 2, 1, 4, 4]
def baseStart_1594882 : Nat := 118140960795 + 1594882 * 2 ^ 59
def prefixEnd_1594882 : Nat := 4983230072969 + 3 ^ 40 * 1594882 * 2
def baseEnd_1594882 : Nat := 181986900712029833453395

theorem tailTrace_1594882 : CollatzResearch.WordTrace tailWord_1594882 prefixEnd_1594882 181986900712029833453395 := by
  unfold tailWord_1594882
  simp only [CollatzResearch.WordTrace]
  refine ⟨14542531352005593251274725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38780083605348248670065933 14542531352005593251274725)
  ·
    refine ⟨2726724628501048734614011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14542531352005593251274725 2726724628501048734614011)
    ·
      refine ⟨4090086942751573101921017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2726724628501048734614011 4090086942751573101921017)
      ·
        refine ⟨3067565207063679826440763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4090086942751573101921017 3067565207063679826440763)
        ·
          refine ⟨4601347810595519739661145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3067565207063679826440763 4601347810595519739661145)
          ·
            refine ⟨3451010857946639804745859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4601347810595519739661145 3451010857946639804745859)
            ·
              refine ⟨5176516286919959707118789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3451010857946639804745859 5176516286919959707118789)
              ·
                refine ⟨970596803797492445084773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5176516286919959707118789 970596803797492445084773)
                ·
                  refine ⟨181986900712029833453395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 970596803797492445084773 181986900712029833453395)
                  ·
                    rfl

theorem cell22_1594882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_1594882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1594882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1594882 prefixEnd_1594882 := by exact prefixLift 1594882
  have htrace : WordTrace (prefixWord ++ tailWord_1594882) baseStart_1594882 baseEnd_1594882 := by
    simpa [prefixWord, tailWord_1594882, baseEnd_1594882] using wordTrace_append hprefix tailTrace_1594882
  have hstable : (prefixWord ++ tailWord_1594882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594882).length < 2 ^ (prefixWord ++ tailWord_1594882).sum := by decide
  have hdescent : baseEnd_1594882 < baseStart_1594882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594906 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 4, 6]
def baseStart_1594906 : Nat := 118140960795 + 1594906 * 2 ^ 59
def prefixEnd_1594906 : Nat := 4983230072969 + 3 ^ 40 * 1594906 * 2
def baseEnd_1594906 : Nat := 545968917826561437760111

theorem tailTrace_1594906 : CollatzResearch.WordTrace tailWord_1594906 prefixEnd_1594906 545968917826561437760111 := by
  unfold tailWord_1594906
  simp only [CollatzResearch.WordTrace]
  refine ⟨14542750189983856275993143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38780667173290283402648381 14542750189983856275993143)
  ·
    refine ⟨21814125284975784413989715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14542750189983856275993143 21814125284975784413989715)
    ·
      refine ⟨32721187927463676620984573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21814125284975784413989715 32721187927463676620984573)
      ·
        refine ⟨12270445472798878732869215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32721187927463676620984573 12270445472798878732869215)
        ·
          refine ⟨18405668209198318099303823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12270445472798878732869215 18405668209198318099303823)
          ·
            refine ⟨27608502313797477148955735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18405668209198318099303823 27608502313797477148955735)
            ·
              refine ⟨41412753470696215723433603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27608502313797477148955735 41412753470696215723433603)
              ·
                refine ⟨62119130206044323585150405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41412753470696215723433603 62119130206044323585150405)
                ·
                  refine ⟨11647336913633310672215701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62119130206044323585150405 11647336913633310672215701)
                  ·
                    refine ⟨545968917826561437760111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11647336913633310672215701 545968917826561437760111)
                    ·
                      rfl

theorem cell22_1594906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 4, 6].length) (baseStart_1594906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1594906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1594906 prefixEnd_1594906 := by exact prefixLift 1594906
  have htrace : WordTrace (prefixWord ++ tailWord_1594906) baseStart_1594906 baseEnd_1594906 := by
    simpa [prefixWord, tailWord_1594906, baseEnd_1594906] using wordTrace_append hprefix tailTrace_1594906
  have hstable : (prefixWord ++ tailWord_1594906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594906).length < 2 ^ (prefixWord ++ tailWord_1594906).sum := by decide
  have hdescent : baseEnd_1594906 < baseStart_1594906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595013 : List Nat := [1, 3, 1, 1, 4, 1, 1, 2, 4, 4]
def baseStart_1595013 : Nat := 118140960795 + 1595013 * 2 ^ 59
def prefixEnd_1595013 : Nat := 4983230072969 + 3 ^ 40 * 1595013 * 2
def baseEnd_1595013 : Nat := 546005546113248825334783

theorem tailTrace_1595013 : CollatzResearch.WordTrace tailWord_1595013 prefixEnd_1595013 546005546113248825334783 := by
  unfold tailWord_1595013
  simp only [CollatzResearch.WordTrace]
  refine ⟨58174903370547782378117693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38783268913698521585411795 58174903370547782378117693)
  ·
    refine ⟨21815588763955418391794135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58174903370547782378117693 21815588763955418391794135)
    ·
      refine ⟨32723383145933127587691203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21815588763955418391794135 32723383145933127587691203)
      ·
        refine ⟨49085074718899691381536805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32723383145933127587691203 49085074718899691381536805)
        ·
          refine ⟨9203451509793692134038151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49085074718899691381536805 9203451509793692134038151)
          ·
            refine ⟨13805177264690538201057227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9203451509793692134038151 13805177264690538201057227)
            ·
              refine ⟨20707765897035807301585841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13805177264690538201057227 20707765897035807301585841)
              ·
                refine ⟨15530824422776855476189381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20707765897035807301585841 15530824422776855476189381)
                ·
                  refine ⟨2912029579270660401785509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15530824422776855476189381 2912029579270660401785509)
                  ·
                    refine ⟨546005546113248825334783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2912029579270660401785509 546005546113248825334783)
                    ·
                      rfl

theorem cell22_1595013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 4, 4].length) (baseStart_1595013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1595013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1595013 prefixEnd_1595013 := by exact prefixLift 1595013
  have htrace : WordTrace (prefixWord ++ tailWord_1595013) baseStart_1595013 baseEnd_1595013 := by
    simpa [prefixWord, tailWord_1595013, baseEnd_1595013] using wordTrace_append hprefix tailTrace_1595013
  have hstable : (prefixWord ++ tailWord_1595013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595013).length < 2 ^ (prefixWord ++ tailWord_1595013).sum := by decide
  have hdescent : baseEnd_1595013 < baseStart_1595013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595058 : List Nat := [3, 2, 1, 1, 1, 2, 3, 1, 2, 6]
def baseStart_1595058 : Nat := 118140960795 + 1595058 * 2 ^ 59
def prefixEnd_1595058 : Nat := 4983230072969 + 3 ^ 40 * 1595058 * 2
def baseEnd_1595058 : Nat := 546020950532883707959645

theorem tailTrace_1595058 : CollatzResearch.WordTrace tailWord_1595058 prefixEnd_1595058 546020950532883707959645 := by
  unfold tailWord_1595058
  simp only [CollatzResearch.WordTrace]
  refine ⟨14544136163846188765876457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38784363103589836709003885 14544136163846188765876457)
  ·
    refine ⟨10908102122884641574407343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14544136163846188765876457 10908102122884641574407343)
    ·
      refine ⟨16362153184326962361611015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10908102122884641574407343 16362153184326962361611015)
      ·
        refine ⟨24543229776490443542416523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16362153184326962361611015 24543229776490443542416523)
        ·
          refine ⟨36814844664735665313624785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24543229776490443542416523 36814844664735665313624785)
          ·
            refine ⟨27611133498551748985218589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36814844664735665313624785 27611133498551748985218589)
            ·
              refine ⟨10354175061956905869456971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27611133498551748985218589 10354175061956905869456971)
              ·
                refine ⟨15531262592935358804185457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10354175061956905869456971 15531262592935358804185457)
                ·
                  refine ⟨11648446944701519103139093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15531262592935358804185457 11648446944701519103139093)
                  ·
                    refine ⟨546020950532883707959645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11648446944701519103139093 546020950532883707959645)
                    ·
                      rfl

theorem cell22_1595058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_1595058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1595058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1595058 prefixEnd_1595058 := by exact prefixLift 1595058
  have htrace : WordTrace (prefixWord ++ tailWord_1595058) baseStart_1595058 baseEnd_1595058 := by
    simpa [prefixWord, tailWord_1595058, baseEnd_1595058] using wordTrace_append hprefix tailTrace_1595058
  have hstable : (prefixWord ++ tailWord_1595058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595058).length < 2 ^ (prefixWord ++ tailWord_1595058).sum := by decide
  have hdescent : baseEnd_1595058 < baseStart_1595058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595062 : List Nat := [5, 1, 3, 1, 1, 1, 3, 7]
def baseStart_1595062 : Nat := 118140960795 + 1595062 * 2 ^ 59
def prefixEnd_1595062 : Nat := 4983230072969 + 3 ^ 40 * 1595062 * 2
def baseEnd_1595062 : Nat := 60669146646069892317737

theorem tailTrace_1595062 : CollatzResearch.WordTrace tailWord_1595062 prefixEnd_1595062 60669146646069892317737 := by
  unfold tailWord_1595062
  simp only [CollatzResearch.WordTrace]
  refine ⟨3636043159210641484165715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38784460364913509164434293 3636043159210641484165715)
  ·
    refine ⟨5454064738815962226248573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3636043159210641484165715 5454064738815962226248573)
    ·
      refine ⟨2045274277055985834843215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5454064738815962226248573 2045274277055985834843215)
      ·
        refine ⟨3067911415583978752264823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2045274277055985834843215 3067911415583978752264823)
        ·
          refine ⟨4601867123375968128397235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3067911415583978752264823 4601867123375968128397235)
          ·
            refine ⟨6902800685063952192595853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4601867123375968128397235 6902800685063952192595853)
            ·
              refine ⟨2588550256898982072223445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6902800685063952192595853 2588550256898982072223445)
              ·
                refine ⟨60669146646069892317737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2588550256898982072223445 60669146646069892317737)
                ·
                  rfl

theorem cell22_1595062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 7].length) (baseStart_1595062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1595062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1595062 prefixEnd_1595062 := by exact prefixLift 1595062
  have htrace : WordTrace (prefixWord ++ tailWord_1595062) baseStart_1595062 baseEnd_1595062 := by
    simpa [prefixWord, tailWord_1595062, baseEnd_1595062] using wordTrace_append hprefix tailTrace_1595062
  have hstable : (prefixWord ++ tailWord_1595062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595062).length < 2 ^ (prefixWord ++ tailWord_1595062).sum := by decide
  have hdescent : baseEnd_1595062 < baseStart_1595062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595150 : List Nat := [4, 1, 1, 2, 1, 1, 2, 4, 1, 5]
def baseStart_1595150 : Nat := 118140960795 + 1595150 * 2 ^ 59
def prefixEnd_1595150 : Nat := 4983230072969 + 3 ^ 40 * 1595150 * 2
def baseEnd_1595150 : Nat := 546052444013026134659363

theorem tailTrace_1595150 : CollatzResearch.WordTrace tailWord_1595150 prefixEnd_1595150 546052444013026134659363 := by
  unfold tailWord_1595150
  simp only [CollatzResearch.WordTrace]
  refine ⟨7272487521381431846981863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38786600114034303183903269 7272487521381431846981863)
  ·
    refine ⟨10908731282072147770472795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7272487521381431846981863 10908731282072147770472795)
    ·
      refine ⟨16363096923108221655709193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10908731282072147770472795 16363096923108221655709193)
      ·
        refine ⟨12272322692331166241781895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16363096923108221655709193 12272322692331166241781895)
        ·
          refine ⟨18408484038496749362672843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12272322692331166241781895 18408484038496749362672843)
          ·
            refine ⟨27612726057745124044009265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18408484038496749362672843 27612726057745124044009265)
            ·
              refine ⟨20709544543308843033006949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27612726057745124044009265 20709544543308843033006949)
              ·
                refine ⟨3883039601870408068688803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20709544543308843033006949 3883039601870408068688803)
                ·
                  refine ⟨5824559402805612103033205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3883039601870408068688803 5824559402805612103033205)
                  ·
                    refine ⟨546052444013026134659363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5824559402805612103033205 546052444013026134659363)
                    ·
                      rfl

theorem cell22_1595150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_1595150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1595150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1595150 prefixEnd_1595150 := by exact prefixLift 1595150
  have htrace : WordTrace (prefixWord ++ tailWord_1595150) baseStart_1595150 baseEnd_1595150 := by
    simpa [prefixWord, tailWord_1595150, baseEnd_1595150] using wordTrace_append hprefix tailTrace_1595150
  have hstable : (prefixWord ++ tailWord_1595150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595150).length < 2 ^ (prefixWord ++ tailWord_1595150).sum := by decide
  have hdescent : baseEnd_1595150 < baseStart_1595150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595154 : List Nat := [3, 2, 4, 1, 1, 1, 2, 3, 1, 4]
def baseStart_1595154 : Nat := 118140960795 + 1595154 * 2 ^ 59
def prefixEnd_1595154 : Nat := 4983230072969 + 3 ^ 40 * 1595154 * 2
def baseEnd_1595154 : Nat := 546053813294771457559351

theorem tailTrace_1595154 : CollatzResearch.WordTrace tailWord_1595154 prefixEnd_1595154 546053813294771457559351 := by
  unfold tailWord_1595154
  simp only [CollatzResearch.WordTrace]
  refine ⟨14545011515759240864750129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38786697375357975639333677 14545011515759240864750129)
  ·
    refine ⟨10908758636819430648562597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14545011515759240864750129 10908758636819430648562597)
    ·
      refine ⟨2045392244403643246605487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10908758636819430648562597 2045392244403643246605487)
      ·
        refine ⟨3068088366605464869908231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2045392244403643246605487 3068088366605464869908231)
        ·
          refine ⟨4602132549908197304862347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3068088366605464869908231 4602132549908197304862347)
          ·
            refine ⟨6903198824862295957293521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4602132549908197304862347 6903198824862295957293521)
            ·
              refine ⟨5177399118646721967970141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6903198824862295957293521 5177399118646721967970141)
              ·
                refine ⟨1941524669492520737988803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5177399118646721967970141 1941524669492520737988803)
                ·
                  refine ⟨2912287004238781106983205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1941524669492520737988803 2912287004238781106983205)
                  ·
                    refine ⟨546053813294771457559351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2912287004238781106983205 546053813294771457559351)
                    ·
                      rfl

theorem cell22_1595154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_1595154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1595154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1595154 prefixEnd_1595154 := by exact prefixLift 1595154
  have htrace : WordTrace (prefixWord ++ tailWord_1595154) baseStart_1595154 baseEnd_1595154 := by
    simpa [prefixWord, tailWord_1595154, baseEnd_1595154] using wordTrace_append hprefix tailTrace_1595154
  have hstable : (prefixWord ++ tailWord_1595154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595154).length < 2 ^ (prefixWord ++ tailWord_1595154).sum := by decide
  have hdescent : baseEnd_1595154 < baseStart_1595154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595167 : List Nat := [1, 1, 2, 4, 2, 1, 2, 4, 2, 3]
def baseStart_1595167 : Nat := 118140960795 + 1595167 * 2 ^ 59
def prefixEnd_1595167 : Nat := 4983230072969 + 3 ^ 40 * 1595167 * 2
def baseEnd_1595167 : Nat := 546058263460443756984311

theorem tailTrace_1595167 : CollatzResearch.WordTrace tailWord_1595167 prefixEnd_1595167 546058263460443756984311 := by
  unfold tailWord_1595167
  simp only [CollatzResearch.WordTrace]
  refine ⟨58180520211989866679223755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38787013474659911119482503 58180520211989866679223755)
  ·
    refine ⟨87270780317984800018835633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58180520211989866679223755 87270780317984800018835633)
    ·
      refine ⟨65453085238488600014126725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87270780317984800018835633 65453085238488600014126725)
      ·
        refine ⟨12272453482216612502648761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65453085238488600014126725 12272453482216612502648761)
        ·
          refine ⟨9204340111662459376986571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12272453482216612502648761 9204340111662459376986571)
          ·
            refine ⟨13806510167493689065479857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9204340111662459376986571 13806510167493689065479857)
            ·
              refine ⟨10354882625620266799109893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13806510167493689065479857 10354882625620266799109893)
              ·
                refine ⟨1941540492303800024833105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10354882625620266799109893 1941540492303800024833105)
                ·
                  refine ⟨1456155369227850018624829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1941540492303800024833105 1456155369227850018624829)
                  ·
                    refine ⟨546058263460443756984311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1456155369227850018624829 546058263460443756984311)
                    ·
                      rfl

theorem cell22_1595167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 4, 2, 3].length) (baseStart_1595167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1595167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1595167 prefixEnd_1595167 := by exact prefixLift 1595167
  have htrace : WordTrace (prefixWord ++ tailWord_1595167) baseStart_1595167 baseEnd_1595167 := by
    simpa [prefixWord, tailWord_1595167, baseEnd_1595167] using wordTrace_append hprefix tailTrace_1595167
  have hstable : (prefixWord ++ tailWord_1595167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595167).length < 2 ^ (prefixWord ++ tailWord_1595167).sum := by decide
  have hdescent : baseEnd_1595167 < baseStart_1595167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595169 : List Nat := [1, 2, 3, 2, 1, 4, 3, 2, 4]
def baseStart_1595169 : Nat := 118140960795 + 1595169 * 2 ^ 59
def prefixEnd_1595169 : Nat := 4983230072969 + 3 ^ 40 * 1595169 * 2
def baseEnd_1595169 : Nat := 182019649367105472811435

theorem tailTrace_1595169 : CollatzResearch.WordTrace tailWord_1595169 prefixEnd_1595169 182019649367105472811435 := by
  unfold tailWord_1595169
  simp only [CollatzResearch.WordTrace]
  refine ⟨58180593157982621020796561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38787062105321747347197707 58180593157982621020796561)
  ·
    refine ⟨43635444868486965765597421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58180593157982621020796561 43635444868486965765597421)
    ·
      refine ⟨16363291825682612162099033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43635444868486965765597421 16363291825682612162099033)
      ·
        refine ⟨12272468869261959121574275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16363291825682612162099033 12272468869261959121574275)
        ·
          refine ⟨18408703303892938682361413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12272468869261959121574275 18408703303892938682361413)
          ·
            refine ⟨3451631869479926002942765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18408703303892938682361413 3451631869479926002942765)
            ·
              refine ⟨1294361951054972251103537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3451631869479926002942765 1294361951054972251103537)
              ·
                refine ⟨970771463291229188327653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1294361951054972251103537 970771463291229188327653)
                ·
                  refine ⟨182019649367105472811435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 970771463291229188327653 182019649367105472811435)
                  ·
                    rfl

theorem cell22_1595169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 2, 4].length) (baseStart_1595169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1595169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1595169 prefixEnd_1595169 := by exact prefixLift 1595169
  have htrace : WordTrace (prefixWord ++ tailWord_1595169) baseStart_1595169 baseEnd_1595169 := by
    simpa [prefixWord, tailWord_1595169, baseEnd_1595169] using wordTrace_append hprefix tailTrace_1595169
  have hstable : (prefixWord ++ tailWord_1595169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595169).length < 2 ^ (prefixWord ++ tailWord_1595169).sum := by decide
  have hdescent : baseEnd_1595169 < baseStart_1595169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595180 : List Nat := [2, 2, 1, 1, 1, 6, 2, 7]
def baseStart_1595180 : Nat := 118140960795 + 1595180 * 2 ^ 59
def prefixEnd_1595180 : Nat := 4983230072969 + 3 ^ 40 * 1595180 * 2
def baseEnd_1595180 : Nat := 60673634847346228489919

theorem tailTrace_1595180 : CollatzResearch.WordTrace tailWord_1595180 prefixEnd_1595180 60673634847346228489919 := by
  unfold tailWord_1595180
  simp only [CollatzResearch.WordTrace]
  refine ⟨29090497180471384949723497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38787329573961846599631329 29090497180471384949723497)
  ·
    refine ⟨21817872885353538712292623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29090497180471384949723497 21817872885353538712292623)
    ·
      refine ⟨32726809328030308068438935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21817872885353538712292623 32726809328030308068438935)
      ·
        refine ⟨49090213992045462102658403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32726809328030308068438935 49090213992045462102658403)
        ·
          refine ⟨73635320988068193153987605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49090213992045462102658403 73635320988068193153987605)
          ·
            refine ⟨3451655671315696554093169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 73635320988068193153987605 3451655671315696554093169)
            ·
              refine ⟨2588741753486772415569877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3451655671315696554093169 2588741753486772415569877)
              ·
                refine ⟨60673634847346228489919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2588741753486772415569877 60673634847346228489919)
                ·
                  rfl

theorem cell22_1595180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 7].length) (baseStart_1595180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1595180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1595180 prefixEnd_1595180 := by exact prefixLift 1595180
  have htrace : WordTrace (prefixWord ++ tailWord_1595180) baseStart_1595180 baseEnd_1595180 := by
    simpa [prefixWord, tailWord_1595180, baseEnd_1595180] using wordTrace_append hprefix tailTrace_1595180
  have hstable : (prefixWord ++ tailWord_1595180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595180).length < 2 ^ (prefixWord ++ tailWord_1595180).sum := by decide
  have hdescent : baseEnd_1595180 < baseStart_1595180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595287 : List Nat := [1, 1, 3, 3, 1, 4, 2, 1, 6]
def baseStart_1595287 : Nat := 118140960795 + 1595287 * 2 ^ 59
def prefixEnd_1595287 : Nat := 4983230072969 + 3 ^ 40 * 1595287 * 2
def baseEnd_1595287 : Nat := 182033113970934481327981

theorem tailTrace_1595287 : CollatzResearch.WordTrace tailWord_1595287 prefixEnd_1595287 182033113970934481327981 := by
  unfold tailWord_1595287
  simp only [CollatzResearch.WordTrace]
  refine ⟨58184896971555127173592115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38789931314370084782394743 58184896971555127173592115)
  ·
    refine ⟨87277345457332690760388173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58184896971555127173592115 87277345457332690760388173)
    ·
      refine ⟨32729004546499759035145565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87277345457332690760388173 32729004546499759035145565)
      ·
        refine ⟨12273376704937409638179587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32729004546499759035145565 12273376704937409638179587)
        ·
          refine ⟨18410065057406114457269381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12273376704937409638179587 18410065057406114457269381)
          ·
            refine ⟨3451887198263646460738009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18410065057406114457269381 3451887198263646460738009)
            ·
              refine ⟨2588915398697734845553507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3451887198263646460738009 2588915398697734845553507)
              ·
                refine ⟨3883373098046602268330261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2588915398697734845553507 3883373098046602268330261)
                ·
                  refine ⟨182033113970934481327981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3883373098046602268330261 182033113970934481327981)
                  ·
                    rfl

theorem cell22_1595287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 6].length) (baseStart_1595287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1595287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1595287 prefixEnd_1595287 := by exact prefixLift 1595287
  have htrace : WordTrace (prefixWord ++ tailWord_1595287) baseStart_1595287 baseEnd_1595287 := by
    simpa [prefixWord, tailWord_1595287, baseEnd_1595287] using wordTrace_append hprefix tailTrace_1595287
  have hstable : (prefixWord ++ tailWord_1595287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595287).length < 2 ^ (prefixWord ++ tailWord_1595287).sum := by decide
  have hdescent : baseEnd_1595287 < baseStart_1595287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595315 : List Nat := [1, 1, 1, 2, 3, 1, 5, 8]
def baseStart_1595315 : Nat := 118140960795 + 1595315 * 2 ^ 59
def prefixEnd_1595315 : Nat := 4983230072969 + 3 ^ 40 * 1595315 * 2
def baseEnd_1595315 : Nat := 60678769653891189364873

theorem tailTrace_1595315 : CollatzResearch.WordTrace tailWord_1595315 prefixEnd_1595315 60678769653891189364873 := by
  unfold tailWord_1595315
  simp only [CollatzResearch.WordTrace]
  refine ⟨58185918215453687955611399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38790612143635791970407599 58185918215453687955611399)
  ·
    refine ⟨87278877323180531933417099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58185918215453687955611399 87278877323180531933417099)
    ·
      refine ⟨130918315984770797900125649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87278877323180531933417099 130918315984770797900125649)
      ·
        refine ⟨98188736988578098425094237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130918315984770797900125649 98188736988578098425094237)
        ·
          refine ⟨36820776370716786909410339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98188736988578098425094237 36820776370716786909410339)
          ·
            refine ⟨55231164556075180364115509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36820776370716786909410339 55231164556075180364115509)
            ·
              refine ⟨5177921677132048159135829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55231164556075180364115509 5177921677132048159135829)
              ·
                refine ⟨60678769653891189364873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5177921677132048159135829 60678769653891189364873)
                ·
                  rfl

theorem cell22_1595315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 8].length) (baseStart_1595315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1595315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1595315 prefixEnd_1595315 := by exact prefixLift 1595315
  have htrace : WordTrace (prefixWord ++ tailWord_1595315) baseStart_1595315 baseEnd_1595315 := by
    simpa [prefixWord, tailWord_1595315, baseEnd_1595315] using wordTrace_append hprefix tailTrace_1595315
  have hstable : (prefixWord ++ tailWord_1595315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595315).length < 2 ^ (prefixWord ++ tailWord_1595315).sum := by decide
  have hdescent : baseEnd_1595315 < baseStart_1595315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595317 : List Nat := [1, 3, 3, 2, 1, 2, 2, 1, 1, 6]
def baseStart_1595317 : Nat := 118140960795 + 1595317 * 2 ^ 59
def prefixEnd_1595317 : Nat := 4983230072969 + 3 ^ 40 * 1595317 * 2
def baseEnd_1595317 : Nat := 546109611525893365733851

theorem tailTrace_1595317 : CollatzResearch.WordTrace tailWord_1595317 prefixEnd_1595317 546109611525893365733851 := by
  unfold tailWord_1595317
  simp only [CollatzResearch.WordTrace]
  refine ⟨58185991161446442297184205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38790660774297628198122803 58185991161446442297184205)
  ·
    refine ⟨21819746685542415861444077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58185991161446442297184205 21819746685542415861444077)
    ·
      refine ⟨8182405007078405948041529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21819746685542415861444077 8182405007078405948041529)
      ·
        refine ⟨6136803755308804461031147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8182405007078405948041529 6136803755308804461031147)
        ·
          refine ⟨9205205632963206691546721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6136803755308804461031147 9205205632963206691546721)
          ·
            refine ⟨6903904224722405018660041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9205205632963206691546721 6903904224722405018660041)
            ·
              refine ⟨5177928168541803763995031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6903904224722405018660041 5177928168541803763995031)
              ·
                refine ⟨7766892252812705645992547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5177928168541803763995031 7766892252812705645992547)
                ·
                  refine ⟨11650338379219058468988821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7766892252812705645992547 11650338379219058468988821)
                  ·
                    refine ⟨546109611525893365733851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11650338379219058468988821 546109611525893365733851)
                    ·
                      rfl

theorem cell22_1595317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_1595317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1595317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1595317 prefixEnd_1595317 := by exact prefixLift 1595317
  have htrace : WordTrace (prefixWord ++ tailWord_1595317) baseStart_1595317 baseEnd_1595317 := by
    simpa [prefixWord, tailWord_1595317, baseEnd_1595317] using wordTrace_append hprefix tailTrace_1595317
  have hstable : (prefixWord ++ tailWord_1595317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595317).length < 2 ^ (prefixWord ++ tailWord_1595317).sum := by decide
  have hdescent : baseEnd_1595317 < baseStart_1595317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595353 : List Nat := [1, 2, 1, 2, 6, 2, 2, 1, 2, 3]
def baseStart_1595353 : Nat := 118140960795 + 1595353 * 2 ^ 59
def prefixEnd_1595353 : Nat := 4983230072969 + 3 ^ 40 * 1595353 * 2
def baseEnd_1595353 : Nat := 546121935061601271833741

theorem tailTrace_1595353 : CollatzResearch.WordTrace tailWord_1595353 prefixEnd_1595353 546121935061601271833741 := by
  unfold tailWord_1595353
  simp only [CollatzResearch.WordTrace]
  refine ⟨58187304189316020445494713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38791536126210680296996475 58187304189316020445494713)
  ·
    refine ⟨43640478141987015334121035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58187304189316020445494713 43640478141987015334121035)
    ·
      refine ⟨65460717212980523001181553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43640478141987015334121035 65460717212980523001181553)
      ·
        refine ⟨49095537909735392250886165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65460717212980523001181553 49095537909735392250886165)
        ·
          refine ⟨2301353339518846511760289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 49095537909735392250886165 2301353339518846511760289)
          ·
            refine ⟨1726015004639134883820217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2301353339518846511760289 1726015004639134883820217)
            ·
              refine ⟨1294511253479351162865163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1726015004639134883820217 1294511253479351162865163)
              ·
                refine ⟨1941766880219026744297745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1294511253479351162865163 1941766880219026744297745)
                ·
                  refine ⟨1456325160164270058223309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1941766880219026744297745 1456325160164270058223309)
                  ·
                    refine ⟨546121935061601271833741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1456325160164270058223309 546121935061601271833741)
                    ·
                      rfl

theorem cell22_1595353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 1, 2, 3].length) (baseStart_1595353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1595353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1595353 prefixEnd_1595353 := by exact prefixLift 1595353
  have htrace : WordTrace (prefixWord ++ tailWord_1595353) baseStart_1595353 baseEnd_1595353 := by
    simpa [prefixWord, tailWord_1595353, baseEnd_1595353] using wordTrace_append hprefix tailTrace_1595353
  have hstable : (prefixWord ++ tailWord_1595353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595353).length < 2 ^ (prefixWord ++ tailWord_1595353).sum := by decide
  have hdescent : baseEnd_1595353 < baseStart_1595353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595441 : List Nat := [1, 2, 2, 3, 1, 3, 4, 1, 1, 4]
def baseStart_1595441 : Nat := 118140960795 + 1595441 * 2 ^ 59
def prefixEnd_1595441 : Nat := 4983230072969 + 3 ^ 40 * 1595441 * 2
def baseEnd_1595441 : Nat := 546152059259998375633471

theorem tailTrace_1595441 : CollatzResearch.WordTrace tailWord_1595441 prefixEnd_1595441 546152059259998375633471 := by
  unfold tailWord_1595441
  simp only [CollatzResearch.WordTrace]
  refine ⟨58190513812997211474698177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38793675875331474316465451 58190513812997211474698177)
  ·
    refine ⟨43642885359747908606023633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58190513812997211474698177 43642885359747908606023633)
    ·
      refine ⟨32732164019810931454517725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43642885359747908606023633 32732164019810931454517725)
      ·
        refine ⟨12274561507429099295444147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32732164019810931454517725 12274561507429099295444147)
        ·
          refine ⟨18411842261143648943166221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12274561507429099295444147 18411842261143648943166221)
          ·
            refine ⟨6904440847928868353687333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18411842261143648943166221 6904440847928868353687333)
            ·
              refine ⟨1294582658986662816316375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6904440847928868353687333 1294582658986662816316375)
              ·
                refine ⟨1941873988479994224474563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1294582658986662816316375 1941873988479994224474563)
                ·
                  refine ⟨2912810982719991336711845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1941873988479994224474563 2912810982719991336711845)
                  ·
                    refine ⟨546152059259998375633471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2912810982719991336711845 546152059259998375633471)
                    ·
                      rfl

theorem cell22_1595441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 1, 1, 4].length) (baseStart_1595441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1595441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1595441 prefixEnd_1595441 := by exact prefixLift 1595441
  have htrace : WordTrace (prefixWord ++ tailWord_1595441) baseStart_1595441 baseEnd_1595441 := by
    simpa [prefixWord, tailWord_1595441, baseEnd_1595441] using wordTrace_append hprefix tailTrace_1595441
  have hstable : (prefixWord ++ tailWord_1595441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595441).length < 2 ^ (prefixWord ++ tailWord_1595441).sum := by decide
  have hdescent : baseEnd_1595441 < baseStart_1595441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595469 : List Nat := [1, 6, 1, 1, 1, 1, 1, 1, 3, 6]
def baseStart_1595469 : Nat := 118140960795 + 1595469 * 2 ^ 59
def prefixEnd_1595469 : Nat := 4983230072969 + 3 ^ 40 * 1595469 * 2
def baseEnd_1595469 : Nat := 546161644232215635933385

theorem tailTrace_1595469 : CollatzResearch.WordTrace tailWord_1595469 prefixEnd_1595469 546161644232215635933385 := by
  unfold tailWord_1595469
  simp only [CollatzResearch.WordTrace]
  refine ⟨58191535056895772256717461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38794356704597181504478307 58191535056895772256717461)
  ·
    refine ⟨2727728205791989324533631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 58191535056895772256717461 2727728205791989324533631)
    ·
      refine ⟨4091592308687983986800447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2727728205791989324533631 4091592308687983986800447)
      ·
        refine ⟨6137388463031975980200671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4091592308687983986800447 6137388463031975980200671)
        ·
          refine ⟨9206082694547963970301007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6137388463031975980200671 9206082694547963970301007)
          ·
            refine ⟨13809124041821945955451511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9206082694547963970301007 13809124041821945955451511)
            ·
              refine ⟨20713686062732918933177267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13809124041821945955451511 20713686062732918933177267)
              ·
                refine ⟨31070529094099378399765901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20713686062732918933177267 31070529094099378399765901)
                ·
                  refine ⟨11651448410287266899912213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31070529094099378399765901 11651448410287266899912213)
                  ·
                    refine ⟨546161644232215635933385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11651448410287266899912213 546161644232215635933385)
                    ·
                      rfl

theorem cell22_1595469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_1595469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1595469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1595469 prefixEnd_1595469 := by exact prefixLift 1595469
  have htrace : WordTrace (prefixWord ++ tailWord_1595469) baseStart_1595469 baseEnd_1595469 := by
    simpa [prefixWord, tailWord_1595469, baseEnd_1595469] using wordTrace_append hprefix tailTrace_1595469
  have hstable : (prefixWord ++ tailWord_1595469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595469).length < 2 ^ (prefixWord ++ tailWord_1595469).sum := by decide
  have hdescent : baseEnd_1595469 < baseStart_1595469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595482 : List Nat := [3, 1, 1, 2, 1, 1, 3, 1, 2, 7]
def baseStart_1595482 : Nat := 118140960795 + 1595482 * 2 ^ 59
def prefixEnd_1595482 : Nat := 4983230072969 + 3 ^ 40 * 1595482 * 2
def baseEnd_1595482 : Nat := 546166094397887935358345

theorem tailTrace_1595482 : CollatzResearch.WordTrace tailWord_1595482 prefixEnd_1595482 546166094397887935358345 := by
  unfold tailWord_1595482
  simp only [CollatzResearch.WordTrace]
  refine ⟨14548002301462168869235175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38794672803899116984627133 14548002301462168869235175)
  ·
    refine ⟨21822003452193253303852763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14548002301462168869235175 21822003452193253303852763)
    ·
      refine ⟨32733005178289879955779145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21822003452193253303852763 32733005178289879955779145)
      ·
        refine ⟨24549753883717409966834359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32733005178289879955779145 24549753883717409966834359)
        ·
          refine ⟨36824630825576114950251539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24549753883717409966834359 36824630825576114950251539)
          ·
            refine ⟨55236946238364172425377309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36824630825576114950251539 55236946238364172425377309)
            ·
              refine ⟨20713854839386564659516491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55236946238364172425377309 20713854839386564659516491)
              ·
                refine ⟨31070782259079846989274737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20713854839386564659516491 31070782259079846989274737)
                ·
                  refine ⟨23303086694309885241956053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31070782259079846989274737 23303086694309885241956053)
                  ·
                    refine ⟨546166094397887935358345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23303086694309885241956053 546166094397887935358345)
                    ·
                      rfl

theorem cell22_1595482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 2, 7].length) (baseStart_1595482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1595482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1595482 prefixEnd_1595482 := by exact prefixLift 1595482
  have htrace : WordTrace (prefixWord ++ tailWord_1595482) baseStart_1595482 baseEnd_1595482 := by
    simpa [prefixWord, tailWord_1595482, baseEnd_1595482] using wordTrace_append hprefix tailTrace_1595482
  have hstable : (prefixWord ++ tailWord_1595482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595482).length < 2 ^ (prefixWord ++ tailWord_1595482).sum := by decide
  have hdescent : baseEnd_1595482 < baseStart_1595482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595484 : List Nat := [2, 2, 4, 1, 1, 3, 1, 8]
def baseStart_1595484 : Nat := 118140960795 + 1595484 * 2 ^ 59
def prefixEnd_1595484 : Nat := 4983230072969 + 3 ^ 40 * 1595484 * 2
def baseEnd_1595484 : Nat := 60685197670973399645371

theorem tailTrace_1595484 : CollatzResearch.WordTrace tailWord_1595484 prefixEnd_1595484 60685197670973399645371 := by
  unfold tailWord_1595484
  simp only [CollatzResearch.WordTrace]
  refine ⟨29096041075920714909256753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38794721434560953212342337 29096041075920714909256753)
  ·
    refine ⟨21822030806940536181942565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29096041075920714909256753 21822030806940536181942565)
    ·
      refine ⟨4091630776301350534114231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21822030806940536181942565 4091630776301350534114231)
      ·
        refine ⟨6137446164452025801171347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4091630776301350534114231 6137446164452025801171347)
        ·
          refine ⟨9206169246678038701757021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6137446164452025801171347 9206169246678038701757021)
          ·
            refine ⟨3452313467504264513158883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9206169246678038701757021 3452313467504264513158883)
            ·
              refine ⟨5178470201256396769738325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3452313467504264513158883 5178470201256396769738325)
              ·
                refine ⟨60685197670973399645371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5178470201256396769738325 60685197670973399645371)
                ·
                  rfl

theorem cell22_1595484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 8].length) (baseStart_1595484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1595484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1595484 prefixEnd_1595484 := by exact prefixLift 1595484
  have htrace : WordTrace (prefixWord ++ tailWord_1595484) baseStart_1595484 baseEnd_1595484 := by
    simpa [prefixWord, tailWord_1595484, baseEnd_1595484] using wordTrace_append hprefix tailTrace_1595484
  have hstable : (prefixWord ++ tailWord_1595484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595484).length < 2 ^ (prefixWord ++ tailWord_1595484).sum := by decide
  have hdescent : baseEnd_1595484 < baseStart_1595484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595490 : List Nat := [3, 3, 2, 2, 2, 2, 1, 3, 4]
def baseStart_1595490 : Nat := 118140960795 + 1595490 * 2 ^ 59
def prefixEnd_1595490 : Nat := 4983230072969 + 3 ^ 40 * 1595490 * 2
def baseEnd_1595490 : Nat := 182056277653792860386107

theorem tailTrace_1595490 : CollatzResearch.WordTrace tailWord_1595490 prefixEnd_1595490 182056277653792860386107 := by
  unfold tailWord_1595490
  simp only [CollatzResearch.WordTrace]
  refine ⟨14548075247454923210807981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38794867326546461895487949 14548075247454923210807981)
  ·
    refine ⟨5455528217795596204052993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14548075247454923210807981 5455528217795596204052993)
    ·
      refine ⟨4091646163346697153039745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5455528217795596204052993 4091646163346697153039745)
      ·
        refine ⟨3068734622510022864779809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4091646163346697153039745 3068734622510022864779809)
        ·
          refine ⟨2301550966882517148584857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3068734622510022864779809 2301550966882517148584857)
          ·
            refine ⟨1726163225161887861438643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2301550966882517148584857 1726163225161887861438643)
            ·
              refine ⟨2589244837742831792157965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1726163225161887861438643 2589244837742831792157965)
              ·
                refine ⟨970966814153561922059237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2589244837742831792157965 970966814153561922059237)
                ·
                  refine ⟨182056277653792860386107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 970966814153561922059237 182056277653792860386107)
                  ·
                    rfl

theorem cell22_1595490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_1595490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1595490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1595490 prefixEnd_1595490 := by exact prefixLift 1595490
  have htrace : WordTrace (prefixWord ++ tailWord_1595490) baseStart_1595490 baseEnd_1595490 := by
    simpa [prefixWord, tailWord_1595490, baseEnd_1595490] using wordTrace_append hprefix tailTrace_1595490
  have hstable : (prefixWord ++ tailWord_1595490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595490).length < 2 ^ (prefixWord ++ tailWord_1595490).sum := by decide
  have hdescent : baseEnd_1595490 < baseStart_1595490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595516 : List Nat := [2, 2, 2, 1, 1, 4, 3, 1, 3, 3]
def baseStart_1595516 : Nat := 118140960795 + 1595516 * 2 ^ 59
def prefixEnd_1595516 : Nat := 4983230072969 + 3 ^ 40 * 1595516 * 2
def baseEnd_1595516 : Nat := 546177733292723180008241

theorem tailTrace_1595516 : CollatzResearch.WordTrace tailWord_1595516 prefixEnd_1595516 546177733292723180008241 := by
  unfold tailWord_1595516
  simp only [CollatzResearch.WordTrace]
  refine ⟨29096624643862749641839201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38795499525150332855785601 29096624643862749641839201)
  ·
    refine ⟨21822468482897062231379401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29096624643862749641839201 21822468482897062231379401)
    ·
      refine ⟨16366851362172796673534551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21822468482897062231379401 16366851362172796673534551)
      ·
        refine ⟨24550277043259195010301827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16366851362172796673534551 24550277043259195010301827)
        ·
          refine ⟨36825415564888792515452741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24550277043259195010301827 36825415564888792515452741)
          ·
            refine ⟨6904765418416648596647389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36825415564888792515452741 6904765418416648596647389)
            ·
              refine ⟨2589287031906243223742771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6904765418416648596647389 2589287031906243223742771)
              ·
                refine ⟨3883930547859364835614157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2589287031906243223742771 3883930547859364835614157)
                ·
                  refine ⟨1456473955447261813355309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3883930547859364835614157 1456473955447261813355309)
                  ·
                    refine ⟨546177733292723180008241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1456473955447261813355309 546177733292723180008241)
                    ·
                      rfl

theorem cell22_1595516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 3, 3].length) (baseStart_1595516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1595516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1595516 prefixEnd_1595516 := by exact prefixLift 1595516
  have htrace : WordTrace (prefixWord ++ tailWord_1595516) baseStart_1595516 baseEnd_1595516 := by
    simpa [prefixWord, tailWord_1595516, baseEnd_1595516] using wordTrace_append hprefix tailTrace_1595516
  have hstable : (prefixWord ++ tailWord_1595516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595516).length < 2 ^ (prefixWord ++ tailWord_1595516).sum := by decide
  have hdescent : baseEnd_1595516 < baseStart_1595516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595529 : List Nat := [1, 2, 1, 1, 4, 2, 3, 3, 5]
def baseStart_1595529 : Nat := 118140960795 + 1595529 * 2 ^ 59
def prefixEnd_1595529 : Nat := 4983230072969 + 3 ^ 40 * 1595529 * 2
def baseEnd_1595529 : Nat := 182060727819465159811067

theorem tailTrace_1595529 : CollatzResearch.WordTrace tailWord_1595529 prefixEnd_1595529 182060727819465159811067 := by
  unfold tailWord_1595529
  simp only [CollatzResearch.WordTrace]
  refine ⟨58193723436678402503901641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38795815624452268335934427 58193723436678402503901641)
  ·
    refine ⟨43645292577508801877926231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58193723436678402503901641 43645292577508801877926231)
    ·
      refine ⟨65467938866263202816889347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43645292577508801877926231 65467938866263202816889347)
      ·
        refine ⟨98201908299394804225334021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65467938866263202816889347 98201908299394804225334021)
        ·
          refine ⟨18412857806136525792250129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98201908299394804225334021 18412857806136525792250129)
          ·
            refine ⟨13809643354602394344187597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18412857806136525792250129 13809643354602394344187597)
            ·
              refine ⟨5178616257975897879070349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13809643354602394344187597 5178616257975897879070349)
              ·
                refine ⟨1941981096740961704651381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5178616257975897879070349 1941981096740961704651381)
                ·
                  refine ⟨182060727819465159811067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1941981096740961704651381 182060727819465159811067)
                  ·
                    rfl

theorem cell22_1595529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 3, 5].length) (baseStart_1595529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1595529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1595529 prefixEnd_1595529 := by exact prefixLift 1595529
  have htrace : WordTrace (prefixWord ++ tailWord_1595529) baseStart_1595529 baseEnd_1595529 := by
    simpa [prefixWord, tailWord_1595529, baseEnd_1595529] using wordTrace_append hprefix tailTrace_1595529
  have hstable : (prefixWord ++ tailWord_1595529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595529).length < 2 ^ (prefixWord ++ tailWord_1595529).sum := by decide
  have hdescent : baseEnd_1595529 < baseStart_1595529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595589 : List Nat := [1, 3, 1, 1, 1, 1, 5, 3, 1, 5]
def baseStart_1595589 : Nat := 118140960795 + 1595589 * 2 ^ 59
def prefixEnd_1595589 : Nat := 4983230072969 + 3 ^ 40 * 1595589 * 2
def baseEnd_1595589 : Nat := 546202722684575322933017

theorem tailTrace_1595589 : CollatzResearch.WordTrace tailWord_1595589 prefixEnd_1595589 546202722684575322933017 := by
  unfold tailWord_1595589
  simp only [CollatzResearch.WordTrace]
  refine ⟨58195911816461032751085821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38797274544307355167390547 58195911816461032751085821)
  ·
    refine ⟨21823466931172887281657183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58195911816461032751085821 21823466931172887281657183)
    ·
      refine ⟨32735200396759330922485775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21823466931172887281657183 32735200396759330922485775)
      ·
        refine ⟨49102800595138996383728663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32735200396759330922485775 49102800595138996383728663)
        ·
          refine ⟨73654200892708494575592995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49102800595138996383728663 73654200892708494575592995)
          ·
            refine ⟨110481301339062741863389493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73654200892708494575592995 110481301339062741863389493)
            ·
              refine ⟨10357622000537132049692765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 110481301339062741863389493 10357622000537132049692765)
              ·
                refine ⟨3884108250201424518634787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10357622000537132049692765 3884108250201424518634787)
                ·
                  refine ⟨5826162375302136777952181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3884108250201424518634787 5826162375302136777952181)
                  ·
                    refine ⟨546202722684575322933017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5826162375302136777952181 546202722684575322933017)
                    ·
                      rfl

theorem cell22_1595589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 5].length) (baseStart_1595589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1595589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1595589 prefixEnd_1595589 := by exact prefixLift 1595589
  have htrace : WordTrace (prefixWord ++ tailWord_1595589) baseStart_1595589 baseEnd_1595589 := by
    simpa [prefixWord, tailWord_1595589, baseEnd_1595589] using wordTrace_append hprefix tailTrace_1595589
  have hstable : (prefixWord ++ tailWord_1595589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595589).length < 2 ^ (prefixWord ++ tailWord_1595589).sum := by decide
  have hdescent : baseEnd_1595589 < baseStart_1595589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595608 : List Nat := [2, 1, 2, 2, 4, 2, 2, 3, 4]
def baseStart_1595608 : Nat := 118140960795 + 1595608 * 2 ^ 59
def prefixEnd_1595608 : Nat := 4983230072969 + 3 ^ 40 * 1595608 * 2
def baseEnd_1595608 : Nat := 182069742257621868902653

theorem tailTrace_1595608 : CollatzResearch.WordTrace tailWord_1595608 prefixEnd_1595608 182069742257621868902653 := by
  unfold tailWord_1595608
  simp only [CollatzResearch.WordTrace]
  refine ⟨29098302401696099498013739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38797736535594799330684985 29098302401696099498013739)
  ·
    refine ⟨43647453602544149247020609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29098302401696099498013739 43647453602544149247020609)
    ·
      refine ⟨32735590201908111935265457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43647453602544149247020609 32735590201908111935265457)
      ·
        refine ⟨24551692651431083951449093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32735590201908111935265457 24551692651431083951449093)
        ·
          refine ⟨4603442372143328240896705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24551692651431083951449093 4603442372143328240896705)
          ·
            refine ⟨3452581779107496180672529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4603442372143328240896705 3452581779107496180672529)
            ·
              refine ⟨2589436334330622135504397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3452581779107496180672529 2589436334330622135504397)
              ·
                refine ⟨971038625373983300814149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2589436334330622135504397 971038625373983300814149)
                ·
                  refine ⟨182069742257621868902653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 971038625373983300814149 182069742257621868902653)
                  ·
                    rfl

theorem cell22_1595608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 3, 4].length) (baseStart_1595608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1595608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1595608 prefixEnd_1595608 := by exact prefixLift 1595608
  have htrace : WordTrace (prefixWord ++ tailWord_1595608) baseStart_1595608 baseEnd_1595608 := by
    simpa [prefixWord, tailWord_1595608, baseEnd_1595608] using wordTrace_append hprefix tailTrace_1595608
  have hstable : (prefixWord ++ tailWord_1595608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595608).length < 2 ^ (prefixWord ++ tailWord_1595608).sum := by decide
  have hdescent : baseEnd_1595608 < baseStart_1595608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595623 : List Nat := [1, 1, 5, 3, 1, 2, 1, 1, 4, 3]
def baseStart_1595623 : Nat := 118140960795 + 1595623 * 2 ^ 59
def prefixEnd_1595623 : Nat := 4983230072969 + 3 ^ 40 * 1595623 * 2
def baseEnd_1595623 : Nat := 546214361579410567582913

theorem tailTrace_1595623 : CollatzResearch.WordTrace tailWord_1595623 prefixEnd_1595623 546214361579410567582913 := by
  unfold tailWord_1595623
  simp only [CollatzResearch.WordTrace]
  refine ⟨58197151898337856557823523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38798101265558571038549015 58197151898337856557823523)
  ·
    refine ⟨87295727847506784836735285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58197151898337856557823523 87295727847506784836735285)
    ·
      refine ⟨8183974485703761078443933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87295727847506784836735285 8183974485703761078443933)
      ·
        refine ⟨3068990432138910404416475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8183974485703761078443933 3068990432138910404416475)
        ·
          refine ⟨4603485648208365606624713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3068990432138910404416475 4603485648208365606624713)
          ·
            refine ⟨3452614236156274204968535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4603485648208365606624713 3452614236156274204968535)
            ·
              refine ⟨5178921354234411307452803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3452614236156274204968535 5178921354234411307452803)
              ·
                refine ⟨7768382031351616961179205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5178921354234411307452803 7768382031351616961179205)
                ·
                  refine ⟨1456571630878428180221101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7768382031351616961179205 1456571630878428180221101)
                  ·
                    refine ⟨546214361579410567582913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1456571630878428180221101 546214361579410567582913)
                    ·
                      rfl

theorem cell22_1595623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_1595623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1595623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1595623 prefixEnd_1595623 := by exact prefixLift 1595623
  have htrace : WordTrace (prefixWord ++ tailWord_1595623) baseStart_1595623 baseEnd_1595623 := by
    simpa [prefixWord, tailWord_1595623, baseEnd_1595623] using wordTrace_append hprefix tailTrace_1595623
  have hstable : (prefixWord ++ tailWord_1595623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595623).length < 2 ^ (prefixWord ++ tailWord_1595623).sum := by decide
  have hdescent : baseEnd_1595623 < baseStart_1595623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595651 : List Nat := [1, 1, 1, 3, 2, 3, 1, 4, 3, 3]
def baseStart_1595651 : Nat := 118140960795 + 1595651 * 2 ^ 59
def prefixEnd_1595651 : Nat := 4983230072969 + 3 ^ 40 * 1595651 * 2
def baseEnd_1595651 : Nat := 546223946551627827882827

theorem tailTrace_1595651 : CollatzResearch.WordTrace tailWord_1595651 prefixEnd_1595651 546223946551627827882827 := by
  unfold tailWord_1595651
  simp only [CollatzResearch.WordTrace]
  refine ⟨58198173142236417339842807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38798782094824278226561871 58198173142236417339842807)
  ·
    refine ⟨87297259713354626009764211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58198173142236417339842807 87297259713354626009764211)
    ·
      refine ⟨130945889570031939014646317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87297259713354626009764211 130945889570031939014646317)
      ·
        refine ⟨49104708588761977130492369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130945889570031939014646317 49104708588761977130492369)
        ·
          refine ⟨36828531441571482847869277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49104708588761977130492369 36828531441571482847869277)
          ·
            refine ⟨13810699290589306067950979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36828531441571482847869277 13810699290589306067950979)
            ·
              refine ⟨20716048935883959101926469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13810699290589306067950979 20716048935883959101926469)
              ·
                refine ⟨3884259175478242331611213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20716048935883959101926469 3884259175478242331611213)
                ·
                  refine ⟨1456597190804340874354205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3884259175478242331611213 1456597190804340874354205)
                  ·
                    refine ⟨546223946551627827882827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1456597190804340874354205 546223946551627827882827)
                    ·
                      rfl

theorem cell22_1595651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 3, 3].length) (baseStart_1595651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1595651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1595651 prefixEnd_1595651 := by exact prefixLift 1595651
  have htrace : WordTrace (prefixWord ++ tailWord_1595651) baseStart_1595651 baseEnd_1595651 := by
    simpa [prefixWord, tailWord_1595651, baseEnd_1595651] using wordTrace_append hprefix tailTrace_1595651
  have hstable : (prefixWord ++ tailWord_1595651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595651).length < 2 ^ (prefixWord ++ tailWord_1595651).sum := by decide
  have hdescent : baseEnd_1595651 < baseStart_1595651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595685 : List Nat := [1, 3, 1, 2, 5, 2, 1, 1, 3, 3]
def baseStart_1595685 : Nat := 118140960795 + 1595685 * 2 ^ 59
def prefixEnd_1595685 : Nat := 4983230072969 + 3 ^ 40 * 1595685 * 2
def baseEnd_1595685 : Nat := 546235585446463072532723

theorem tailTrace_1595685 : CollatzResearch.WordTrace tailWord_1595685 prefixEnd_1595685 546235585446463072532723 := by
  unfold tailWord_1595685
  simp only [CollatzResearch.WordTrace]
  refine ⟨58199413224113241146580509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38799608816075494097720339 58199413224113241146580509)
  ·
    refine ⟨21824779959042465429967691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58199413224113241146580509 21824779959042465429967691)
    ·
      refine ⟨32737169938563698144951537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21824779959042465429967691 32737169938563698144951537)
      ·
        refine ⟨24552877453922773608713653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32737169938563698144951537 24552877453922773608713653)
        ·
          refine ⟨2301832261305260025816905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24552877453922773608713653 2301832261305260025816905)
          ·
            refine ⟨1726374195978945019362679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2301832261305260025816905 1726374195978945019362679)
            ·
              refine ⟨2589561293968417529044019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1726374195978945019362679 2589561293968417529044019)
              ·
                refine ⟨3884341940952626293566029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2589561293968417529044019 3884341940952626293566029)
                ·
                  refine ⟨1456628227857234860087261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3884341940952626293566029 1456628227857234860087261)
                  ·
                    refine ⟨546235585446463072532723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1456628227857234860087261 546235585446463072532723)
                    ·
                      rfl

theorem cell22_1595685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 3, 3].length) (baseStart_1595685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1595685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1595685 prefixEnd_1595685 := by exact prefixLift 1595685
  have htrace : WordTrace (prefixWord ++ tailWord_1595685) baseStart_1595685 baseEnd_1595685 := by
    simpa [prefixWord, tailWord_1595685, baseEnd_1595685] using wordTrace_append hprefix tailTrace_1595685
  have hstable : (prefixWord ++ tailWord_1595685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595685).length < 2 ^ (prefixWord ++ tailWord_1595685).sum := by decide
  have hdescent : baseEnd_1595685 < baseStart_1595685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595698 : List Nat := [3, 2, 1, 1, 5, 1, 1, 3, 5]
def baseStart_1595698 : Nat := 118140960795 + 1595698 * 2 ^ 59
def prefixEnd_1595698 : Nat := 4983230072969 + 3 ^ 40 * 1595698 * 2
def baseEnd_1595698 : Nat := 182080011870711790652561

theorem tailTrace_1595698 : CollatzResearch.WordTrace tailWord_1595698 prefixEnd_1595698 182080011870711790652561 := by
  unfold tailWord_1595698
  simp only [CollatzResearch.WordTrace]
  refine ⟨14549971843266536091700937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38799924915377429577869165 14549971843266536091700937)
  ·
    refine ⟨10912478882449902068775703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14549971843266536091700937 10912478882449902068775703)
    ·
      refine ⟨16368718323674853103163555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10912478882449902068775703 16368718323674853103163555)
      ·
        refine ⟨24553077485512279654745333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16368718323674853103163555 24553077485512279654745333)
        ·
          refine ⟨2301851014266776217632375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24553077485512279654745333 2301851014266776217632375)
          ·
            refine ⟨3452776521400164326448563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2301851014266776217632375 3452776521400164326448563)
            ·
              refine ⟨5179164782100246489672845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3452776521400164326448563 5179164782100246489672845)
              ·
                refine ⟨1942186793287592433627317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5179164782100246489672845 1942186793287592433627317)
                ·
                  refine ⟨182080011870711790652561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1942186793287592433627317 182080011870711790652561)
                  ·
                    rfl

theorem cell22_1595698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 3, 5].length) (baseStart_1595698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1595698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1595698 prefixEnd_1595698 := by exact prefixLift 1595698
  have htrace : WordTrace (prefixWord ++ tailWord_1595698) baseStart_1595698 baseEnd_1595698 := by
    simpa [prefixWord, tailWord_1595698, baseEnd_1595698] using wordTrace_append hprefix tailTrace_1595698
  have hstable : (prefixWord ++ tailWord_1595698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595698).length < 2 ^ (prefixWord ++ tailWord_1595698).sum := by decide
  have hdescent : baseEnd_1595698 < baseStart_1595698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595711 : List Nat := [1, 1, 2, 2, 4, 1, 3, 1, 3, 4]
def baseStart_1595711 : Nat := 118140960795 + 1595711 * 2 ^ 59
def prefixEnd_1595711 : Nat := 4983230072969 + 3 ^ 40 * 1595711 * 2
def baseEnd_1595711 : Nat := 546244485777807671382643

theorem tailTrace_1595711 : CollatzResearch.WordTrace tailWord_1595711 prefixEnd_1595711 546244485777807671382643 := by
  unfold tailWord_1595711
  simp only [CollatzResearch.WordTrace]
  refine ⟨58200361522019047587026987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38800241014679365058017991 58200361522019047587026987)
  ·
    refine ⟨87300542283028571380540481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58200361522019047587026987 87300542283028571380540481)
    ·
      refine ⟨65475406712271428535405361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87300542283028571380540481 65475406712271428535405361)
      ·
        refine ⟨49106555034203571401554021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65475406712271428535405361 49106555034203571401554021)
        ·
          refine ⟨9207479068913169637791379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49106555034203571401554021 9207479068913169637791379)
          ·
            refine ⟨13811218603369754456687069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9207479068913169637791379 13811218603369754456687069)
            ·
              refine ⟨5179206976263657921257651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13811218603369754456687069 5179206976263657921257651)
              ·
                refine ⟨7768810464395486881886477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5179206976263657921257651 7768810464395486881886477)
                ·
                  refine ⟨2913303924148307580707429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7768810464395486881886477 2913303924148307580707429)
                  ·
                    refine ⟨546244485777807671382643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2913303924148307580707429 546244485777807671382643)
                    ·
                      rfl

theorem cell22_1595711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 3, 4].length) (baseStart_1595711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1595711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1595711 prefixEnd_1595711 := by exact prefixLift 1595711
  have htrace : WordTrace (prefixWord ++ tailWord_1595711) baseStart_1595711 baseEnd_1595711 := by
    simpa [prefixWord, tailWord_1595711, baseEnd_1595711] using wordTrace_append hprefix tailTrace_1595711
  have hstable : (prefixWord ++ tailWord_1595711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595711).length < 2 ^ (prefixWord ++ tailWord_1595711).sum := by decide
  have hdescent : baseEnd_1595711 < baseStart_1595711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595773 : List Nat := [1, 4, 1, 1, 2, 3, 3, 1, 2, 4]
def baseStart_1595773 : Nat := 118140960795 + 1595773 * 2 ^ 59
def prefixEnd_1595773 : Nat := 4983230072969 + 3 ^ 40 * 1595773 * 2
def baseEnd_1595773 : Nat := 546265709644860176332453

theorem tailTrace_1595773 : CollatzResearch.WordTrace tailWord_1595773 prefixEnd_1595773 546265709644860176332453 := by
  unfold tailWord_1595773
  simp only [CollatzResearch.WordTrace]
  refine ⟨58202622847794432175783973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38801748565196288117189315 58202622847794432175783973)
  ·
    refine ⟨10912991783961456032959495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58202622847794432175783973 10912991783961456032959495)
    ·
      refine ⟨16369487675942184049439243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10912991783961456032959495 16369487675942184049439243)
      ·
        refine ⟨24554231513913276074158865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16369487675942184049439243 24554231513913276074158865)
        ·
          refine ⟨18415673635434957055619149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24554231513913276074158865 18415673635434957055619149)
          ·
            refine ⟨6905877613288108895857181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18415673635434957055619149 6905877613288108895857181)
            ·
              refine ⟨2589704104983040835946443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6905877613288108895857181 2589704104983040835946443)
              ·
                refine ⟨3884556157474561253919665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2589704104983040835946443 3884556157474561253919665)
                ·
                  refine ⟨2913417118105920940439749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3884556157474561253919665 2913417118105920940439749)
                  ·
                    refine ⟨546265709644860176332453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2913417118105920940439749 546265709644860176332453)
                    ·
                      rfl

theorem cell22_1595773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_1595773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1595773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1595773 prefixEnd_1595773 := by exact prefixLift 1595773
  have htrace : WordTrace (prefixWord ++ tailWord_1595773) baseStart_1595773 baseEnd_1595773 := by
    simpa [prefixWord, tailWord_1595773, baseEnd_1595773] using wordTrace_append hprefix tailTrace_1595773
  have hstable : (prefixWord ++ tailWord_1595773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595773).length < 2 ^ (prefixWord ++ tailWord_1595773).sum := by decide
  have hdescent : baseEnd_1595773 < baseStart_1595773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595809 : List Nat := [1, 2, 3, 5, 1, 1, 3, 1, 2, 3]
def baseStart_1595809 : Nat := 118140960795 + 1595809 * 2 ^ 59
def prefixEnd_1595809 : Nat := 4983230072969 + 3 ^ 40 * 1595809 * 2
def baseEnd_1595809 : Nat := 546278033180568082432343

theorem tailTrace_1595809 : CollatzResearch.WordTrace tailWord_1595809 prefixEnd_1595809 546278033180568082432343 := by
  unfold tailWord_1595809
  simp only [CollatzResearch.WordTrace]
  refine ⟨58203935875664010324094481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38802623917109340216062987 58203935875664010324094481)
  ·
    refine ⟨43652951906748007743070861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58203935875664010324094481 43652951906748007743070861)
    ·
      refine ⟨16369856965030502903651573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43652951906748007743070861 16369856965030502903651573)
      ·
        refine ⟨1534674090471609647217335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16369856965030502903651573 1534674090471609647217335)
        ·
          refine ⟨2302011135707414470826003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1534674090471609647217335 2302011135707414470826003)
          ·
            refine ⟨3453016703561121706239005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2302011135707414470826003 3453016703561121706239005)
            ·
              refine ⟨1294881263835420639839627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3453016703561121706239005 1294881263835420639839627)
              ·
                refine ⟨1942321895753130959759441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1294881263835420639839627 1942321895753130959759441)
                ·
                  refine ⟨1456741421814848219819581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1942321895753130959759441 1456741421814848219819581)
                  ·
                    refine ⟨546278033180568082432343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1456741421814848219819581 546278033180568082432343)
                    ·
                      rfl

theorem cell22_1595809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 1, 2, 3].length) (baseStart_1595809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1595809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1595809 prefixEnd_1595809 := by exact prefixLift 1595809
  have htrace : WordTrace (prefixWord ++ tailWord_1595809) baseStart_1595809 baseEnd_1595809 := by
    simpa [prefixWord, tailWord_1595809, baseEnd_1595809] using wordTrace_append hprefix tailTrace_1595809
  have hstable : (prefixWord ++ tailWord_1595809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595809).length < 2 ^ (prefixWord ++ tailWord_1595809).sum := by decide
  have hdescent : baseEnd_1595809 < baseStart_1595809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595837 : List Nat := [1, 4, 1, 2, 2, 2, 3, 3, 1, 3]
def baseStart_1595837 : Nat := 118140960795 + 1595837 * 2 ^ 59
def prefixEnd_1595837 : Nat := 4983230072969 + 3 ^ 40 * 1595837 * 2
def baseEnd_1595837 : Nat := 546287618152785342732257

theorem tailTrace_1595837 : CollatzResearch.WordTrace tailWord_1595837 prefixEnd_1595837 546287618152785342732257 := by
  unfold tailWord_1595837
  simp only [CollatzResearch.WordTrace]
  refine ⟨58204957119562571106113765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38803304746375047404075843 58204957119562571106113765)
  ·
    refine ⟨10913429459917982082396331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58204957119562571106113765 10913429459917982082396331)
    ·
      refine ⟨16370144189876973123594497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10913429459917982082396331 16370144189876973123594497)
      ·
        refine ⟨12277608142407729842695873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16370144189876973123594497 12277608142407729842695873)
        ·
          refine ⟨9208206106805797382021905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12277608142407729842695873 9208206106805797382021905)
          ·
            refine ⟨6906154580104348036516429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9208206106805797382021905 6906154580104348036516429)
            ·
              refine ⟨2589807967539130513693661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6906154580104348036516429 2589807967539130513693661)
              ·
                refine ⟨971177987827173942635123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2589807967539130513693661 971177987827173942635123)
                ·
                  refine ⟨1456766981740760913952685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 971177987827173942635123 1456766981740760913952685)
                  ·
                    refine ⟨546287618152785342732257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1456766981740760913952685 546287618152785342732257)
                    ·
                      rfl

theorem cell22_1595837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 3, 1, 3].length) (baseStart_1595837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1595837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1595837 prefixEnd_1595837 := by exact prefixLift 1595837
  have htrace : WordTrace (prefixWord ++ tailWord_1595837) baseStart_1595837 baseEnd_1595837 := by
    simpa [prefixWord, tailWord_1595837, baseEnd_1595837] using wordTrace_append hprefix tailTrace_1595837
  have hstable : (prefixWord ++ tailWord_1595837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595837).length < 2 ^ (prefixWord ++ tailWord_1595837).sum := by decide
  have hdescent : baseEnd_1595837 < baseStart_1595837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595880 : List Nat := [2, 1, 4, 1, 1, 3, 3, 2, 1, 4]
def baseStart_1595880 : Nat := 118140960795 + 1595880 * 2 ^ 59
def prefixEnd_1595880 : Nat := 4983230072969 + 3 ^ 40 * 1595880 * 2
def baseEnd_1595880 : Nat := 546302337931547563907125

theorem tailTrace_1595880 : CollatzResearch.WordTrace tailWord_1595880 prefixEnd_1595880 546302337931547563907125 := by
  unfold tailWord_1595880
  simp only [CollatzResearch.WordTrace]
  refine ⟨29103262729203394724964547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38804350305604526299952729 29103262729203394724964547)
  ·
    refine ⟨43654894093805092087446821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29103262729203394724964547 43654894093805092087446821)
    ·
      refine ⟨8185292642588454766396279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43654894093805092087446821 8185292642588454766396279)
      ·
        refine ⟨12277938963882682149594419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8185292642588454766396279 12277938963882682149594419)
        ·
          refine ⟨18416908445824023224391629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12277938963882682149594419 18416908445824023224391629)
          ·
            refine ⟨6906340667184008709146861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18416908445824023224391629 6906340667184008709146861)
            ·
              refine ⟨2589877750194003265930073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6906340667184008709146861 2589877750194003265930073)
              ·
                refine ⟨1942408312645502449447555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2589877750194003265930073 1942408312645502449447555)
                ·
                  refine ⟨2913612468968253674171333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1942408312645502449447555 2913612468968253674171333)
                  ·
                    refine ⟨546302337931547563907125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2913612468968253674171333 546302337931547563907125)
                    ·
                      rfl

theorem cell22_1595880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_1595880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1595880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1595880 prefixEnd_1595880 := by exact prefixLift 1595880
  have htrace : WordTrace (prefixWord ++ tailWord_1595880) baseStart_1595880 baseEnd_1595880 := by
    simpa [prefixWord, tailWord_1595880, baseEnd_1595880] using wordTrace_append hprefix tailTrace_1595880
  have hstable : (prefixWord ++ tailWord_1595880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595880).length < 2 ^ (prefixWord ++ tailWord_1595880).sum := by decide
  have hdescent : baseEnd_1595880 < baseStart_1595880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595927 : List Nat := [1, 1, 3, 6, 1, 1, 2, 1, 1, 5]
def baseStart_1595927 : Nat := 118140960795 + 1595927 * 2 ^ 59
def prefixEnd_1595927 : Nat := 4983230072969 + 3 ^ 40 * 1595927 * 2
def baseEnd_1595927 : Nat := 546318426992055107981981

theorem tailTrace_1595927 : CollatzResearch.WordTrace tailWord_1595927 prefixEnd_1595927 546318426992055107981981 := by
  unfold tailWord_1595927
  simp only [CollatzResearch.WordTrace]
  refine ⟨58208239689236516476890035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38805493126157677651260023 58208239689236516476890035)
  ·
    refine ⟨87312359533854774715335053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58208239689236516476890035 87312359533854774715335053)
    ·
      refine ⟨32742134825195540518250645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87312359533854774715335053 32742134825195540518250645)
      ·
        refine ⟨1534787569931040961792999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 32742134825195540518250645 1534787569931040961792999)
        ·
          refine ⟨2302181354896561442689499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1534787569931040961792999 2302181354896561442689499)
          ·
            refine ⟨3453272032344842164034249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2302181354896561442689499 3453272032344842164034249)
            ·
              refine ⟨2589954024258631623025687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3453272032344842164034249 2589954024258631623025687)
              ·
                refine ⟨3884931036387947434538531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2589954024258631623025687 3884931036387947434538531)
                ·
                  refine ⟨5827396554581921151807797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3884931036387947434538531 5827396554581921151807797)
                  ·
                    refine ⟨546318426992055107981981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5827396554581921151807797 546318426992055107981981)
                    ·
                      rfl

theorem cell22_1595927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 5].length) (baseStart_1595927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1595927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1595927 prefixEnd_1595927 := by exact prefixLift 1595927
  have htrace : WordTrace (prefixWord ++ tailWord_1595927) baseStart_1595927 baseEnd_1595927 := by
    simpa [prefixWord, tailWord_1595927, baseEnd_1595927] using wordTrace_append hprefix tailTrace_1595927
  have hstable : (prefixWord ++ tailWord_1595927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595927).length < 2 ^ (prefixWord ++ tailWord_1595927).sum := by decide
  have hdescent : baseEnd_1595927 < baseStart_1595927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595983 : List Nat := [1, 1, 2, 1, 1, 2, 6, 1, 2, 5]
def baseStart_1595983 : Nat := 118140960795 + 1595983 * 2 ^ 59
def prefixEnd_1595983 : Nat := 4983230072969 + 3 ^ 40 * 1595983 * 2
def baseEnd_1595983 : Nat := 546337596936489628581809

theorem tailTrace_1595983 : CollatzResearch.WordTrace tailWord_1595983 prefixEnd_1595983 546337596936489628581809 := by
  unfold tailWord_1595983
  simp only [CollatzResearch.WordTrace]
  refine ⟨58210282177033638040928603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38806854784689092027285735 58210282177033638040928603)
  ·
    refine ⟨87315423265550457061392905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58210282177033638040928603 87315423265550457061392905)
    ·
      refine ⟨65486567449162842796044679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87315423265550457061392905 65486567449162842796044679)
      ·
        refine ⟨98229851173744264194067019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65486567449162842796044679 98229851173744264194067019)
        ·
          refine ⟨147344776760616396291100529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98229851173744264194067019 147344776760616396291100529)
          ·
            refine ⟨110508582570462297218325397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147344776760616396291100529 110508582570462297218325397)
            ·
              refine ⟨5180089807990420182109003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 110508582570462297218325397 5180089807990420182109003)
              ·
                refine ⟨7770134711985630273163505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5180089807990420182109003 7770134711985630273163505)
                ·
                  refine ⟨5827601033989222704872629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7770134711985630273163505 5827601033989222704872629)
                  ·
                    refine ⟨546337596936489628581809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5827601033989222704872629 546337596936489628581809)
                    ·
                      rfl

theorem cell22_1595983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 5].length) (baseStart_1595983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1595983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1595983 prefixEnd_1595983 := by exact prefixLift 1595983
  have htrace : WordTrace (prefixWord ++ tailWord_1595983) baseStart_1595983 baseEnd_1595983 := by
    simpa [prefixWord, tailWord_1595983, baseEnd_1595983] using wordTrace_append hprefix tailTrace_1595983
  have hstable : (prefixWord ++ tailWord_1595983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595983).length < 2 ^ (prefixWord ++ tailWord_1595983).sum := by decide
  have hdescent : baseEnd_1595983 < baseStart_1595983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596015 : List Nat := [1, 1, 2, 1, 3, 2, 4, 3, 1, 4]
def baseStart_1596015 : Nat := 118140960795 + 1596015 * 2 ^ 59
def prefixEnd_1596015 : Nat := 4983230072969 + 3 ^ 40 * 1596015 * 2
def baseEnd_1596015 : Nat := 546348551190452211781711

theorem tailTrace_1596015 : CollatzResearch.WordTrace tailWord_1596015 prefixEnd_1596015 546348551190452211781711 := by
  unfold tailWord_1596015
  simp only [CollatzResearch.WordTrace]
  refine ⟨58211449312917707506093499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38807632875278471670728999 58211449312917707506093499)
  ·
    refine ⟨87317173969376561259140249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58211449312917707506093499 87317173969376561259140249)
    ·
      refine ⟨65487880477032420944355187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87317173969376561259140249 65487880477032420944355187)
      ·
        refine ⟨98231820715548631416532781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65487880477032420944355187 98231820715548631416532781)
        ·
          refine ⟨36836932768330736781199793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98231820715548631416532781 36836932768330736781199793)
          ·
            refine ⟨27627699576248052585899845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36836932768330736781199793 27627699576248052585899845)
            ·
              refine ⟨5180193670546509859856221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27627699576248052585899845 5180193670546509859856221)
              ·
                refine ⟨1942572626454941197446083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5180193670546509859856221 1942572626454941197446083)
                ·
                  refine ⟨2913858939682411796169125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1942572626454941197446083 2913858939682411796169125)
                  ·
                    refine ⟨546348551190452211781711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2913858939682411796169125 546348551190452211781711)
                    ·
                      rfl

theorem cell22_1596015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 3, 1, 4].length) (baseStart_1596015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1596015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1596015 prefixEnd_1596015 := by exact prefixLift 1596015
  have htrace : WordTrace (prefixWord ++ tailWord_1596015) baseStart_1596015 baseEnd_1596015 := by
    simpa [prefixWord, tailWord_1596015, baseEnd_1596015] using wordTrace_append hprefix tailTrace_1596015
  have hstable : (prefixWord ++ tailWord_1596015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596015).length < 2 ^ (prefixWord ++ tailWord_1596015).sum := by decide
  have hdescent : baseEnd_1596015 < baseStart_1596015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596043 : List Nat := [1, 1, 1, 1, 4, 1, 2, 4, 1, 6]
def baseStart_1596043 : Nat := 118140960795 + 1596043 * 2 ^ 59
def prefixEnd_1596043 : Nat := 4983230072969 + 3 ^ 40 * 1596043 * 2
def baseEnd_1596043 : Nat := 546358136162669472081625

theorem tailTrace_1596043 : CollatzResearch.WordTrace tailWord_1596043 prefixEnd_1596043 546358136162669472081625 := by
  unfold tailWord_1596043
  simp only [CollatzResearch.WordTrace]
  refine ⟨58212470556816268288112783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38808313704544178858741855 58212470556816268288112783)
  ·
    refine ⟨87318705835224402432169175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58212470556816268288112783 87318705835224402432169175)
    ·
      refine ⟨130978058752836603648253763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87318705835224402432169175 130978058752836603648253763)
      ·
        refine ⟨196467088129254905472380645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130978058752836603648253763 196467088129254905472380645)
        ·
          refine ⟨36837579024235294776071371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 196467088129254905472380645 36837579024235294776071371)
          ·
            refine ⟨55256368536352942164107057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36837579024235294776071371 55256368536352942164107057)
            ·
              refine ⟨41442276402264706623080293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55256368536352942164107057 41442276402264706623080293)
              ·
                refine ⟨7770426825424632491827555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41442276402264706623080293 7770426825424632491827555)
                ·
                  refine ⟨11655640238136948737741333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7770426825424632491827555 11655640238136948737741333)
                  ·
                    refine ⟨546358136162669472081625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11655640238136948737741333 546358136162669472081625)
                    ·
                      rfl

theorem cell22_1596043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 6].length) (baseStart_1596043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1596043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1596043 prefixEnd_1596043 := by exact prefixLift 1596043
  have htrace : WordTrace (prefixWord ++ tailWord_1596043) baseStart_1596043 baseEnd_1596043 := by
    simpa [prefixWord, tailWord_1596043, baseEnd_1596043] using wordTrace_append hprefix tailTrace_1596043
  have hstable : (prefixWord ++ tailWord_1596043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596043).length < 2 ^ (prefixWord ++ tailWord_1596043).sum := by decide
  have hdescent : baseEnd_1596043 < baseStart_1596043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596062 : List Nat := [4, 3, 1, 1, 1, 1, 3, 2, 1, 5]
def baseStart_1596062 : Nat := 118140960795 + 1596062 * 2 ^ 59
def prefixEnd_1596062 : Nat := 4983230072969 + 3 ^ 40 * 1596062 * 2
def baseEnd_1596062 : Nat := 546364640250959755856567

theorem tailTrace_1596062 : CollatzResearch.WordTrace tailWord_1596062 prefixEnd_1596062 546364640250959755856567 := by
  unfold tailWord_1596062
  simp only [CollatzResearch.WordTrace]
  refine ⟨7276645442968429316631805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38808775695831623022036293 7276645442968429316631805)
  ·
    refine ⟨2728742041113160993736927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7276645442968429316631805 2728742041113160993736927)
    ·
      refine ⟨4093113061669741490605391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2728742041113160993736927 4093113061669741490605391)
      ·
        refine ⟨6139669592504612235908087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4093113061669741490605391 6139669592504612235908087)
        ·
          refine ⟨9209504388756918353862131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6139669592504612235908087 9209504388756918353862131)
          ·
            refine ⟨13814256583135377530793197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9209504388756918353862131 13814256583135377530793197)
            ·
              refine ⟨5180346218675766574047449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13814256583135377530793197 5180346218675766574047449)
              ·
                refine ⟨3885259664006824930535587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5180346218675766574047449 3885259664006824930535587)
                ·
                  refine ⟨5827889496010237395803381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3885259664006824930535587 5827889496010237395803381)
                  ·
                    refine ⟨546364640250959755856567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5827889496010237395803381 546364640250959755856567)
                    ·
                      rfl

theorem cell22_1596062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_1596062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1596062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1596062 prefixEnd_1596062 := by exact prefixLift 1596062
  have htrace : WordTrace (prefixWord ++ tailWord_1596062) baseStart_1596062 baseEnd_1596062 := by
    simpa [prefixWord, tailWord_1596062, baseEnd_1596062] using wordTrace_append hprefix tailTrace_1596062
  have hstable : (prefixWord ++ tailWord_1596062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596062).length < 2 ^ (prefixWord ++ tailWord_1596062).sum := by decide
  have hdescent : baseEnd_1596062 < baseStart_1596062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596077 : List Nat := [1, 5, 2, 1, 1, 2, 2, 2, 2, 4]
def baseStart_1596077 : Nat := 118140960795 + 1596077 * 2 ^ 59
def prefixEnd_1596077 : Nat := 4983230072969 + 3 ^ 40 * 1596077 * 2
def baseEnd_1596077 : Nat := 546369775057504716731521

theorem tailTrace_1596077 : CollatzResearch.WordTrace tailWord_1596077 prefixEnd_1596077 546369775057504716731521 := by
  unfold tailWord_1596077
  simp only [CollatzResearch.WordTrace]
  refine ⟨58213710638693092094850485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38809140425795394729900323 58213710638693092094850485)
  ·
    refine ⟨5457535372377477383892233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58213710638693092094850485 5457535372377477383892233)
    ·
      refine ⟨4093151529283108037919175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5457535372377477383892233 4093151529283108037919175)
      ·
        refine ⟨6139727293924662056878763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4093151529283108037919175 6139727293924662056878763)
        ·
          refine ⟨9209590940886993085318145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6139727293924662056878763 9209590940886993085318145)
          ·
            refine ⟨6907193205665244813988609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9209590940886993085318145 6907193205665244813988609)
            ·
              refine ⟨5180394904248933610491457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6907193205665244813988609 5180394904248933610491457)
              ·
                refine ⟨3885296178186700207868593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5180394904248933610491457 3885296178186700207868593)
                ·
                  refine ⟨2913972133640025155901445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3885296178186700207868593 2913972133640025155901445)
                  ·
                    refine ⟨546369775057504716731521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2913972133640025155901445 546369775057504716731521)
                    ·
                      rfl

theorem cell22_1596077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_1596077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1596077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1596077 prefixEnd_1596077 := by exact prefixLift 1596077
  have htrace : WordTrace (prefixWord ++ tailWord_1596077) baseStart_1596077 baseEnd_1596077 := by
    simpa [prefixWord, tailWord_1596077, baseEnd_1596077] using wordTrace_append hprefix tailTrace_1596077
  have hstable : (prefixWord ++ tailWord_1596077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596077).length < 2 ^ (prefixWord ++ tailWord_1596077).sum := by decide
  have hdescent : baseEnd_1596077 < baseStart_1596077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596197 : List Nat := [1, 3, 1, 2, 3, 1, 1, 3, 4, 3]
def baseStart_1596197 : Nat := 118140960795 + 1596197 * 2 ^ 59
def prefixEnd_1596197 : Nat := 4983230072969 + 3 ^ 40 * 1596197 * 2
def baseEnd_1596197 : Nat := 546410853509864403731153

theorem tailTrace_1596197 : CollatzResearch.WordTrace tailWord_1596197 prefixEnd_1596197 546410853509864403731153 := by
  unfold tailWord_1596197
  simp only [CollatzResearch.WordTrace]
  refine ⟨58218087398258352589218845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38812058265505568392812563 58218087398258352589218845)
  ·
    refine ⟨21831782774346882220957067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58218087398258352589218845 21831782774346882220957067)
    ·
      refine ⟨32747674161520323331435601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21831782774346882220957067 32747674161520323331435601)
      ·
        refine ⟨24560755621140242498576701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32747674161520323331435601 24560755621140242498576701)
        ·
          refine ⟨9210283357927590936966263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24560755621140242498576701 9210283357927590936966263)
          ·
            refine ⟨13815425036891386405449395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9210283357927590936966263 13815425036891386405449395)
            ·
              refine ⟨20723137555337079608174093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13815425036891386405449395 20723137555337079608174093)
              ·
                refine ⟨7771176583251404853065285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20723137555337079608174093 7771176583251404853065285)
                ·
                  refine ⟨1457095609359638409949741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7771176583251404853065285 1457095609359638409949741)
                  ·
                    refine ⟨546410853509864403731153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1457095609359638409949741 546410853509864403731153)
                    ·
                      rfl

theorem cell22_1596197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 4, 3].length) (baseStart_1596197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1596197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1596197 prefixEnd_1596197 := by exact prefixLift 1596197
  have htrace : WordTrace (prefixWord ++ tailWord_1596197) baseStart_1596197 baseEnd_1596197 := by
    simpa [prefixWord, tailWord_1596197, baseEnd_1596197] using wordTrace_append hprefix tailTrace_1596197
  have hstable : (prefixWord ++ tailWord_1596197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596197).length < 2 ^ (prefixWord ++ tailWord_1596197).sum := by decide
  have hdescent : baseEnd_1596197 < baseStart_1596197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596205 : List Nat := [1, 5, 3, 2, 2, 1, 2, 1, 5]
def baseStart_1596205 : Nat := 118140960795 + 1596205 * 2 ^ 59
def prefixEnd_1596205 : Nat := 4983230072969 + 3 ^ 40 * 1596205 * 2
def baseEnd_1596205 : Nat := 182137864024451683177043

theorem tailTrace_1596205 : CollatzResearch.WordTrace tailWord_1596205 prefixEnd_1596205 182137864024451683177043 := by
  unfold tailWord_1596205
  simp only [CollatzResearch.WordTrace]
  refine ⟨58218379182229369955510069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38812252788152913303673379 58218379182229369955510069)
  ·
    refine ⟨5457973048334003433329069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58218379182229369955510069 5457973048334003433329069)
    ·
      refine ⟨2046739893125251287498401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5457973048334003433329069 2046739893125251287498401)
      ·
        refine ⟨1535054919843938465623801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2046739893125251287498401 1535054919843938465623801)
        ·
          refine ⟨1151291189882953849217851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1535054919843938465623801 1151291189882953849217851)
          ·
            refine ⟨1726936784824430773826777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1151291189882953849217851 1726936784824430773826777)
            ·
              refine ⟨1295202588618323080370083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1726936784824430773826777 1295202588618323080370083)
              ·
                refine ⟨1942803882927484620555125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1295202588618323080370083 1942803882927484620555125)
                ·
                  refine ⟨182137864024451683177043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1942803882927484620555125 182137864024451683177043)
                  ·
                    rfl

theorem cell22_1596205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_1596205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1596205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1596205 prefixEnd_1596205 := by exact prefixLift 1596205
  have htrace : WordTrace (prefixWord ++ tailWord_1596205) baseStart_1596205 baseEnd_1596205 := by
    simpa [prefixWord, tailWord_1596205, baseEnd_1596205] using wordTrace_append hprefix tailTrace_1596205
  have hstable : (prefixWord ++ tailWord_1596205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596205).length < 2 ^ (prefixWord ++ tailWord_1596205).sum := by decide
  have hdescent : baseEnd_1596205 < baseStart_1596205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596272 : List Nat := [2, 1, 1, 1, 4, 1, 4, 3, 5]
def baseStart_1596272 : Nat := 118140960795 + 1596272 * 2 ^ 59
def prefixEnd_1596272 : Nat := 4983230072969 + 3 ^ 40 * 1596272 * 2
def baseEnd_1596272 : Nat := 182145509180863069368641

theorem tailTrace_1596272 : CollatzResearch.WordTrace tailWord_1596272 prefixEnd_1596272 182145509180863069368641 := by
  unfold tailWord_1596272
  simp only [CollatzResearch.WordTrace]
  refine ⟨29110411436493320199099535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38813881915324426932132713 29110411436493320199099535)
  ·
    refine ⟨43665617154739980298649303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29110411436493320199099535 43665617154739980298649303)
    ·
      refine ⟨65498425732109970447973955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43665617154739980298649303 65498425732109970447973955)
      ·
        refine ⟨98247638598164955671960933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65498425732109970447973955 98247638598164955671960933)
        ·
          refine ⟨18421432237155929188492675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98247638598164955671960933 18421432237155929188492675)
          ·
            refine ⟨27632148355733893782739013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18421432237155929188492675 27632148355733893782739013)
            ·
              refine ⟨5181027816700105084263565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27632148355733893782739013 5181027816700105084263565)
              ·
                refine ⟨1942885431262539406598837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5181027816700105084263565 1942885431262539406598837)
                ·
                  refine ⟨182145509180863069368641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1942885431262539406598837 182145509180863069368641)
                  ·
                    rfl

theorem cell22_1596272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 3, 5].length) (baseStart_1596272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1596272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1596272 prefixEnd_1596272 := by exact prefixLift 1596272
  have htrace : WordTrace (prefixWord ++ tailWord_1596272) baseStart_1596272 baseEnd_1596272 := by
    simpa [prefixWord, tailWord_1596272, baseEnd_1596272] using wordTrace_append hprefix tailTrace_1596272
  have hstable : (prefixWord ++ tailWord_1596272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596272).length < 2 ^ (prefixWord ++ tailWord_1596272).sum := by decide
  have hdescent : baseEnd_1596272 < baseStart_1596272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596310 : List Nat := [5, 3, 1, 1, 1, 2, 2, 1, 3, 3]
def baseStart_1596310 : Nat := 118140960795 + 1596310 * 2 ^ 59
def prefixEnd_1596310 : Nat := 4983230072969 + 3 ^ 40 * 1596310 * 2
def baseEnd_1596310 : Nat := 546449535719169775655807

theorem tailTrace_1596310 : CollatzResearch.WordTrace tailWord_1596310 prefixEnd_1596310 546449535719169775655807 := by
  unfold tailWord_1596310
  simp only [CollatzResearch.WordTrace]
  refine ⟨3638888052928060805505149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38814805897899315258721589 3638888052928060805505149)
  ·
    refine ⟨1364583019848022802064431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3638888052928060805505149 1364583019848022802064431)
    ·
      refine ⟨2046874529772034203096647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1364583019848022802064431 2046874529772034203096647)
      ·
        refine ⟨3070311794658051304644971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2046874529772034203096647 3070311794658051304644971)
        ·
          refine ⟨4605467691987076956967457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3070311794658051304644971 4605467691987076956967457)
          ·
            refine ⟨3454100768990307717725593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4605467691987076956967457 3454100768990307717725593)
            ·
              refine ⟨2590575576742730788294195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3454100768990307717725593 2590575576742730788294195)
              ·
                refine ⟨3885863365114096182441293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2590575576742730788294195 3885863365114096182441293)
                ·
                  refine ⟨1457198761917786068415485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3885863365114096182441293 1457198761917786068415485)
                  ·
                    refine ⟨546449535719169775655807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1457198761917786068415485 546449535719169775655807)
                    ·
                      rfl

theorem cell22_1596310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_1596310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1596310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1596310 prefixEnd_1596310 := by exact prefixLift 1596310
  have htrace : WordTrace (prefixWord ++ tailWord_1596310) baseStart_1596310 baseEnd_1596310 := by
    simpa [prefixWord, tailWord_1596310, baseEnd_1596310] using wordTrace_append hprefix tailTrace_1596310
  have hstable : (prefixWord ++ tailWord_1596310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596310).length < 2 ^ (prefixWord ++ tailWord_1596310).sum := by decide
  have hdescent : baseEnd_1596310 < baseStart_1596310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596364 : List Nat := [2, 2, 1, 4, 1, 1, 3, 2, 2, 4]
def baseStart_1596364 : Nat := 118140960795 + 1596364 * 2 ^ 59
def prefixEnd_1596364 : Nat := 4983230072969 + 3 ^ 40 * 1596364 * 2
def baseEnd_1596364 : Nat := 546468021022731634805641

theorem tailTrace_1596364 : CollatzResearch.WordTrace tailWord_1596364 prefixEnd_1596364 546468021022731634805641 := by
  unfold tailWord_1596364
  simp only [CollatzResearch.WordTrace]
  refine ⟨29112089194326670055274073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38816118925768893407032097 29112089194326670055274073)
  ·
    refine ⟨21834066895745002541455555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29112089194326670055274073 21834066895745002541455555)
    ·
      refine ⟨32751100343617503812183333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21834066895745002541455555 32751100343617503812183333)
      ·
        refine ⟨6140831314428281964784375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32751100343617503812183333 6140831314428281964784375)
        ·
          refine ⟨9211246971642422947176563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6140831314428281964784375 9211246971642422947176563)
          ·
            refine ⟨13816870457463634420764845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9211246971642422947176563 13816870457463634420764845)
            ·
              refine ⟨5181326421548862907786817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13816870457463634420764845 5181326421548862907786817)
              ·
                refine ⟨3885994816161647180840113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5181326421548862907786817 3885994816161647180840113)
                ·
                  refine ⟨2914496112121235385630085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3885994816161647180840113 2914496112121235385630085)
                  ·
                    refine ⟨546468021022731634805641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2914496112121235385630085 546468021022731634805641)
                    ·
                      rfl

theorem cell22_1596364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 2, 4].length) (baseStart_1596364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1596364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1596364 prefixEnd_1596364 := by exact prefixLift 1596364
  have htrace : WordTrace (prefixWord ++ tailWord_1596364) baseStart_1596364 baseEnd_1596364 := by
    simpa [prefixWord, tailWord_1596364, baseEnd_1596364] using wordTrace_append hprefix tailTrace_1596364
  have hstable : (prefixWord ++ tailWord_1596364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596364).length < 2 ^ (prefixWord ++ tailWord_1596364).sum := by decide
  have hdescent : baseEnd_1596364 < baseStart_1596364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596404 : List Nat := [2, 6, 2, 1, 1, 1, 3, 1, 1, 4]
def baseStart_1596404 : Nat := 118140960795 + 1596404 * 2 ^ 59
def prefixEnd_1596404 : Nat := 4983230072969 + 3 ^ 40 * 1596404 * 2
def baseEnd_1596404 : Nat := 546481713840184863805519

theorem tailTrace_1596404 : CollatzResearch.WordTrace tailWord_1596404 prefixEnd_1596404 546481713840184863805519 := by
  unfold tailWord_1596404
  simp only [CollatzResearch.WordTrace]
  refine ⟨29112818654254213471002133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38817091539005617961336177 29112818654254213471002133)
  ·
    refine ⟨1364663374418166256453225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 29112818654254213471002133 1364663374418166256453225)
    ·
      refine ⟨1023497530813624692339919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1364663374418166256453225 1023497530813624692339919)
      ·
        refine ⟨1535246296220437038509879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1023497530813624692339919 1535246296220437038509879)
        ·
          refine ⟨2302869444330655557764819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1535246296220437038509879 2302869444330655557764819)
          ·
            refine ⟨3454304166495983336647229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2302869444330655557764819 3454304166495983336647229)
            ·
              refine ⟨1295364062435993751242711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3454304166495983336647229 1295364062435993751242711)
              ·
                refine ⟨1943046093653990626864067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1295364062435993751242711 1943046093653990626864067)
                ·
                  refine ⟨2914569140480985940296101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1943046093653990626864067 2914569140480985940296101)
                  ·
                    refine ⟨546481713840184863805519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2914569140480985940296101 546481713840184863805519)
                    ·
                      rfl

theorem cell22_1596404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_1596404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1596404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1596404 prefixEnd_1596404 := by exact prefixLift 1596404
  have htrace : WordTrace (prefixWord ++ tailWord_1596404) baseStart_1596404 baseEnd_1596404 := by
    simpa [prefixWord, tailWord_1596404, baseEnd_1596404] using wordTrace_append hprefix tailTrace_1596404
  have hstable : (prefixWord ++ tailWord_1596404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596404).length < 2 ^ (prefixWord ++ tailWord_1596404).sum := by decide
  have hdescent : baseEnd_1596404 < baseStart_1596404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596411 : List Nat := [1, 1, 1, 1, 1, 3, 3, 7, 1, 3]
def baseStart_1596411 : Nat := 118140960795 + 1596411 * 2 ^ 59
def prefixEnd_1596411 : Nat := 4983230072969 + 3 ^ 40 * 1596411 * 2
def baseEnd_1596411 : Nat := 546484110083239178880497

theorem tailTrace_1596411 : CollatzResearch.WordTrace tailWord_1596411 prefixEnd_1596411 546484110083239178880497 := by
  unfold tailWord_1596411
  simp only [CollatzResearch.WordTrace]
  refine ⟨58225892619483067137509087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38817261746322044758339391 58225892619483067137509087)
  ·
    refine ⟨87338838929224600706263631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58225892619483067137509087 87338838929224600706263631)
    ·
      refine ⟨131008258393836901059395447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87338838929224600706263631 131008258393836901059395447)
      ·
        refine ⟨196512387590755351589093171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131008258393836901059395447 196512387590755351589093171)
        ·
          refine ⟨294768581386133027383639757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196512387590755351589093171 294768581386133027383639757)
          ·
            refine ⟨110538218019799885268864909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 294768581386133027383639757 110538218019799885268864909)
            ·
              refine ⟨41451831757424956975824341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110538218019799885268864909 41451831757424956975824341)
              ·
                refine ⟨971527306814647429120883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 41451831757424956975824341 971527306814647429120883)
                ·
                  refine ⟨1457290960221971143681325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 971527306814647429120883 1457290960221971143681325)
                  ·
                    refine ⟨546484110083239178880497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1457290960221971143681325 546484110083239178880497)
                    ·
                      rfl

theorem cell22_1596411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7, 1, 3].length) (baseStart_1596411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1596411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1596411 prefixEnd_1596411 := by exact prefixLift 1596411
  have htrace : WordTrace (prefixWord ++ tailWord_1596411) baseStart_1596411 baseEnd_1596411 := by
    simpa [prefixWord, tailWord_1596411, baseEnd_1596411] using wordTrace_append hprefix tailTrace_1596411
  have hstable : (prefixWord ++ tailWord_1596411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596411).length < 2 ^ (prefixWord ++ tailWord_1596411).sum := by decide
  have hdescent : baseEnd_1596411 < baseStart_1596411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596424 : List Nat := [2, 1, 3, 2, 1, 3, 1, 4, 5]
def baseStart_1596424 : Nat := 118140960795 + 1596424 * 2 ^ 59
def prefixEnd_1596424 : Nat := 4983230072969 + 3 ^ 40 * 1596424 * 2
def baseEnd_1596424 : Nat := 182162853416303826101819

theorem tailTrace_1596424 : CollatzResearch.WordTrace tailWord_1596424 prefixEnd_1596424 182162853416303826101819 := by
  unfold tailWord_1596424
  simp only [CollatzResearch.WordTrace]
  refine ⟨29113183384217985178866163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38817577845623980238488217 29113183384217985178866163)
  ·
    refine ⟨43669775076326977768299245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29113183384217985178866163 43669775076326977768299245)
    ·
      refine ⟨16376165653622616663112217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43669775076326977768299245 16376165653622616663112217)
      ·
        refine ⟨12282124240216962497334163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16376165653622616663112217 12282124240216962497334163)
        ·
          refine ⟨18423186360325443746001245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12282124240216962497334163 18423186360325443746001245)
          ·
            refine ⟨6908694885122041404750467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18423186360325443746001245 6908694885122041404750467)
            ·
              refine ⟨10363042327683062107125701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6908694885122041404750467 10363042327683062107125701)
              ·
                refine ⟨1943070436440574145086069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10363042327683062107125701 1943070436440574145086069)
                ·
                  refine ⟨182162853416303826101819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1943070436440574145086069 182162853416303826101819)
                  ·
                    rfl

theorem cell22_1596424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 4, 5].length) (baseStart_1596424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1596424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1596424 prefixEnd_1596424 := by exact prefixLift 1596424
  have htrace : WordTrace (prefixWord ++ tailWord_1596424) baseStart_1596424 baseEnd_1596424 := by
    simpa [prefixWord, tailWord_1596424, baseEnd_1596424] using wordTrace_append hprefix tailTrace_1596424
  have hstable : (prefixWord ++ tailWord_1596424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596424).length < 2 ^ (prefixWord ++ tailWord_1596424).sum := by decide
  have hdescent : baseEnd_1596424 < baseStart_1596424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596428 : List Nat := [2, 2, 1, 2, 3, 3, 1, 4, 1, 3]
def baseStart_1596428 : Nat := 118140960795 + 1596428 * 2 ^ 59
def prefixEnd_1596428 : Nat := 4983230072969 + 3 ^ 40 * 1596428 * 2
def baseEnd_1596428 : Nat := 546489929530656801205445

theorem tailTrace_1596428 : CollatzResearch.WordTrace tailWord_1596428 prefixEnd_1596428 546489929530656801205445 := by
  unfold tailWord_1596428
  simp only [CollatzResearch.WordTrace]
  refine ⟨29113256330210739520438969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38817675106947652693918625 29113256330210739520438969)
  ·
    refine ⟨21834942247658054640329227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29113256330210739520438969 21834942247658054640329227)
    ·
      refine ⟨32752413371487081960493841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21834942247658054640329227 32752413371487081960493841)
      ·
        refine ⟨24564310028615311470370381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32752413371487081960493841 24564310028615311470370381)
        ·
          refine ⟨9211616260730741801388893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24564310028615311470370381 9211616260730741801388893)
          ·
            refine ⟨3454356097774028175520835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9211616260730741801388893 3454356097774028175520835)
            ·
              refine ⟨5181534146661042263281253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3454356097774028175520835 5181534146661042263281253)
              ·
                refine ⟨971537652498945424365235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5181534146661042263281253 971537652498945424365235)
                ·
                  refine ⟨1457306478748418136547853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 971537652498945424365235 1457306478748418136547853)
                  ·
                    refine ⟨546489929530656801205445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1457306478748418136547853 546489929530656801205445)
                    ·
                      rfl

theorem cell22_1596428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 4, 1, 3].length) (baseStart_1596428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1596428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1596428 prefixEnd_1596428 := by exact prefixLift 1596428
  have htrace : WordTrace (prefixWord ++ tailWord_1596428) baseStart_1596428 baseEnd_1596428 := by
    simpa [prefixWord, tailWord_1596428, baseEnd_1596428] using wordTrace_append hprefix tailTrace_1596428
  have hstable : (prefixWord ++ tailWord_1596428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596428).length < 2 ^ (prefixWord ++ tailWord_1596428).sum := by decide
  have hdescent : baseEnd_1596428 < baseStart_1596428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596439 : List Nat := [1, 1, 3, 5, 1, 1, 1, 1, 1, 7]
def baseStart_1596439 : Nat := 118140960795 + 1596439 * 2 ^ 59
def prefixEnd_1596439 : Nat := 4983230072969 + 3 ^ 40 * 1596439 * 2
def baseEnd_1596439 : Nat := 546493695055456439180411

theorem tailTrace_1596439 : CollatzResearch.WordTrace tailWord_1596439 prefixEnd_1596439 546493695055456439180411 := by
  unfold tailWord_1596439
  simp only [CollatzResearch.WordTrace]
  refine ⟨58226913863381627919528371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38817942575587751946352247 58226913863381627919528371)
  ·
    refine ⟨87340370795072441879292557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58226913863381627919528371 87340370795072441879292557)
    ·
      refine ⟨32752639048152165704734709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87340370795072441879292557 32752639048152165704734709)
      ·
        refine ⟨3070559910764265534818879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32752639048152165704734709 3070559910764265534818879)
        ·
          refine ⟨4605839866146398302228319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3070559910764265534818879 4605839866146398302228319)
          ·
            refine ⟨6908759799219597453342479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4605839866146398302228319 6908759799219597453342479)
            ·
              refine ⟨10363139698829396180013719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6908759799219597453342479 10363139698829396180013719)
              ·
                refine ⟨15544709548244094270020579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10363139698829396180013719 15544709548244094270020579)
                ·
                  refine ⟨23317064322366141405030869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15544709548244094270020579 23317064322366141405030869)
                  ·
                    refine ⟨546493695055456439180411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23317064322366141405030869 546493695055456439180411)
                    ·
                      rfl

theorem cell22_1596439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 7].length) (baseStart_1596439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1596439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1596439 prefixEnd_1596439 := by exact prefixLift 1596439
  have htrace : WordTrace (prefixWord ++ tailWord_1596439) baseStart_1596439 baseEnd_1596439 := by
    simpa [prefixWord, tailWord_1596439, baseEnd_1596439] using wordTrace_append hprefix tailTrace_1596439
  have hstable : (prefixWord ++ tailWord_1596439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596439).length < 2 ^ (prefixWord ++ tailWord_1596439).sum := by decide
  have hdescent : baseEnd_1596439 < baseStart_1596439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596552 : List Nat := [2, 1, 3, 4, 2, 2, 2, 1, 2, 3]
def baseStart_1596552 : Nat := 118140960795 + 1596552 * 2 ^ 59
def prefixEnd_1596552 : Nat := 4983230072969 + 3 ^ 40 * 1596552 * 2
def baseEnd_1596552 : Nat := 546532377264761811105065

theorem tailTrace_1596552 : CollatzResearch.WordTrace tailWord_1596552 prefixEnd_1596552 546532377264761811105065 := by
  unfold tailWord_1596552
  simp only [CollatzResearch.WordTrace]
  refine ⟨29115517655986124109195955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38820690207981498812261273 29115517655986124109195955)
  ·
    refine ⟨43673276483979186163793933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29115517655986124109195955 43673276483979186163793933)
    ·
      refine ⟨16377478681492194811422725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43673276483979186163793933 16377478681492194811422725)
      ·
        refine ⟨3070777252779786527141761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16377478681492194811422725 3070777252779786527141761)
        ·
          refine ⟨2303082939584839895356321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3070777252779786527141761 2303082939584839895356321)
          ·
            refine ⟨1727312204688629921517241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2303082939584839895356321 1727312204688629921517241)
            ·
              refine ⟨1295484153516472441137931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1727312204688629921517241 1295484153516472441137931)
              ·
                refine ⟨1943226230274708661706897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1295484153516472441137931 1943226230274708661706897)
                ·
                  refine ⟨1457419672706031496280173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1943226230274708661706897 1457419672706031496280173)
                  ·
                    refine ⟨546532377264761811105065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1457419672706031496280173 546532377264761811105065)
                    ·
                      rfl

theorem cell22_1596552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 1, 2, 3].length) (baseStart_1596552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1596552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1596552 prefixEnd_1596552 := by exact prefixLift 1596552
  have htrace : WordTrace (prefixWord ++ tailWord_1596552) baseStart_1596552 baseEnd_1596552 := by
    simpa [prefixWord, tailWord_1596552, baseEnd_1596552] using wordTrace_append hprefix tailTrace_1596552
  have hstable : (prefixWord ++ tailWord_1596552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596552).length < 2 ^ (prefixWord ++ tailWord_1596552).sum := by decide
  have hdescent : baseEnd_1596552 < baseStart_1596552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596593 : List Nat := [1, 2, 2, 5, 1, 2, 2, 2, 5]
def baseStart_1596593 : Nat := 118140960795 + 1596593 * 2 ^ 59
def prefixEnd_1596593 : Nat := 4983230072969 + 3 ^ 40 * 1596593 * 2
def baseEnd_1596593 : Nat := 182182137467550456943313

theorem tailTrace_1596593 : CollatzResearch.WordTrace tailWord_1596593 prefixEnd_1596593 182182137467550456943313 := by
  unfold tailWord_1596593
  simp only [CollatzResearch.WordTrace]
  refine ⟨58232530704823712220634433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38821687136549141480422955 58232530704823712220634433)
  ·
    refine ⟨43674398028617784165475825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58232530704823712220634433 43674398028617784165475825)
    ·
      refine ⟨32755798521463338124106869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43674398028617784165475825 32755798521463338124106869)
      ·
        refine ⟨3070856111387187949135019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32755798521463338124106869 3070856111387187949135019)
        ·
          refine ⟨4606284167080781923702529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3070856111387187949135019 4606284167080781923702529)
          ·
            refine ⟨3454713125310586442776897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4606284167080781923702529 3454713125310586442776897)
            ·
              refine ⟨2591034843982939832082673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3454713125310586442776897 2591034843982939832082673)
              ·
                refine ⟨1943276132987204874062005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2591034843982939832082673 1943276132987204874062005)
                ·
                  refine ⟨182182137467550456943313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1943276132987204874062005 182182137467550456943313)
                  ·
                    rfl

theorem cell22_1596593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 2, 5].length) (baseStart_1596593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1596593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1596593 prefixEnd_1596593 := by exact prefixLift 1596593
  have htrace : WordTrace (prefixWord ++ tailWord_1596593) baseStart_1596593 baseEnd_1596593 := by
    simpa [prefixWord, tailWord_1596593, baseEnd_1596593] using wordTrace_append hprefix tailTrace_1596593
  have hstable : (prefixWord ++ tailWord_1596593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596593).length < 2 ^ (prefixWord ++ tailWord_1596593).sum := by decide
  have hdescent : baseEnd_1596593 < baseStart_1596593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596614 : List Nat := [6, 1, 2, 2, 1, 1, 1, 2, 3, 3]
def baseStart_1596614 : Nat := 118140960795 + 1596614 * 2 ^ 59
def prefixEnd_1596614 : Nat := 4983230072969 + 3 ^ 40 * 1596614 * 2
def baseEnd_1596614 : Nat := 546553601131814316054875

theorem tailTrace_1596614 : CollatzResearch.WordTrace tailWord_1596614 prefixEnd_1596614 546553601131814316054875 := by
  unfold tailWord_1596614
  simp only [CollatzResearch.WordTrace]
  refine ⟨1819790519929613525223403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 38822197758498421871432597 1819790519929613525223403)
  ·
    refine ⟨2729685779894420287835105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1819790519929613525223403 2729685779894420287835105)
    ·
      refine ⟨2047264334920815215876329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2729685779894420287835105 2047264334920815215876329)
      ·
        refine ⟨1535448251190611411907247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2047264334920815215876329 1535448251190611411907247)
        ·
          refine ⟨2303172376785917117860871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1535448251190611411907247 2303172376785917117860871)
          ·
            refine ⟨3454758565178875676791307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2303172376785917117860871 3454758565178875676791307)
            ·
              refine ⟨5182137847768313515186961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3454758565178875676791307 5182137847768313515186961)
              ·
                refine ⟨3886603385826235136390221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5182137847768313515186961 3886603385826235136390221)
                ·
                  refine ⟨1457476269684838176146333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3886603385826235136390221 1457476269684838176146333)
                  ·
                    refine ⟨546553601131814316054875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1457476269684838176146333 546553601131814316054875)
                    ·
                      rfl

theorem cell22_1596614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_1596614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1596614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1596614 prefixEnd_1596614 := by exact prefixLift 1596614
  have htrace : WordTrace (prefixWord ++ tailWord_1596614) baseStart_1596614 baseEnd_1596614 := by
    simpa [prefixWord, tailWord_1596614, baseEnd_1596614] using wordTrace_append hprefix tailTrace_1596614
  have hstable : (prefixWord ++ tailWord_1596614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596614).length < 2 ^ (prefixWord ++ tailWord_1596614).sum := by decide
  have hdescent : baseEnd_1596614 < baseStart_1596614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596640 : List Nat := [2, 1, 1, 3, 1, 6, 2, 1, 1, 4]
def baseStart_1596640 : Nat := 118140960795 + 1596640 * 2 ^ 59
def prefixEnd_1596640 : Nat := 4983230072969 + 3 ^ 40 * 1596640 * 2
def baseEnd_1596640 : Nat := 546562501463158914904795

theorem tailTrace_1596640 : CollatzResearch.WordTrace tailWord_1596640 prefixEnd_1596640 546562501463158914904795 := by
  unfold tailWord_1596640
  simp only [CollatzResearch.WordTrace]
  refine ⟨29117122467826719623797687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38822829957102292831730249 29117122467826719623797687)
  ·
    refine ⟨43675683701740079435696531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29117122467826719623797687 43675683701740079435696531)
    ·
      refine ⟨65513525552610119153544797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43675683701740079435696531 65513525552610119153544797)
      ·
        refine ⟨24567572082228794682579299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65513525552610119153544797 24567572082228794682579299)
        ·
          refine ⟨36851358123343192023868949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24567572082228794682579299 36851358123343192023868949)
          ·
            refine ⟨1727407412031712126118857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 36851358123343192023868949 1727407412031712126118857)
            ·
              refine ⟨1295555559023784094589143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1727407412031712126118857 1295555559023784094589143)
              ·
                refine ⟨1943333338535676141883715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1295555559023784094589143 1943333338535676141883715)
                ·
                  refine ⟨2915000007803514212825573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1943333338535676141883715 2915000007803514212825573)
                  ·
                    refine ⟨546562501463158914904795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2915000007803514212825573 546562501463158914904795)
                    ·
                      rfl

theorem cell22_1596640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 1, 1, 4].length) (baseStart_1596640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1596640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1596640 prefixEnd_1596640 := by exact prefixLift 1596640
  have htrace : WordTrace (prefixWord ++ tailWord_1596640) baseStart_1596640 baseEnd_1596640 := by
    simpa [prefixWord, tailWord_1596640, baseEnd_1596640] using wordTrace_append hprefix tailTrace_1596640
  have hstable : (prefixWord ++ tailWord_1596640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596640).length < 2 ^ (prefixWord ++ tailWord_1596640).sum := by decide
  have hdescent : baseEnd_1596640 < baseStart_1596640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596670 : List Nat := [4, 2, 2, 1, 1, 4, 1, 1, 1, 5]
def baseStart_1596670 : Nat := 118140960795 + 1596670 * 2 ^ 59
def prefixEnd_1596670 : Nat := 4983230072969 + 3 ^ 40 * 1596670 * 2
def baseEnd_1596670 : Nat := 546572771076248836654703

theorem tailTrace_1596670 : CollatzResearch.WordTrace tailWord_1596670 prefixEnd_1596670 546572771076248836654703 := by
  unfold tailWord_1596670
  simp only [CollatzResearch.WordTrace]
  refine ⟨7279417390693094296398433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38823559417029836247458309 7279417390693094296398433)
  ·
    refine ⟨5459563043019820722298825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7279417390693094296398433 5459563043019820722298825)
    ·
      refine ⟨4094672282264865541724119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5459563043019820722298825 4094672282264865541724119)
      ·
        refine ⟨6142008423397298312586179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4094672282264865541724119 6142008423397298312586179)
        ·
          refine ⟨9213012635095947468879269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6142008423397298312586179 9213012635095947468879269)
          ·
            refine ⟨1727439869080490150414863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9213012635095947468879269 1727439869080490150414863)
            ·
              refine ⟨2591159803620735225622295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1727439869080490150414863 2591159803620735225622295)
              ·
                refine ⟨3886739705431102838433443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2591159803620735225622295 3886739705431102838433443)
                ·
                  refine ⟨5830109558146654257650165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3886739705431102838433443 5830109558146654257650165)
                  ·
                    refine ⟨546572771076248836654703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5830109558146654257650165 546572771076248836654703)
                    ·
                      rfl

theorem cell22_1596670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_1596670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1596670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1596670 prefixEnd_1596670 := by exact prefixLift 1596670
  have htrace : WordTrace (prefixWord ++ tailWord_1596670) baseStart_1596670 baseEnd_1596670 := by
    simpa [prefixWord, tailWord_1596670, baseEnd_1596670] using wordTrace_append hprefix tailTrace_1596670
  have hstable : (prefixWord ++ tailWord_1596670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596670).length < 2 ^ (prefixWord ++ tailWord_1596670).sum := by decide
  have hdescent : baseEnd_1596670 < baseStart_1596670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596683 : List Nat := [1, 1, 1, 1, 5, 5, 2, 6]
def baseStart_1596683 : Nat := 118140960795 + 1596683 * 2 ^ 59
def prefixEnd_1596683 : Nat := 4983230072969 + 3 ^ 40 * 1596683 * 2
def baseEnd_1596683 : Nat := 60730802360213459564407

theorem tailTrace_1596683 : CollatzResearch.WordTrace tailWord_1596683 prefixEnd_1596683 60730802360213459564407 := by
  unfold tailWord_1596683
  simp only [CollatzResearch.WordTrace]
  refine ⟨58235813274497657591410703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38823875516331771727607135 58235813274497657591410703)
  ·
    refine ⟨87353719911746486387116055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58235813274497657591410703 87353719911746486387116055)
    ·
      refine ⟨131030579867619729580674083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87353719911746486387116055 131030579867619729580674083)
      ·
        refine ⟨196545869801429594371011125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131030579867619729580674083 196545869801429594371011125)
        ·
          refine ⟨18426175293884024472282293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 196545869801429594371011125 18426175293884024472282293)
          ·
            refine ⟨1727453933801627294276465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18426175293884024472282293 1727453933801627294276465)
            ·
              refine ⟨1295590450351220470707349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1727453933801627294276465 1295590450351220470707349)
              ·
                refine ⟨60730802360213459564407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1295590450351220470707349 60730802360213459564407)
                ·
                  rfl

theorem cell22_1596683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 6].length) (baseStart_1596683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1596683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1596683 prefixEnd_1596683 := by exact prefixLift 1596683
  have htrace : WordTrace (prefixWord ++ tailWord_1596683) baseStart_1596683 baseEnd_1596683 := by
    simpa [prefixWord, tailWord_1596683, baseEnd_1596683] using wordTrace_append hprefix tailTrace_1596683
  have hstable : (prefixWord ++ tailWord_1596683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596683).length < 2 ^ (prefixWord ++ tailWord_1596683).sum := by decide
  have hdescent : baseEnd_1596683 < baseStart_1596683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596702 : List Nat := [4, 3, 2, 1, 2, 1, 1, 2, 2, 4]
def baseStart_1596702 : Nat := 118140960795 + 1596702 * 2 ^ 59
def prefixEnd_1596702 : Nat := 4983230072969 + 3 ^ 40 * 1596702 * 2
def baseEnd_1596702 : Nat := 546583725330211419854605

theorem tailTrace_1596702 : CollatzResearch.WordTrace tailWord_1596702 prefixEnd_1596702 546583725330211419854605 := by
  unfold tailWord_1596702
  simp only [CollatzResearch.WordTrace]
  refine ⟨7279563282678602979544045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38824337507619215890901573 7279563282678602979544045)
  ·
    refine ⟨2729836231004476117329017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7279563282678602979544045 2729836231004476117329017)
    ·
      refine ⟨2047377173253357087996763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2729836231004476117329017 2047377173253357087996763)
      ·
        refine ⟨3071065759880035631995145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2047377173253357087996763 3071065759880035631995145)
        ·
          refine ⟨2303299319910026723996359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3071065759880035631995145 2303299319910026723996359)
          ·
            refine ⟨3454948979865040085994539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2303299319910026723996359 3454948979865040085994539)
            ·
              refine ⟨5182423469797560128991809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3454948979865040085994539 5182423469797560128991809)
              ·
                refine ⟨3886817602348170096743857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5182423469797560128991809 3886817602348170096743857)
                ·
                  refine ⟨2915113201761127572557893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3886817602348170096743857 2915113201761127572557893)
                  ·
                    refine ⟨546583725330211419854605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2915113201761127572557893 546583725330211419854605)
                    ·
                      rfl

theorem cell22_1596702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_1596702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1596702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1596702 prefixEnd_1596702 := by exact prefixLift 1596702
  have htrace : WordTrace (prefixWord ++ tailWord_1596702) baseStart_1596702 baseEnd_1596702 := by
    simpa [prefixWord, tailWord_1596702, baseEnd_1596702] using wordTrace_append hprefix tailTrace_1596702
  have hstable : (prefixWord ++ tailWord_1596702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596702).length < 2 ^ (prefixWord ++ tailWord_1596702).sum := by decide
  have hdescent : baseEnd_1596702 < baseStart_1596702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596803 : List Nat := [1, 1, 1, 3, 5, 2, 1, 1, 1, 6]
def baseStart_1596803 : Nat := 118140960795 + 1596803 * 2 ^ 59
def prefixEnd_1596803 : Nat := 4983230072969 + 3 ^ 40 * 1596803 * 2
def baseEnd_1596803 : Nat := 546618299694280823079295

theorem tailTrace_1596803 : CollatzResearch.WordTrace tailWord_1596803 prefixEnd_1596803 546618299694280823079295 := by
  unfold tailWord_1596803
  simp only [CollatzResearch.WordTrace]
  refine ⟨58240190034062918085779063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38826793356041945390519375 58240190034062918085779063)
  ·
    refine ⟨87360285051094377128668595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58240190034062918085779063 87360285051094377128668595)
    ·
      refine ⟨131040427576641565693002893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87360285051094377128668595 131040427576641565693002893)
      ·
        refine ⟨49140160341240587134876085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131040427576641565693002893 49140160341240587134876085)
        ·
          refine ⟨4606890031991305043894633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49140160341240587134876085 4606890031991305043894633)
          ·
            refine ⟨3455167523993478782920975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4606890031991305043894633 3455167523993478782920975)
            ·
              refine ⟨5182751285990218174381463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3455167523993478782920975 5182751285990218174381463)
              ·
                refine ⟨7774126928985327261572195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5182751285990218174381463 7774126928985327261572195)
                ·
                  refine ⟨11661190393477990892358293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7774126928985327261572195 11661190393477990892358293)
                  ·
                    refine ⟨546618299694280823079295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11661190393477990892358293 546618299694280823079295)
                    ·
                      rfl

theorem cell22_1596803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 6].length) (baseStart_1596803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1596803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1596803 prefixEnd_1596803 := by exact prefixLift 1596803
  have htrace : WordTrace (prefixWord ++ tailWord_1596803) baseStart_1596803 baseEnd_1596803 := by
    simpa [prefixWord, tailWord_1596803, baseEnd_1596803] using wordTrace_append hprefix tailTrace_1596803
  have hstable : (prefixWord ++ tailWord_1596803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596803).length < 2 ^ (prefixWord ++ tailWord_1596803).sum := by decide
  have hdescent : baseEnd_1596803 < baseStart_1596803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596809 : List Nat := [1, 2, 1, 1, 8, 1, 2, 1, 1, 4]
def baseStart_1596809 : Nat := 118140960795 + 1596809 * 2 ^ 59
def prefixEnd_1596809 : Nat := 4983230072969 + 3 ^ 40 * 1596809 * 2
def baseEnd_1596809 : Nat := 546620353616898807429277

theorem tailTrace_1596809 : CollatzResearch.WordTrace tailWord_1596809 prefixEnd_1596809 546620353616898807429277 := by
  unfold tailWord_1596809
  simp only [CollatzResearch.WordTrace]
  refine ⟨58240408872041181110497481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38826939248027454073664987 58240408872041181110497481)
  ·
    refine ⟨43680306654030885832873111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58240408872041181110497481 43680306654030885832873111)
    ·
      refine ⟨65520459981046328749309667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43680306654030885832873111 65520459981046328749309667)
      ·
        refine ⟨98280689971569493123964501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65520459981046328749309667 98280689971569493123964501)
        ·
          refine ⟨1151726835604329997546459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 98280689971569493123964501 1151726835604329997546459)
          ·
            refine ⟨1727590253406494996319689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1151726835604329997546459 1727590253406494996319689)
            ·
              refine ⟨1295692690054871247239767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1727590253406494996319689 1295692690054871247239767)
              ·
                refine ⟨1943539035082306870859651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1295692690054871247239767 1943539035082306870859651)
                ·
                  refine ⟨2915308552623460306289477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1943539035082306870859651 2915308552623460306289477)
                  ·
                    refine ⟨546620353616898807429277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2915308552623460306289477 546620353616898807429277)
                    ·
                      rfl

theorem cell22_1596809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 1, 1, 4].length) (baseStart_1596809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1596809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1596809 prefixEnd_1596809 := by exact prefixLift 1596809
  have htrace : WordTrace (prefixWord ++ tailWord_1596809) baseStart_1596809 baseEnd_1596809 := by
    simpa [prefixWord, tailWord_1596809, baseEnd_1596809] using wordTrace_append hprefix tailTrace_1596809
  have hstable : (prefixWord ++ tailWord_1596809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596809).length < 2 ^ (prefixWord ++ tailWord_1596809).sum := by decide
  have hdescent : baseEnd_1596809 < baseStart_1596809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596867 : List Nat := [1, 1, 1, 3, 1, 1, 7, 3, 1, 3]
def baseStart_1596867 : Nat := 118140960795 + 1596867 * 2 ^ 59
def prefixEnd_1596867 : Nat := 4983230072969 + 3 ^ 40 * 1596867 * 2
def baseEnd_1596867 : Nat := 546640208202205989479099

theorem tailTrace_1596867 : CollatzResearch.WordTrace tailWord_1596867 prefixEnd_1596867 546640208202205989479099 := by
  unfold tailWord_1596867
  simp only [CollatzResearch.WordTrace]
  refine ⟨58242524305831057016108855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38828349537220704677405903 58242524305831057016108855)
  ·
    refine ⟨87363786458746585524163283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58242524305831057016108855 87363786458746585524163283)
    ·
      refine ⟨131045679688119878286244925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87363786458746585524163283 131045679688119878286244925)
      ·
        refine ⟨49142129883044954357341847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131045679688119878286244925 49142129883044954357341847)
        ·
          refine ⟨73713194824567431536012771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49142129883044954357341847 73713194824567431536012771)
          ·
            refine ⟨110569792236851147304019157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73713194824567431536012771 110569792236851147304019157)
            ·
              refine ⟨2591479505551198764937949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 110569792236851147304019157 2591479505551198764937949)
              ·
                refine ⟨971804814581699536851731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2591479505551198764937949 971804814581699536851731)
                ·
                  refine ⟨1457707221872549305277597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 971804814581699536851731 1457707221872549305277597)
                  ·
                    refine ⟨546640208202205989479099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1457707221872549305277597 546640208202205989479099)
                    ·
                      rfl

theorem cell22_1596867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 3, 1, 3].length) (baseStart_1596867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1596867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1596867 prefixEnd_1596867 := by exact prefixLift 1596867
  have htrace : WordTrace (prefixWord ++ tailWord_1596867) baseStart_1596867 baseEnd_1596867 := by
    simpa [prefixWord, tailWord_1596867, baseEnd_1596867] using wordTrace_append hprefix tailTrace_1596867
  have hstable : (prefixWord ++ tailWord_1596867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596867).length < 2 ^ (prefixWord ++ tailWord_1596867).sum := by decide
  have hdescent : baseEnd_1596867 < baseStart_1596867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596878 : List Nat := [4, 1, 1, 1, 2, 1, 2, 1, 4, 5]
def baseStart_1596878 : Nat := 118140960795 + 1596878 * 2 ^ 59
def prefixEnd_1596878 : Nat := 4983230072969 + 3 ^ 40 * 1596878 * 2
def baseEnd_1596878 : Nat := 546643973727005627454065

theorem tailTrace_1596878 : CollatzResearch.WordTrace tailWord_1596878 prefixEnd_1596878 546643973727005627454065 := by
  unfold tailWord_1596878
  simp only [CollatzResearch.WordTrace]
  refine ⟨7280365688598900736844911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38828617005860803929839525 7280365688598900736844911)
  ·
    refine ⟨10920548532898351105267367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7280365688598900736844911 10920548532898351105267367)
    ·
      refine ⟨16380822799347526657901051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10920548532898351105267367 16380822799347526657901051)
      ·
        refine ⟨24571234199021289986851577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16380822799347526657901051 24571234199021289986851577)
        ·
          refine ⟨18428425649265967490138683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24571234199021289986851577 18428425649265967490138683)
          ·
            refine ⟨27642638473898951235208025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18428425649265967490138683 27642638473898951235208025)
            ·
              refine ⟨20731978855424213426406019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27642638473898951235208025 20731978855424213426406019)
              ·
                refine ⟨31097968283136320139609029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20731978855424213426406019 31097968283136320139609029)
                ·
                  refine ⟨5830869053088060026176693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31097968283136320139609029 5830869053088060026176693)
                  ·
                    refine ⟨546643973727005627454065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5830869053088060026176693 546643973727005627454065)
                    ·
                      rfl

theorem cell22_1596878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_1596878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1596878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1596878 prefixEnd_1596878 := by exact prefixLift 1596878
  have htrace : WordTrace (prefixWord ++ tailWord_1596878) baseStart_1596878 baseEnd_1596878 := by
    simpa [prefixWord, tailWord_1596878, baseEnd_1596878] using wordTrace_append hprefix tailTrace_1596878
  have hstable : (prefixWord ++ tailWord_1596878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596878).length < 2 ^ (prefixWord ++ tailWord_1596878).sum := by decide
  have hdescent : baseEnd_1596878 < baseStart_1596878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596884 : List Nat := [2, 4, 1, 2, 3, 2, 1, 1, 3, 3]
def baseStart_1596884 : Nat := 118140960795 + 1596884 * 2 ^ 59
def prefixEnd_1596884 : Nat := 4983230072969 + 3 ^ 40 * 1596884 * 2
def baseEnd_1596884 : Nat := 546646027649623611804047

theorem tailTrace_1596884 : CollatzResearch.WordTrace tailWord_1596884 prefixEnd_1596884 546646027649623611804047 := by
  unfold tailWord_1596884
  simp only [CollatzResearch.WordTrace]
  refine ⟨29121572173384734459738853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38828762897846312612985137 29121572173384734459738853)
  ·
    refine ⟨5460294782509637711201035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29121572173384734459738853 5460294782509637711201035)
    ·
      refine ⟨8190442173764456566801553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5460294782509637711201035 8190442173764456566801553)
      ·
        refine ⟨6142831630323342425101165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8190442173764456566801553 6142831630323342425101165)
        ·
          refine ⟨2303561861371253409412937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6142831630323342425101165 2303561861371253409412937)
          ·
            refine ⟨1727671396028440057059703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2303561861371253409412937 1727671396028440057059703)
            ·
              refine ⟨2591507094042660085589555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1727671396028440057059703 2591507094042660085589555)
              ·
                refine ⟨3887260641063990128384333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2591507094042660085589555 3887260641063990128384333)
                ·
                  refine ⟨1457722740398996298144125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3887260641063990128384333 1457722740398996298144125)
                  ·
                    refine ⟨546646027649623611804047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1457722740398996298144125 546646027649623611804047)
                    ·
                      rfl

theorem cell22_1596884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_1596884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1596884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1596884 prefixEnd_1596884 := by exact prefixLift 1596884
  have htrace : WordTrace (prefixWord ++ tailWord_1596884) baseStart_1596884 baseEnd_1596884 := by
    simpa [prefixWord, tailWord_1596884, baseEnd_1596884] using wordTrace_append hprefix tailTrace_1596884
  have hstable : (prefixWord ++ tailWord_1596884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596884).length < 2 ^ (prefixWord ++ tailWord_1596884).sum := by decide
  have hdescent : baseEnd_1596884 < baseStart_1596884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596897 : List Nat := [1, 2, 3, 1, 2, 5, 2, 1, 5]
def baseStart_1596897 : Nat := 118140960795 + 1596897 * 2 ^ 59
def prefixEnd_1596897 : Nat := 4983230072969 + 3 ^ 40 * 1596897 * 2
def baseEnd_1596897 : Nat := 182216825938431970409669

theorem tailTrace_1596897 : CollatzResearch.WordTrace tailWord_1596897 prefixEnd_1596897 182216825938431970409669 := by
  unfold tailWord_1596897
  simp only [CollatzResearch.WordTrace]
  refine ⟨58243618495722372139700945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38829078997148248093133963 58243618495722372139700945)
  ·
    refine ⟨43682713871791779104775709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58243618495722372139700945 43682713871791779104775709)
    ·
      refine ⟨16381017701921917164290891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43682713871791779104775709 16381017701921917164290891)
      ·
        refine ⟨24571526552882875746436337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16381017701921917164290891 24571526552882875746436337)
        ·
          refine ⟨18428644914662156809827253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24571526552882875746436337 18428644914662156809827253)
          ·
            refine ⟨1727685460749577200921305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18428644914662156809827253 1727685460749577200921305)
            ·
              refine ⟨1295764095562182900690979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1727685460749577200921305 1295764095562182900690979)
              ·
                refine ⟨1943646143343274351036469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1295764095562182900690979 1943646143343274351036469)
                ·
                  refine ⟨182216825938431970409669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1943646143343274351036469 182216825938431970409669)
                  ·
                    rfl

theorem cell22_1596897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 1, 5].length) (baseStart_1596897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1596897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1596897 prefixEnd_1596897 := by exact prefixLift 1596897
  have htrace : WordTrace (prefixWord ++ tailWord_1596897) baseStart_1596897 baseEnd_1596897 := by
    simpa [prefixWord, tailWord_1596897, baseEnd_1596897] using wordTrace_append hprefix tailTrace_1596897
  have hstable : (prefixWord ++ tailWord_1596897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596897).length < 2 ^ (prefixWord ++ tailWord_1596897).sum := by decide
  have hdescent : baseEnd_1596897 < baseStart_1596897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596910 : List Nat := [4, 1, 2, 1, 2, 1, 3, 1, 3, 4]
def baseStart_1596910 : Nat := 118140960795 + 1596910 * 2 ^ 59
def prefixEnd_1596910 : Nat := 4983230072969 + 3 ^ 40 * 1596910 * 2
def baseEnd_1596910 : Nat := 546654927980968210653967

theorem tailTrace_1596910 : CollatzResearch.WordTrace tailWord_1596910 prefixEnd_1596910 546654927980968210653967 := by
  unfold tailWord_1596910
  simp only [CollatzResearch.WordTrace]
  refine ⟨7280511580584409419990523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38829395096450183573282789 7280511580584409419990523)
  ·
    refine ⟨10920767370876614129985785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7280511580584409419990523 10920767370876614129985785)
    ·
      refine ⟨8190575528157460597489339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10920767370876614129985785 8190575528157460597489339)
      ·
        refine ⟨12285863292236190896234009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8190575528157460597489339 12285863292236190896234009)
        ·
          refine ⟨9214397469177143172175507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12285863292236190896234009 9214397469177143172175507)
          ·
            refine ⟨13821596203765714758263261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9214397469177143172175507 13821596203765714758263261)
            ·
              refine ⟨5183098576412143034348723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13821596203765714758263261 5183098576412143034348723)
              ·
                refine ⟨7774647864618214551523085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5183098576412143034348723 7774647864618214551523085)
                ·
                  refine ⟨2915492949231830456821157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7774647864618214551523085 2915492949231830456821157)
                  ·
                    refine ⟨546654927980968210653967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2915492949231830456821157 546654927980968210653967)
                    ·
                      rfl

theorem cell22_1596910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_1596910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1596910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1596910 prefixEnd_1596910 := by exact prefixLift 1596910
  have htrace : WordTrace (prefixWord ++ tailWord_1596910) baseStart_1596910 baseEnd_1596910 := by
    simpa [prefixWord, tailWord_1596910, baseEnd_1596910] using wordTrace_append hprefix tailTrace_1596910
  have hstable : (prefixWord ++ tailWord_1596910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596910).length < 2 ^ (prefixWord ++ tailWord_1596910).sum := by decide
  have hdescent : baseEnd_1596910 < baseStart_1596910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596923 : List Nat := [1, 1, 1, 1, 1, 3, 2, 6, 1, 5]
def baseStart_1596923 : Nat := 118140960795 + 1596923 * 2 ^ 59
def prefixEnd_1596923 : Nat := 4983230072969 + 3 ^ 40 * 1596923 * 2
def baseEnd_1596923 : Nat := 546659378146640510078927

theorem tailTrace_1596923 : CollatzResearch.WordTrace tailWord_1596923 prefixEnd_1596923 546659378146640510078927 := by
  unfold tailWord_1596923
  simp only [CollatzResearch.WordTrace]
  refine ⟨58244566793628178580147423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38829711195752119053431615 58244566793628178580147423)
  ·
    refine ⟨87366850190442267870221135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58244566793628178580147423 87366850190442267870221135)
    ·
      refine ⟨131050275285663401805331703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87366850190442267870221135 131050275285663401805331703)
      ·
        refine ⟨196575412928495102707997555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131050275285663401805331703 196575412928495102707997555)
        ·
          refine ⟨294863119392742654061996333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196575412928495102707997555 294863119392742654061996333)
          ·
            refine ⟨110573669772278495273248625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 294863119392742654061996333 110573669772278495273248625)
            ·
              refine ⟨82930252329208871454936469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110573669772278495273248625 82930252329208871454936469)
              ·
                refine ⟨3887355577931665849450147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 82930252329208871454936469 3887355577931665849450147)
                ·
                  refine ⟨5831033366897498774175221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3887355577931665849450147 5831033366897498774175221)
                  ·
                    refine ⟨546659378146640510078927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5831033366897498774175221 546659378146640510078927)
                    ·
                      rfl

theorem cell22_1596923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 5].length) (baseStart_1596923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1596923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1596923 prefixEnd_1596923 := by exact prefixLift 1596923
  have htrace : WordTrace (prefixWord ++ tailWord_1596923) baseStart_1596923 baseEnd_1596923 := by
    simpa [prefixWord, tailWord_1596923, baseEnd_1596923] using wordTrace_append hprefix tailTrace_1596923
  have hstable : (prefixWord ++ tailWord_1596923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596923).length < 2 ^ (prefixWord ++ tailWord_1596923).sum := by decide
  have hdescent : baseEnd_1596923 < baseStart_1596923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596957 : List Nat := [1, 4, 2, 2, 1, 1, 1, 5, 2, 3]
def baseStart_1596957 : Nat := 118140960795 + 1596957 * 2 ^ 59
def prefixEnd_1596957 : Nat := 4983230072969 + 3 ^ 40 * 1596957 * 2
def baseEnd_1596957 : Nat := 546671017041475754728823

theorem tailTrace_1596957 : CollatzResearch.WordTrace tailWord_1596957 prefixEnd_1596957 546671017041475754728823 := by
  unfold tailWord_1596957
  simp only [CollatzResearch.WordTrace]
  refine ⟨58245806875505002386885125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38830537917003334924590083 58245806875505002386885125)
  ·
    refine ⟨10921088789157187947540961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58245806875505002386885125 10921088789157187947540961)
    ·
      refine ⟨8190816591867890960655721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10921088789157187947540961 8190816591867890960655721)
      ·
        refine ⟨6143112443900918220491791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8190816591867890960655721 6143112443900918220491791)
        ·
          refine ⟨9214668665851377330737687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6143112443900918220491791 9214668665851377330737687)
          ·
            refine ⟨13822002998777065996106531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9214668665851377330737687 13822002998777065996106531)
            ·
              refine ⟨20733004498165598994159797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13822002998777065996106531 20733004498165598994159797)
              ·
                refine ⟨1943719171703024905702481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20733004498165598994159797 1943719171703024905702481)
                ·
                  refine ⟨1457789378777268679276861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1943719171703024905702481 1457789378777268679276861)
                  ·
                    refine ⟨546671017041475754728823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1457789378777268679276861 546671017041475754728823)
                    ·
                      rfl

theorem cell22_1596957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_1596957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1596957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1596957 prefixEnd_1596957 := by exact prefixLift 1596957
  have htrace : WordTrace (prefixWord ++ tailWord_1596957) baseStart_1596957 baseEnd_1596957 := by
    simpa [prefixWord, tailWord_1596957, baseEnd_1596957] using wordTrace_append hprefix tailTrace_1596957
  have hstable : (prefixWord ++ tailWord_1596957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596957).length < 2 ^ (prefixWord ++ tailWord_1596957).sum := by decide
  have hdescent : baseEnd_1596957 < baseStart_1596957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597002 : List Nat := [3, 1, 2, 1, 1, 3, 4, 1, 3, 3]
def baseStart_1597002 : Nat := 118140960795 + 1597002 * 2 ^ 59
def prefixEnd_1597002 : Nat := 4983230072969 + 3 ^ 40 * 1597002 * 2
def baseEnd_1597002 : Nat := 546686421461110637353685

theorem tailTrace_1597002 : CollatzResearch.WordTrace tailWord_1597002 prefixEnd_1597002 546686421461110637353685 := by
  unfold tailWord_1597002
  simp only [CollatzResearch.WordTrace]
  refine ⟨14561862040085493768068315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38831632106894650048182173 14561862040085493768068315)
  ·
    refine ⟨21842793060128240652102473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14561862040085493768068315 21842793060128240652102473)
    ·
      refine ⟨16382094795096180489076855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21842793060128240652102473 16382094795096180489076855)
      ·
        refine ⟨24573142192644270733615283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16382094795096180489076855 24573142192644270733615283)
        ·
          refine ⟨36859713288966406100422925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24573142192644270733615283 36859713288966406100422925)
          ·
            refine ⟨13822392483362402287658597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36859713288966406100422925 13822392483362402287658597)
            ·
              refine ⟨2591698590630450428935987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13822392483362402287658597 2591698590630450428935987)
              ·
                refine ⟨3887547885945675643403981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2591698590630450428935987 3887547885945675643403981)
                ·
                  refine ⟨1457830457229628366276493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3887547885945675643403981 1457830457229628366276493)
                  ·
                    refine ⟨546686421461110637353685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1457830457229628366276493 546686421461110637353685)
                    ·
                      rfl

theorem cell22_1597002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 3, 3].length) (baseStart_1597002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1597002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1597002 prefixEnd_1597002 := by exact prefixLift 1597002
  have htrace : WordTrace (prefixWord ++ tailWord_1597002) baseStart_1597002 baseEnd_1597002 := by
    simpa [prefixWord, tailWord_1597002, baseEnd_1597002] using wordTrace_append hprefix tailTrace_1597002
  have hstable : (prefixWord ++ tailWord_1597002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597002).length < 2 ^ (prefixWord ++ tailWord_1597002).sum := by decide
  have hdescent : baseEnd_1597002 < baseStart_1597002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597021 : List Nat := [1, 4, 4, 2, 1, 2, 2, 6]
def baseStart_1597021 : Nat := 118140960795 + 1597021 * 2 ^ 59
def prefixEnd_1597021 : Nat := 4983230072969 + 3 ^ 40 * 1597021 * 2
def baseEnd_1597021 : Nat := 60743658394377880125403

theorem tailTrace_1597021 : CollatzResearch.WordTrace tailWord_1597021 prefixEnd_1597021 60743658394377880125403 := by
  unfold tailWord_1597021
  simp only [CollatzResearch.WordTrace]
  refine ⟨58248141147273141317214917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38832094098182094211476611 58248141147273141317214917)
  ·
    refine ⟨10921526465113713996977797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58248141147273141317214917 10921526465113713996977797)
    ·
      refine ⟨2047786212208821374433337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10921526465113713996977797 2047786212208821374433337)
      ·
        refine ⟨1535839659156616030825003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2047786212208821374433337 1535839659156616030825003)
        ·
          refine ⟨2303759488734924046237505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1535839659156616030825003 2303759488734924046237505)
          ·
            refine ⟨1727819616551193034678129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2303759488734924046237505 1727819616551193034678129)
            ·
              refine ⟨1295864712413394776008597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1727819616551193034678129 1295864712413394776008597)
              ·
                refine ⟨60743658394377880125403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1295864712413394776008597 60743658394377880125403)
                ·
                  rfl

theorem cell22_1597021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 6].length) (baseStart_1597021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1597021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1597021 prefixEnd_1597021 := by exact prefixLift 1597021
  have htrace : WordTrace (prefixWord ++ tailWord_1597021) baseStart_1597021 baseEnd_1597021 := by
    simpa [prefixWord, tailWord_1597021, baseEnd_1597021] using wordTrace_append hprefix tailTrace_1597021
  have hstable : (prefixWord ++ tailWord_1597021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597021).length < 2 ^ (prefixWord ++ tailWord_1597021).sum := by decide
  have hdescent : baseEnd_1597021 < baseStart_1597021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597079 : List Nat := [1, 1, 3, 3, 2, 4, 1, 2, 1, 4]
def baseStart_1597079 : Nat := 118140960795 + 1597079 * 2 ^ 59
def prefixEnd_1597079 : Nat := 4983230072969 + 3 ^ 40 * 1597079 * 2
def baseEnd_1597079 : Nat := 546712780134708103178449

theorem tailTrace_1597079 : CollatzResearch.WordTrace tailWord_1597079 prefixEnd_1597079 546712780134708103178449 := by
  unfold tailWord_1597079
  simp only [CollatzResearch.WordTrace]
  refine ⟨58250256581063017222826291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38833504387375344815217527 58250256581063017222826291)
  ·
    refine ⟨87375384871594525834239437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58250256581063017222826291 87375384871594525834239437)
    ·
      refine ⟨32765769326847947187839789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87375384871594525834239437 32765769326847947187839789)
      ·
        refine ⟨12287163497567980195439921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32765769326847947187839789 12287163497567980195439921)
        ·
          refine ⟨9215372623175985146579941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12287163497567980195439921 9215372623175985146579941)
          ·
            refine ⟨1727882366845497214983739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9215372623175985146579941 1727882366845497214983739)
            ·
              refine ⟨2591823550268245822475609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1727882366845497214983739 2591823550268245822475609)
              ·
                refine ⟨1943867662701184366856707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2591823550268245822475609 1943867662701184366856707)
                ·
                  refine ⟨2915801494051776550285061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1943867662701184366856707 2915801494051776550285061)
                  ·
                    refine ⟨546712780134708103178449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2915801494051776550285061 546712780134708103178449)
                    ·
                      rfl

theorem cell22_1597079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 2, 1, 4].length) (baseStart_1597079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1597079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1597079 prefixEnd_1597079 := by exact prefixLift 1597079
  have htrace : WordTrace (prefixWord ++ tailWord_1597079) baseStart_1597079 baseEnd_1597079 := by
    simpa [prefixWord, tailWord_1597079, baseEnd_1597079] using wordTrace_append hprefix tailTrace_1597079
  have hstable : (prefixWord ++ tailWord_1597079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597079).length < 2 ^ (prefixWord ++ tailWord_1597079).sum := by decide
  have hdescent : baseEnd_1597079 < baseStart_1597079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597092 : List Nat := [2, 3, 1, 2, 2, 3, 1, 2, 1, 5]
def baseStart_1597092 : Nat := 118140960795 + 1597092 * 2 ^ 59
def prefixEnd_1597092 : Nat := 4983230072969 + 3 ^ 40 * 1597092 * 2
def baseEnd_1597092 : Nat := 546717230300380402603409

theorem tailTrace_1597092 : CollatzResearch.WordTrace tailWord_1597092 prefixEnd_1597092 546717230300380402603409 := by
  unfold tailWord_1597092
  simp only [CollatzResearch.WordTrace]
  refine ⟨29125365365007960221524765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38833820486677280295366353 29125365365007960221524765)
  ·
    refine ⟨10922012011877985083071787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29125365365007960221524765 10922012011877985083071787)
    ·
      refine ⟨16383018017816977624607681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10922012011877985083071787 16383018017816977624607681)
      ·
        refine ⟨12287263513362733218455761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16383018017816977624607681 12287263513362733218455761)
        ·
          refine ⟨9215447635022049913841821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12287263513362733218455761 9215447635022049913841821)
          ·
            refine ⟨3455792863133268717690683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9215447635022049913841821 3455792863133268717690683)
            ·
              refine ⟨5183689294699903076536025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3455792863133268717690683 5183689294699903076536025)
              ·
                refine ⟨3887766971024927307402019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5183689294699903076536025 3887766971024927307402019)
                ·
                  refine ⟨5831650456537390961103029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3887766971024927307402019 5831650456537390961103029)
                  ·
                    refine ⟨546717230300380402603409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5831650456537390961103029 546717230300380402603409)
                    ·
                      rfl

theorem cell22_1597092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_1597092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1597092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1597092 prefixEnd_1597092 := by exact prefixLift 1597092
  have htrace : WordTrace (prefixWord ++ tailWord_1597092) baseStart_1597092 baseEnd_1597092 := by
    simpa [prefixWord, tailWord_1597092, baseEnd_1597092] using wordTrace_append hprefix tailTrace_1597092
  have hstable : (prefixWord ++ tailWord_1597092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597092).length < 2 ^ (prefixWord ++ tailWord_1597092).sum := by decide
  have hdescent : baseEnd_1597092 < baseStart_1597092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597111 : List Nat := [1, 1, 3, 1, 5, 3, 2, 2, 4]
def baseStart_1597111 : Nat := 118140960795 + 1597111 * 2 ^ 59
def prefixEnd_1597111 : Nat := 4983230072969 + 3 ^ 40 * 1597111 * 2
def baseEnd_1597111 : Nat := 182241244796223562126117

theorem tailTrace_1597111 : CollatzResearch.WordTrace tailWord_1597111 prefixEnd_1597111 182241244796223562126117 := by
  unfold tailWord_1597111
  simp only [CollatzResearch.WordTrace]
  refine ⟨58251423716947086687991187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38834282477964724458660791 58251423716947086687991187)
  ·
    refine ⟨87377135575420630031986781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58251423716947086687991187 87377135575420630031986781)
    ·
      refine ⟨32766425840782736261995043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87377135575420630031986781 32766425840782736261995043)
      ·
        refine ⟨49149638761174104392992565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32766425840782736261995043 49149638761174104392992565)
        ·
          refine ⟨4607778633860072286843053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49149638761174104392992565 4607778633860072286843053)
          ·
            refine ⟨1727916987697527107566145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4607778633860072286843053 1727916987697527107566145)
            ·
              refine ⟨1295937740773145330674609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1727916987697527107566145 1295937740773145330674609)
              ·
                refine ⟨971953305579858998005957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1295937740773145330674609 971953305579858998005957)
                ·
                  refine ⟨182241244796223562126117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 971953305579858998005957 182241244796223562126117)
                  ·
                    rfl

theorem cell22_1597111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 2, 4].length) (baseStart_1597111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1597111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1597111 prefixEnd_1597111 := by exact prefixLift 1597111
  have htrace : WordTrace (prefixWord ++ tailWord_1597111) baseStart_1597111 baseEnd_1597111 := by
    simpa [prefixWord, tailWord_1597111, baseEnd_1597111] using wordTrace_append hprefix tailTrace_1597111
  have hstable : (prefixWord ++ tailWord_1597111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597111).length < 2 ^ (prefixWord ++ tailWord_1597111).sum := by decide
  have hdescent : baseEnd_1597111 < baseStart_1597111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597126 : List Nat := [6, 1, 2, 1, 1, 1, 1, 3, 1, 5]
def baseStart_1597126 : Nat := 118140960795 + 1597126 * 2 ^ 59
def prefixEnd_1597126 : Nat := 4983230072969 + 3 ^ 40 * 1597126 * 2
def baseEnd_1597126 : Nat := 546728869195215647253305

theorem tailTrace_1597126 : CollatzResearch.WordTrace tailWord_1597126 prefixEnd_1597126 546728869195215647253305 := by
  unfold tailWord_1597126
  simp only [CollatzResearch.WordTrace]
  refine ⟨1820374087871648257805851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 38834647207928496166524821 1820374087871648257805851)
  ·
    refine ⟨2730561131807472386708777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1820374087871648257805851 2730561131807472386708777)
    ·
      refine ⟨2047920848855604290031583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2730561131807472386708777 2047920848855604290031583)
      ·
        refine ⟨3071881273283406435047375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2047920848855604290031583 3071881273283406435047375)
        ·
          refine ⟨4607821909925109652571063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3071881273283406435047375 4607821909925109652571063)
          ·
            refine ⟨6911732864887664478856595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4607821909925109652571063 6911732864887664478856595)
            ·
              refine ⟨10367599297331496718284893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6911732864887664478856595 10367599297331496718284893)
              ·
                refine ⟨3887849736499311269356835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10367599297331496718284893 3887849736499311269356835)
                ·
                  refine ⟨5831774604748966904035253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3887849736499311269356835 5831774604748966904035253)
                  ·
                    refine ⟨546728869195215647253305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5831774604748966904035253 546728869195215647253305)
                    ·
                      rfl

theorem cell22_1597126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_1597126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1597126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1597126 prefixEnd_1597126 := by exact prefixLift 1597126
  have htrace : WordTrace (prefixWord ++ tailWord_1597126) baseStart_1597126 baseEnd_1597126 := by
    simpa [prefixWord, tailWord_1597126, baseEnd_1597126] using wordTrace_append hprefix tailTrace_1597126
  have hstable : (prefixWord ++ tailWord_1597126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597126).length < 2 ^ (prefixWord ++ tailWord_1597126).sum := by decide
  have hdescent : baseEnd_1597126 < baseStart_1597126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597137 : List Nat := [1, 2, 2, 1, 2, 4, 1, 1, 5, 3]
def baseStart_1597137 : Nat := 118140960795 + 1597137 * 2 ^ 59
def prefixEnd_1597137 : Nat := 4983230072969 + 3 ^ 40 * 1597137 * 2
def baseEnd_1597137 : Nat := 546732634720015285228271

theorem tailTrace_1597137 : CollatzResearch.WordTrace tailWord_1597137 prefixEnd_1597137 546732634720015285228271 := by
  unfold tailWord_1597137
  simp only [CollatzResearch.WordTrace]
  refine ⟨58252372014852893128437665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38834914676568595418958443 58252372014852893128437665)
  ·
    refine ⟨43689279011139669846328249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58252372014852893128437665 43689279011139669846328249)
    ·
      refine ⟨32766959258354752384746187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43689279011139669846328249 32766959258354752384746187)
      ·
        refine ⟨49150438887532128577119281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32766959258354752384746187 49150438887532128577119281)
        ·
          refine ⟨36862829165649096432839461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49150438887532128577119281 36862829165649096432839461)
          ·
            refine ⟨6911780468559205581157399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36862829165649096432839461 6911780468559205581157399)
            ·
              refine ⟨10367670702838808371736099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6911780468559205581157399 10367670702838808371736099)
              ·
                refine ⟨15551506054258212557604149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10367670702838808371736099 15551506054258212557604149)
                ·
                  refine ⟨1457953692586707427275389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15551506054258212557604149 1457953692586707427275389)
                  ·
                    refine ⟨546732634720015285228271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1457953692586707427275389 546732634720015285228271)
                    ·
                      rfl

theorem cell22_1597137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 5, 3].length) (baseStart_1597137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1597137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1597137 prefixEnd_1597137 := by exact prefixLift 1597137
  have htrace : WordTrace (prefixWord ++ tailWord_1597137) baseStart_1597137 baseEnd_1597137 := by
    simpa [prefixWord, tailWord_1597137, baseEnd_1597137] using wordTrace_append hprefix tailTrace_1597137
  have hstable : (prefixWord ++ tailWord_1597137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597137).length < 2 ^ (prefixWord ++ tailWord_1597137).sum := by decide
  have hdescent : baseEnd_1597137 < baseStart_1597137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597190 : List Nat := [6, 2, 2, 1, 1, 1, 1, 8]
def baseStart_1597190 : Nat := 118140960795 + 1597190 * 2 ^ 59
def prefixEnd_1597190 : Nat := 4983230072969 + 3 ^ 40 * 1597190 * 2
def baseEnd_1597190 : Nat := 60750086411460090405901

theorem tailTrace_1597190 : CollatzResearch.WordTrace tailWord_1597190 prefixEnd_1597190 60750086411460090405901 := by
  unfold tailWord_1597190
  simp only [CollatzResearch.WordTrace]
  refine ⟨1820447033864402599378657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 38836203389107255453411349 1820447033864402599378657)
  ·
    refine ⟨1365335275398301949533993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1820447033864402599378657 1365335275398301949533993)
    ·
      refine ⟨1024001456548726462150495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1365335275398301949533993 1024001456548726462150495)
      ·
        refine ⟨1536002184823089693225743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1024001456548726462150495 1536002184823089693225743)
        ·
          refine ⟨2304003277234634539838615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1536002184823089693225743 2304003277234634539838615)
          ·
            refine ⟨3456004915851951809757923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2304003277234634539838615 3456004915851951809757923)
            ·
              refine ⟨5184007373777927714636885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3456004915851951809757923 5184007373777927714636885)
              ·
                refine ⟨60750086411460090405901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5184007373777927714636885 60750086411460090405901)
                ·
                  rfl

theorem cell22_1597190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_1597190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1597190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1597190 prefixEnd_1597190 := by exact prefixLift 1597190
  have htrace : WordTrace (prefixWord ++ tailWord_1597190) baseStart_1597190 baseEnd_1597190 := by
    simpa [prefixWord, tailWord_1597190, baseEnd_1597190] using wordTrace_append hprefix tailTrace_1597190
  have hstable : (prefixWord ++ tailWord_1597190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597190).length < 2 ^ (prefixWord ++ tailWord_1597190).sum := by decide
  have hdescent : baseEnd_1597190 < baseStart_1597190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597227 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 8, 3]
def baseStart_1597227 : Nat := 118140960795 + 1597227 * 2 ^ 59
def prefixEnd_1597227 : Nat := 4983230072969 + 3 ^ 40 * 1597227 * 2
def baseEnd_1597227 : Nat := 546763443559285050477995

theorem tailTrace_1597227 : CollatzResearch.WordTrace tailWord_1597227 prefixEnd_1597227 546763443559285050477995 := by
  unfold tailWord_1597227
  simp only [CollatzResearch.WordTrace]
  refine ⟨58255654584526838499213935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38837103056351225666142623 58255654584526838499213935)
  ·
    refine ⟨87383481876790257748820903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58255654584526838499213935 87383481876790257748820903)
    ·
      refine ⟨131075222815185386623231355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87383481876790257748820903 131075222815185386623231355)
      ·
        refine ⟨196612834222778079934847033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131075222815185386623231355 196612834222778079934847033)
        ·
          refine ⟨147459625667083559951135275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196612834222778079934847033 147459625667083559951135275)
          ·
            refine ⟨221189438500625339926702913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147459625667083559951135275 221189438500625339926702913)
            ·
              refine ⟨165892078875469004945027185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221189438500625339926702913 165892078875469004945027185)
              ·
                refine ⟨124419059156601753708770389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165892078875469004945027185 124419059156601753708770389)
                ·
                  refine ⟨1458035849491426801274653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 124419059156601753708770389 1458035849491426801274653)
                  ·
                    refine ⟨546763443559285050477995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1458035849491426801274653 546763443559285050477995)
                    ·
                      rfl

theorem cell22_1597227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 8, 3].length) (baseStart_1597227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1597227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1597227 prefixEnd_1597227 := by exact prefixLift 1597227
  have htrace : WordTrace (prefixWord ++ tailWord_1597227) baseStart_1597227 baseEnd_1597227 := by
    simpa [prefixWord, tailWord_1597227, baseEnd_1597227] using wordTrace_append hprefix tailTrace_1597227
  have hstable : (prefixWord ++ tailWord_1597227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597227).length < 2 ^ (prefixWord ++ tailWord_1597227).sum := by decide
  have hdescent : baseEnd_1597227 < baseStart_1597227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597261 : List Nat := [1, 6, 1, 2, 1, 2, 1, 2, 1, 5]
def baseStart_1597261 : Nat := 118140960795 + 1597261 * 2 ^ 59
def prefixEnd_1597261 : Nat := 4983230072969 + 3 ^ 40 * 1597261 * 2
def baseEnd_1597261 : Nat := 546775082454120295127891

theorem tailTrace_1597261 : CollatzResearch.WordTrace tailWord_1597261 prefixEnd_1597261 546775082454120295127891 := by
  unfold tailWord_1597261
  simp only [CollatzResearch.WordTrace]
  refine ⟨58256894666403662305951637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38837929777602441537301091 58256894666403662305951637)
  ·
    refine ⟨2730791937487671670591483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 58256894666403662305951637 2730791937487671670591483)
    ·
      refine ⟨4096187906231507505887225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2730791937487671670591483 4096187906231507505887225)
      ·
        refine ⟨3072140929673630629415419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4096187906231507505887225 3072140929673630629415419)
        ·
          refine ⟨4608211394510445944123129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3072140929673630629415419 4608211394510445944123129)
          ·
            refine ⟨3456158545882834458092347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4608211394510445944123129 3456158545882834458092347)
            ·
              refine ⟨5184237818824251687138521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3456158545882834458092347 5184237818824251687138521)
              ·
                refine ⟨3888178364118188765353891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5184237818824251687138521 3888178364118188765353891)
                ·
                  refine ⟨5832267546177283148030837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3888178364118188765353891 5832267546177283148030837)
                  ·
                    refine ⟨546775082454120295127891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5832267546177283148030837 546775082454120295127891)
                    ·
                      rfl

theorem cell22_1597261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_1597261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1597261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1597261 prefixEnd_1597261 := by exact prefixLift 1597261
  have htrace : WordTrace (prefixWord ++ tailWord_1597261) baseStart_1597261 baseEnd_1597261 := by
    simpa [prefixWord, tailWord_1597261, baseEnd_1597261] using wordTrace_append hprefix tailTrace_1597261
  have hstable : (prefixWord ++ tailWord_1597261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597261).length < 2 ^ (prefixWord ++ tailWord_1597261).sum := by decide
  have hdescent : baseEnd_1597261 < baseStart_1597261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
