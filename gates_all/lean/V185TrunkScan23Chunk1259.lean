import V185TrunkScan23Chunk1258

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7456887 : List Nat := [1, 1, 3, 1, 1, 5, 1, 1, 5, 2, 2]
def baseStart_7456887 : Nat := 118140960795 + 7456887 * 2 ^ 59
def prefixEnd_7456887 : Nat := 4983230072969 + 3 ^ 40 * 7456887 * 2
def baseEnd_7456887 : Nat := 3828967217263471629018907

theorem tailTrace_7456887 : CollatzResearch.WordTrace tailWord_7456887 prefixEnd_7456887 3828967217263471629018907 := by
  unfold tailWord_7456887
  simp only [CollatzResearch.WordTrace]
  refine ⟨271975012535979408753416915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181316675023986272502277943 271975012535979408753416915)
  ·
    refine ⟨407962518803969113130125373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271975012535979408753416915 407962518803969113130125373)
    ·
      refine ⟨152985944551488417423797015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 407962518803969113130125373 152985944551488417423797015)
      ·
        refine ⟨229478916827232626135695523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152985944551488417423797015 229478916827232626135695523)
        ·
          refine ⟨344218375240848939203543285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229478916827232626135695523 344218375240848939203543285)
          ·
            refine ⟨32270472678829588050332183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 344218375240848939203543285 32270472678829588050332183)
            ·
              refine ⟨48405709018244382075498275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32270472678829588050332183 48405709018244382075498275)
              ·
                refine ⟨72608563527366573113247413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48405709018244382075498275 72608563527366573113247413)
                ·
                  refine ⟨6807052830690616229366945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72608563527366573113247413 6807052830690616229366945)
                  ·
                    refine ⟨5105289623017962172025209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6807052830690616229366945 5105289623017962172025209)
                    ·
                      refine ⟨3828967217263471629018907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5105289623017962172025209 3828967217263471629018907)
                      ·
                        rfl

theorem cell23_7456887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 5, 2, 2].length) (baseStart_7456887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456887 prefixEnd_7456887 := by exact prefixLift 7456887
  have htrace : WordTrace (prefixWord ++ tailWord_7456887) baseStart_7456887 baseEnd_7456887 := by
    simpa [prefixWord, tailWord_7456887, baseEnd_7456887] using wordTrace_append hprefix tailTrace_7456887
  have hstable : (prefixWord ++ tailWord_7456887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456887).length < 2 ^ (prefixWord ++ tailWord_7456887).sum := by decide
  have hdescent : baseEnd_7456887 < baseStart_7456887 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456900 : List Nat := [2, 3, 2, 1, 2, 1, 1, 4, 1, 2, 4]
def baseStart_7456900 : Nat := 118140960795 + 7456900 * 2 ^ 59
def prefixEnd_7456900 : Nat := 4983230072969 + 3 ^ 40 * 7456900 * 2
def baseEnd_7456900 : Nat := 3828973892511980078156347

theorem tailTrace_7456900 : CollatzResearch.WordTrace tailWord_7456900 prefixEnd_7456900 3828973892511980078156347 := by
  unfold tailWord_7456900
  simp only [CollatzResearch.WordTrace]
  refine ⟨135987743342466155986820077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181316991123288207982426769 135987743342466155986820077)
  ·
    refine ⟨50995403753424808495057529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135987743342466155986820077 50995403753424808495057529)
    ·
      refine ⟨38246552815068606371293147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50995403753424808495057529 38246552815068606371293147)
      ·
        refine ⟨57369829222602909556939721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38246552815068606371293147 57369829222602909556939721)
        ·
          refine ⟨43027371916952182167704791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57369829222602909556939721 43027371916952182167704791)
          ·
            refine ⟨64541057875428273251557187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43027371916952182167704791 64541057875428273251557187)
            ·
              refine ⟨96811586813142409877335781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64541057875428273251557187 96811586813142409877335781)
              ·
                refine ⟨18152172527464201852000459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96811586813142409877335781 18152172527464201852000459)
                ·
                  refine ⟨27228258791196302778000689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18152172527464201852000459 27228258791196302778000689)
                  ·
                    refine ⟨20421194093397227083500517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27228258791196302778000689 20421194093397227083500517)
                    ·
                      refine ⟨3828973892511980078156347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20421194093397227083500517 3828973892511980078156347)
                      ·
                        rfl

theorem cell23_7456900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_7456900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456900 prefixEnd_7456900 := by exact prefixLift 7456900
  have htrace : WordTrace (prefixWord ++ tailWord_7456900) baseStart_7456900 baseEnd_7456900 := by
    simpa [prefixWord, tailWord_7456900, baseEnd_7456900] using wordTrace_append hprefix tailTrace_7456900
  have hstable : (prefixWord ++ tailWord_7456900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456900).length < 2 ^ (prefixWord ++ tailWord_7456900).sum := by decide
  have hdescent : baseEnd_7456900 < baseStart_7456900 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456904 : List Nat := [2, 1, 3, 4, 1, 1, 4, 1, 1, 1, 4]
def baseStart_7456904 : Nat := 118140960795 + 7456904 * 2 ^ 59
def prefixEnd_7456904 : Nat := 4983230072969 + 3 ^ 40 * 7456904 * 2
def baseEnd_7456904 : Nat := 3828975946434598062506329

theorem tailTrace_7456904 : CollatzResearch.WordTrace tailWord_7456904 prefixEnd_7456904 3828975946434598062506329 := by
  unfold tailWord_7456904
  simp only [CollatzResearch.WordTrace]
  refine ⟨135987816288458910328392883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181317088384611880437857177 135987816288458910328392883)
  ·
    refine ⟨203981724432688365492589325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135987816288458910328392883 203981724432688365492589325)
    ·
      refine ⟨76493146662258137059720997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203981724432688365492589325 76493146662258137059720997)
      ·
        refine ⟨14342464999173400698697687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76493146662258137059720997 14342464999173400698697687)
        ·
          refine ⟨21513697498760101048046531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14342464999173400698697687 21513697498760101048046531)
          ·
            refine ⟨32270546248140151572069797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21513697498760101048046531 32270546248140151572069797)
            ·
              refine ⟨6050727421526278419763087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32270546248140151572069797 6050727421526278419763087)
              ·
                refine ⟨9076091132289417629644631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6050727421526278419763087 9076091132289417629644631)
                ·
                  refine ⟨13614136698434126444466947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9076091132289417629644631 13614136698434126444466947)
                  ·
                    refine ⟨20421205047651189666700421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13614136698434126444466947 20421205047651189666700421)
                    ·
                      refine ⟨3828975946434598062506329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20421205047651189666700421 3828975946434598062506329)
                      ·
                        rfl

theorem cell23_7456904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_7456904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456904 prefixEnd_7456904 := by exact prefixLift 7456904
  have htrace : WordTrace (prefixWord ++ tailWord_7456904) baseStart_7456904 baseEnd_7456904 := by
    simpa [prefixWord, tailWord_7456904, baseEnd_7456904] using wordTrace_append hprefix tailTrace_7456904
  have hstable : (prefixWord ++ tailWord_7456904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456904).length < 2 ^ (prefixWord ++ tailWord_7456904).sum := by decide
  have hdescent : baseEnd_7456904 < baseStart_7456904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456910 : List Nat := [4, 1, 1, 3, 3, 1, 10]
def baseStart_7456910 : Nat := 118140960795 + 7456910 * 2 ^ 59
def prefixEnd_7456910 : Nat := 4983230072969 + 3 ^ 40 * 7456910 * 2
def baseEnd_7456910 : Nat := 47271346016278086901621

theorem tailTrace_7456910 : CollatzResearch.WordTrace tailWord_7456910 prefixEnd_7456910 47271346016278086901621 := by
  unfold tailWord_7456910
  simp only [CollatzResearch.WordTrace]
  refine ⟨33996981426862010460188023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181317234276597389121002789 33996981426862010460188023)
  ·
    refine ⟨50995472140293015690282035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33996981426862010460188023 50995472140293015690282035)
    ·
      refine ⟨76493208210439523535423053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50995472140293015690282035 76493208210439523535423053)
      ·
        refine ⟨28684953078914821325783645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76493208210439523535423053 28684953078914821325783645)
        ·
          refine ⟨10756857404593057997168867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28684953078914821325783645 10756857404593057997168867)
          ·
            refine ⟨16135286106889586995753301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10756857404593057997168867 16135286106889586995753301)
            ·
              refine ⟨47271346016278086901621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16135286106889586995753301 47271346016278086901621)
              ·
                rfl

theorem cell23_7456910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 10].length) (baseStart_7456910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456910 prefixEnd_7456910 := by exact prefixLift 7456910
  have htrace : WordTrace (prefixWord ++ tailWord_7456910) baseStart_7456910 baseEnd_7456910 := by
    simpa [prefixWord, tailWord_7456910, baseEnd_7456910] using wordTrace_append hprefix tailTrace_7456910
  have hstable : (prefixWord ++ tailWord_7456910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456910).length < 2 ^ (prefixWord ++ tailWord_7456910).sum := by decide
  have hdescent : baseEnd_7456910 < baseStart_7456910 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456988 : List Nat := [2, 2, 5, 2, 1, 1, 1, 3, 2, 1, 3]
def baseStart_7456988 : Nat := 118140960795 + 7456988 * 2 ^ 59
def prefixEnd_7456988 : Nat := 4983230072969 + 3 ^ 40 * 7456988 * 2
def baseEnd_7456988 : Nat := 3829019078809575733855943

theorem tailTrace_7456988 : CollatzResearch.WordTrace tailWord_7456988 prefixEnd_7456988 3829019078809575733855943 := by
  unfold tailWord_7456988
  simp only [CollatzResearch.WordTrace]
  refine ⟨135989348154306751501421809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181319130872409002001895745 135989348154306751501421809)
  ·
    refine ⟨101992011115730063626066357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135989348154306751501421809 101992011115730063626066357)
    ·
      refine ⟨9561751042099693464943721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101992011115730063626066357 9561751042099693464943721)
      ·
        refine ⟨7171313281574770098707791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9561751042099693464943721 7171313281574770098707791)
        ·
          refine ⟨10756969922362155148061687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7171313281574770098707791 10756969922362155148061687)
          ·
            refine ⟨16135454883543232722092531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10756969922362155148061687 16135454883543232722092531)
            ·
              refine ⟨24203182325314849083138797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16135454883543232722092531 24203182325314849083138797)
              ·
                refine ⟨9076193371993068406177049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24203182325314849083138797 9076193371993068406177049)
                ·
                  refine ⟨6807145028994801304632787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9076193371993068406177049 6807145028994801304632787)
                  ·
                    refine ⟨10210717543492201956949181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6807145028994801304632787 10210717543492201956949181)
                    ·
                      refine ⟨3829019078809575733855943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10210717543492201956949181 3829019078809575733855943)
                      ·
                        rfl

theorem cell23_7456988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_7456988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456988 prefixEnd_7456988 := by exact prefixLift 7456988
  have htrace : WordTrace (prefixWord ++ tailWord_7456988) baseStart_7456988 baseEnd_7456988 := by
    simpa [prefixWord, tailWord_7456988, baseEnd_7456988] using wordTrace_append hprefix tailTrace_7456988
  have hstable : (prefixWord ++ tailWord_7456988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456988).length < 2 ^ (prefixWord ++ tailWord_7456988).sum := by decide
  have hdescent : baseEnd_7456988 < baseStart_7456988 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7457028 : List Nat := [2, 3, 2, 2, 3, 1, 2, 2, 2, 2, 2]
def baseStart_7457028 : Nat := 118140960795 + 7457028 * 2 ^ 59
def prefixEnd_7457028 : Nat := 4983230072969 + 3 ^ 40 * 7457028 * 2
def baseEnd_7457028 : Nat := 3829039618035755577355759

theorem tailTrace_7457028 : CollatzResearch.WordTrace tailWord_7457028 prefixEnd_7457028 3829039618035755577355759 := by
  unfold tailWord_7457028
  simp only [CollatzResearch.WordTrace]
  refine ⟨135990077614234294917149869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181320103485645726556199825 135990077614234294917149869)
  ·
    refine ⟨50996279105337860593931201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135990077614234294917149869 50996279105337860593931201)
    ·
      refine ⟨38247209329003395445448401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50996279105337860593931201 38247209329003395445448401)
      ·
        refine ⟨28685406996752546584086301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38247209329003395445448401 28685406996752546584086301)
        ·
          refine ⟨10757027623782204969032363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28685406996752546584086301 10757027623782204969032363)
          ·
            refine ⟨16135541435673307453548545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10757027623782204969032363 16135541435673307453548545)
            ·
              refine ⟨12101656076754980590161409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16135541435673307453548545 12101656076754980590161409)
              ·
                refine ⟨9076242057566235442621057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12101656076754980590161409 9076242057566235442621057)
                ·
                  refine ⟨6807181543174676581965793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9076242057566235442621057 6807181543174676581965793)
                  ·
                    refine ⟨5105386157381007436474345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6807181543174676581965793 5105386157381007436474345)
                    ·
                      refine ⟨3829039618035755577355759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5105386157381007436474345 3829039618035755577355759)
                      ·
                        rfl

theorem cell23_7457028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_7457028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7457028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7457028 prefixEnd_7457028 := by exact prefixLift 7457028
  have htrace : WordTrace (prefixWord ++ tailWord_7457028) baseStart_7457028 baseEnd_7457028 := by
    simpa [prefixWord, tailWord_7457028, baseEnd_7457028] using wordTrace_append hprefix tailTrace_7457028
  have hstable : (prefixWord ++ tailWord_7457028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7457028).length < 2 ^ (prefixWord ++ tailWord_7457028).sum := by decide
  have hdescent : baseEnd_7457028 < baseStart_7457028 := by decide
  rcases family_descends (prefixWord ++ tailWord_7457028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7457034 : List Nat := [3, 1, 2, 2, 1, 1, 6, 2, 5]
def baseStart_7457034 : Nat := 118140960795 + 7457034 * 2 ^ 59
def prefixEnd_7457034 : Nat := 4983230072969 + 3 ^ 40 * 7457034 * 2
def baseEnd_7457034 : Nat := 425449188768853617097859

theorem tailTrace_7457034 : CollatzResearch.WordTrace tailWord_7457034 prefixEnd_7457034 425449188768853617097859 := by
  unfold tailWord_7457034
  simp only [CollatzResearch.WordTrace]
  refine ⟨67995093516611713214754539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181320249377631235239345437 67995093516611713214754539)
  ·
    refine ⟨101992640274917569822131809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67995093516611713214754539 101992640274917569822131809)
    ·
      refine ⟨76494480206188177366598857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101992640274917569822131809 76494480206188177366598857)
      ·
        refine ⟨57370860154641133024949143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76494480206188177366598857 57370860154641133024949143)
        ·
          refine ⟨86056290231961699537423715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57370860154641133024949143 86056290231961699537423715)
          ·
            refine ⟨129084435347942549306135573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86056290231961699537423715 129084435347942549306135573)
            ·
              refine ⟨6050832906934806998725105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 129084435347942549306135573 6050832906934806998725105)
              ·
                refine ⟨4538124680201105249043829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6050832906934806998725105 4538124680201105249043829)
                ·
                  refine ⟨425449188768853617097859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4538124680201105249043829 425449188768853617097859)
                  ·
                    rfl

theorem cell23_7457034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 2, 5].length) (baseStart_7457034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7457034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7457034 prefixEnd_7457034 := by exact prefixLift 7457034
  have htrace : WordTrace (prefixWord ++ tailWord_7457034) baseStart_7457034 baseEnd_7457034 := by
    simpa [prefixWord, tailWord_7457034, baseEnd_7457034] using wordTrace_append hprefix tailTrace_7457034
  have hstable : (prefixWord ++ tailWord_7457034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7457034).length < 2 ^ (prefixWord ++ tailWord_7457034).sum := by decide
  have hdescent : baseEnd_7457034 < baseStart_7457034 := by decide
  rcases family_descends (prefixWord ++ tailWord_7457034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7457077 : List Nat := [1, 3, 3, 1, 2, 1, 1, 2, 5, 4]
def baseStart_7457077 : Nat := 118140960795 + 7457077 * 2 ^ 59
def prefixEnd_7457077 : Nat := 4983230072969 + 3 ^ 40 * 7457077 * 2
def baseEnd_7457077 : Nat := 1276354926195941961881011

theorem tailTrace_7457077 : CollatzResearch.WordTrace tailWord_7457077 prefixEnd_7457077 1276354926195941961881011 := by
  unfold tailWord_7457077
  simp only [CollatzResearch.WordTrace]
  refine ⟨271981942405291071202833485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181321294936860714135222323 271981942405291071202833485)
  ·
    refine ⟨101993228401984151701062557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271981942405291071202833485 101993228401984151701062557)
    ·
      refine ⟨38247460650744056887898459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101993228401984151701062557 38247460650744056887898459)
      ·
        refine ⟨57371190976116085331847689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38247460650744056887898459 57371190976116085331847689)
        ·
          refine ⟨43028393232087063998885767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57371190976116085331847689 43028393232087063998885767)
          ·
            refine ⟨64542589848130595998328651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43028393232087063998885767 64542589848130595998328651)
            ·
              refine ⟨96813884772195893997492977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64542589848130595998328651 96813884772195893997492977)
              ·
                refine ⟨72610413579146920498119733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96813884772195893997492977 72610413579146920498119733)
                ·
                  refine ⟨6807226273045023796698725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72610413579146920498119733 6807226273045023796698725)
                  ·
                    refine ⟨1276354926195941961881011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6807226273045023796698725 1276354926195941961881011)
                    ·
                      rfl

theorem cell23_7457077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_7457077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7457077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7457077 prefixEnd_7457077 := by exact prefixLift 7457077
  have htrace : WordTrace (prefixWord ++ tailWord_7457077) baseStart_7457077 baseEnd_7457077 := by
    simpa [prefixWord, tailWord_7457077, baseEnd_7457077] using wordTrace_append hprefix tailTrace_7457077
  have hstable : (prefixWord ++ tailWord_7457077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7457077).length < 2 ^ (prefixWord ++ tailWord_7457077).sum := by decide
  have hdescent : baseEnd_7457077 < baseStart_7457077 := by decide
  rcases family_descends (prefixWord ++ tailWord_7457077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7457080 : List Nat := [2, 1, 2, 1, 3, 1, 3, 1, 2, 1, 6]
def baseStart_7457080 : Nat := 118140960795 + 7457080 * 2 ^ 59
def prefixEnd_7457080 : Nat := 4983230072969 + 3 ^ 40 * 7457080 * 2
def baseEnd_7457080 : Nat := 3829066319029789373905519

theorem tailTrace_7457080 : CollatzResearch.WordTrace tailWord_7457080 prefixEnd_7457080 3829066319029789373905519 := by
  unfold tailWord_7457080
  simp only [CollatzResearch.WordTrace]
  refine ⟨135991025912140101357596347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181321367882853468476795129 135991025912140101357596347)
  ·
    refine ⟨203986538868210152036394521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135991025912140101357596347 203986538868210152036394521)
    ·
      refine ⟨152989904151157614027295891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203986538868210152036394521 152989904151157614027295891)
      ·
        refine ⟨229484856226736421040943837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152989904151157614027295891 229484856226736421040943837)
        ·
          refine ⟨86056821085026157890353939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229484856226736421040943837 86056821085026157890353939)
          ·
            refine ⟨129085231627539236835530909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86056821085026157890353939 129085231627539236835530909)
            ·
              refine ⟨48406961860327213813324091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129085231627539236835530909 48406961860327213813324091)
              ·
                refine ⟨72610442790490820719986137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48406961860327213813324091 72610442790490820719986137)
                ·
                  refine ⟨54457832092868115539989603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72610442790490820719986137 54457832092868115539989603)
                  ·
                    refine ⟨81686748139302173309984405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54457832092868115539989603 81686748139302173309984405)
                    ·
                      refine ⟨3829066319029789373905519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81686748139302173309984405 3829066319029789373905519)
                      ·
                        rfl

theorem cell23_7457080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 2, 1, 6].length) (baseStart_7457080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7457080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7457080 prefixEnd_7457080 := by exact prefixLift 7457080
  have htrace : WordTrace (prefixWord ++ tailWord_7457080) baseStart_7457080 baseEnd_7457080 := by
    simpa [prefixWord, tailWord_7457080, baseEnd_7457080] using wordTrace_append hprefix tailTrace_7457080
  have hstable : (prefixWord ++ tailWord_7457080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7457080).length < 2 ^ (prefixWord ++ tailWord_7457080).sum := by decide
  have hdescent : baseEnd_7457080 < baseStart_7457080 := by decide
  rcases family_descends (prefixWord ++ tailWord_7457080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7457087 : List Nat := [1, 1, 2, 2, 4, 1, 2, 1, 4, 2, 3]
def baseStart_7457087 : Nat := 118140960795 + 7457087 * 2 ^ 59
def prefixEnd_7457087 : Nat := 4983230072969 + 3 ^ 40 * 7457087 * 2
def baseEnd_7457087 : Nat := 3829069913394370846517987

theorem tailTrace_7457087 : CollatzResearch.WordTrace tailWord_7457087 prefixEnd_7457087 3829069913394370846517987 := by
  unfold tailWord_7457087
  simp only [CollatzResearch.WordTrace]
  refine ⟨271982307135254842910697515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181321538090169895273798343 271982307135254842910697515)
  ·
    refine ⟨407973460702882264366046273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271982307135254842910697515 407973460702882264366046273)
    ·
      refine ⟨305980095527161698274534705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 407973460702882264366046273 305980095527161698274534705)
      ·
        refine ⟨229485071645371273705901029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305980095527161698274534705 229485071645371273705901029)
        ·
          refine ⟨43028450933507113819856443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 229485071645371273705901029 43028450933507113819856443)
          ·
            refine ⟨64542676400260670729784665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43028450933507113819856443 64542676400260670729784665)
            ·
              refine ⟨48407007300195503047338499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64542676400260670729784665 48407007300195503047338499)
              ·
                refine ⟨72610510950293254571007749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48407007300195503047338499 72610510950293254571007749)
                ·
                  refine ⟨13614470803179985232063953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72610510950293254571007749 13614470803179985232063953)
                  ·
                    refine ⟨10210853102384988924047965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13614470803179985232063953 10210853102384988924047965)
                    ·
                      refine ⟨3829069913394370846517987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10210853102384988924047965 3829069913394370846517987)
                      ·
                        rfl

theorem cell23_7457087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 4, 2, 3].length) (baseStart_7457087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7457087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7457087 prefixEnd_7457087 := by exact prefixLift 7457087
  have htrace : WordTrace (prefixWord ++ tailWord_7457087) baseStart_7457087 baseEnd_7457087 := by
    simpa [prefixWord, tailWord_7457087, baseEnd_7457087] using wordTrace_append hprefix tailTrace_7457087
  have hstable : (prefixWord ++ tailWord_7457087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7457087).length < 2 ^ (prefixWord ++ tailWord_7457087).sum := by decide
  have hdescent : baseEnd_7457087 < baseStart_7457087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7457087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7457128 : List Nat := [2, 1, 4, 2, 2, 3, 1, 3, 1, 4]
def baseStart_7457128 : Nat := 118140960795 + 7457128 * 2 ^ 59
def prefixEnd_7457128 : Nat := 4983230072969 + 3 ^ 40 * 7457128 * 2
def baseEnd_7457128 : Nat := 1276363655367068395368433

theorem tailTrace_7457128 : CollatzResearch.WordTrace tailWord_7457128 prefixEnd_7457128 1276363655367068395368433 := by
  unfold tailWord_7457128
  simp only [CollatzResearch.WordTrace]
  refine ⟨135991901264053153456470019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181322535018737537941960025 135991901264053153456470019)
  ·
    refine ⟨203987851896079730184705029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135991901264053153456470019 203987851896079730184705029)
    ·
      refine ⟨38247722230514949409632193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203987851896079730184705029 38247722230514949409632193)
      ·
        refine ⟨28685791672886212057224145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38247722230514949409632193 28685791672886212057224145)
        ·
          refine ⟨21514343754664659042918109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28685791672886212057224145 21514343754664659042918109)
          ·
            refine ⟨8067878907999247141094291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21514343754664659042918109 8067878907999247141094291)
            ·
              refine ⟨12101818361998870711641437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8067878907999247141094291 12101818361998870711641437)
              ·
                refine ⟨4538181885749576516865539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12101818361998870711641437 4538181885749576516865539)
                ·
                  refine ⟨6807272828624364775298309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4538181885749576516865539 6807272828624364775298309)
                  ·
                    refine ⟨1276363655367068395368433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6807272828624364775298309 1276363655367068395368433)
                    ·
                      rfl

theorem cell23_7457128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_7457128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7457128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7457128 prefixEnd_7457128 := by exact prefixLift 7457128
  have htrace : WordTrace (prefixWord ++ tailWord_7457128) baseStart_7457128 baseEnd_7457128 := by
    simpa [prefixWord, tailWord_7457128, baseEnd_7457128] using wordTrace_append hprefix tailTrace_7457128
  have hstable : (prefixWord ++ tailWord_7457128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7457128).length < 2 ^ (prefixWord ++ tailWord_7457128).sum := by decide
  have hdescent : baseEnd_7457128 < baseStart_7457128 := by decide
  rcases family_descends (prefixWord ++ tailWord_7457128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7457157 : List Nat := [1, 3, 1, 1, 3, 1, 1, 4, 3, 1, 4]
def baseStart_7457157 : Nat := 118140960795 + 7457157 * 2 ^ 59
def prefixEnd_7457157 : Nat := 4983230072969 + 3 ^ 40 * 7457157 * 2
def baseEnd_7457157 : Nat := 3829105857040185572642665

theorem tailTrace_7457157 : CollatzResearch.WordTrace tailWord_7457157 prefixEnd_7457157 3829105857040185572642665 := by
  unfold tailWord_7457157
  simp only [CollatzResearch.WordTrace]
  refine ⟨271984860245001244865745725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181323240163334163243830483 271984860245001244865745725)
  ·
    refine ⟨101994322591875466824654647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271984860245001244865745725 101994322591875466824654647)
    ·
      refine ⟨152991483887813200236981971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101994322591875466824654647 152991483887813200236981971)
      ·
        refine ⟨229487225831719800355472957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152991483887813200236981971 229487225831719800355472957)
        ·
          refine ⟨86057709686894925133302359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229487225831719800355472957 86057709686894925133302359)
          ·
            refine ⟨129086564530342387699953539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86057709686894925133302359 129086564530342387699953539)
            ·
              refine ⟨193629846795513581549930309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129086564530342387699953539 193629846795513581549930309)
              ·
                refine ⟨36305596274158796540611933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 193629846795513581549930309 36305596274158796540611933)
                ·
                  refine ⟨13614598602809548702729475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36305596274158796540611933 13614598602809548702729475)
                  ·
                    refine ⟨20421897904214323054094213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13614598602809548702729475 20421897904214323054094213)
                    ·
                      refine ⟨3829105857040185572642665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20421897904214323054094213 3829105857040185572642665)
                      ·
                        rfl

theorem cell23_7457157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 3, 1, 4].length) (baseStart_7457157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7457157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7457157 prefixEnd_7457157 := by exact prefixLift 7457157
  have htrace : WordTrace (prefixWord ++ tailWord_7457157) baseStart_7457157 baseEnd_7457157 := by
    simpa [prefixWord, tailWord_7457157, baseEnd_7457157] using wordTrace_append hprefix tailTrace_7457157
  have hstable : (prefixWord ++ tailWord_7457157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7457157).length < 2 ^ (prefixWord ++ tailWord_7457157).sum := by decide
  have hdescent : baseEnd_7457157 < baseStart_7457157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7457157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7457187 : List Nat := [1, 1, 1, 4, 1, 4, 1, 1, 3, 2, 4]
def baseStart_7457187 : Nat := 118140960795 + 7457187 * 2 ^ 59
def prefixEnd_7457187 : Nat := 4983230072969 + 3 ^ 40 * 7457187 * 2
def baseEnd_7457187 : Nat := 3829121261459820455267527

theorem tailTrace_7457187 : CollatzResearch.WordTrace tailWord_7457187 prefixEnd_7457187 3829121261459820455267527 := by
  unfold tailWord_7457187
  simp only [CollatzResearch.WordTrace]
  refine ⟨271985954434892559989337815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181323969623261706659558543 271985954434892559989337815)
  ·
    refine ⟨407978931652338839984006723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271985954434892559989337815 407978931652338839984006723)
    ·
      refine ⟨611968397478508259976010085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407978931652338839984006723 611968397478508259976010085)
      ·
        refine ⟨114744074527220298745501891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 611968397478508259976010085 114744074527220298745501891)
        ·
          refine ⟨172116111790830448118252837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114744074527220298745501891 172116111790830448118252837)
          ·
            refine ⟨32271770960780709022172407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172116111790830448118252837 32271770960780709022172407)
            ·
              refine ⟨48407656441171063533258611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32271770960780709022172407 48407656441171063533258611)
              ·
                refine ⟨72611484661756595299887917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48407656441171063533258611 72611484661756595299887917)
                ·
                  refine ⟨27229306748158723237457969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72611484661756595299887917 27229306748158723237457969)
                  ·
                    refine ⟨20421980061119042428093477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27229306748158723237457969 20421980061119042428093477)
                    ·
                      refine ⟨3829121261459820455267527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20421980061119042428093477 3829121261459820455267527)
                      ·
                        rfl

theorem cell23_7457187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_7457187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7457187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7457187 prefixEnd_7457187 := by exact prefixLift 7457187
  have htrace : WordTrace (prefixWord ++ tailWord_7457187) baseStart_7457187 baseEnd_7457187 := by
    simpa [prefixWord, tailWord_7457187, baseEnd_7457187] using wordTrace_append hprefix tailTrace_7457187
  have hstable : (prefixWord ++ tailWord_7457187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7457187).length < 2 ^ (prefixWord ++ tailWord_7457187).sum := by decide
  have hdescent : baseEnd_7457187 < baseStart_7457187 := by decide
  rcases family_descends (prefixWord ++ tailWord_7457187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7457197 : List Nat := [1, 5, 2, 2, 13]
def baseStart_7457197 : Nat := 118140960795 + 7457197 * 2 ^ 59
def prefixEnd_7457197 : Nat := 4983230072969 + 3 ^ 40 * 7457197 * 2
def baseEnd_7457197 : Nat := 5252573931778279034489

theorem tailTrace_7457197 : CollatzResearch.WordTrace tailWord_7457197 prefixEnd_7457197 5252573931778279034489 := by
  unfold tailWord_7457197
  simp only [CollatzResearch.WordTrace]
  refine ⟨271986319164856331697201845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181324212776570887798134563 271986319164856331697201845)
  ·
    refine ⟨25498717421705281096612673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 271986319164856331697201845 25498717421705281096612673)
    ·
      refine ⟨19124038066278960822459505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25498717421705281096612673 19124038066278960822459505)
      ·
        refine ⟨14343028549709220616844629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19124038066278960822459505 14343028549709220616844629)
        ·
          refine ⟨5252573931778279034489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 14343028549709220616844629 5252573931778279034489)
          ·
            rfl

theorem cell23_7457197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 13].length) (baseStart_7457197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7457197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7457197 prefixEnd_7457197 := by exact prefixLift 7457197
  have htrace : WordTrace (prefixWord ++ tailWord_7457197) baseStart_7457197 baseEnd_7457197 := by
    simpa [prefixWord, tailWord_7457197, baseEnd_7457197] using wordTrace_append hprefix tailTrace_7457197
  have hstable : (prefixWord ++ tailWord_7457197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7457197).length < 2 ^ (prefixWord ++ tailWord_7457197).sum := by decide
  have hdescent : baseEnd_7457197 < baseStart_7457197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7457197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7457201 : List Nat := [1, 2, 2, 4, 1, 3, 2, 2, 2, 4]
def baseStart_7457201 : Nat := 118140960795 + 7457201 * 2 ^ 59
def prefixEnd_7457201 : Nat := 4983230072969 + 3 ^ 40 * 7457201 * 2
def baseEnd_7457201 : Nat := 1276376150062994466830821

theorem tailTrace_7457201 : CollatzResearch.WordTrace tailWord_7457201 prefixEnd_7457201 1276376150062994466830821 := by
  unfold tailWord_7457201
  simp only [CollatzResearch.WordTrace]
  refine ⟨271986465056841840380347457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181324310037894560253564971 271986465056841840380347457)
  ·
    refine ⟨203989848792631380285260593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271986465056841840380347457 203989848792631380285260593)
    ·
      refine ⟨152992386594473535213945445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203989848792631380285260593 152992386594473535213945445)
      ·
        refine ⟨28686072486463787852614771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152992386594473535213945445 28686072486463787852614771)
        ·
          refine ⟨43029108729695681778922157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28686072486463787852614771 43029108729695681778922157)
          ·
            refine ⟨16135915773635880667095809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43029108729695681778922157 16135915773635880667095809)
            ·
              refine ⟨12101936830226910500321857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16135915773635880667095809 12101936830226910500321857)
              ·
                refine ⟨9076452622670182875241393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12101936830226910500321857 9076452622670182875241393)
                ·
                  refine ⟨6807339467002637156431045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9076452622670182875241393 6807339467002637156431045)
                  ·
                    refine ⟨1276376150062994466830821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6807339467002637156431045 1276376150062994466830821)
                    ·
                      rfl

theorem cell23_7457201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 2, 2, 4].length) (baseStart_7457201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7457201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7457201 prefixEnd_7457201 := by exact prefixLift 7457201
  have htrace : WordTrace (prefixWord ++ tailWord_7457201) baseStart_7457201 baseEnd_7457201 := by
    simpa [prefixWord, tailWord_7457201, baseEnd_7457201] using wordTrace_append hprefix tailTrace_7457201
  have hstable : (prefixWord ++ tailWord_7457201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7457201).length < 2 ^ (prefixWord ++ tailWord_7457201).sum := by decide
  have hdescent : baseEnd_7457201 < baseStart_7457201 := by decide
  rcases family_descends (prefixWord ++ tailWord_7457201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7457224 : List Nat := [2, 1, 3, 1, 3, 2, 1, 3, 1, 3, 3]
def baseStart_7457224 : Nat := 118140960795 + 7457224 * 2 ^ 59
def prefixEnd_7457224 : Nat := 4983230072969 + 3 ^ 40 * 7457224 * 2
def baseEnd_7457224 : Nat := 3829140260244036810504857

theorem tailTrace_7457224 : CollatzResearch.WordTrace tailWord_7457224 prefixEnd_7457224 3829140260244036810504857 := by
  unfold tailWord_7457224
  simp only [CollatzResearch.WordTrace]
  refine ⟨135993651967879257654217363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181324869290505676872289817 135993651967879257654217363)
  ·
    refine ⟨203990477951818886481326045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135993651967879257654217363 203990477951818886481326045)
    ·
      refine ⟨76496429231932082430497267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203990477951818886481326045 76496429231932082430497267)
      ·
        refine ⟨114744643847898123645745901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76496429231932082430497267 114744643847898123645745901)
        ·
          refine ⟨43029241442961796367154713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114744643847898123645745901 43029241442961796367154713)
          ·
            refine ⟨32271931082221347275366035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43029241442961796367154713 32271931082221347275366035)
            ·
              refine ⟨48407896623332020913049053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32271931082221347275366035 48407896623332020913049053)
              ·
                refine ⟨18152961233749507842393395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48407896623332020913049053 18152961233749507842393395)
                ·
                  refine ⟨27229441850624261763590093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18152961233749507842393395 27229441850624261763590093)
                  ·
                    refine ⟨10211040693984098161346285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27229441850624261763590093 10211040693984098161346285)
                    ·
                      refine ⟨3829140260244036810504857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10211040693984098161346285 3829140260244036810504857)
                      ·
                        rfl

theorem cell23_7457224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 1, 3, 3].length) (baseStart_7457224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7457224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7457224 prefixEnd_7457224 := by exact prefixLift 7457224
  have htrace : WordTrace (prefixWord ++ tailWord_7457224) baseStart_7457224 baseEnd_7457224 := by
    simpa [prefixWord, tailWord_7457224, baseEnd_7457224] using wordTrace_append hprefix tailTrace_7457224
  have hstable : (prefixWord ++ tailWord_7457224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7457224).length < 2 ^ (prefixWord ++ tailWord_7457224).sum := by decide
  have hdescent : baseEnd_7457224 < baseStart_7457224 := by decide
  rcases family_descends (prefixWord ++ tailWord_7457224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7457258 : List Nat := [3, 1, 3, 1, 3, 1, 3, 2, 2, 1, 3]
def baseStart_7457258 : Nat := 118140960795 + 7457258 * 2 ^ 59
def prefixEnd_7457258 : Nat := 4983230072969 + 3 ^ 40 * 7457258 * 2
def baseEnd_7457258 : Nat := 3829157718586289677479701

theorem tailTrace_7457258 : CollatzResearch.WordTrace tailWord_7457258 prefixEnd_7457258 3829157718586289677479701 := by
  unfold tailWord_7457258
  simp only [CollatzResearch.WordTrace]
  refine ⟨67997136004408834778793107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181325696011756892743448285 67997136004408834778793107)
  ·
    refine ⟨101995704006613252168189661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67997136004408834778793107 101995704006613252168189661)
    ·
      refine ⟨38248389002479969563071123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101995704006613252168189661 38248389002479969563071123)
      ·
        refine ⟨57372583503719954344606685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38248389002479969563071123 57372583503719954344606685)
        ·
          refine ⟨21514718813894982879227507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57372583503719954344606685 21514718813894982879227507)
          ·
            refine ⟨32272078220842474318841261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21514718813894982879227507 32272078220842474318841261)
            ·
              refine ⟨12102029332815927869565473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32272078220842474318841261 12102029332815927869565473)
              ·
                refine ⟨9076521999611945902174105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12102029332815927869565473 9076521999611945902174105)
                ·
                  refine ⟨6807391499708959426630579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9076521999611945902174105 6807391499708959426630579)
                  ·
                    refine ⟨10211087249563439139945869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6807391499708959426630579 10211087249563439139945869)
                    ·
                      refine ⟨3829157718586289677479701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10211087249563439139945869 3829157718586289677479701)
                      ·
                        rfl

theorem cell23_7457258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_7457258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7457258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7457258 prefixEnd_7457258 := by exact prefixLift 7457258
  have htrace : WordTrace (prefixWord ++ tailWord_7457258) baseStart_7457258 baseEnd_7457258 := by
    simpa [prefixWord, tailWord_7457258, baseEnd_7457258] using wordTrace_append hprefix tailTrace_7457258
  have hstable : (prefixWord ++ tailWord_7457258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7457258).length < 2 ^ (prefixWord ++ tailWord_7457258).sum := by decide
  have hdescent : baseEnd_7457258 < baseStart_7457258 := by decide
  rcases family_descends (prefixWord ++ tailWord_7457258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7457347 : List Nat := [1, 1, 1, 3, 1, 2, 1, 3, 2, 8]
def baseStart_7457347 : Nat := 118140960795 + 7457347 * 2 ^ 59
def prefixEnd_7457347 : Nat := 4983230072969 + 3 ^ 40 * 7457347 * 2
def baseEnd_7457347 : Nat := 1276401139454846609755597

theorem tailTrace_7457347 : CollatzResearch.WordTrace tailWord_7457347 prefixEnd_7457347 1276401139454846609755597 := by
  unfold tailWord_7457347
  simp only [CollatzResearch.WordTrace]
  refine ⟨271991790114312907315162295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181327860076208604876774863 271991790114312907315162295)
  ·
    refine ⟨407987685171469360972743443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271991790114312907315162295 407987685171469360972743443)
    ·
      refine ⟨611981527757204041459115165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407987685171469360972743443 611981527757204041459115165)
      ·
        refine ⟨229493072908951515547168187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 611981527757204041459115165 229493072908951515547168187)
        ·
          refine ⟨344239609363427273320752281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229493072908951515547168187 344239609363427273320752281)
          ·
            refine ⟨258179707022570454990564211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 344239609363427273320752281 258179707022570454990564211)
            ·
              refine ⟨387269560533855682485846317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258179707022570454990564211 387269560533855682485846317)
              ·
                refine ⟨145226085200195880932192369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 387269560533855682485846317 145226085200195880932192369)
                ·
                  refine ⟨108919563900146910699144277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145226085200195880932192369 108919563900146910699144277)
                  ·
                    refine ⟨1276401139454846609755597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 108919563900146910699144277 1276401139454846609755597)
                    ·
                      rfl

theorem cell23_7457347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 8].length) (baseStart_7457347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7457347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7457347 prefixEnd_7457347 := by exact prefixLift 7457347
  have htrace : WordTrace (prefixWord ++ tailWord_7457347) baseStart_7457347 baseEnd_7457347 := by
    simpa [prefixWord, tailWord_7457347, baseEnd_7457347] using wordTrace_append hprefix tailTrace_7457347
  have hstable : (prefixWord ++ tailWord_7457347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7457347).length < 2 ^ (prefixWord ++ tailWord_7457347).sum := by decide
  have hdescent : baseEnd_7457347 < baseStart_7457347 := by decide
  rcases family_descends (prefixWord ++ tailWord_7457347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7457351 : List Nat := [1, 1, 4, 1, 4, 2, 2, 1, 2, 5]
def baseStart_7457351 : Nat := 118140960795 + 7457351 * 2 ^ 59
def prefixEnd_7457351 : Nat := 4983230072969 + 3 ^ 40 * 7457351 * 2
def baseEnd_7457351 : Nat := 1276401824095719271205591

theorem tailTrace_7457351 : CollatzResearch.WordTrace tailWord_7457351 prefixEnd_7457351 1276401824095719271205591 := by
  unfold tailWord_7457351
  simp only [CollatzResearch.WordTrace]
  refine ⟨271991936006298415998307907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181327957337532277332205271 271991936006298415998307907)
  ·
    refine ⟨407987904009447623997461861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271991936006298415998307907 407987904009447623997461861)
    ·
      refine ⟨76497732001771429499524099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 407987904009447623997461861 76497732001771429499524099)
      ·
        refine ⟨114746598002657144249286149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76497732001771429499524099 114746598002657144249286149)
        ·
          refine ⟨21514987125498214546741153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114746598002657144249286149 21514987125498214546741153)
          ·
            refine ⟨16136240344123660910055865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21514987125498214546741153 16136240344123660910055865)
            ·
              refine ⟨12102180258092745682541899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16136240344123660910055865 12102180258092745682541899)
              ·
                refine ⟨18153270387139118523812849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12102180258092745682541899 18153270387139118523812849)
                ·
                  refine ⟨13614952790354338892859637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18153270387139118523812849 13614952790354338892859637)
                  ·
                    refine ⟨1276401824095719271205591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13614952790354338892859637 1276401824095719271205591)
                    ·
                      rfl

theorem cell23_7457351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 2, 5].length) (baseStart_7457351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7457351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7457351 prefixEnd_7457351 := by exact prefixLift 7457351
  have htrace : WordTrace (prefixWord ++ tailWord_7457351) baseStart_7457351 baseEnd_7457351 := by
    simpa [prefixWord, tailWord_7457351, baseEnd_7457351] using wordTrace_append hprefix tailTrace_7457351
  have hstable : (prefixWord ++ tailWord_7457351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7457351).length < 2 ^ (prefixWord ++ tailWord_7457351).sum := by decide
  have hdescent : baseEnd_7457351 < baseStart_7457351 := by decide
  rcases family_descends (prefixWord ++ tailWord_7457351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7457372 : List Nat := [2, 2, 4, 1, 4, 1, 2, 2, 5]
def baseStart_7457372 : Nat := 118140960795 + 7457372 * 2 ^ 59
def prefixEnd_7457372 : Nat := 4983230072969 + 3 ^ 40 * 7457372 * 2
def baseEnd_7457372 : Nat := 425468472820100247939353

theorem tailTrace_7457372 : CollatzResearch.WordTrace tailWord_7457372 prefixEnd_7457372 425468472820100247939353 := by
  unfold tailWord_7457372
  simp only [CollatzResearch.WordTrace]
  refine ⟨135996350969611168292411185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181328467959481557723214913 135996350969611168292411185)
  ·
    refine ⟨101997263227208376219308389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135996350969611168292411185 101997263227208376219308389)
    ·
      refine ⟨19124486855101570541120323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101997263227208376219308389 19124486855101570541120323)
      ·
        refine ⟨28686730282652355811680485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19124486855101570541120323 28686730282652355811680485)
        ·
          refine ⟨5378761927997316714690091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28686730282652355811680485 5378761927997316714690091)
          ·
            refine ⟨8068142891995975072035137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5378761927997316714690091 8068142891995975072035137)
            ·
              refine ⟨6051107168996981304026353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8068142891995975072035137 6051107168996981304026353)
              ·
                refine ⟨4538330376747735978019765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6051107168996981304026353 4538330376747735978019765)
                ·
                  refine ⟨425468472820100247939353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4538330376747735978019765 425468472820100247939353)
                  ·
                    rfl

theorem cell23_7457372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 2, 5].length) (baseStart_7457372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7457372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7457372 prefixEnd_7457372 := by exact prefixLift 7457372
  have htrace : WordTrace (prefixWord ++ tailWord_7457372) baseStart_7457372 baseEnd_7457372 := by
    simpa [prefixWord, tailWord_7457372, baseEnd_7457372] using wordTrace_append hprefix tailTrace_7457372
  have hstable : (prefixWord ++ tailWord_7457372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7457372).length < 2 ^ (prefixWord ++ tailWord_7457372).sum := by decide
  have hdescent : baseEnd_7457372 < baseStart_7457372 := by decide
  rcases family_descends (prefixWord ++ tailWord_7457372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7457405 : List Nat := [1, 4, 1, 1, 6, 1, 1, 1, 2, 1, 4]
def baseStart_7457405 : Nat := 118140960795 + 7457405 * 2 ^ 59
def prefixEnd_7457405 : Nat := 4983230072969 + 3 ^ 40 * 7457405 * 2
def baseEnd_7457405 : Nat := 3829233200242500602341525

theorem tailTrace_7457405 : CollatzResearch.WordTrace tailWord_7457405 prefixEnd_7457405 3829233200242500602341525 := by
  unfold tailWord_7457405
  simp only [CollatzResearch.WordTrace]
  refine ⟨271993905548102783220773669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181329270365401855480515779 271993905548102783220773669)
  ·
    refine ⟨50998857290269271853895063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 271993905548102783220773669 50998857290269271853895063)
    ·
      refine ⟨76498285935403907780842595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50998857290269271853895063 76498285935403907780842595)
      ·
        refine ⟨114747428903105861671263893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76498285935403907780842595 114747428903105861671263893)
        ·
          refine ⟨5378785729833087265840495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 114747428903105861671263893 5378785729833087265840495)
          ·
            refine ⟨8068178594749630898760743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5378785729833087265840495 8068178594749630898760743)
            ·
              refine ⟨12102267892124446348141115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8068178594749630898760743 12102267892124446348141115)
              ·
                refine ⟨18153401838186669522211673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12102267892124446348141115 18153401838186669522211673)
                ·
                  refine ⟨13615051378640002141658755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18153401838186669522211673 13615051378640002141658755)
                  ·
                    refine ⟨20422577067960003212488133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13615051378640002141658755 20422577067960003212488133)
                    ·
                      refine ⟨3829233200242500602341525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20422577067960003212488133 3829233200242500602341525)
                      ·
                        rfl

theorem cell23_7457405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 2, 1, 4].length) (baseStart_7457405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7457405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7457405 prefixEnd_7457405 := by exact prefixLift 7457405
  have htrace : WordTrace (prefixWord ++ tailWord_7457405) baseStart_7457405 baseEnd_7457405 := by
    simpa [prefixWord, tailWord_7457405, baseEnd_7457405] using wordTrace_append hprefix tailTrace_7457405
  have hstable : (prefixWord ++ tailWord_7457405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7457405).length < 2 ^ (prefixWord ++ tailWord_7457405).sum := by decide
  have hdescent : baseEnd_7457405 < baseStart_7457405 := by decide
  rcases family_descends (prefixWord ++ tailWord_7457405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7457408 : List Nat := [2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 3]
def baseStart_7457408 : Nat := 118140960795 + 7457408 * 2 ^ 59
def prefixEnd_7457408 : Nat := 4983230072969 + 3 ^ 40 * 7457408 * 2
def baseEnd_7457408 : Nat := 3829234740684464090604011

theorem tailTrace_7457408 : CollatzResearch.WordTrace tailWord_7457408 prefixEnd_7457408 3829234740684464090604011 := by
  unfold tailWord_7457408
  simp only [CollatzResearch.WordTrace]
  refine ⟨135997007483545957366566439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181329343311394609822088585 135997007483545957366566439)
  ·
    refine ⟨203995511225318936049849659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135997007483545957366566439 203995511225318936049849659)
    ·
      refine ⟨305993266837978404074774489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203995511225318936049849659 305993266837978404074774489)
      ·
        refine ⟨229494950128483803056080867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305993266837978404074774489 229494950128483803056080867)
        ·
          refine ⟨344242425192725704584121301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229494950128483803056080867 344242425192725704584121301)
          ·
            refine ⟨8068181840454508701190343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 344242425192725704584121301 8068181840454508701190343)
            ·
              refine ⟨12102272760681763051785515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8068181840454508701190343 12102272760681763051785515)
              ·
                refine ⟨18153409141022644577678273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12102272760681763051785515 18153409141022644577678273)
                ·
                  refine ⟨13615056855766983433258705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18153409141022644577678273 13615056855766983433258705)
                  ·
                    refine ⟨10211292641825237574944029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13615056855766983433258705 10211292641825237574944029)
                    ·
                      refine ⟨3829234740684464090604011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10211292641825237574944029 3829234740684464090604011)
                      ·
                        rfl

theorem cell23_7457408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 3].length) (baseStart_7457408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7457408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7457408 prefixEnd_7457408 := by exact prefixLift 7457408
  have htrace : WordTrace (prefixWord ++ tailWord_7457408) baseStart_7457408 baseEnd_7457408 := by
    simpa [prefixWord, tailWord_7457408, baseEnd_7457408] using wordTrace_append hprefix tailTrace_7457408
  have hstable : (prefixWord ++ tailWord_7457408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7457408).length < 2 ^ (prefixWord ++ tailWord_7457408).sum := by decide
  have hdescent : baseEnd_7457408 < baseStart_7457408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7457408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7457428 : List Nat := [2, 4, 2, 2, 1, 1, 3, 2, 6]
def baseStart_7457428 : Nat := 118140960795 + 7457428 * 2 ^ 59
def prefixEnd_7457428 : Nat := 4983230072969 + 3 ^ 40 * 7457428 * 2
def baseEnd_7457428 : Nat := 425471667810839334705991

theorem tailTrace_7457428 : CollatzResearch.WordTrace tailWord_7457428 prefixEnd_7457428 425471667810839334705991 := by
  unfold tailWord_7457428
  simp only [CollatzResearch.WordTrace]
  refine ⟨135997372213509729074430469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181329829618012972099240625 135997372213509729074430469)
  ·
    refine ⟨25499507290033074201455713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135997372213509729074430469 25499507290033074201455713)
    ·
      refine ⟨19124630467524805651091785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25499507290033074201455713 19124630467524805651091785)
      ·
        refine ⟨14343472850643604238318839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19124630467524805651091785 14343472850643604238318839)
        ·
          refine ⟨21515209275965406357478259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14343472850643604238318839 21515209275965406357478259)
          ·
            refine ⟨32272813913948109536217389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21515209275965406357478259 32272813913948109536217389)
            ·
              refine ⟨12102305217730541076081521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32272813913948109536217389 12102305217730541076081521)
              ·
                refine ⟨9076728913297905807061141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12102305217730541076081521 9076728913297905807061141)
                ·
                  refine ⟨425471667810839334705991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9076728913297905807061141 425471667810839334705991)
                  ·
                    rfl

theorem cell23_7457428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 2, 6].length) (baseStart_7457428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7457428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7457428 prefixEnd_7457428 := by exact prefixLift 7457428
  have htrace : WordTrace (prefixWord ++ tailWord_7457428) baseStart_7457428 baseEnd_7457428 := by
    simpa [prefixWord, tailWord_7457428, baseEnd_7457428] using wordTrace_append hprefix tailTrace_7457428
  have hstable : (prefixWord ++ tailWord_7457428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7457428).length < 2 ^ (prefixWord ++ tailWord_7457428).sum := by decide
  have hdescent : baseEnd_7457428 < baseStart_7457428 := by decide
  rcases family_descends (prefixWord ++ tailWord_7457428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7457471 : List Nat := [1, 1, 2, 2, 2, 4, 1, 2, 4, 4]
def baseStart_7457471 : Nat := 118140960795 + 7457471 * 2 ^ 59
def prefixEnd_7457471 : Nat := 4983230072969 + 3 ^ 40 * 7457471 * 2
def baseEnd_7457471 : Nat := 1276422363321899114705407

theorem tailTrace_7457471 : CollatzResearch.WordTrace tailWord_7457471 prefixEnd_7457471 1276422363321899114705407 := by
  unfold tailWord_7457471
  simp only [CollatzResearch.WordTrace]
  refine ⟨271996312765863676492676267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181330875177242450995117511 271996312765863676492676267)
  ·
    refine ⟨407994469148795514739014401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271996312765863676492676267 407994469148795514739014401)
    ·
      refine ⟨305995851861596636054260801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 407994469148795514739014401 305995851861596636054260801)
      ·
        refine ⟨229496888896197477040695601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305995851861596636054260801 229496888896197477040695601)
        ·
          refine ⟨172122666672148107780521701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229496888896197477040695601 172122666672148107780521701)
          ·
            refine ⟨32273000001027770208847819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172122666672148107780521701 32273000001027770208847819)
            ·
              refine ⟨48409500001541655313271729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32273000001027770208847819 48409500001541655313271729)
              ·
                refine ⟨36307125001156241484953797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48409500001541655313271729 36307125001156241484953797)
                ·
                  refine ⟨6807585937716795278428837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36307125001156241484953797 6807585937716795278428837)
                  ·
                    refine ⟨1276422363321899114705407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6807585937716795278428837 1276422363321899114705407)
                    ·
                      rfl

theorem cell23_7457471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 4, 4].length) (baseStart_7457471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7457471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7457471 prefixEnd_7457471 := by exact prefixLift 7457471
  have htrace : WordTrace (prefixWord ++ tailWord_7457471) baseStart_7457471 baseEnd_7457471 := by
    simpa [prefixWord, tailWord_7457471, baseEnd_7457471] using wordTrace_append hprefix tailTrace_7457471
  have hstable : (prefixWord ++ tailWord_7457471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7457471).length < 2 ^ (prefixWord ++ tailWord_7457471).sum := by decide
  have hdescent : baseEnd_7457471 < baseStart_7457471 := by decide
  rcases family_descends (prefixWord ++ tailWord_7457471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7457472 : List Nat := [2, 1, 1, 2, 4, 4, 1, 3, 1, 1, 3]
def baseStart_7457472 : Nat := 118140960795 + 7457472 * 2 ^ 59
def prefixEnd_7457472 : Nat := 4983230072969 + 3 ^ 40 * 7457472 * 2
def baseEnd_7457472 : Nat := 3829267603446351840203717

theorem tailTrace_7457472 : CollatzResearch.WordTrace tailWord_7457472 prefixEnd_7457472 3829267603446351840203717 := by
  unfold tailWord_7457472
  simp only [CollatzResearch.WordTrace]
  refine ⟨135998174619430026831731335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181330899492573369108975113 135998174619430026831731335)
  ·
    refine ⟨203997261929145040247597003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135998174619430026831731335 203997261929145040247597003)
    ·
      refine ⟨305995892893717560371395505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203997261929145040247597003 305995892893717560371395505)
      ·
        refine ⟨229496919670288170278546629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305995892893717560371395505 229496919670288170278546629)
        ·
          refine ⟨43030672438179031927227493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 229496919670288170278546629 43030672438179031927227493)
          ·
            refine ⟨8068251082158568486355155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43030672438179031927227493 8068251082158568486355155)
            ·
              refine ⟨12102376623237852729532733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8068251082158568486355155 12102376623237852729532733)
              ·
                refine ⟨4538391233714194773574775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12102376623237852729532733 4538391233714194773574775)
                ·
                  refine ⟨6807586850571292160362163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4538391233714194773574775 6807586850571292160362163)
                  ·
                    refine ⟨10211380275856938240543245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6807586850571292160362163 10211380275856938240543245)
                    ·
                      refine ⟨3829267603446351840203717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10211380275856938240543245 3829267603446351840203717)
                      ·
                        rfl

theorem cell23_7457472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 3, 1, 1, 3].length) (baseStart_7457472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7457472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7457472 prefixEnd_7457472 := by exact prefixLift 7457472
  have htrace : WordTrace (prefixWord ++ tailWord_7457472) baseStart_7457472 baseEnd_7457472 := by
    simpa [prefixWord, tailWord_7457472, baseEnd_7457472] using wordTrace_append hprefix tailTrace_7457472
  have hstable : (prefixWord ++ tailWord_7457472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7457472).length < 2 ^ (prefixWord ++ tailWord_7457472).sum := by decide
  have hdescent : baseEnd_7457472 < baseStart_7457472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7457472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7457495 : List Nat := [1, 1, 3, 2, 1, 4, 3, 1, 3, 2, 2]
def baseStart_7457495 : Nat := 118140960795 + 7457495 * 2 ^ 59
def prefixEnd_7457495 : Nat := 4983230072969 + 3 ^ 40 * 7457495 * 2
def baseEnd_7457495 : Nat := 3829279413501405250216111

theorem tailTrace_7457495 : CollatzResearch.WordTrace tailWord_7457495 prefixEnd_7457495 3829279413501405250216111 := by
  unfold tailWord_7457495
  simp only [CollatzResearch.WordTrace]
  refine ⟨271997188117776728591549939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181331458745184485727699959 271997188117776728591549939)
  ·
    refine ⟨407995782176665092887324909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271997188117776728591549939 407995782176665092887324909)
    ·
      refine ⟨152998418316249409832746841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 407995782176665092887324909 152998418316249409832746841)
      ·
        refine ⟨114748813737187057374560131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152998418316249409832746841 114748813737187057374560131)
        ·
          refine ⟨172123220605780586061840197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114748813737187057374560131 172123220605780586061840197)
          ·
            refine ⟨32273103863583859886595037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172123220605780586061840197 32273103863583859886595037)
            ·
              refine ⟨12102413948843947457473139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32273103863583859886595037 12102413948843947457473139)
              ·
                refine ⟨18153620923265921186209709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12102413948843947457473139 18153620923265921186209709)
                ·
                  refine ⟨6807607846224720444828641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18153620923265921186209709 6807607846224720444828641)
                  ·
                    refine ⟨5105705884668540333621481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6807607846224720444828641 5105705884668540333621481)
                    ·
                      refine ⟨3829279413501405250216111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5105705884668540333621481 3829279413501405250216111)
                      ·
                        rfl

theorem cell23_7457495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 3, 2, 2].length) (baseStart_7457495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7457495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7457495 prefixEnd_7457495 := by exact prefixLift 7457495
  have htrace : WordTrace (prefixWord ++ tailWord_7457495) baseStart_7457495 baseEnd_7457495 := by
    simpa [prefixWord, tailWord_7457495, baseEnd_7457495] using wordTrace_append hprefix tailTrace_7457495
  have hstable : (prefixWord ++ tailWord_7457495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7457495).length < 2 ^ (prefixWord ++ tailWord_7457495).sum := by decide
  have hdescent : baseEnd_7457495 < baseStart_7457495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7457495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7457504 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 6]
def baseStart_7457504 : Nat := 118140960795 + 7457504 * 2 ^ 59
def prefixEnd_7457504 : Nat := 4983230072969 + 3 ^ 40 * 7457504 * 2
def baseEnd_7457504 : Nat := 3829284034827295715003569

theorem tailTrace_7457504 : CollatzResearch.WordTrace tailWord_7457504 prefixEnd_7457504 3829284034827295715003569 := by
  unfold tailWord_7457504
  simp only [CollatzResearch.WordTrace]
  refine ⟨135998758187372061564313783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181331677583162748752418377 135998758187372061564313783)
  ·
    refine ⟨203998137281058092346470675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135998758187372061564313783 203998137281058092346470675)
    ·
      refine ⟨305997205921587138519706013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203998137281058092346470675 305997205921587138519706013)
      ·
        refine ⟨114748952220595176944889755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 305997205921587138519706013 114748952220595176944889755)
        ·
          refine ⟨172123428330892765417334633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114748952220595176944889755 172123428330892765417334633)
          ·
            refine ⟨129092571248169574063000975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172123428330892765417334633 129092571248169574063000975)
            ·
              refine ⟨193638856872254361094501463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129092571248169574063000975 193638856872254361094501463)
              ·
                refine ⟨290458285308381541641752195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193638856872254361094501463 290458285308381541641752195)
                ·
                  refine ⟨435687427962572312462628293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 290458285308381541641752195 435687427962572312462628293)
                  ·
                    refine ⟨81691392742982308586742805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 435687427962572312462628293 81691392742982308586742805)
                    ·
                      refine ⟨3829284034827295715003569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81691392742982308586742805 3829284034827295715003569)
                      ·
                        rfl

theorem cell23_7457504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_7457504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7457504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7457504 prefixEnd_7457504 := by exact prefixLift 7457504
  have htrace : WordTrace (prefixWord ++ tailWord_7457504) baseStart_7457504 baseEnd_7457504 := by
    simpa [prefixWord, tailWord_7457504, baseEnd_7457504] using wordTrace_append hprefix tailTrace_7457504
  have hstable : (prefixWord ++ tailWord_7457504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7457504).length < 2 ^ (prefixWord ++ tailWord_7457504).sum := by decide
  have hdescent : baseEnd_7457504 < baseStart_7457504 := by decide
  rcases family_descends (prefixWord ++ tailWord_7457504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7457505 : List Nat := [1, 2, 3, 1, 4, 1, 4, 1, 2, 4]
def baseStart_7457505 : Nat := 118140960795 + 7457505 * 2 ^ 59
def prefixEnd_7457505 : Nat := 4983230072969 + 3 ^ 40 * 7457505 * 2
def baseEnd_7457505 : Nat := 1276428182769316737030355

theorem tailTrace_7457505 : CollatzResearch.WordTrace tailWord_7457505 prefixEnd_7457505 1276428182769316737030355 := by
  unfold tailWord_7457505
  simp only [CollatzResearch.WordTrace]
  refine ⟨271997552847740500299413969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181331701898493666866275979 271997552847740500299413969)
  ·
    refine ⟨203998164635805375224560477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271997552847740500299413969 203998164635805375224560477)
    ·
      refine ⟨76499311738427015709210179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203998164635805375224560477 76499311738427015709210179)
      ·
        refine ⟨114748967607640523563815269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76499311738427015709210179 114748967607640523563815269)
        ·
          refine ⟨21515431426432598168215363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114748967607640523563815269 21515431426432598168215363)
          ·
            refine ⟨32273147139648897252323045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21515431426432598168215363 32273147139648897252323045)
            ·
              refine ⟨6051215088684168234810571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32273147139648897252323045 6051215088684168234810571)
              ·
                refine ⟨9076822633026252352215857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6051215088684168234810571 9076822633026252352215857)
                ·
                  refine ⟨6807616974769689264161893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9076822633026252352215857 6807616974769689264161893)
                  ·
                    refine ⟨1276428182769316737030355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6807616974769689264161893 1276428182769316737030355)
                    ·
                      rfl

theorem cell23_7457505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 1, 2, 4].length) (baseStart_7457505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7457505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7457505 prefixEnd_7457505 := by exact prefixLift 7457505
  have htrace : WordTrace (prefixWord ++ tailWord_7457505) baseStart_7457505 baseEnd_7457505 := by
    simpa [prefixWord, tailWord_7457505, baseEnd_7457505] using wordTrace_append hprefix tailTrace_7457505
  have hstable : (prefixWord ++ tailWord_7457505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7457505).length < 2 ^ (prefixWord ++ tailWord_7457505).sum := by decide
  have hdescent : baseEnd_7457505 < baseStart_7457505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7457505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7457512 : List Nat := [2, 1, 4, 1, 5, 1, 1, 2, 1, 1, 4]
def baseStart_7457512 : Nat := 118140960795 + 7457512 * 2 ^ 59
def prefixEnd_7457512 : Nat := 4983230072969 + 3 ^ 40 * 7457512 * 2
def baseEnd_7457512 : Nat := 3829288142672531683703533

theorem tailTrace_7457512 : CollatzResearch.WordTrace tailWord_7457512 prefixEnd_7457512 3829288142672531683703533 := by
  unfold tailWord_7457512
  simp only [CollatzResearch.WordTrace]
  refine ⟨135998904079357570247459395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181331872105810093663279193 135998904079357570247459395)
  ·
    refine ⟨203998356119036355371189093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135998904079357570247459395 203998356119036355371189093)
    ·
      refine ⟨38249691772319316632097955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203998356119036355371189093 38249691772319316632097955)
      ·
        refine ⟨57374537658478974948146933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38249691772319316632097955 57374537658478974948146933)
        ·
          refine ⟨5378862905482403901388775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57374537658478974948146933 5378862905482403901388775)
          ·
            refine ⟨8068294358223605852083163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5378862905482403901388775 8068294358223605852083163)
            ·
              refine ⟨12102441537335408778124745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8068294358223605852083163 12102441537335408778124745)
              ·
                refine ⟨9076831153001556583593559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12102441537335408778124745 9076831153001556583593559)
                ·
                  refine ⟨13615246729502334875390339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9076831153001556583593559 13615246729502334875390339)
                  ·
                    refine ⟨20422870094253502313085509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13615246729502334875390339 20422870094253502313085509)
                    ·
                      refine ⟨3829288142672531683703533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20422870094253502313085509 3829288142672531683703533)
                      ·
                        rfl

theorem cell23_7457512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 2, 1, 1, 4].length) (baseStart_7457512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7457512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7457512 prefixEnd_7457512 := by exact prefixLift 7457512
  have htrace : WordTrace (prefixWord ++ tailWord_7457512) baseStart_7457512 baseEnd_7457512 := by
    simpa [prefixWord, tailWord_7457512, baseEnd_7457512] using wordTrace_append hprefix tailTrace_7457512
  have hstable : (prefixWord ++ tailWord_7457512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7457512).length < 2 ^ (prefixWord ++ tailWord_7457512).sum := by decide
  have hdescent : baseEnd_7457512 < baseStart_7457512 := by decide
  rcases family_descends (prefixWord ++ tailWord_7457512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7457571 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 4, 4, 3]
def baseStart_7457571 : Nat := 118140960795 + 7457571 * 2 ^ 59
def prefixEnd_7457571 : Nat := 4983230072969 + 3 ^ 40 * 7457571 * 2
def baseEnd_7457571 : Nat := 3829318438031146952865761

theorem tailTrace_7457571 : CollatzResearch.WordTrace tailWord_7457571 prefixEnd_7457571 3829318438031146952865761 := by
  unfold tailWord_7457571
  simp only [CollatzResearch.WordTrace]
  refine ⟨271999960065501393571316567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181333306710334262380877711 271999960065501393571316567)
  ·
    refine ⟨407999940098252090356974851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271999960065501393571316567 407999940098252090356974851)
    ·
      refine ⟨611999910147378135535462277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407999940098252090356974851 611999910147378135535462277)
      ·
        refine ⟨114749983152633400412899177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 611999910147378135535462277 114749983152633400412899177)
        ·
          refine ⟨86062487364475050309674383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114749983152633400412899177 86062487364475050309674383)
          ·
            refine ⟨129093731046712575464511575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86062487364475050309674383 129093731046712575464511575)
            ·
              refine ⟨193640596570068863196767363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129093731046712575464511575 193640596570068863196767363)
              ·
                refine ⟨290460894855103294795151045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193640596570068863196767363 290460894855103294795151045)
                ·
                  refine ⟨54461417785331867774090821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 290460894855103294795151045 54461417785331867774090821)
                  ·
                    refine ⟨10211515834749725207642029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54461417785331867774090821 10211515834749725207642029)
                    ·
                      refine ⟨3829318438031146952865761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10211515834749725207642029 3829318438031146952865761)
                      ·
                        rfl

theorem cell23_7457571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 4, 3].length) (baseStart_7457571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7457571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7457571 prefixEnd_7457571 := by exact prefixLift 7457571
  have htrace : WordTrace (prefixWord ++ tailWord_7457571) baseStart_7457571 baseEnd_7457571 := by
    simpa [prefixWord, tailWord_7457571, baseEnd_7457571] using wordTrace_append hprefix tailTrace_7457571
  have hstable : (prefixWord ++ tailWord_7457571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7457571).length < 2 ^ (prefixWord ++ tailWord_7457571).sum := by decide
  have hdescent : baseEnd_7457571 < baseStart_7457571 := by decide
  rcases family_descends (prefixWord ++ tailWord_7457571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7457585 : List Nat := [1, 2, 2, 3, 2, 1, 2, 2, 4, 2, 2]
def baseStart_7457585 : Nat := 118140960795 + 7457585 * 2 ^ 59
def prefixEnd_7457585 : Nat := 4983230072969 + 3 ^ 40 * 7457585 * 2
def baseEnd_7457585 : Nat := 3829325626760309898090697

theorem tailTrace_7457585 : CollatzResearch.WordTrace tailWord_7457585 prefixEnd_7457585 3829325626760309898090697 := by
  unfold tailWord_7457585
  simp only [CollatzResearch.WordTrace]
  refine ⟨272000470687450673962326209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181333647124967115974884139 272000470687450673962326209)
  ·
    refine ⟨204000353015588005471744657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272000470687450673962326209 204000353015588005471744657)
    ·
      refine ⟨153000264761691004103808493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204000353015588005471744657 153000264761691004103808493)
      ·
        refine ⟨57375099285634126538928185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153000264761691004103808493 57375099285634126538928185)
        ·
          refine ⟨43031324464225594904196139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57375099285634126538928185 43031324464225594904196139)
          ·
            refine ⟨64546986696338392356294209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43031324464225594904196139 64546986696338392356294209)
            ·
              refine ⟨48410240022253794267220657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64546986696338392356294209 48410240022253794267220657)
              ·
                refine ⟨36307680016690345700415493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48410240022253794267220657 36307680016690345700415493)
                ·
                  refine ⟨6807690003129439818827905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36307680016690345700415493 6807690003129439818827905)
                  ·
                    refine ⟨5105767502347079864120929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6807690003129439818827905 5105767502347079864120929)
                    ·
                      refine ⟨3829325626760309898090697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5105767502347079864120929 3829325626760309898090697)
                      ·
                        rfl

theorem cell23_7457585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 4, 2, 2].length) (baseStart_7457585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7457585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7457585 prefixEnd_7457585 := by exact prefixLift 7457585
  have htrace : WordTrace (prefixWord ++ tailWord_7457585) baseStart_7457585 baseEnd_7457585 := by
    simpa [prefixWord, tailWord_7457585, baseEnd_7457585] using wordTrace_append hprefix tailTrace_7457585
  have hstable : (prefixWord ++ tailWord_7457585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7457585).length < 2 ^ (prefixWord ++ tailWord_7457585).sum := by decide
  have hdescent : baseEnd_7457585 < baseStart_7457585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7457585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7457589 : List Nat := [1, 3, 3, 1, 3, 3, 2, 1, 1, 3, 2]
def baseStart_7457589 : Nat := 118140960795 + 7457589 * 2 ^ 59
def prefixEnd_7457589 : Nat := 4983230072969 + 3 ^ 40 * 7457589 * 2
def baseEnd_7457589 : Nat := 3829327680682927882440679

theorem tailTrace_7457589 : CollatzResearch.WordTrace tailWord_7457589 prefixEnd_7457589 3829327680682927882440679 := by
  unfold tailWord_7457589
  simp only [CollatzResearch.WordTrace]
  refine ⟨272000616579436182645471821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181333744386290788430314547 272000616579436182645471821)
  ·
    refine ⟨102000231217288568492051933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272000616579436182645471821 102000231217288568492051933)
    ·
      refine ⟨38250086706483213184519475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102000231217288568492051933 38250086706483213184519475)
      ·
        refine ⟨57375130059724819776779213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38250086706483213184519475 57375130059724819776779213)
        ·
          refine ⟨21515673772396807416292205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57375130059724819776779213 21515673772396807416292205)
          ·
            refine ⟨8068377664648802781109577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21515673772396807416292205 8068377664648802781109577)
            ·
              refine ⟨6051283248486602085832183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8068377664648802781109577 6051283248486602085832183)
              ·
                refine ⟨9076924872729903128748275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6051283248486602085832183 9076924872729903128748275)
                ·
                  refine ⟨13615387309094854693122413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9076924872729903128748275 13615387309094854693122413)
                  ·
                    refine ⟨5105770240910570509920905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13615387309094854693122413 5105770240910570509920905)
                    ·
                      refine ⟨3829327680682927882440679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5105770240910570509920905 3829327680682927882440679)
                      ·
                        rfl

theorem cell23_7457589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 1, 1, 3, 2].length) (baseStart_7457589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7457589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7457589 prefixEnd_7457589 := by exact prefixLift 7457589
  have htrace : WordTrace (prefixWord ++ tailWord_7457589) baseStart_7457589 baseEnd_7457589 := by
    simpa [prefixWord, tailWord_7457589, baseEnd_7457589] using wordTrace_append hprefix tailTrace_7457589
  have hstable : (prefixWord ++ tailWord_7457589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7457589).length < 2 ^ (prefixWord ++ tailWord_7457589).sum := by decide
  have hdescent : baseEnd_7457589 < baseStart_7457589 := by decide
  rcases family_descends (prefixWord ++ tailWord_7457589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7457608 : List Nat := [2, 1, 3, 1, 1, 3, 1, 6, 5]
def baseStart_7457608 : Nat := 118140960795 + 7457608 * 2 ^ 59
def prefixEnd_7457608 : Nat := 4983230072969 + 3 ^ 40 * 7457608 * 2
def baseEnd_7457608 : Nat := 425481937423929256455899

theorem tailTrace_7457608 : CollatzResearch.WordTrace tailWord_7457608 prefixEnd_7457608 425481937423929256455899 := by
  unfold tailWord_7457608
  simp only [CollatzResearch.WordTrace]
  refine ⟨136000654783183674445206739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181334206377578232593608985 136000654783183674445206739)
  ·
    refine ⟨204000982174775511667810109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136000654783183674445206739 204000982174775511667810109)
    ·
      refine ⟨76500368315540816875428791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204000982174775511667810109 76500368315540816875428791)
      ·
        refine ⟨114750552473311225313143187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76500368315540816875428791 114750552473311225313143187)
        ·
          refine ⟨172125828709966837969714781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114750552473311225313143187 172125828709966837969714781)
          ·
            refine ⟨64547185766237564238643043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172125828709966837969714781 64547185766237564238643043)
            ·
              refine ⟨96820778649356346357964565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64547185766237564238643043 96820778649356346357964565)
              ·
                refine ⟨4538473999188578735529589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 96820778649356346357964565 4538473999188578735529589)
                ·
                  refine ⟨425481937423929256455899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4538473999188578735529589 425481937423929256455899)
                  ·
                    rfl

theorem cell23_7457608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 6, 5].length) (baseStart_7457608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7457608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7457608 prefixEnd_7457608 := by exact prefixLift 7457608
  have htrace : WordTrace (prefixWord ++ tailWord_7457608) baseStart_7457608 baseEnd_7457608 := by
    simpa [prefixWord, tailWord_7457608, baseEnd_7457608] using wordTrace_append hprefix tailTrace_7457608
  have hstable : (prefixWord ++ tailWord_7457608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7457608).length < 2 ^ (prefixWord ++ tailWord_7457608).sum := by decide
  have hdescent : baseEnd_7457608 < baseStart_7457608 := by decide
  rcases family_descends (prefixWord ++ tailWord_7457608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7457618 : List Nat := [3, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3]
def baseStart_7457618 : Nat := 118140960795 + 7457618 * 2 ^ 59
def prefixEnd_7457618 : Nat := 4983230072969 + 3 ^ 40 * 7457618 * 2
def baseEnd_7457618 : Nat := 3829342571621908268978045

theorem tailTrace_7457618 : CollatzResearch.WordTrace tailWord_7457618 prefixEnd_7457618 3829342571621908268978045 := by
  unfold tailWord_7457618
  simp only [CollatzResearch.WordTrace]
  refine ⟨68000418574082780149569377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181334449530887413732185005 68000418574082780149569377)
  ·
    refine ⟨51000313930562085112177033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68000418574082780149569377 51000313930562085112177033)
    ·
      refine ⟨38250235447921563834132775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51000313930562085112177033 38250235447921563834132775)
      ·
        refine ⟨57375353171882345751199163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38250235447921563834132775 57375353171882345751199163)
        ·
          refine ⟨86063029757823518626798745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57375353171882345751199163 86063029757823518626798745)
          ·
            refine ⟨64547272318367638970099059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86063029757823518626798745 64547272318367638970099059)
            ·
              refine ⟨96820908477551458455148589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64547272318367638970099059 96820908477551458455148589)
              ·
                refine ⟨36307840679081796920680721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96820908477551458455148589 36307840679081796920680721)
                ·
                  refine ⟨27230880509311347690510541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36307840679081796920680721 27230880509311347690510541)
                  ·
                    refine ⟨10211580190991755383941453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27230880509311347690510541 10211580190991755383941453)
                    ·
                      refine ⟨3829342571621908268978045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10211580190991755383941453 3829342571621908268978045)
                      ·
                        rfl

theorem cell23_7457618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_7457618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7457618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7457618 prefixEnd_7457618 := by exact prefixLift 7457618
  have htrace : WordTrace (prefixWord ++ tailWord_7457618) baseStart_7457618 baseEnd_7457618 := by
    simpa [prefixWord, tailWord_7457618, baseEnd_7457618] using wordTrace_append hprefix tailTrace_7457618
  have hstable : (prefixWord ++ tailWord_7457618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7457618).length < 2 ^ (prefixWord ++ tailWord_7457618).sum := by decide
  have hdescent : baseEnd_7457618 < baseStart_7457618 := by decide
  rcases family_descends (prefixWord ++ tailWord_7457618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7457621 : List Nat := [1, 3, 2, 2, 2, 1, 1, 1, 3, 7]
def baseStart_7457621 : Nat := 118140960795 + 7457621 * 2 ^ 59
def prefixEnd_7457621 : Nat := 4983230072969 + 3 ^ 40 * 7457621 * 2
def baseEnd_7457621 : Nat := 1276448037354623919080177

theorem tailTrace_7457621 : CollatzResearch.WordTrace tailWord_7457621 prefixEnd_7457621 1276448037354623919080177 := by
  unfold tailWord_7457621
  simp only [CollatzResearch.WordTrace]
  refine ⟨272001783715320252110636717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181334522476880168073757811 272001783715320252110636717)
  ·
    refine ⟨102000668893245094541488769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272001783715320252110636717 102000668893245094541488769)
    ·
      refine ⟨76500501669933820906116577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102000668893245094541488769 76500501669933820906116577)
      ·
        refine ⟨57375376252450365679587433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76500501669933820906116577 57375376252450365679587433)
        ·
          refine ⟨43031532189337774259690575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57375376252450365679587433 43031532189337774259690575)
          ·
            refine ⟨64547298284006661389535863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43031532189337774259690575 64547298284006661389535863)
            ·
              refine ⟨96820947426009992084303795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64547298284006661389535863 96820947426009992084303795)
              ·
                refine ⟨145231421139014988126455693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96820947426009992084303795 145231421139014988126455693)
                ·
                  refine ⟨54461782927130620547420885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145231421139014988126455693 54461782927130620547420885)
                  ·
                    refine ⟨1276448037354623919080177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54461782927130620547420885 1276448037354623919080177)
                    ·
                      rfl

theorem cell23_7457621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 7].length) (baseStart_7457621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7457621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7457621 prefixEnd_7457621 := by exact prefixLift 7457621
  have htrace : WordTrace (prefixWord ++ tailWord_7457621) baseStart_7457621 baseEnd_7457621 := by
    simpa [prefixWord, tailWord_7457621, baseEnd_7457621] using wordTrace_append hprefix tailTrace_7457621
  have hstable : (prefixWord ++ tailWord_7457621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7457621).length < 2 ^ (prefixWord ++ tailWord_7457621).sum := by decide
  have hdescent : baseEnd_7457621 < baseStart_7457621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7457621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7457692 : List Nat := [2, 2, 3, 3, 2, 1, 2, 1, 2, 1, 4]
def baseStart_7457692 : Nat := 118140960795 + 7457692 * 2 ^ 59
def prefixEnd_7457692 : Nat := 4983230072969 + 3 ^ 40 * 7457692 * 2
def baseEnd_7457692 : Nat := 3829380569190340979452705

theorem tailTrace_7457692 : CollatzResearch.WordTrace tailWord_7457692 prefixEnd_7457692 3829380569190340979452705 := by
  unfold tailWord_7457692
  simp only [CollatzResearch.WordTrace]
  refine ⟨136002186649031515618235665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181336248865375354157647553 136002186649031515618235665)
  ·
    refine ⟨102001639986773636713676749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136002186649031515618235665 102001639986773636713676749)
    ·
      refine ⟨38250614995040113767628781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102001639986773636713676749 38250614995040113767628781)
      ·
        refine ⟨14343980623140042662860793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38250614995040113767628781 14343980623140042662860793)
        ·
          refine ⟨10757985467355031997145595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14343980623140042662860793 10757985467355031997145595)
          ·
            refine ⟨16136978201032547995718393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10757985467355031997145595 16136978201032547995718393)
            ·
              refine ⟨12102733650774410996788795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16136978201032547995718393 12102733650774410996788795)
              ·
                refine ⟨18154100476161616495183193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12102733650774410996788795 18154100476161616495183193)
                ·
                  refine ⟨13615575357121212371387395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18154100476161616495183193 13615575357121212371387395)
                  ·
                    refine ⟨20423363035681818557081093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13615575357121212371387395 20423363035681818557081093)
                    ·
                      refine ⟨3829380569190340979452705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20423363035681818557081093 3829380569190340979452705)
                      ·
                        rfl

theorem cell23_7457692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_7457692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7457692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7457692 prefixEnd_7457692 := by exact prefixLift 7457692
  have htrace : WordTrace (prefixWord ++ tailWord_7457692) baseStart_7457692 baseEnd_7457692 := by
    simpa [prefixWord, tailWord_7457692, baseEnd_7457692] using wordTrace_append hprefix tailTrace_7457692
  have hstable : (prefixWord ++ tailWord_7457692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7457692).length < 2 ^ (prefixWord ++ tailWord_7457692).sum := by decide
  have hdescent : baseEnd_7457692 < baseStart_7457692 := by decide
  rcases family_descends (prefixWord ++ tailWord_7457692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7457695 : List Nat := [1, 1, 2, 5, 2, 1, 1, 3, 2, 2, 3]
def baseStart_7457695 : Nat := 118140960795 + 7457695 * 2 ^ 59
def prefixEnd_7457695 : Nat := 4983230072969 + 3 ^ 40 * 7457695 * 2
def baseEnd_7457695 : Nat := 3829382109632304467715191

theorem tailTrace_7457695 : CollatzResearch.WordTrace tailWord_7457695 prefixEnd_7457695 3829382109632304467715191 := by
  unfold tailWord_7457695
  simp only [CollatzResearch.WordTrace]
  refine ⟨272004482717052162748830539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181336321811368108499220359 272004482717052162748830539)
  ·
    refine ⟨408006724075578244123245809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272004482717052162748830539 408006724075578244123245809)
    ·
      refine ⟨306005043056683683092434357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408006724075578244123245809 306005043056683683092434357)
      ·
        refine ⟨28687972786564095289915721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 306005043056683683092434357 28687972786564095289915721)
        ·
          refine ⟨21515979589923071467436791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28687972786564095289915721 21515979589923071467436791)
          ·
            refine ⟨32273969384884607201155187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21515979589923071467436791 32273969384884607201155187)
            ·
              refine ⟨48410954077326910801732781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32273969384884607201155187 48410954077326910801732781)
              ·
                refine ⟨18154107778997591550649793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48410954077326910801732781 18154107778997591550649793)
                ·
                  refine ⟨13615580834248193662987345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18154107778997591550649793 13615580834248193662987345)
                  ·
                    refine ⟨10211685625686145247240509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13615580834248193662987345 10211685625686145247240509)
                    ·
                      refine ⟨3829382109632304467715191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10211685625686145247240509 3829382109632304467715191)
                      ·
                        rfl

theorem cell23_7457695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_7457695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7457695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7457695 prefixEnd_7457695 := by exact prefixLift 7457695
  have htrace : WordTrace (prefixWord ++ tailWord_7457695) baseStart_7457695 baseEnd_7457695 := by
    simpa [prefixWord, tailWord_7457695, baseEnd_7457695] using wordTrace_append hprefix tailTrace_7457695
  have hstable : (prefixWord ++ tailWord_7457695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7457695).length < 2 ^ (prefixWord ++ tailWord_7457695).sum := by decide
  have hdescent : baseEnd_7457695 < baseStart_7457695 := by decide
  rcases family_descends (prefixWord ++ tailWord_7457695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7457701 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 3, 1, 8]
def baseStart_7457701 : Nat := 118140960795 + 7457701 * 2 ^ 59
def prefixEnd_7457701 : Nat := 4983230072969 + 3 ^ 40 * 7457701 * 2
def baseEnd_7457701 : Nat := 3829385190516231444240163

theorem tailTrace_7457701 : CollatzResearch.WordTrace tailWord_7457701 prefixEnd_7457701 3829385190516231444240163 := by
  unfold tailWord_7457701
  simp only [CollatzResearch.WordTrace]
  refine ⟨272004701555030425773548957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181336467703353617182365971 272004701555030425773548957)
  ·
    refine ⟨102001763083136409665080859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272004701555030425773548957 102001763083136409665080859)
    ·
      refine ⟨153002644624704614497621289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102001763083136409665080859 153002644624704614497621289)
      ·
        refine ⟨114751983468528460873215967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153002644624704614497621289 114751983468528460873215967)
        ·
          refine ⟨172127975202792691309823951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114751983468528460873215967 172127975202792691309823951)
          ·
            refine ⟨258191962804189036964735927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172127975202792691309823951 258191962804189036964735927)
            ·
              refine ⟨387287944206283555447103891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258191962804189036964735927 387287944206283555447103891)
              ·
                refine ⟨580931916309425333170655837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 387287944206283555447103891 580931916309425333170655837)
                ·
                  refine ⟨217849468616034499938995939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 580931916309425333170655837 217849468616034499938995939)
                  ·
                    refine ⟨326774202924051749908493909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 217849468616034499938995939 326774202924051749908493909)
                    ·
                      refine ⟨3829385190516231444240163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 326774202924051749908493909 3829385190516231444240163)
                      ·
                        rfl

theorem cell23_7457701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_7457701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7457701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7457701 prefixEnd_7457701 := by exact prefixLift 7457701
  have htrace : WordTrace (prefixWord ++ tailWord_7457701) baseStart_7457701 baseEnd_7457701 := by
    simpa [prefixWord, tailWord_7457701, baseEnd_7457701] using wordTrace_append hprefix tailTrace_7457701
  have hstable : (prefixWord ++ tailWord_7457701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7457701).length < 2 ^ (prefixWord ++ tailWord_7457701).sum := by decide
  have hdescent : baseEnd_7457701 < baseStart_7457701 := by decide
  rcases family_descends (prefixWord ++ tailWord_7457701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7457728 : List Nat := [2, 1, 1, 2, 3, 3, 1, 2, 3, 5]
def baseStart_7457728 : Nat := 118140960795 + 7457728 * 2 ^ 59
def prefixEnd_7457728 : Nat := 4983230072969 + 3 ^ 40 * 7457728 * 2
def baseEnd_7457728 : Nat := 1276466351497967612867513

theorem tailTrace_7457728 : CollatzResearch.WordTrace tailWord_7457728 prefixEnd_7457728 1276466351497967612867513 := by
  unfold tailWord_7457728
  simp only [CollatzResearch.WordTrace]
  refine ⟨136002843162966304692390919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181337124217288406256521225 136002843162966304692390919)
  ·
    refine ⟨204004264744449457038586379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136002843162966304692390919 204004264744449457038586379)
    ·
      refine ⟨306006397116674185557879569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204004264744449457038586379 306006397116674185557879569)
      ·
        refine ⟨229504797837505639168409677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306006397116674185557879569 229504797837505639168409677)
        ·
          refine ⟨86064299189064614688153629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229504797837505639168409677 86064299189064614688153629)
          ·
            refine ⟨32274112195899230508057611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86064299189064614688153629 32274112195899230508057611)
            ·
              refine ⟨48411168293848845762086417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32274112195899230508057611 48411168293848845762086417)
              ·
                refine ⟨36308376220386634321564813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48411168293848845762086417 36308376220386634321564813)
                ·
                  refine ⟨13615641082644987870586805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36308376220386634321564813 13615641082644987870586805)
                  ·
                    refine ⟨1276466351497967612867513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13615641082644987870586805 1276466351497967612867513)
                    ·
                      rfl

theorem cell23_7457728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 3, 5].length) (baseStart_7457728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7457728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7457728 prefixEnd_7457728 := by exact prefixLift 7457728
  have htrace : WordTrace (prefixWord ++ tailWord_7457728) baseStart_7457728 baseEnd_7457728 := by
    simpa [prefixWord, tailWord_7457728, baseEnd_7457728] using wordTrace_append hprefix tailTrace_7457728
  have hstable : (prefixWord ++ tailWord_7457728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7457728).length < 2 ^ (prefixWord ++ tailWord_7457728).sum := by decide
  have hdescent : baseEnd_7457728 < baseStart_7457728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7457728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7457735 : List Nat := [1, 1, 4, 1, 1, 2, 2, 2, 4, 3, 2]
def baseStart_7457735 : Nat := 118140960795 + 7457735 * 2 ^ 59
def prefixEnd_7457735 : Nat := 4983230072969 + 3 ^ 40 * 7457735 * 2
def baseEnd_7457735 : Nat := 3829402648858484311215007

theorem tailTrace_7457735 : CollatzResearch.WordTrace tailWord_7457735 prefixEnd_7457735 3829402648858484311215007 := by
  unfold tailWord_7457735
  simp only [CollatzResearch.WordTrace]
  refine ⟨272005941636907249580286659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181337294424604833053524439 272005941636907249580286659)
  ·
    refine ⟨408008912455360874370429989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272005941636907249580286659 408008912455360874370429989)
    ·
      refine ⟨76501671085380163944455623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 408008912455360874370429989 76501671085380163944455623)
      ·
        refine ⟨114752506628070245916683435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76501671085380163944455623 114752506628070245916683435)
        ·
          refine ⟨172128759942105368875025153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114752506628070245916683435 172128759942105368875025153)
          ·
            refine ⟨129096569956579026656268865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172128759942105368875025153 129096569956579026656268865)
            ·
              refine ⟨96822427467434269992201649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129096569956579026656268865 96822427467434269992201649)
              ·
                refine ⟨72616820600575702494151237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96822427467434269992201649 72616820600575702494151237)
                ·
                  refine ⟨13615653862607944217653357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72616820600575702494151237 13615653862607944217653357)
                  ·
                    refine ⟨5105870198477979081620009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13615653862607944217653357 5105870198477979081620009)
                    ·
                      refine ⟨3829402648858484311215007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5105870198477979081620009 3829402648858484311215007)
                      ·
                        rfl

theorem cell23_7457735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 4, 3, 2].length) (baseStart_7457735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7457735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7457735 prefixEnd_7457735 := by exact prefixLift 7457735
  have htrace : WordTrace (prefixWord ++ tailWord_7457735) baseStart_7457735 baseEnd_7457735 := by
    simpa [prefixWord, tailWord_7457735, baseEnd_7457735] using wordTrace_append hprefix tailTrace_7457735
  have hstable : (prefixWord ++ tailWord_7457735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7457735).length < 2 ^ (prefixWord ++ tailWord_7457735).sum := by decide
  have hdescent : baseEnd_7457735 < baseStart_7457735 := by decide
  rcases family_descends (prefixWord ++ tailWord_7457735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7457742 : List Nat := [4, 1, 1, 1, 2, 4, 1, 2, 3, 1, 3]
def baseStart_7457742 : Nat := 118140960795 + 7457742 * 2 ^ 59
def prefixEnd_7457742 : Nat := 4983230072969 + 3 ^ 40 * 7457742 * 2
def baseEnd_7457742 : Nat := 3829406243223065783827475

theorem tailTrace_7457742 : CollatzResearch.WordTrace tailWord_7457742 prefixEnd_7457742 3829406243223065783827475 := by
  unfold tailWord_7457742
  simp only [CollatzResearch.WordTrace]
  refine ⟨34000774618485236221973935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181337464631921259850527653 34000774618485236221973935)
  ·
    refine ⟨51001161927727854332960903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34000774618485236221973935 51001161927727854332960903)
    ·
      refine ⟨76501742891591781499441355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51001161927727854332960903 76501742891591781499441355)
      ·
        refine ⟨114752614337387672249162033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76501742891591781499441355 114752614337387672249162033)
        ·
          refine ⟨86064460753040754186871525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114752614337387672249162033 86064460753040754186871525)
          ·
            refine ⟨16137086391195141410038411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86064460753040754186871525 16137086391195141410038411)
            ·
              refine ⟨24205629586792712115057617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16137086391195141410038411 24205629586792712115057617)
              ·
                refine ⟨18154222190094534086293213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24205629586792712115057617 18154222190094534086293213)
                ·
                  refine ⟨6807833321285450282359955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18154222190094534086293213 6807833321285450282359955)
                  ·
                    refine ⟨10211749981928175423539933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6807833321285450282359955 10211749981928175423539933)
                    ·
                      refine ⟨3829406243223065783827475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10211749981928175423539933 3829406243223065783827475)
                      ·
                        rfl

theorem cell23_7457742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 3, 1, 3].length) (baseStart_7457742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7457742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7457742 prefixEnd_7457742 := by exact prefixLift 7457742
  have htrace : WordTrace (prefixWord ++ tailWord_7457742) baseStart_7457742 baseEnd_7457742 := by
    simpa [prefixWord, tailWord_7457742, baseEnd_7457742] using wordTrace_append hprefix tailTrace_7457742
  have hstable : (prefixWord ++ tailWord_7457742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7457742).length < 2 ^ (prefixWord ++ tailWord_7457742).sum := by decide
  have hdescent : baseEnd_7457742 < baseStart_7457742 := by decide
  rcases family_descends (prefixWord ++ tailWord_7457742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7457752 : List Nat := [2, 1, 2, 2, 2, 3, 3, 1, 2, 3, 2]
def baseStart_7457752 : Nat := 118140960795 + 7457752 * 2 ^ 59
def prefixEnd_7457752 : Nat := 4983230072969 + 3 ^ 40 * 7457752 * 2
def baseEnd_7457752 : Nat := 3829411378029610744702429

theorem tailTrace_7457752 : CollatzResearch.WordTrace tailWord_7457752 prefixEnd_7457752 3829411378029610744702429 := by
  unfold tailWord_7457752
  simp only [CollatzResearch.WordTrace]
  refine ⟨136003280838922830741827755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181337707785230440989103673 136003280838922830741827755)
  ·
    refine ⟨204004921258384246112741633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136003280838922830741827755 204004921258384246112741633)
    ·
      refine ⟨153003690943788184584556225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204004921258384246112741633 153003690943788184584556225)
      ·
        refine ⟨114752768207841138438417169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153003690943788184584556225 114752768207841138438417169)
        ·
          refine ⟨86064576155880853828812877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114752768207841138438417169 86064576155880853828812877)
          ·
            refine ⟨32274216058455320185804829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86064576155880853828812877 32274216058455320185804829)
            ·
              refine ⟨12102831021920745069676811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32274216058455320185804829 12102831021920745069676811)
              ·
                refine ⟨18154246532881117604515217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12102831021920745069676811 18154246532881117604515217)
                ·
                  refine ⟨13615684899660838203386413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18154246532881117604515217 13615684899660838203386413)
                  ·
                    refine ⟨5105881837372814326269905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13615684899660838203386413 5105881837372814326269905)
                    ·
                      refine ⟨3829411378029610744702429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5105881837372814326269905 3829411378029610744702429)
                      ·
                        rfl

theorem cell23_7457752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 2, 3, 2].length) (baseStart_7457752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7457752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7457752 prefixEnd_7457752 := by exact prefixLift 7457752
  have htrace : WordTrace (prefixWord ++ tailWord_7457752) baseStart_7457752 baseEnd_7457752 := by
    simpa [prefixWord, tailWord_7457752, baseEnd_7457752] using wordTrace_append hprefix tailTrace_7457752
  have hstable : (prefixWord ++ tailWord_7457752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7457752).length < 2 ^ (prefixWord ++ tailWord_7457752).sum := by decide
  have hdescent : baseEnd_7457752 < baseStart_7457752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7457752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7457775 : List Nat := [1, 1, 2, 1, 4, 4, 1, 1, 4, 4]
def baseStart_7457775 : Nat := 118140960795 + 7457775 * 2 ^ 59
def prefixEnd_7457775 : Nat := 4983230072969 + 3 ^ 40 * 7457775 * 2
def baseEnd_7457775 : Nat := 1276474396028221384904941

theorem tailTrace_7457775 : CollatzResearch.WordTrace tailWord_7457775 prefixEnd_7457775 1276474396028221384904941 := by
  unfold tailWord_7457775
  simp only [CollatzResearch.WordTrace]
  refine ⟨272007400556762336411742779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181338267037841557607828519 272007400556762336411742779)
  ·
    refine ⟨408011100835143504617614169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272007400556762336411742779 408011100835143504617614169)
    ·
      refine ⟨306008325626357628463210627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408011100835143504617614169 306008325626357628463210627)
      ·
        refine ⟨459012488439536442694815941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306008325626357628463210627 459012488439536442694815941)
        ·
          refine ⟨86064841582413083005277989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 459012488439536442694815941 86064841582413083005277989)
          ·
            refine ⟨16137157796702453063489623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86064841582413083005277989 16137157796702453063489623)
            ·
              refine ⟨24205736695053679595234435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16137157796702453063489623 24205736695053679595234435)
              ·
                refine ⟨36308605042580519392851653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24205736695053679595234435 36308605042580519392851653)
                ·
                  refine ⟨6807863445483847386159685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36308605042580519392851653 6807863445483847386159685)
                  ·
                    refine ⟨1276474396028221384904941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6807863445483847386159685 1276474396028221384904941)
                    ·
                      rfl

theorem cell23_7457775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 4, 4].length) (baseStart_7457775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7457775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7457775 prefixEnd_7457775 := by exact prefixLift 7457775
  have htrace : WordTrace (prefixWord ++ tailWord_7457775) baseStart_7457775 baseEnd_7457775 := by
    simpa [prefixWord, tailWord_7457775, baseEnd_7457775] using wordTrace_append hprefix tailTrace_7457775
  have hstable : (prefixWord ++ tailWord_7457775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7457775).length < 2 ^ (prefixWord ++ tailWord_7457775).sum := by decide
  have hdescent : baseEnd_7457775 < baseStart_7457775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7457775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7457802 : List Nat := [3, 1, 2, 2, 3, 1, 1, 4, 1, 2, 3]
def baseStart_7457802 : Nat := 118140960795 + 7457802 * 2 ^ 59
def prefixEnd_7457802 : Nat := 4983230072969 + 3 ^ 40 * 7457802 * 2
def baseEnd_7457802 : Nat := 3829437052062335549077199

theorem tailTrace_7457802 : CollatzResearch.WordTrace tailWord_7457802 prefixEnd_7457802 3829437052062335549077199 := by
  unfold tailWord_7457802
  simp only [CollatzResearch.WordTrace]
  refine ⟨68002096331916130005743915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181338923551776346681983773 68002096331916130005743915)
  ·
    refine ⟨102003144497874195008615873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68002096331916130005743915 102003144497874195008615873)
    ·
      refine ⟨76502358373405646256461905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102003144497874195008615873 76502358373405646256461905)
      ·
        refine ⟨57376768780054234692346429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76502358373405646256461905 57376768780054234692346429)
        ·
          refine ⟨21516288292520338009629911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57376768780054234692346429 21516288292520338009629911)
          ·
            refine ⟨32274432438780507014444867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21516288292520338009629911 32274432438780507014444867)
            ·
              refine ⟨48411648658170760521667301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32274432438780507014444867 48411648658170760521667301)
              ·
                refine ⟨9077184123407017597812619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48411648658170760521667301 9077184123407017597812619)
                ·
                  refine ⟨13615776185110526396718929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9077184123407017597812619 13615776185110526396718929)
                  ·
                    refine ⟨10211832138832894797539197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13615776185110526396718929 10211832138832894797539197)
                    ·
                      refine ⟨3829437052062335549077199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10211832138832894797539197 3829437052062335549077199)
                      ·
                        rfl

theorem cell23_7457802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_7457802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7457802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7457802 prefixEnd_7457802 := by exact prefixLift 7457802
  have htrace : WordTrace (prefixWord ++ tailWord_7457802) baseStart_7457802 baseEnd_7457802 := by
    simpa [prefixWord, tailWord_7457802, baseEnd_7457802] using wordTrace_append hprefix tailTrace_7457802
  have hstable : (prefixWord ++ tailWord_7457802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7457802).length < 2 ^ (prefixWord ++ tailWord_7457802).sum := by decide
  have hdescent : baseEnd_7457802 < baseStart_7457802 := by decide
  rcases family_descends (prefixWord ++ tailWord_7457802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7457816 : List Nat := [2, 1, 2, 3, 2, 2, 3, 3, 1, 2, 2]
def baseStart_7457816 : Nat := 118140960795 + 7457816 * 2 ^ 59
def prefixEnd_7457816 : Nat := 4983230072969 + 3 ^ 40 * 7457816 * 2
def baseEnd_7457816 : Nat := 3829444240791498494302135

theorem tailTrace_7457816 : CollatzResearch.WordTrace tailWord_7457816 prefixEnd_7457816 3829444240791498494302135 := by
  unfold tailWord_7457816
  simp only [CollatzResearch.WordTrace]
  refine ⟨136004447974806900206992651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181339263966409200275990201 136004447974806900206992651)
  ·
    refine ⟨204006671962210350310488977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136004447974806900206992651 204006671962210350310488977)
    ·
      refine ⟨153005003971657762732866733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204006671962210350310488977 153005003971657762732866733)
      ·
        refine ⟨57376876489371661024825025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153005003971657762732866733 57376876489371661024825025)
        ·
          refine ⟨43032657367028745768618769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57376876489371661024825025 43032657367028745768618769)
          ·
            refine ⟨32274493025271559326464077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43032657367028745768618769 32274493025271559326464077)
            ·
              refine ⟨12102934884476834747424029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32274493025271559326464077 12102934884476834747424029)
              ·
                refine ⟨4538600581678813030284011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12102934884476834747424029 4538600581678813030284011)
                ·
                  refine ⟨6807900872518219545426017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4538600581678813030284011 6807900872518219545426017)
                  ·
                    refine ⟨5105925654388664659069513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6807900872518219545426017 5105925654388664659069513)
                    ·
                      refine ⟨3829444240791498494302135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5105925654388664659069513 3829444240791498494302135)
                      ·
                        rfl

theorem cell23_7457816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 3, 1, 2, 2].length) (baseStart_7457816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7457816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7457816 prefixEnd_7457816 := by exact prefixLift 7457816
  have htrace : WordTrace (prefixWord ++ tailWord_7457816) baseStart_7457816 baseEnd_7457816 := by
    simpa [prefixWord, tailWord_7457816, baseEnd_7457816] using wordTrace_append hprefix tailTrace_7457816
  have hstable : (prefixWord ++ tailWord_7457816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7457816).length < 2 ^ (prefixWord ++ tailWord_7457816).sum := by decide
  have hdescent : baseEnd_7457816 < baseStart_7457816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7457816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7457842 : List Nat := [3, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2]
def baseStart_7457842 : Nat := 118140960795 + 7457842 * 2 ^ 59
def prefixEnd_7457842 : Nat := 4983230072969 + 3 ^ 40 * 7457842 * 2
def baseEnd_7457842 : Nat := 3829457591288515392577015

theorem tailTrace_7457842 : CollatzResearch.WordTrace tailWord_7457842 prefixEnd_7457842 3829457591288515392577015 := by
  unfold tailWord_7457842
  simp only [CollatzResearch.WordTrace]
  refine ⟨68002461061879901713607945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181339896165013071236287853 68002461061879901713607945)
  ·
    refine ⟨51001845796409926285205959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68002461061879901713607945 51001845796409926285205959)
    ·
      refine ⟨76502768694614889427808939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51001845796409926285205959 76502768694614889427808939)
      ·
        refine ⟨114754153041922334141713409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76502768694614889427808939 114754153041922334141713409)
        ·
          refine ⟨86065614781441750606285057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114754153041922334141713409 86065614781441750606285057)
          ·
            refine ⟨64549211086081312954713793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86065614781441750606285057 64549211086081312954713793)
            ·
              refine ⟨48411908314560984716035345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64549211086081312954713793 48411908314560984716035345)
              ·
                refine ⟨36308931235920738537026509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48411908314560984716035345 36308931235920738537026509)
                ·
                  refine ⟨13615849213470276951384941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36308931235920738537026509 13615849213470276951384941)
                  ·
                    refine ⟨5105943455051353856769353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13615849213470276951384941 5105943455051353856769353)
                    ·
                      refine ⟨3829457591288515392577015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5105943455051353856769353 3829457591288515392577015)
                      ·
                        rfl

theorem cell23_7457842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2].length) (baseStart_7457842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7457842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7457842 prefixEnd_7457842 := by exact prefixLift 7457842
  have htrace : WordTrace (prefixWord ++ tailWord_7457842) baseStart_7457842 baseEnd_7457842 := by
    simpa [prefixWord, tailWord_7457842, baseEnd_7457842] using wordTrace_append hprefix tailTrace_7457842
  have hstable : (prefixWord ++ tailWord_7457842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7457842).length < 2 ^ (prefixWord ++ tailWord_7457842).sum := by decide
  have hdescent : baseEnd_7457842 < baseStart_7457842 := by decide
  rcases family_descends (prefixWord ++ tailWord_7457842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7457849 : List Nat := [1, 2, 1, 5, 2, 2, 1, 3, 2, 1, 3]
def baseStart_7457849 : Nat := 118140960795 + 7457849 * 2 ^ 59
def prefixEnd_7457849 : Nat := 4983230072969 + 3 ^ 40 * 7457849 * 2
def baseEnd_7457849 : Nat := 3829461185653096865189483

theorem tailTrace_7457849 : CollatzResearch.WordTrace tailWord_7457849 prefixEnd_7457849 3829461185653096865189483 := by
  unfold tailWord_7457849
  simp only [CollatzResearch.WordTrace]
  refine ⟨272010099558494247049936601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181340066372329498033291067 272010099558494247049936601)
  ·
    refine ⟨204007574668870685287452451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272010099558494247049936601 204007574668870685287452451)
    ·
      refine ⟨306011362003306027931178677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204007574668870685287452451 306011362003306027931178677)
      ·
        refine ⟨28688565187809940118548001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 306011362003306027931178677 28688565187809940118548001)
        ·
          refine ⟨21516423890857455088911001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28688565187809940118548001 21516423890857455088911001)
          ·
            refine ⟨16137317918143091316683251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21516423890857455088911001 16137317918143091316683251)
            ·
              refine ⟨24205976877214636975024877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16137317918143091316683251 24205976877214636975024877)
              ·
                refine ⟨9077241328955488865634329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24205976877214636975024877 9077241328955488865634329)
                ·
                  refine ⟨6807930996716616649225747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9077241328955488865634329 6807930996716616649225747)
                  ·
                    refine ⟨10211896495074924973838621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6807930996716616649225747 10211896495074924973838621)
                    ·
                      refine ⟨3829461185653096865189483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10211896495074924973838621 3829461185653096865189483)
                      ·
                        rfl

theorem cell23_7457849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_7457849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7457849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7457849 prefixEnd_7457849 := by exact prefixLift 7457849
  have htrace : WordTrace (prefixWord ++ tailWord_7457849) baseStart_7457849 baseEnd_7457849 := by
    simpa [prefixWord, tailWord_7457849, baseEnd_7457849] using wordTrace_append hprefix tailTrace_7457849
  have hstable : (prefixWord ++ tailWord_7457849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7457849).length < 2 ^ (prefixWord ++ tailWord_7457849).sum := by decide
  have hdescent : baseEnd_7457849 < baseStart_7457849 := by decide
  rcases family_descends (prefixWord ++ tailWord_7457849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7457872 : List Nat := [2, 1, 1, 1, 1, 3, 1, 3, 6, 2, 2]
def baseStart_7457872 : Nat := 118140960795 + 7457872 * 2 ^ 59
def prefixEnd_7457872 : Nat := 4983230072969 + 3 ^ 40 * 7457872 * 2
def baseEnd_7457872 : Nat := 3829472995708150275201877

theorem tailTrace_7457872 : CollatzResearch.WordTrace tailWord_7457872 prefixEnd_7457872 3829472995708150275201877 := by
  unfold tailWord_7457872
  simp only [CollatzResearch.WordTrace]
  refine ⟨136005469218705460989011935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181340625624940614652015913 136005469218705460989011935)
  ·
    refine ⟨204008203828058191483517903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136005469218705460989011935 204008203828058191483517903)
    ·
      refine ⟨306012305742087287225276855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204008203828058191483517903 306012305742087287225276855)
      ·
        refine ⟨459018458613130930837915283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306012305742087287225276855 459018458613130930837915283)
        ·
          refine ⟨688527687919696396256872925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459018458613130930837915283 688527687919696396256872925)
          ·
            refine ⟨258197882969886148596327347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 688527687919696396256872925 258197882969886148596327347)
            ·
              refine ⟨387296824454829222894491021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258197882969886148596327347 387296824454829222894491021)
              ·
                refine ⟨145236309170560958585434133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 387296824454829222894491021 145236309170560958585434133)
                ·
                  refine ⟨6807951992370044933692225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 145236309170560958585434133 6807951992370044933692225)
                  ·
                    refine ⟨5105963994277533700269169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6807951992370044933692225 5105963994277533700269169)
                    ·
                      refine ⟨3829472995708150275201877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5105963994277533700269169 3829472995708150275201877)
                      ·
                        rfl

theorem cell23_7457872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 6, 2, 2].length) (baseStart_7457872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7457872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7457872 prefixEnd_7457872 := by exact prefixLift 7457872
  have htrace : WordTrace (prefixWord ++ tailWord_7457872) baseStart_7457872 baseEnd_7457872 := by
    simpa [prefixWord, tailWord_7457872, baseEnd_7457872] using wordTrace_append hprefix tailTrace_7457872
  have hstable : (prefixWord ++ tailWord_7457872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7457872).length < 2 ^ (prefixWord ++ tailWord_7457872).sum := by decide
  have hdescent : baseEnd_7457872 < baseStart_7457872 := by decide
  rcases family_descends (prefixWord ++ tailWord_7457872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7457889 : List Nat := [1, 2, 3, 1, 1, 2, 3, 4, 2, 2, 2]
def baseStart_7457889 : Nat := 118140960795 + 7457889 * 2 ^ 59
def prefixEnd_7457889 : Nat := 4983230072969 + 3 ^ 40 * 7457889 * 2
def baseEnd_7457889 : Nat := 3829481724879276708689299

theorem tailTrace_7457889 : CollatzResearch.WordTrace tailWord_7457889 prefixEnd_7457889 3829481724879276708689299 := by
  unfold tailWord_7457889
  simp only [CollatzResearch.WordTrace]
  refine ⟨272011558478349333881392721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181341038985566222587595147 272011558478349333881392721)
  ·
    refine ⟨204008668858762000411044541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272011558478349333881392721 204008668858762000411044541)
    ·
      refine ⟨76503250822035750154141703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204008668858762000411044541 76503250822035750154141703)
      ·
        refine ⟨114754876233053625231212555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76503250822035750154141703 114754876233053625231212555)
        ·
          refine ⟨172132314349580437846818833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114754876233053625231212555 172132314349580437846818833)
          ·
            refine ⟨129099235762185328385114125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172132314349580437846818833 129099235762185328385114125)
            ·
              refine ⟨48412213410819498144417797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129099235762185328385114125 48412213410819498144417797)
              ·
                refine ⟨9077290014528655902078337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48412213410819498144417797 9077290014528655902078337)
                ·
                  refine ⟨6807967510896491926558753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9077290014528655902078337 6807967510896491926558753)
                  ·
                    refine ⟨5105975633172368944919065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6807967510896491926558753 5105975633172368944919065)
                    ·
                      refine ⟨3829481724879276708689299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5105975633172368944919065 3829481724879276708689299)
                      ·
                        rfl

theorem cell23_7457889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 4, 2, 2, 2].length) (baseStart_7457889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7457889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7457889 prefixEnd_7457889 := by exact prefixLift 7457889
  have htrace : WordTrace (prefixWord ++ tailWord_7457889) baseStart_7457889 baseEnd_7457889 := by
    simpa [prefixWord, tailWord_7457889, baseEnd_7457889] using wordTrace_append hprefix tailTrace_7457889
  have hstable : (prefixWord ++ tailWord_7457889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7457889).length < 2 ^ (prefixWord ++ tailWord_7457889).sum := by decide
  have hdescent : baseEnd_7457889 < baseStart_7457889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7457889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7457902 : List Nat := [4, 1, 2, 2, 1, 3, 1, 1, 2, 2, 4]
def baseStart_7457902 : Nat := 118140960795 + 7457902 * 2 ^ 59
def prefixEnd_7457902 : Nat := 4983230072969 + 3 ^ 40 * 7457902 * 2
def baseEnd_7457902 : Nat := 3829488400127785157826739

theorem tailTrace_7457902 : CollatzResearch.WordTrace tailWord_7457902 prefixEnd_7457902 3829488400127785157826739 := by
  unfold tailWord_7457902
  simp only [CollatzResearch.WordTrace]
  refine ⟨34001504078412779637701995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181341355084868158067743973 34001504078412779637701995)
  ·
    refine ⟨51002256117619169456552993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34001504078412779637701995 51002256117619169456552993)
    ·
      refine ⟨38251692088214377092414745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51002256117619169456552993 38251692088214377092414745)
      ·
        refine ⟨28688769066160782819311059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38251692088214377092414745 28688769066160782819311059)
        ·
          refine ⟨43033153599241174228966589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28688769066160782819311059 43033153599241174228966589)
          ·
            refine ⟨16137432599715440335862471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43033153599241174228966589 16137432599715440335862471)
            ·
              refine ⟨24206148899573160503793707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16137432599715440335862471 24206148899573160503793707)
              ·
                refine ⟨36309223349359740755690561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24206148899573160503793707 36309223349359740755690561)
                ·
                  refine ⟨27231917512019805566767921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36309223349359740755690561 27231917512019805566767921)
                  ·
                    refine ⟨20423938134014854175075941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27231917512019805566767921 20423938134014854175075941)
                    ·
                      refine ⟨3829488400127785157826739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20423938134014854175075941 3829488400127785157826739)
                      ·
                        rfl

theorem cell23_7457902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_7457902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7457902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7457902 prefixEnd_7457902 := by exact prefixLift 7457902
  have htrace : WordTrace (prefixWord ++ tailWord_7457902) baseStart_7457902 baseEnd_7457902 := by
    simpa [prefixWord, tailWord_7457902, baseEnd_7457902] using wordTrace_append hprefix tailTrace_7457902
  have hstable : (prefixWord ++ tailWord_7457902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7457902).length < 2 ^ (prefixWord ++ tailWord_7457902).sum := by decide
  have hdescent : baseEnd_7457902 < baseStart_7457902 := by decide
  rcases family_descends (prefixWord ++ tailWord_7457902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7457975 : List Nat := [1, 1, 3, 1, 4, 1, 1, 1, 2, 4, 4]
def baseStart_7457975 : Nat := 118140960795 + 7457975 * 2 ^ 59
def prefixEnd_7457975 : Nat := 4983230072969 + 3 ^ 40 * 7457975 * 2
def baseEnd_7457975 : Nat := 3829525884215563372213903

theorem tailTrace_7457975 : CollatzResearch.WordTrace tailWord_7457975 prefixEnd_7457975 3829525884215563372213903 := by
  unfold tailWord_7457975
  simp only [CollatzResearch.WordTrace]
  refine ⟨272014695156037770569023379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181343130104025180379348919 272014695156037770569023379)
  ·
    refine ⟨408022042734056655853535069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272014695156037770569023379 408022042734056655853535069)
    ·
      refine ⟨153008266025271245945075651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 408022042734056655853535069 153008266025271245945075651)
      ·
        refine ⟨229512399037906868917613477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153008266025271245945075651 229512399037906868917613477)
        ·
          refine ⟨43033574819607537922052527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 229512399037906868917613477 43033574819607537922052527)
          ·
            refine ⟨64550362229411306883078791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43033574819607537922052527 64550362229411306883078791)
            ·
              refine ⟨96825543344116960324618187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64550362229411306883078791 96825543344116960324618187)
              ·
                refine ⟨145238315016175440486927281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96825543344116960324618187 145238315016175440486927281)
                ·
                  refine ⟨108928736262131580365195461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145238315016175440486927281 108928736262131580365195461)
                  ·
                    refine ⟨20424138049149671318474149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 108928736262131580365195461 20424138049149671318474149)
                    ·
                      refine ⟨3829525884215563372213903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20424138049149671318474149 3829525884215563372213903)
                      ·
                        rfl

theorem cell23_7457975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 4, 4].length) (baseStart_7457975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7457975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7457975 prefixEnd_7457975 := by exact prefixLift 7457975
  have htrace : WordTrace (prefixWord ++ tailWord_7457975) baseStart_7457975 baseEnd_7457975 := by
    simpa [prefixWord, tailWord_7457975, baseEnd_7457975] using wordTrace_append hprefix tailTrace_7457975
  have hstable : (prefixWord ++ tailWord_7457975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7457975).length < 2 ^ (prefixWord ++ tailWord_7457975).sum := by decide
  have hdescent : baseEnd_7457975 < baseStart_7457975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7457975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7458002 : List Nat := [3, 2, 2, 2, 1, 1, 2, 4, 6]
def baseStart_7458002 : Nat := 118140960795 + 7458002 * 2 ^ 59
def prefixEnd_7458002 : Nat := 4983230072969 + 3 ^ 40 * 7458002 * 2
def baseEnd_7458002 : Nat := 425504416465914974064031

theorem tailTrace_7458002 : CollatzResearch.WordTrace tailWord_7458002 prefixEnd_7458002 425504416465914974064031 := by
  unfold tailWord_7458002
  simp only [CollatzResearch.WordTrace]
  refine ⟨68003919981734988545064065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181343786617959969453504173 68003919981734988545064065)
  ·
    refine ⟨51002939986301241408798049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68003919981734988545064065 51002939986301241408798049)
    ·
      refine ⟨38252204989725931056598537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51002939986301241408798049 38252204989725931056598537)
      ·
        refine ⟨28689153742294448292448903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38252204989725931056598537 28689153742294448292448903)
        ·
          refine ⟨43033730613441672438673355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28689153742294448292448903 43033730613441672438673355)
          ·
            refine ⟨64550595920162508658010033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43033730613441672438673355 64550595920162508658010033)
            ·
              refine ⟨48412946940121881493507525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64550595920162508658010033 48412946940121881493507525)
              ·
                refine ⟨9077427551272852780032661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48412946940121881493507525 9077427551272852780032661)
                ·
                  refine ⟨425504416465914974064031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9077427551272852780032661 425504416465914974064031)
                  ·
                    rfl

theorem cell23_7458002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 4, 6].length) (baseStart_7458002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7458002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7458002 prefixEnd_7458002 := by exact prefixLift 7458002
  have htrace : WordTrace (prefixWord ++ tailWord_7458002) baseStart_7458002 baseEnd_7458002 := by
    simpa [prefixWord, tailWord_7458002, baseEnd_7458002] using wordTrace_append hprefix tailTrace_7458002
  have hstable : (prefixWord ++ tailWord_7458002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7458002).length < 2 ^ (prefixWord ++ tailWord_7458002).sum := by decide
  have hdescent : baseEnd_7458002 < baseStart_7458002 := by decide
  rcases family_descends (prefixWord ++ tailWord_7458002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7458079 : List Nat := [1, 1, 2, 4, 4, 1, 2, 1, 1, 6]
def baseStart_7458079 : Nat := 118140960795 + 7458079 * 2 ^ 59
def prefixEnd_7458079 : Nat := 4983230072969 + 3 ^ 40 * 7458079 * 2
def baseEnd_7458079 : Nat := 1276526428734543655104475

theorem tailTrace_7458079 : CollatzResearch.WordTrace tailWord_7458079 prefixEnd_7458079 1276526428734543655104475 := by
  unfold tailWord_7458079
  simp only [CollatzResearch.WordTrace]
  refine ⟨272018488347660996330809291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181345658898440664220539527 272018488347660996330809291)
  ·
    refine ⟨408027732521491494496213937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272018488347660996330809291 408027732521491494496213937)
    ·
      refine ⟨306020799391118620872160453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408027732521491494496213937 306020799391118620872160453)
      ·
        refine ⟨57378899885834741413530085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 306020799391118620872160453 57378899885834741413530085)
        ·
          refine ⟨10758543728594014015036891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57378899885834741413530085 10758543728594014015036891)
          ·
            refine ⟨16137815592891021022555337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10758543728594014015036891 16137815592891021022555337)
            ·
              refine ⟨12103361694668265766916503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16137815592891021022555337 12103361694668265766916503)
              ·
                refine ⟨18155042542002398650374755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12103361694668265766916503 18155042542002398650374755)
                ·
                  refine ⟨27232563813003597975562133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18155042542002398650374755 27232563813003597975562133)
                  ·
                    refine ⟨1276526428734543655104475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27232563813003597975562133 1276526428734543655104475)
                    ·
                      rfl

theorem cell23_7458079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 6].length) (baseStart_7458079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7458079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7458079 prefixEnd_7458079 := by exact prefixLift 7458079
  have htrace : WordTrace (prefixWord ++ tailWord_7458079) baseStart_7458079 baseEnd_7458079 := by
    simpa [prefixWord, tailWord_7458079, baseEnd_7458079] using wordTrace_append hprefix tailTrace_7458079
  have hstable : (prefixWord ++ tailWord_7458079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7458079).length < 2 ^ (prefixWord ++ tailWord_7458079).sum := by decide
  have hdescent : baseEnd_7458079 < baseStart_7458079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7458079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7458109 : List Nat := [1, 4, 1, 5, 1, 1, 10]
def baseStart_7458109 : Nat := 118140960795 + 7458109 * 2 ^ 59
def prefixEnd_7458109 : Nat := 4983230072969 + 3 ^ 40 * 7458109 * 2
def baseEnd_7458109 : Nat := 47278946797818096888127

theorem tailTrace_7458109 : CollatzResearch.WordTrace tailWord_7458109 prefixEnd_7458109 47278946797818096888127 := by
  unfold tailWord_7458109
  simp only [CollatzResearch.WordTrace]
  refine ⟨272019582537552311454401381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181346388358368207636267587 272019582537552311454401381)
  ·
    refine ⟨51003671725791058397700259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 272019582537552311454401381 51003671725791058397700259)
    ·
      refine ⟨76505507588686587596550389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51003671725791058397700259 76505507588686587596550389)
      ·
        refine ⟨7172391336439367587176599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76505507588686587596550389 7172391336439367587176599)
        ·
          refine ⟨10758587004659051380764899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7172391336439367587176599 10758587004659051380764899)
          ·
            refine ⟨16137880506988577071147349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10758587004659051380764899 16137880506988577071147349)
            ·
              refine ⟨47278946797818096888127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16137880506988577071147349 47278946797818096888127)
              ·
                rfl

theorem cell23_7458109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 10].length) (baseStart_7458109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7458109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7458109 prefixEnd_7458109 := by exact prefixLift 7458109
  have htrace : WordTrace (prefixWord ++ tailWord_7458109) baseStart_7458109 baseEnd_7458109 := by
    simpa [prefixWord, tailWord_7458109, baseEnd_7458109] using wordTrace_append hprefix tailTrace_7458109
  have hstable : (prefixWord ++ tailWord_7458109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7458109).length < 2 ^ (prefixWord ++ tailWord_7458109).sum := by decide
  have hdescent : baseEnd_7458109 < baseStart_7458109 := by decide
  rcases family_descends (prefixWord ++ tailWord_7458109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7458113 : List Nat := [1, 2, 5, 2, 1, 3, 1, 2, 2, 4]
def baseStart_7458113 : Nat := 118140960795 + 7458113 * 2 ^ 59
def prefixEnd_7458113 : Nat := 4983230072969 + 3 ^ 40 * 7458113 * 2
def baseEnd_7458113 : Nat := 1276532248181961277429423

theorem tailTrace_7458113 : CollatzResearch.WordTrace tailWord_7458113 prefixEnd_7458113 1276532248181961277429423 := by
  unfold tailWord_7458113
  simp only [CollatzResearch.WordTrace]
  refine ⟨272019728429537820137546993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181346485619691880091697995 272019728429537820137546993)
  ·
    refine ⟨204014796322153365103160245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272019728429537820137546993 204014796322153365103160245)
    ·
      refine ⟨19126387155201877978421273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 204014796322153365103160245 19126387155201877978421273)
      ·
        refine ⟨14344790366401408483815955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19126387155201877978421273 14344790366401408483815955)
        ·
          refine ⟨21517185549602112725723933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14344790366401408483815955 21517185549602112725723933)
          ·
            refine ⟨8068944581100792272146475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21517185549602112725723933 8068944581100792272146475)
            ·
              refine ⟨12103416871651188408219713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8068944581100792272146475 12103416871651188408219713)
              ·
                refine ⟨9077562653738391306164785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12103416871651188408219713 9077562653738391306164785)
                ·
                  refine ⟨6808171990303793479623589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9077562653738391306164785 6808171990303793479623589)
                  ·
                    refine ⟨1276532248181961277429423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6808171990303793479623589 1276532248181961277429423)
                    ·
                      rfl

theorem cell23_7458113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_7458113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7458113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7458113 prefixEnd_7458113 := by exact prefixLift 7458113
  have htrace : WordTrace (prefixWord ++ tailWord_7458113) baseStart_7458113 baseEnd_7458113 := by
    simpa [prefixWord, tailWord_7458113, baseEnd_7458113] using wordTrace_append hprefix tailTrace_7458113
  have hstable : (prefixWord ++ tailWord_7458113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7458113).length < 2 ^ (prefixWord ++ tailWord_7458113).sum := by decide
  have hdescent : baseEnd_7458113 < baseStart_7458113 := by decide
  rcases family_descends (prefixWord ++ tailWord_7458113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7458154 : List Nat := [3, 1, 3, 3, 3, 1, 1, 3, 1, 2, 2]
def baseStart_7458154 : Nat := 118140960795 + 7458154 * 2 ^ 59
def prefixEnd_7458154 : Nat := 4983230072969 + 3 ^ 40 * 7458154 * 2
def baseEnd_7458154 : Nat := 3829617797252718171875581

theorem tailTrace_7458154 : CollatzResearch.WordTrace tailWord_7458154 prefixEnd_7458154 3829617797252718171875581 := by
  unfold tailWord_7458154
  simp only [CollatzResearch.WordTrace]
  refine ⟨68005305955597321034947379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181347482548259522759859677 68005305955597321034947379)
  ·
    refine ⟨102007958933395981552421069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68005305955597321034947379 102007958933395981552421069)
    ·
      refine ⟨38252984600023493082157901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102007958933395981552421069 38252984600023493082157901)
      ·
        refine ⟨14344869225008809905809213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38252984600023493082157901 14344869225008809905809213)
        ·
          refine ⟨5379325959378303714678455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14344869225008809905809213 5379325959378303714678455)
          ·
            refine ⟨8068988939067455572017683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5379325959378303714678455 8068988939067455572017683)
            ·
              refine ⟨12103483408601183358026525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8068988939067455572017683 12103483408601183358026525)
              ·
                refine ⟨4538806278225443759259947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12103483408601183358026525 4538806278225443759259947)
                ·
                  refine ⟨6808209417338165638889921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4538806278225443759259947 6808209417338165638889921)
                  ·
                    refine ⟨5106157063003624229167441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6808209417338165638889921 5106157063003624229167441)
                    ·
                      refine ⟨3829617797252718171875581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5106157063003624229167441 3829617797252718171875581)
                      ·
                        rfl

theorem cell23_7458154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_7458154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7458154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7458154 prefixEnd_7458154 := by exact prefixLift 7458154
  have htrace : WordTrace (prefixWord ++ tailWord_7458154) baseStart_7458154 baseEnd_7458154 := by
    simpa [prefixWord, tailWord_7458154, baseEnd_7458154] using wordTrace_append hprefix tailTrace_7458154
  have hstable : (prefixWord ++ tailWord_7458154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7458154).length < 2 ^ (prefixWord ++ tailWord_7458154).sum := by decide
  have hdescent : baseEnd_7458154 < baseStart_7458154 := by decide
  rcases family_descends (prefixWord ++ tailWord_7458154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7458159 : List Nat := [1, 1, 2, 1, 3, 1, 4, 1, 3, 4, 2]
def baseStart_7458159 : Nat := 118140960795 + 7458159 * 2 ^ 59
def prefixEnd_7458159 : Nat := 4983230072969 + 3 ^ 40 * 7458159 * 2
def baseEnd_7458159 : Nat := 3829620364655990652313057

theorem tailTrace_7458159 : CollatzResearch.WordTrace tailWord_7458159 prefixEnd_7458159 3829620364655990652313057 := by
  unfold tailWord_7458159
  simp only [CollatzResearch.WordTrace]
  refine ⟨272021406187371169993721531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181347604124914113329147687 272021406187371169993721531)
  ·
    refine ⟨408032109281056754990582297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272021406187371169993721531 408032109281056754990582297)
    ·
      refine ⟨306024081960792566242936723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408032109281056754990582297 306024081960792566242936723)
      ·
        refine ⟨459036122941188849364405085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306024081960792566242936723 459036122941188849364405085)
        ·
          refine ⟨172138546102945818511651907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 459036122941188849364405085 172138546102945818511651907)
          ·
            refine ⟨258207819154418727767477861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172138546102945818511651907 258207819154418727767477861)
            ·
              refine ⟨48413966091453511456402099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 258207819154418727767477861 48413966091453511456402099)
              ·
                refine ⟨72620949137180267184603149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48413966091453511456402099 72620949137180267184603149)
                ·
                  refine ⟨27232855926442600194226181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72620949137180267184603149 27232855926442600194226181)
                  ·
                    refine ⟨5106160486207987536417409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27232855926442600194226181 5106160486207987536417409)
                    ·
                      refine ⟨3829620364655990652313057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5106160486207987536417409 3829620364655990652313057)
                      ·
                        rfl

theorem cell23_7458159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 4, 2].length) (baseStart_7458159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7458159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7458159 prefixEnd_7458159 := by exact prefixLift 7458159
  have htrace : WordTrace (prefixWord ++ tailWord_7458159) baseStart_7458159 baseEnd_7458159 := by
    simpa [prefixWord, tailWord_7458159, baseEnd_7458159] using wordTrace_append hprefix tailTrace_7458159
  have hstable : (prefixWord ++ tailWord_7458159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7458159).length < 2 ^ (prefixWord ++ tailWord_7458159).sum := by decide
  have hdescent : baseEnd_7458159 < baseStart_7458159 := by decide
  rcases family_descends (prefixWord ++ tailWord_7458159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7458266 : List Nat := [3, 1, 1, 2, 3, 2, 3, 1, 2, 1, 4]
def baseStart_7458266 : Nat := 118140960795 + 7458266 * 2 ^ 59
def prefixEnd_7458266 : Nat := 4983230072969 + 3 ^ 40 * 7458266 * 2
def baseEnd_7458266 : Nat := 3829675307086021733675065

theorem tailTrace_7458266 : CollatzResearch.WordTrace tailWord_7458266 prefixEnd_7458266 3829675307086021733675065 := by
  unfold tailWord_7458266
  simp only [CollatzResearch.WordTrace]
  refine ⟨68006327199495881816966663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181350205865322351511911101 68006327199495881816966663)
  ·
    refine ⟨102009490799243822725449995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68006327199495881816966663 102009490799243822725449995)
    ·
      refine ⟨153014236198865734088174993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102009490799243822725449995 153014236198865734088174993)
      ·
        refine ⟨114760677149149300566131245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153014236198865734088174993 114760677149149300566131245)
        ·
          refine ⟨43035253930930987712299217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114760677149149300566131245 43035253930930987712299217)
          ·
            refine ⟨32276440448198240784224413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43035253930930987712299217 32276440448198240784224413)
            ·
              refine ⟨12103665168074340294084155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32276440448198240784224413 12103665168074340294084155)
              ·
                refine ⟨18155497752111510441126233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12103665168074340294084155 18155497752111510441126233)
                ·
                  refine ⟨13616623314083632830844675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18155497752111510441126233 13616623314083632830844675)
                  ·
                    refine ⟨20424934971125449246267013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13616623314083632830844675 20424934971125449246267013)
                    ·
                      refine ⟨3829675307086021733675065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20424934971125449246267013 3829675307086021733675065)
                      ·
                        rfl

theorem cell23_7458266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 2, 1, 4].length) (baseStart_7458266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7458266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7458266 prefixEnd_7458266 := by exact prefixLift 7458266
  have htrace : WordTrace (prefixWord ++ tailWord_7458266) baseStart_7458266 baseEnd_7458266 := by
    simpa [prefixWord, tailWord_7458266, baseEnd_7458266] using wordTrace_append hprefix tailTrace_7458266
  have hstable : (prefixWord ++ tailWord_7458266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7458266).length < 2 ^ (prefixWord ++ tailWord_7458266).sum := by decide
  have hdescent : baseEnd_7458266 < baseStart_7458266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7458266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7458279 : List Nat := [1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 6]
def baseStart_7458279 : Nat := 118140960795 + 7458279 * 2 ^ 59
def prefixEnd_7458279 : Nat := 4983230072969 + 3 ^ 40 * 7458279 * 2
def baseEnd_7458279 : Nat := 3829681982334530182812505

theorem tailTrace_7458279 : CollatzResearch.WordTrace tailWord_7458279 prefixEnd_7458279 3829681982334530182812505 := by
  unfold tailWord_7458279
  simp only [CollatzResearch.WordTrace]
  refine ⟨272025782946936430488089891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181350521964624286992059927 272025782946936430488089891)
  ·
    refine ⟨408038674420404645732134837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272025782946936430488089891 408038674420404645732134837)
    ·
      refine ⟨38253625726912935537387641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 408038674420404645732134837 38253625726912935537387641)
      ·
        refine ⟨28690219295184701653040731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38253625726912935537387641 28690219295184701653040731)
        ·
          refine ⟨43035328942777052479561097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28690219295184701653040731 43035328942777052479561097)
          ·
            refine ⟨32276496707082789359670823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43035328942777052479561097 32276496707082789359670823)
            ·
              refine ⟨48414745060624184039506235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32276496707082789359670823 48414745060624184039506235)
              ·
                refine ⟨72622117590936276059259353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48414745060624184039506235 72622117590936276059259353)
                ·
                  refine ⟨54466588193202207044444515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72622117590936276059259353 54466588193202207044444515)
                  ·
                    refine ⟨81699882289803310566666773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54466588193202207044444515 81699882289803310566666773)
                    ·
                      refine ⟨3829681982334530182812505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81699882289803310566666773 3829681982334530182812505)
                      ·
                        rfl

theorem cell23_7458279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_7458279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7458279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7458279 prefixEnd_7458279 := by exact prefixLift 7458279
  have htrace : WordTrace (prefixWord ++ tailWord_7458279) baseStart_7458279 baseEnd_7458279 := by
    simpa [prefixWord, tailWord_7458279, baseEnd_7458279] using wordTrace_append hprefix tailTrace_7458279
  have hstable : (prefixWord ++ tailWord_7458279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7458279).length < 2 ^ (prefixWord ++ tailWord_7458279).sum := by decide
  have hdescent : baseEnd_7458279 < baseStart_7458279 := by decide
  rcases family_descends (prefixWord ++ tailWord_7458279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7458286 : List Nat := [4, 1, 2, 1, 2, 1, 2, 1, 4, 2, 3]
def baseStart_7458286 : Nat := 118140960795 + 7458286 * 2 ^ 59
def prefixEnd_7458286 : Nat := 4983230072969 + 3 ^ 40 * 7458286 * 2
def baseEnd_7458286 : Nat := 3829685576699111655424973

theorem tailTrace_7458286 : CollatzResearch.WordTrace tailWord_7458286 prefixEnd_7458286 3829685576699111655424973 := by
  unfold tailWord_7458286
  simp only [CollatzResearch.WordTrace]
  refine ⟨34003254782238883835449339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181350692171940713789063141 34003254782238883835449339)
  ·
    refine ⟨51004882173358325753174009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34003254782238883835449339 51004882173358325753174009)
    ·
      refine ⟨38253661630018744314880507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51004882173358325753174009 38253661630018744314880507)
      ·
        refine ⟨57380492445028116472320761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38253661630018744314880507 57380492445028116472320761)
        ·
          refine ⟨43035369333771087354240571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57380492445028116472320761 43035369333771087354240571)
          ·
            refine ⟨64553054000656631031360857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43035369333771087354240571 64553054000656631031360857)
            ·
              refine ⟨48414790500492473273520643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64553054000656631031360857 48414790500492473273520643)
              ·
                refine ⟨72622185750738709910280965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48414790500492473273520643 72622185750738709910280965)
                ·
                  refine ⟨13616659828263508108177681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72622185750738709910280965 13616659828263508108177681)
                  ·
                    refine ⟨10212494871197631081133261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13616659828263508108177681 10212494871197631081133261)
                    ·
                      refine ⟨3829685576699111655424973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10212494871197631081133261 3829685576699111655424973)
                      ·
                        rfl

theorem cell23_7458286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_7458286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7458286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7458286 prefixEnd_7458286 := by exact prefixLift 7458286
  have htrace : WordTrace (prefixWord ++ tailWord_7458286) baseStart_7458286 baseEnd_7458286 := by
    simpa [prefixWord, tailWord_7458286, baseEnd_7458286] using wordTrace_append hprefix tailTrace_7458286
  have hstable : (prefixWord ++ tailWord_7458286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7458286).length < 2 ^ (prefixWord ++ tailWord_7458286).sum := by decide
  have hdescent : baseEnd_7458286 < baseStart_7458286 := by decide
  rcases family_descends (prefixWord ++ tailWord_7458286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7458289 : List Nat := [1, 2, 2, 2, 3, 3, 1, 1, 8]
def baseStart_7458289 : Nat := 118140960795 + 7458289 * 2 ^ 59
def prefixEnd_7458289 : Nat := 4983230072969 + 3 ^ 40 * 7458289 * 2
def baseEnd_7458289 : Nat := 425520790793452793743051

theorem tailTrace_7458289 : CollatzResearch.WordTrace tailWord_7458289 prefixEnd_7458289 425520790793452793743051 := by
  unfold tailWord_7458289
  simp only [CollatzResearch.WordTrace]
  refine ⟨272026147676900202195953921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181350765117933468130635947 272026147676900202195953921)
  ·
    refine ⟨204019610757675151646965441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272026147676900202195953921 204019610757675151646965441)
    ·
      refine ⟨153014708068256363735224081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204019610757675151646965441 153014708068256363735224081)
      ·
        refine ⟨114761031051192272801418061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153014708068256363735224081 114761031051192272801418061)
        ·
          refine ⟨43035386644197102300531773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114761031051192272801418061 43035386644197102300531773)
          ·
            refine ⟨16138269991573913362699415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43035386644197102300531773 16138269991573913362699415)
            ·
              refine ⟨24207404987360870044049123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16138269991573913362699415 24207404987360870044049123)
              ·
                refine ⟨36311107481041305066073685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24207404987360870044049123 36311107481041305066073685)
                ·
                  refine ⟨425520790793452793743051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36311107481041305066073685 425520790793452793743051)
                  ·
                    rfl

theorem cell23_7458289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 8].length) (baseStart_7458289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7458289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7458289 prefixEnd_7458289 := by exact prefixLift 7458289
  have htrace : WordTrace (prefixWord ++ tailWord_7458289) baseStart_7458289 baseEnd_7458289 := by
    simpa [prefixWord, tailWord_7458289, baseEnd_7458289] using wordTrace_append hprefix tailTrace_7458289
  have hstable : (prefixWord ++ tailWord_7458289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7458289).length < 2 ^ (prefixWord ++ tailWord_7458289).sum := by decide
  have hdescent : baseEnd_7458289 < baseStart_7458289 := by decide
  rcases family_descends (prefixWord ++ tailWord_7458289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7458293 : List Nat := [1, 3, 5, 1, 1, 1, 1, 3, 3, 4]
def baseStart_7458293 : Nat := 118140960795 + 7458293 * 2 ^ 59
def prefixEnd_7458293 : Nat := 4983230072969 + 3 ^ 40 * 7458293 * 2
def baseEnd_7458293 : Nat := 1276563057021231042679147

theorem tailTrace_7458293 : CollatzResearch.WordTrace tailWord_7458293 prefixEnd_7458293 1276563057021231042679147 := by
  unfold tailWord_7458293
  simp only [CollatzResearch.WordTrace]
  refine ⟨272026293568885710879099533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181350862379257140586066355 272026293568885710879099533)
  ·
    refine ⟨102009860088332141579662325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272026293568885710879099533 102009860088332141579662325)
    ·
      refine ⟨9563424383281138273093343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102009860088332141579662325 9563424383281138273093343)
      ·
        refine ⟨14345136574921707409640015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9563424383281138273093343 14345136574921707409640015)
        ·
          refine ⟨21517704862382561114460023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14345136574921707409640015 21517704862382561114460023)
          ·
            refine ⟨32276557293573841671690035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21517704862382561114460023 32276557293573841671690035)
            ·
              refine ⟨48414835940360762507535053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32276557293573841671690035 48414835940360762507535053)
              ·
                refine ⟨18155563477635285940325645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48414835940360762507535053 18155563477635285940325645)
                ·
                  refine ⟨6808336304113232227622117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18155563477635285940325645 6808336304113232227622117)
                  ·
                    refine ⟨1276563057021231042679147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6808336304113232227622117 1276563057021231042679147)
                    ·
                      rfl

theorem cell23_7458293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_7458293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7458293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7458293 prefixEnd_7458293 := by exact prefixLift 7458293
  have htrace : WordTrace (prefixWord ++ tailWord_7458293) baseStart_7458293 baseEnd_7458293 := by
    simpa [prefixWord, tailWord_7458293, baseEnd_7458293] using wordTrace_append hprefix tailTrace_7458293
  have hstable : (prefixWord ++ tailWord_7458293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7458293).length < 2 ^ (prefixWord ++ tailWord_7458293).sum := by decide
  have hdescent : baseEnd_7458293 < baseStart_7458293 := by decide
  rcases family_descends (prefixWord ++ tailWord_7458293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7458350 : List Nat := [4, 1, 3, 1, 2, 1, 3, 1, 3, 1, 3]
def baseStart_7458350 : Nat := 118140960795 + 7458350 * 2 ^ 59
def prefixEnd_7458350 : Nat := 4983230072969 + 3 ^ 40 * 7458350 * 2
def baseEnd_7458350 : Nat := 3829718439460999405024679

theorem tailTrace_7458350 : CollatzResearch.WordTrace tailWord_7458350 prefixEnd_7458350 3829718439460999405024679 := by
  unfold tailWord_7458350
  simp only [CollatzResearch.WordTrace]
  refine ⟨34003546566209901201740563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181352248353119473075949669 34003546566209901201740563)
  ·
    refine ⟨51005319849314851802610845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34003546566209901201740563 51005319849314851802610845)
    ·
      refine ⟨19126994943493069425979067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51005319849314851802610845 19126994943493069425979067)
      ·
        refine ⟨28690492415239604138968601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19126994943493069425979067 28690492415239604138968601)
        ·
          refine ⟨21517869311429703104226451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28690492415239604138968601 21517869311429703104226451)
          ·
            refine ⟨32276803967144554656339677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21517869311429703104226451 32276803967144554656339677)
            ·
              refine ⟨12103801487679207996127379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32276803967144554656339677 12103801487679207996127379)
              ·
                refine ⟨18155702231518811994191069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12103801487679207996127379 18155702231518811994191069)
                ·
                  refine ⟨6808388336819554497821651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18155702231518811994191069 6808388336819554497821651)
                  ·
                    refine ⟨10212582505229331746732477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6808388336819554497821651 10212582505229331746732477)
                    ·
                      refine ⟨3829718439460999405024679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10212582505229331746732477 3829718439460999405024679)
                      ·
                        rfl

theorem cell23_7458350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_7458350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7458350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7458350 prefixEnd_7458350 := by exact prefixLift 7458350
  have htrace : WordTrace (prefixWord ++ tailWord_7458350) baseStart_7458350 baseEnd_7458350 := by
    simpa [prefixWord, tailWord_7458350, baseEnd_7458350] using wordTrace_append hprefix tailTrace_7458350
  have hstable : (prefixWord ++ tailWord_7458350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7458350).length < 2 ^ (prefixWord ++ tailWord_7458350).sum := by decide
  have hdescent : baseEnd_7458350 < baseStart_7458350 := by decide
  rcases family_descends (prefixWord ++ tailWord_7458350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7458373 : List Nat := [1, 3, 1, 1, 1, 4, 2, 1, 5, 2, 2]
def baseStart_7458373 : Nat := 118140960795 + 7458373 * 2 ^ 59
def prefixEnd_7458373 : Nat := 4983230072969 + 3 ^ 40 * 7458373 * 2
def baseEnd_7458373 : Nat := 3829730249516052815037073

theorem tailTrace_7458373 : CollatzResearch.WordTrace tailWord_7458373 prefixEnd_7458373 3829730249516052815037073 := by
  unfold tailWord_7458373
  simp only [CollatzResearch.WordTrace]
  refine ⟨272029211408595884542011773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181352807605730589694674515 272029211408595884542011773)
  ·
    refine ⟨102010954278223456703254415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272029211408595884542011773 102010954278223456703254415)
    ·
      refine ⟨153016431417335185054881623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102010954278223456703254415 153016431417335185054881623)
      ·
        refine ⟨229524647126002777582322435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153016431417335185054881623 229524647126002777582322435)
        ·
          refine ⟨344286970689004166373483653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229524647126002777582322435 344286970689004166373483653)
          ·
            refine ⟨64553807004188281195028185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 344286970689004166373483653 64553807004188281195028185)
            ·
              refine ⟨48415355253141210896271139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64553807004188281195028185 48415355253141210896271139)
              ·
                refine ⟨72623032879711816344406709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48415355253141210896271139 72623032879711816344406709)
                ·
                  refine ⟨6808409332472982782288129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72623032879711816344406709 6808409332472982782288129)
                  ·
                    refine ⟨5106306999354737086716097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6808409332472982782288129 5106306999354737086716097)
                    ·
                      refine ⟨3829730249516052815037073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5106306999354737086716097 3829730249516052815037073)
                      ·
                        rfl

theorem cell23_7458373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 5, 2, 2].length) (baseStart_7458373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7458373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7458373 prefixEnd_7458373 := by exact prefixLift 7458373
  have htrace : WordTrace (prefixWord ++ tailWord_7458373) baseStart_7458373 baseEnd_7458373 := by
    simpa [prefixWord, tailWord_7458373, baseEnd_7458373] using wordTrace_append hprefix tailTrace_7458373
  have hstable : (prefixWord ++ tailWord_7458373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7458373).length < 2 ^ (prefixWord ++ tailWord_7458373).sum := by decide
  have hdescent : baseEnd_7458373 < baseStart_7458373 := by decide
  rcases family_descends (prefixWord ++ tailWord_7458373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7458386 : List Nat := [3, 2, 2, 1, 2, 2, 1, 1, 3, 2, 4]
def baseStart_7458386 : Nat := 118140960795 + 7458386 * 2 ^ 59
def prefixEnd_7458386 : Nat := 4983230072969 + 3 ^ 40 * 7458386 * 2
def baseEnd_7458386 : Nat := 3829736924764561264174513

theorem tailTrace_7458386 : CollatzResearch.WordTrace tailWord_7458386 prefixEnd_7458386 3829736924764561264174513 := by
  unfold tailWord_7458386
  simp only [CollatzResearch.WordTrace]
  refine ⟨68007421389387196940558753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181353123705032525174823341 68007421389387196940558753)
  ·
    refine ⟨51005566042040397705419065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68007421389387196940558753 51005566042040397705419065)
    ·
      refine ⟨38254174531530298279064299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51005566042040397705419065 38254174531530298279064299)
      ·
        refine ⟨57381261797295447418596449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38254174531530298279064299 57381261797295447418596449)
        ·
          refine ⟨43035946347971585563947337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57381261797295447418596449 43035946347971585563947337)
          ·
            refine ⟨32276959760978689172960503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43035946347971585563947337 32276959760978689172960503)
            ·
              refine ⟨48415439641468033759440755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32276959760978689172960503 48415439641468033759440755)
              ·
                refine ⟨72623159462202050639161133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48415439641468033759440755 72623159462202050639161133)
                ·
                  refine ⟨27233684798325768989685425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72623159462202050639161133 27233684798325768989685425)
                  ·
                    refine ⟨20425263598744326742264069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27233684798325768989685425 20425263598744326742264069)
                    ·
                      refine ⟨3829736924764561264174513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20425263598744326742264069 3829736924764561264174513)
                      ·
                        rfl

theorem cell23_7458386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_7458386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7458386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7458386 prefixEnd_7458386 := by exact prefixLift 7458386
  have htrace : WordTrace (prefixWord ++ tailWord_7458386) baseStart_7458386 baseEnd_7458386 := by
    simpa [prefixWord, tailWord_7458386, baseEnd_7458386] using wordTrace_append hprefix tailTrace_7458386
  have hstable : (prefixWord ++ tailWord_7458386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7458386).length < 2 ^ (prefixWord ++ tailWord_7458386).sum := by decide
  have hdescent : baseEnd_7458386 < baseStart_7458386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7458386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7458409 : List Nat := [1, 2, 1, 1, 1, 4, 3, 1, 2, 7]
def baseStart_7458409 : Nat := 118140960795 + 7458409 * 2 ^ 59
def prefixEnd_7458409 : Nat := 4983230072969 + 3 ^ 40 * 7458409 * 2
def baseEnd_7458409 : Nat := 1276582911606538224728969

theorem tailTrace_7458409 : CollatzResearch.WordTrace tailWord_7458409 prefixEnd_7458409 1276582911606538224728969 := by
  unfold tailWord_7458409
  simp only [CollatzResearch.WordTrace]
  refine ⟨272030524436465462690322281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181353682957643641793548187 272030524436465462690322281)
  ·
    refine ⟨204022893327349097017741711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272030524436465462690322281 204022893327349097017741711)
    ·
      refine ⟨306034339991023645526612567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204022893327349097017741711 306034339991023645526612567)
      ·
        refine ⟨459051509986535468289918851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306034339991023645526612567 459051509986535468289918851)
        ·
          refine ⟨688577264979803202434878277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459051509986535468289918851 688577264979803202434878277)
          ·
            refine ⟨129108237183713100456539677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 688577264979803202434878277 129108237183713100456539677)
            ·
              refine ⟨48415588943892412671202379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129108237183713100456539677 48415588943892412671202379)
              ·
                refine ⟨72623383415838619006803569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48415588943892412671202379 72623383415838619006803569)
                ·
                  refine ⟨54467537561878964255102677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72623383415838619006803569 54467537561878964255102677)
                  ·
                    refine ⟨1276582911606538224728969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54467537561878964255102677 1276582911606538224728969)
                    ·
                      rfl

theorem cell23_7458409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 7].length) (baseStart_7458409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7458409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7458409 prefixEnd_7458409 := by exact prefixLift 7458409
  have htrace : WordTrace (prefixWord ++ tailWord_7458409) baseStart_7458409 baseEnd_7458409 := by
    simpa [prefixWord, tailWord_7458409, baseEnd_7458409] using wordTrace_append hprefix tailTrace_7458409
  have hstable : (prefixWord ++ tailWord_7458409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7458409).length < 2 ^ (prefixWord ++ tailWord_7458409).sum := by decide
  have hdescent : baseEnd_7458409 < baseStart_7458409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7458409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7458413 : List Nat := [1, 5, 1, 1, 4, 2, 1, 8]
def baseStart_7458413 : Nat := 118140960795 + 7458413 * 2 ^ 59
def prefixEnd_7458413 : Nat := 4983230072969 + 3 ^ 40 * 7458413 * 2
def baseEnd_7458413 : Nat := 141842621805267876242107

theorem tailTrace_7458413 : CollatzResearch.WordTrace tailWord_7458413 prefixEnd_7458413 141842621805267876242107 := by
  unfold tailWord_7458413
  simp only [CollatzResearch.WordTrace]
  refine ⟨272030670328450971373467893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181353780218967314248978595 272030670328450971373467893)
  ·
    refine ⟨25502875343292278566262615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 272030670328450971373467893 25502875343292278566262615)
    ·
      refine ⟨38254313014938417849393923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25502875343292278566262615 38254313014938417849393923)
      ·
        refine ⟨57381469522407626774090885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38254313014938417849393923 57381469522407626774090885)
        ·
          refine ⟨10759025535451430020142041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57381469522407626774090885 10759025535451430020142041)
          ·
            refine ⟨8069269151588572515106531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10759025535451430020142041 8069269151588572515106531)
            ·
              refine ⟨12103903727382858772659797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8069269151588572515106531 12103903727382858772659797)
              ·
                refine ⟨141842621805267876242107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12103903727382858772659797 141842621805267876242107)
                ·
                  rfl

theorem cell23_7458413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 8].length) (baseStart_7458413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7458413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7458413 prefixEnd_7458413 := by exact prefixLift 7458413
  have htrace : WordTrace (prefixWord ++ tailWord_7458413) baseStart_7458413 baseEnd_7458413 := by
    simpa [prefixWord, tailWord_7458413, baseEnd_7458413] using wordTrace_append hprefix tailTrace_7458413
  have hstable : (prefixWord ++ tailWord_7458413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7458413).length < 2 ^ (prefixWord ++ tailWord_7458413).sum := by decide
  have hdescent : baseEnd_7458413 < baseStart_7458413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7458413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7458456 : List Nat := [2, 1, 2, 4, 1, 2, 1, 2, 2, 6]
def baseStart_7458456 : Nat := 118140960795 + 7458456 * 2 ^ 59
def prefixEnd_7458456 : Nat := 4983230072969 + 3 ^ 40 * 7458456 * 2
def baseEnd_7458456 : Nat := 1276590956136791996766397

theorem tailTrace_7458456 : CollatzResearch.WordTrace tailWord_7458456 prefixEnd_7458456 1276590956136791996766397 := by
  unfold tailWord_7458456
  simp only [CollatzResearch.WordTrace]
  refine ⟨136016119333647594858641611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181354825778196793144855481 136016119333647594858641611)
  ·
    refine ⟨204024179000471392287962417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136016119333647594858641611 204024179000471392287962417)
    ·
      refine ⟨153018134250353544215971813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204024179000471392287962417 153018134250353544215971813)
      ·
        refine ⟨28690900171941289540494715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153018134250353544215971813 28690900171941289540494715)
        ·
          refine ⟨43036350257911934310742073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28690900171941289540494715 43036350257911934310742073)
          ·
            refine ⟨32277262693433950733056555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43036350257911934310742073 32277262693433950733056555)
            ·
              refine ⟨48415894040150926099584833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32277262693433950733056555 48415894040150926099584833)
              ·
                refine ⟨36311920530113194574688625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48415894040150926099584833 36311920530113194574688625)
                ·
                  refine ⟨27233940397584895931016469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36311920530113194574688625 27233940397584895931016469)
                  ·
                    refine ⟨1276590956136791996766397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27233940397584895931016469 1276590956136791996766397)
                    ·
                      rfl

theorem cell23_7458456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 2, 6].length) (baseStart_7458456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7458456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7458456 prefixEnd_7458456 := by exact prefixLift 7458456
  have htrace : WordTrace (prefixWord ++ tailWord_7458456) baseStart_7458456 baseEnd_7458456 := by
    simpa [prefixWord, tailWord_7458456, baseEnd_7458456] using wordTrace_append hprefix tailTrace_7458456
  have hstable : (prefixWord ++ tailWord_7458456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7458456).length < 2 ^ (prefixWord ++ tailWord_7458456).sum := by decide
  have hdescent : baseEnd_7458456 < baseStart_7458456 := by decide
  rcases family_descends (prefixWord ++ tailWord_7458456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7458480 : List Nat := [2, 1, 1, 1, 2, 1, 4, 5, 2, 2, 2]
def baseStart_7458480 : Nat := 118140960795 + 7458480 * 2 ^ 59
def prefixEnd_7458480 : Nat := 4983230072969 + 3 ^ 40 * 7458480 * 2
def baseEnd_7458480 : Nat := 3829785191946083896399081

theorem tailTrace_7458480 : CollatzResearch.WordTrace tailWord_7458480 prefixEnd_7458480 3829785191946083896399081 := by
  unfold tailWord_7458480
  simp only [CollatzResearch.WordTrace]
  refine ⟨136016557009604120908078447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181355409346138827877437929 136016557009604120908078447)
  ·
    refine ⟨204024835514406181362117671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136016557009604120908078447 204024835514406181362117671)
    ·
      refine ⟨306037253271609272043176507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204024835514406181362117671 306037253271609272043176507)
      ·
        refine ⟨459055879907413908064764761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306037253271609272043176507 459055879907413908064764761)
        ·
          refine ⟨344291909930560431048573571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 459055879907413908064764761 344291909930560431048573571)
          ·
            refine ⟨516437864895840646572860357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344291909930560431048573571 516437864895840646572860357)
            ·
              refine ⟨96832099667970121232411317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 516437864895840646572860357 96832099667970121232411317)
              ·
                refine ⟨9078009343872198865538561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96832099667970121232411317 9078009343872198865538561)
                ·
                  refine ⟨6808507007904149149153921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9078009343872198865538561 6808507007904149149153921)
                  ·
                    refine ⟨5106380255928111861865441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6808507007904149149153921 5106380255928111861865441)
                    ·
                      refine ⟨3829785191946083896399081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5106380255928111861865441 3829785191946083896399081)
                      ·
                        rfl

theorem cell23_7458480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 5, 2, 2, 2].length) (baseStart_7458480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7458480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7458480 prefixEnd_7458480 := by exact prefixLift 7458480
  have htrace : WordTrace (prefixWord ++ tailWord_7458480) baseStart_7458480 baseEnd_7458480 := by
    simpa [prefixWord, tailWord_7458480, baseEnd_7458480] using wordTrace_append hprefix tailTrace_7458480
  have hstable : (prefixWord ++ tailWord_7458480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7458480).length < 2 ^ (prefixWord ++ tailWord_7458480).sum := by decide
  have hdescent : baseEnd_7458480 < baseStart_7458480 := by decide
  rcases family_descends (prefixWord ++ tailWord_7458480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7458520 : List Nat := [2, 1, 2, 2, 3, 1, 5, 2, 5]
def baseStart_7458520 : Nat := 118140960795 + 7458520 * 2 ^ 59
def prefixEnd_7458520 : Nat := 4983230072969 + 3 ^ 40 * 7458520 * 2
def baseEnd_7458520 : Nat := 425533970130251526655433

theorem tailTrace_7458520 : CollatzResearch.WordTrace tailWord_7458520 prefixEnd_7458520 425533970130251526655433 := by
  unfold tailWord_7458520
  simp only [CollatzResearch.WordTrace]
  refine ⟨136017286469531664323806507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181356381959375552431742009 136017286469531664323806507)
  ·
    refine ⟨204025929704297496485709761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136017286469531664323806507 204025929704297496485709761)
    ·
      refine ⟨153019447278223122364282321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204025929704297496485709761 153019447278223122364282321)
      ·
        refine ⟨114764585458667341773211741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153019447278223122364282321 114764585458667341773211741)
        ·
          refine ⟨43036719547000253164954403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114764585458667341773211741 43036719547000253164954403)
          ·
            refine ⟨64555079320500379747431605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43036719547000253164954403 64555079320500379747431605)
            ·
              refine ⟨6052038686296910601321713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64555079320500379747431605 6052038686296910601321713)
              ·
                refine ⟨4539029014722682950991285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6052038686296910601321713 4539029014722682950991285)
                ·
                  refine ⟨425533970130251526655433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4539029014722682950991285 425533970130251526655433)
                  ·
                    rfl

theorem cell23_7458520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 2, 5].length) (baseStart_7458520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7458520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7458520 prefixEnd_7458520 := by exact prefixLift 7458520
  have htrace : WordTrace (prefixWord ++ tailWord_7458520) baseStart_7458520 baseEnd_7458520 := by
    simpa [prefixWord, tailWord_7458520, baseEnd_7458520] using wordTrace_append hprefix tailTrace_7458520
  have hstable : (prefixWord ++ tailWord_7458520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7458520).length < 2 ^ (prefixWord ++ tailWord_7458520).sum := by decide
  have hdescent : baseEnd_7458520 < baseStart_7458520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7458520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7458531 : List Nat := [1, 1, 1, 7, 2, 2, 2, 1, 2, 2, 2]
def baseStart_7458531 : Nat := 118140960795 + 7458531 * 2 ^ 59
def prefixEnd_7458531 : Nat := 4983230072969 + 3 ^ 40 * 7458531 * 2
def baseEnd_7458531 : Nat := 3829811379459463196861347

theorem tailTrace_7458531 : CollatzResearch.WordTrace tailWord_7458531 prefixEnd_7458531 3829811379459463196861347 := by
  unfold tailWord_7458531
  simp only [CollatzResearch.WordTrace]
  refine ⟨272034974142023477526263447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181356649428015651684175631 272034974142023477526263447)
  ·
    refine ⟨408052461213035216289395171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272034974142023477526263447 408052461213035216289395171)
    ·
      refine ⟨612078691819552824434092757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408052461213035216289395171 612078691819552824434092757)
      ·
        refine ⟨14345594339520769322674049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 612078691819552824434092757 14345594339520769322674049)
        ·
          refine ⟨10759195754640576992005537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14345594339520769322674049 10759195754640576992005537)
          ·
            refine ⟨8069396815980432744004153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10759195754640576992005537 8069396815980432744004153)
            ·
              refine ⟨6052047611985324558003115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8069396815980432744004153 6052047611985324558003115)
              ·
                refine ⟨9078071417977986837004673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6052047611985324558003115 9078071417977986837004673)
                ·
                  refine ⟨6808553563483490127753505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9078071417977986837004673 6808553563483490127753505)
                  ·
                    refine ⟨5106415172612617595815129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6808553563483490127753505 5106415172612617595815129)
                    ·
                      refine ⟨3829811379459463196861347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5106415172612617595815129 3829811379459463196861347)
                      ·
                        rfl

theorem cell23_7458531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_7458531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7458531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7458531 prefixEnd_7458531 := by exact prefixLift 7458531
  have htrace : WordTrace (prefixWord ++ tailWord_7458531) baseStart_7458531 baseEnd_7458531 := by
    simpa [prefixWord, tailWord_7458531, baseEnd_7458531] using wordTrace_append hprefix tailTrace_7458531
  have hstable : (prefixWord ++ tailWord_7458531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7458531).length < 2 ^ (prefixWord ++ tailWord_7458531).sum := by decide
  have hdescent : baseEnd_7458531 < baseStart_7458531 := by decide
  rcases family_descends (prefixWord ++ tailWord_7458531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7458550 : List Nat := [5, 1, 1, 1, 1, 4, 2, 1, 2, 5]
def baseStart_7458550 : Nat := 118140960795 + 7458550 * 2 ^ 59
def prefixEnd_7458550 : Nat := 4983230072969 + 3 ^ 40 * 7458550 * 2
def baseEnd_7458550 : Nat := 1276607045197299540841253

theorem tailTrace_7458550 : CollatzResearch.WordTrace tailWord_7458550 prefixEnd_7458550 1276607045197299540841253 := by
  unfold tailWord_7458550
  simp only [CollatzResearch.WordTrace]
  refine ⟨17002229195559665235700319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 181357111419303095847470069 17002229195559665235700319)
  ·
    refine ⟨25503343793339497853550479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17002229195559665235700319 25503343793339497853550479)
    ·
      refine ⟨38255015690009246780325719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25503343793339497853550479 38255015690009246780325719)
      ·
        refine ⟨57382523535013870170488579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38255015690009246780325719 57382523535013870170488579)
        ·
          refine ⟨86073785302520805255732869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57382523535013870170488579 86073785302520805255732869)
          ·
            refine ⟨16138834744222650985449913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86073785302520805255732869 16138834744222650985449913)
            ·
              refine ⟨12104126058166988239087435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16138834744222650985449913 12104126058166988239087435)
              ·
                refine ⟨18156189087250482358631153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12104126058166988239087435 18156189087250482358631153)
                ·
                  refine ⟨13617141815437861768973365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18156189087250482358631153 13617141815437861768973365)
                  ·
                    refine ⟨1276607045197299540841253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13617141815437861768973365 1276607045197299540841253)
                    ·
                      rfl

theorem cell23_7458550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_7458550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7458550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7458550 prefixEnd_7458550 := by exact prefixLift 7458550
  have htrace : WordTrace (prefixWord ++ tailWord_7458550) baseStart_7458550 baseEnd_7458550 := by
    simpa [prefixWord, tailWord_7458550, baseEnd_7458550] using wordTrace_append hprefix tailTrace_7458550
  have hstable : (prefixWord ++ tailWord_7458550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7458550).length < 2 ^ (prefixWord ++ tailWord_7458550).sum := by decide
  have hdescent : baseEnd_7458550 < baseStart_7458550 := by decide
  rcases family_descends (prefixWord ++ tailWord_7458550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7458553 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 6, 4, 2]
def baseStart_7458553 : Nat := 118140960795 + 7458553 * 2 ^ 59
def prefixEnd_7458553 : Nat := 4983230072969 + 3 ^ 40 * 7458553 * 2
def baseEnd_7458553 : Nat := 3829822676033862110786245

theorem tailTrace_7458553 : CollatzResearch.WordTrace tailWord_7458553 prefixEnd_7458553 3829822676033862110786245 := by
  unfold tailWord_7458553
  simp only [CollatzResearch.WordTrace]
  refine ⟨272035776547943775283564313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181357184365295850189042875 272035776547943775283564313)
  ·
    refine ⟨204026832410957831462673235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272035776547943775283564313 204026832410957831462673235)
    ·
      refine ⟨306040248616436747194009853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204026832410957831462673235 306040248616436747194009853)
      ·
        refine ⟨114765093231163780197753695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 306040248616436747194009853 114765093231163780197753695)
        ·
          refine ⟨172147639846745670296630543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114765093231163780197753695 172147639846745670296630543)
          ·
            refine ⟨258221459770118505444945815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172147639846745670296630543 258221459770118505444945815)
            ·
              refine ⟨387332189655177758167418723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258221459770118505444945815 387332189655177758167418723)
              ·
                refine ⟨580998284482766637251128085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 387332189655177758167418723 580998284482766637251128085)
                ·
                  refine ⟨27234294585129686121146629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 580998284482766637251128085 27234294585129686121146629)
                  ·
                    refine ⟨5106430234711816147714993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27234294585129686121146629 5106430234711816147714993)
                    ·
                      refine ⟨3829822676033862110786245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5106430234711816147714993 3829822676033862110786245)
                      ·
                        rfl

theorem cell23_7458553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 4, 2].length) (baseStart_7458553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7458553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7458553 prefixEnd_7458553 := by exact prefixLift 7458553
  have htrace : WordTrace (prefixWord ++ tailWord_7458553) baseStart_7458553 baseEnd_7458553 := by
    simpa [prefixWord, tailWord_7458553, baseEnd_7458553] using wordTrace_append hprefix tailTrace_7458553
  have hstable : (prefixWord ++ tailWord_7458553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7458553).length < 2 ^ (prefixWord ++ tailWord_7458553).sum := by decide
  have hdescent : baseEnd_7458553 < baseStart_7458553 := by decide
  rcases family_descends (prefixWord ++ tailWord_7458553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7458593 : List Nat := [1, 2, 3, 2, 1, 3, 2, 3, 6]
def baseStart_7458593 : Nat := 118140960795 + 7458593 * 2 ^ 59
def prefixEnd_7458593 : Nat := 4983230072969 + 3 ^ 40 * 7458593 * 2
def baseEnd_7458593 : Nat := 425538135028893550476229

theorem tailTrace_7458593 : CollatzResearch.WordTrace tailWord_7458593 prefixEnd_7458593 425538135028893550476229 := by
  unfold tailWord_7458593
  simp only [CollatzResearch.WordTrace]
  refine ⟨272037235467798862115020433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181358156978532574743346955 272037235467798862115020433)
  ·
    refine ⟨204027926600849146586265325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272037235467798862115020433 204027926600849146586265325)
    ·
      refine ⟨76510472475318429969849497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204027926600849146586265325 76510472475318429969849497)
      ·
        refine ⟨57382854356488822477387123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76510472475318429969849497 57382854356488822477387123)
        ·
          refine ⟨86074281534733233716080685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57382854356488822477387123 86074281534733233716080685)
          ·
            refine ⟨32277855575524962643530257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86074281534733233716080685 32277855575524962643530257)
            ·
              refine ⟨24208391681643721982647693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32277855575524962643530257 24208391681643721982647693)
              ·
                refine ⟨9078146880616395743492885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24208391681643721982647693 9078146880616395743492885)
                ·
                  refine ⟨425538135028893550476229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9078146880616395743492885 425538135028893550476229)
                  ·
                    rfl

theorem cell23_7458593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 3, 6].length) (baseStart_7458593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7458593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7458593 prefixEnd_7458593 := by exact prefixLift 7458593
  have htrace : WordTrace (prefixWord ++ tailWord_7458593) baseStart_7458593 baseEnd_7458593 := by
    simpa [prefixWord, tailWord_7458593, baseEnd_7458593] using wordTrace_append hprefix tailTrace_7458593
  have hstable : (prefixWord ++ tailWord_7458593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7458593).length < 2 ^ (prefixWord ++ tailWord_7458593).sum := by decide
  have hdescent : baseEnd_7458593 < baseStart_7458593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7458593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7458614 : List Nat := [5, 1, 2, 2, 1, 1, 1, 5, 1, 4]
def baseStart_7458614 : Nat := 118140960795 + 7458614 * 2 ^ 59
def prefixEnd_7458614 : Nat := 4983230072969 + 3 ^ 40 * 7458614 * 2
def baseEnd_7458614 : Nat := 1276617999451262124041155

theorem tailTrace_7458614 : CollatzResearch.WordTrace tailWord_7458614 prefixEnd_7458614 1276617999451262124041155 := by
  unfold tailWord_7458614
  simp only [CollatzResearch.WordTrace]
  refine ⟨17002375087545173918845931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 181358667600481855134356597 17002375087545173918845931)
  ·
    refine ⟨25503562631317760878268897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17002375087545173918845931 25503562631317760878268897)
    ·
      refine ⟨19127671973488320658701673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25503562631317760878268897 19127671973488320658701673)
      ·
        refine ⟨14345753980116240494026255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19127671973488320658701673 14345753980116240494026255)
        ·
          refine ⟨21518630970174360741039383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14345753980116240494026255 21518630970174360741039383)
          ·
            refine ⟨32277946455261541111559075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21518630970174360741039383 32277946455261541111559075)
            ·
              refine ⟨48416919682892311667338613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32277946455261541111559075 48416919682892311667338613)
              ·
                refine ⟨4539086220271154218812995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48416919682892311667338613 4539086220271154218812995)
                ·
                  refine ⟨6808629330406731328219493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4539086220271154218812995 6808629330406731328219493)
                  ·
                    refine ⟨1276617999451262124041155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6808629330406731328219493 1276617999451262124041155)
                    ·
                      rfl

theorem cell23_7458614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_7458614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7458614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7458614 prefixEnd_7458614 := by exact prefixLift 7458614
  have htrace : WordTrace (prefixWord ++ tailWord_7458614) baseStart_7458614 baseEnd_7458614 := by
    simpa [prefixWord, tailWord_7458614, baseEnd_7458614] using wordTrace_append hprefix tailTrace_7458614
  have hstable : (prefixWord ++ tailWord_7458614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7458614).length < 2 ^ (prefixWord ++ tailWord_7458614).sum := by decide
  have hdescent : baseEnd_7458614 < baseStart_7458614 := by decide
  rcases family_descends (prefixWord ++ tailWord_7458614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7458663 : List Nat := [1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 5]
def baseStart_7458663 : Nat := 118140960795 + 7458663 * 2 ^ 59
def prefixEnd_7458663 : Nat := 4983230072969 + 3 ^ 40 * 7458663 * 2
def baseEnd_7458663 : Nat := 3829879158905856680410739

theorem tailTrace_7458663 : CollatzResearch.WordTrace tailWord_7458663 prefixEnd_7458663 3829879158905856680410739 := by
  unfold tailWord_7458663
  simp only [CollatzResearch.WordTrace]
  refine ⟨272039788577545264070068643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181359859051696842713379095 272039788577545264070068643)
  ·
    refine ⟨408059682866317896105102965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272039788577545264070068643 408059682866317896105102965)
    ·
      refine ⟨38255595268717302759853403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 408059682866317896105102965 38255595268717302759853403)
      ·
        refine ⟨57383392903075954139780105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38255595268717302759853403 57383392903075954139780105)
        ·
          refine ⟨43037544677306965604835079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57383392903075954139780105 43037544677306965604835079)
          ·
            refine ⟨64556317015960448407252619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43037544677306965604835079 64556317015960448407252619)
            ·
              refine ⟨96834475523940672610878929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64556317015960448407252619 96834475523940672610878929)
              ·
                refine ⟨72625856642955504458159197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96834475523940672610878929 72625856642955504458159197)
                ·
                  refine ⟨27234696241108314171809699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72625856642955504458159197 27234696241108314171809699)
                  ·
                    refine ⟨40852044361662471257714549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27234696241108314171809699 40852044361662471257714549)
                    ·
                      refine ⟨3829879158905856680410739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40852044361662471257714549 3829879158905856680410739)
                      ·
                        rfl

theorem cell23_7458663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_7458663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7458663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7458663 prefixEnd_7458663 := by exact prefixLift 7458663
  have htrace : WordTrace (prefixWord ++ tailWord_7458663) baseStart_7458663 baseEnd_7458663 := by
    simpa [prefixWord, tailWord_7458663, baseEnd_7458663] using wordTrace_append hprefix tailTrace_7458663
  have hstable : (prefixWord ++ tailWord_7458663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7458663).length < 2 ^ (prefixWord ++ tailWord_7458663).sum := by decide
  have hdescent : baseEnd_7458663 < baseStart_7458663 := by decide
  rcases family_descends (prefixWord ++ tailWord_7458663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7458673 : List Nat := [1, 2, 2, 2, 1, 3, 2, 1, 3, 2, 4]
def baseStart_7458673 : Nat := 118140960795 + 7458673 * 2 ^ 59
def prefixEnd_7458673 : Nat := 4983230072969 + 3 ^ 40 * 7458673 * 2
def baseEnd_7458673 : Nat := 3829884293712401641285693

theorem tailTrace_7458673 : CollatzResearch.WordTrace tailWord_7458673 prefixEnd_7458673 3829884293712401641285693 := by
  unfold tailWord_7458673
  simp only [CollatzResearch.WordTrace]
  refine ⟨272040153307509035777932673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181360102205006023851955115 272040153307509035777932673)
  ·
    refine ⟨204030114980631776833449505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272040153307509035777932673 204030114980631776833449505)
    ·
      refine ⟨153022586235473832625087129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204030114980631776833449505 153022586235473832625087129)
      ·
        refine ⟨114766939676605374468815347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153022586235473832625087129 114766939676605374468815347)
        ·
          refine ⟨172150409514908061703223021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114766939676605374468815347 172150409514908061703223021)
          ·
            refine ⟨64556403568090523138708633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172150409514908061703223021 64556403568090523138708633)
            ·
              refine ⟨48417302676067892354031475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64556403568090523138708633 48417302676067892354031475)
              ·
                refine ⟨72625954014101838531047213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48417302676067892354031475 72625954014101838531047213)
                ·
                  refine ⟨27234732755288189449142705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72625954014101838531047213 27234732755288189449142705)
                  ·
                    refine ⟨20426049566466142086857029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27234732755288189449142705 20426049566466142086857029)
                    ·
                      refine ⟨3829884293712401641285693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20426049566466142086857029 3829884293712401641285693)
                      ·
                        rfl

theorem cell23_7458673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_7458673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7458673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7458673 prefixEnd_7458673 := by exact prefixLift 7458673
  have htrace : WordTrace (prefixWord ++ tailWord_7458673) baseStart_7458673 baseEnd_7458673 := by
    simpa [prefixWord, tailWord_7458673, baseEnd_7458673] using wordTrace_append hprefix tailTrace_7458673
  have hstable : (prefixWord ++ tailWord_7458673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7458673).length < 2 ^ (prefixWord ++ tailWord_7458673).sum := by decide
  have hdescent : baseEnd_7458673 < baseStart_7458673 := by decide
  rcases family_descends (prefixWord ++ tailWord_7458673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7458714 : List Nat := [3, 1, 1, 4, 2, 3, 1, 2, 1, 2, 3]
def baseStart_7458714 : Nat := 118140960795 + 7458714 * 2 ^ 59
def prefixEnd_7458714 : Nat := 4983230072969 + 3 ^ 40 * 7458714 * 2
def baseEnd_7458714 : Nat := 3829905346419235980873005

theorem tailTrace_7458714 : CollatzResearch.WordTrace tailWord_7458714 prefixEnd_7458714 3829905346419235980873005 := by
  unfold tailWord_7458714
  simp only [CollatzResearch.WordTrace]
  refine ⟨68010412175090124945043799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181361099133573666520116797 68010412175090124945043799)
  ·
    refine ⟨102015618262635187417565699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68010412175090124945043799 102015618262635187417565699)
    ·
      refine ⟨153023427393952781126348549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102015618262635187417565699 153023427393952781126348549)
      ·
        refine ⟨28691892636366146461190353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153023427393952781126348549 28691892636366146461190353)
        ·
          refine ⟨21518919477274609845892765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28691892636366146461190353 21518919477274609845892765)
          ·
            refine ⟨8069594803977978692209787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21518919477274609845892765 8069594803977978692209787)
            ·
              refine ⟨12104392205966968038314681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8069594803977978692209787 12104392205966968038314681)
              ·
                refine ⟨9078294154475226028736011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12104392205966968038314681 9078294154475226028736011)
                ·
                  refine ⟨13617441231712839043104017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9078294154475226028736011 13617441231712839043104017)
                  ·
                    refine ⟨10213080923784629282328013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13617441231712839043104017 10213080923784629282328013)
                    ·
                      refine ⟨3829905346419235980873005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10213080923784629282328013 3829905346419235980873005)
                      ·
                        rfl

theorem cell23_7458714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_7458714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7458714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7458714 prefixEnd_7458714 := by exact prefixLift 7458714
  have htrace : WordTrace (prefixWord ++ tailWord_7458714) baseStart_7458714 baseEnd_7458714 := by
    simpa [prefixWord, tailWord_7458714, baseEnd_7458714] using wordTrace_append hprefix tailTrace_7458714
  have hstable : (prefixWord ++ tailWord_7458714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7458714).length < 2 ^ (prefixWord ++ tailWord_7458714).sum := by decide
  have hdescent : baseEnd_7458714 < baseStart_7458714 := by decide
  rcases family_descends (prefixWord ++ tailWord_7458714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7458727 : List Nat := [1, 1, 6, 1, 2, 2, 1, 2, 1, 3, 3]
def baseStart_7458727 : Nat := 118140960795 + 7458727 * 2 ^ 59
def prefixEnd_7458727 : Nat := 4983230072969 + 3 ^ 40 * 7458727 * 2
def baseEnd_7458727 : Nat := 3829912021667744430010445

theorem tailTrace_7458727 : CollatzResearch.WordTrace tailWord_7458727 prefixEnd_7458727 3829912021667744430010445 := by
  unfold tailWord_7458727
  simp only [CollatzResearch.WordTrace]
  refine ⟨272042122849313403000398435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181361415232875602000265623 272042122849313403000398435)
  ·
    refine ⟨408063184273970104500597653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272042122849313403000398435 408063184273970104500597653)
    ·
      refine ⟨19127961762842348648465515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 408063184273970104500597653 19127961762842348648465515)
      ·
        refine ⟨28691942644263522972698273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19127961762842348648465515 28691942644263522972698273)
        ·
          refine ⟨21518956983197642229523705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28691942644263522972698273 21518956983197642229523705)
          ·
            refine ⟨16139217737398231672142779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21518956983197642229523705 16139217737398231672142779)
            ·
              refine ⟨24208826606097347508214169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16139217737398231672142779 24208826606097347508214169)
              ·
                refine ⟨18156619954573010631160627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24208826606097347508214169 18156619954573010631160627)
                ·
                  refine ⟨27234929931859515946740941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18156619954573010631160627 27234929931859515946740941)
                  ·
                    refine ⟨10213098724447318480027853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27234929931859515946740941 10213098724447318480027853)
                    ·
                      refine ⟨3829912021667744430010445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10213098724447318480027853 3829912021667744430010445)
                      ·
                        rfl

theorem cell23_7458727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_7458727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7458727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7458727 prefixEnd_7458727 := by exact prefixLift 7458727
  have htrace : WordTrace (prefixWord ++ tailWord_7458727) baseStart_7458727 baseEnd_7458727 := by
    simpa [prefixWord, tailWord_7458727, baseEnd_7458727] using wordTrace_append hprefix tailTrace_7458727
  have hstable : (prefixWord ++ tailWord_7458727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7458727).length < 2 ^ (prefixWord ++ tailWord_7458727).sum := by decide
  have hdescent : baseEnd_7458727 < baseStart_7458727 := by decide
  rcases family_descends (prefixWord ++ tailWord_7458727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7458734 : List Nat := [4, 1, 5, 1, 2, 10]
def baseStart_7458734 : Nat := 118140960795 + 7458734 * 2 ^ 59
def prefixEnd_7458734 : Nat := 4983230072969 + 3 ^ 40 * 7458734 * 2
def baseEnd_7458734 : Nat := 15760969613301752685691

theorem tailTrace_7458734 : CollatzResearch.WordTrace tailWord_7458734 prefixEnd_7458734 15760969613301752685691 := by
  unfold tailWord_7458734
  simp only [CollatzResearch.WordTrace]
  refine ⟨34005297270036005399487907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181361585440192028797268837 34005297270036005399487907)
  ·
    refine ⟨51007945905054008099231861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34005297270036005399487907 51007945905054008099231861)
    ·
      refine ⟨4781994928598813259302987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51007945905054008099231861 4781994928598813259302987)
      ·
        refine ⟨7172992392898219888954481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4781994928598813259302987 7172992392898219888954481)
        ·
          refine ⟨5379744294673664916715861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7172992392898219888954481 5379744294673664916715861)
          ·
            refine ⟨15760969613301752685691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5379744294673664916715861 15760969613301752685691)
            ·
              rfl

theorem cell23_7458734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 10].length) (baseStart_7458734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7458734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7458734 prefixEnd_7458734 := by exact prefixLift 7458734
  have htrace : WordTrace (prefixWord ++ tailWord_7458734) baseStart_7458734 baseEnd_7458734 := by
    simpa [prefixWord, tailWord_7458734, baseEnd_7458734] using wordTrace_append hprefix tailTrace_7458734
  have hstable : (prefixWord ++ tailWord_7458734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7458734).length < 2 ^ (prefixWord ++ tailWord_7458734).sum := by decide
  have hdescent : baseEnd_7458734 < baseStart_7458734 := by decide
  rcases family_descends (prefixWord ++ tailWord_7458734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7458743 : List Nat := [1, 1, 3, 1, 3, 1, 1, 4, 2, 6]
def baseStart_7458743 : Nat := 118140960795 + 7458743 * 2 ^ 59
def prefixEnd_7458743 : Nat := 4983230072969 + 3 ^ 40 * 7458743 * 2
def baseEnd_7458743 : Nat := 1276640079119405455803457

theorem tailTrace_7458743 : CollatzResearch.WordTrace tailWord_7458743 prefixEnd_7458743 1276640079119405455803457 := by
  unfold tailWord_7458743
  simp only [CollatzResearch.WordTrace]
  refine ⟨272042706417255437732980883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181361804278170291821987255 272042706417255437732980883)
  ·
    refine ⟨408064059625883156599471325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272042706417255437732980883 408064059625883156599471325)
    ·
      refine ⟨153024022359706183724801747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 408064059625883156599471325 153024022359706183724801747)
      ·
        refine ⟨229536033539559275587202621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153024022359706183724801747 229536033539559275587202621)
        ·
          refine ⟨86076012577334728345200983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229536033539559275587202621 86076012577334728345200983)
          ·
            refine ⟨129114018866002092517801475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86076012577334728345200983 129114018866002092517801475)
            ·
              refine ⟨193671028299003138776702213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129114018866002092517801475 193671028299003138776702213)
              ·
                refine ⟨36313317806063088520631665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 193671028299003138776702213 36313317806063088520631665)
                ·
                  refine ⟨27234988354547316390473749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36313317806063088520631665 27234988354547316390473749)
                  ·
                    refine ⟨1276640079119405455803457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27234988354547316390473749 1276640079119405455803457)
                    ·
                      rfl

theorem cell23_7458743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 6].length) (baseStart_7458743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7458743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7458743 prefixEnd_7458743 := by exact prefixLift 7458743
  have htrace : WordTrace (prefixWord ++ tailWord_7458743) baseStart_7458743 baseEnd_7458743 := by
    simpa [prefixWord, tailWord_7458743, baseEnd_7458743] using wordTrace_append hprefix tailTrace_7458743
  have hstable : (prefixWord ++ tailWord_7458743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7458743).length < 2 ^ (prefixWord ++ tailWord_7458743).sum := by decide
  have hdescent : baseEnd_7458743 < baseStart_7458743 := by decide
  rcases family_descends (prefixWord ++ tailWord_7458743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7458750 : List Nat := [4, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4]
def baseStart_7458750 : Nat := 118140960795 + 7458750 * 2 ^ 59
def prefixEnd_7458750 : Nat := 4983230072969 + 3 ^ 40 * 7458750 * 2
def baseEnd_7458750 : Nat := 3829923831722797840022839

theorem tailTrace_7458750 : CollatzResearch.WordTrace tailWord_7458750 prefixEnd_7458750 3829923831722797840022839 := by
  unfold tailWord_7458750
  simp only [CollatzResearch.WordTrace]
  refine ⟨34005370216028759741060713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181361974485486718618990469 34005370216028759741060713)
  ·
    refine ⟨25504027662021569805795535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34005370216028759741060713 25504027662021569805795535)
    ·
      refine ⟨38256041493032354708693303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25504027662021569805795535 38256041493032354708693303)
      ·
        refine ⟨57384062239548532063039955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38256041493032354708693303 57384062239548532063039955)
        ·
          refine ⟨86076093359322798094559933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57384062239548532063039955 86076093359322798094559933)
          ·
            refine ⟨32278535009746049285459975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86076093359322798094559933 32278535009746049285459975)
            ·
              refine ⟨48417802514619073928189963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32278535009746049285459975 48417802514619073928189963)
              ·
                refine ⟨72626703771928610892284945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48417802514619073928189963 72626703771928610892284945)
                ·
                  refine ⟨54470027828946458169213709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72626703771928610892284945 54470027828946458169213709)
                  ·
                    refine ⟨20426260435854921813455141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54470027828946458169213709 20426260435854921813455141)
                    ·
                      refine ⟨3829923831722797840022839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20426260435854921813455141 3829923831722797840022839)
                      ·
                        rfl

theorem cell23_7458750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_7458750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7458750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7458750 prefixEnd_7458750 := by exact prefixLift 7458750
  have htrace : WordTrace (prefixWord ++ tailWord_7458750) baseStart_7458750 baseEnd_7458750 := by
    simpa [prefixWord, tailWord_7458750, baseEnd_7458750] using wordTrace_append hprefix tailTrace_7458750
  have hstable : (prefixWord ++ tailWord_7458750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7458750).length < 2 ^ (prefixWord ++ tailWord_7458750).sum := by decide
  have hdescent : baseEnd_7458750 < baseStart_7458750 := by decide
  rcases family_descends (prefixWord ++ tailWord_7458750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7458760 : List Nat := [2, 1, 3, 1, 4, 2, 1, 1, 2, 6]
def baseStart_7458760 : Nat := 118140960795 + 7458760 * 2 ^ 59
def prefixEnd_7458760 : Nat := 4983230072969 + 3 ^ 40 * 7458760 * 2
def baseEnd_7458760 : Nat := 1276642988843114266965931

theorem tailTrace_7458760 : CollatzResearch.WordTrace tailWord_7458760 prefixEnd_7458760 1276642988843114266965931 := by
  unfold tailWord_7458760
  simp only [CollatzResearch.WordTrace]
  refine ⟨136021663229096924818174867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181362217638795899757566489 136021663229096924818174867)
  ·
    refine ⟨204032494843645387227262301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136021663229096924818174867 204032494843645387227262301)
    ·
      refine ⟨76512185566367020210223363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204032494843645387227262301 76512185566367020210223363)
      ·
        refine ⟨114768278349550530315335045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76512185566367020210223363 114768278349550530315335045)
        ·
          refine ⟨21519052190540724434125321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114768278349550530315335045 21519052190540724434125321)
          ·
            refine ⟨16139289142905543325593991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21519052190540724434125321 16139289142905543325593991)
            ·
              refine ⟨24208933714358314988390987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16139289142905543325593991 24208933714358314988390987)
              ·
                refine ⟨36313400571537472482586481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24208933714358314988390987 36313400571537472482586481)
                ·
                  refine ⟨27235050428653104361939861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36313400571537472482586481 27235050428653104361939861)
                  ·
                    refine ⟨1276642988843114266965931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27235050428653104361939861 1276642988843114266965931)
                    ·
                      rfl

theorem cell23_7458760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 2, 6].length) (baseStart_7458760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7458760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7458760 prefixEnd_7458760 := by exact prefixLift 7458760
  have htrace : WordTrace (prefixWord ++ tailWord_7458760) baseStart_7458760 baseEnd_7458760 := by
    simpa [prefixWord, tailWord_7458760, baseEnd_7458760] using wordTrace_append hprefix tailTrace_7458760
  have hstable : (prefixWord ++ tailWord_7458760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7458760).length < 2 ^ (prefixWord ++ tailWord_7458760).sum := by decide
  have hdescent : baseEnd_7458760 < baseStart_7458760 := by decide
  rcases family_descends (prefixWord ++ tailWord_7458760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7458767 : List Nat := [1, 1, 2, 1, 1, 5, 4, 1, 1, 4, 2]
def baseStart_7458767 : Nat := 118140960795 + 7458767 * 2 ^ 59
def prefixEnd_7458767 : Nat := 4983230072969 + 3 ^ 40 * 7458767 * 2
def baseEnd_7458767 : Nat := 3829932560893924273510261

theorem tailTrace_7458767 : CollatzResearch.WordTrace tailWord_7458767 prefixEnd_7458767 3829932560893924273510261 := by
  unfold tailWord_7458767
  simp only [CollatzResearch.WordTrace]
  refine ⟨272043581769168489831854555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181362387846112326554569703 272043581769168489831854555)
  ·
    refine ⟨408065372653752734747781833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272043581769168489831854555 408065372653752734747781833)
    ·
      refine ⟨306049029490314551060836375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408065372653752734747781833 306049029490314551060836375)
      ·
        refine ⟨459073544235471826591254563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306049029490314551060836375 459073544235471826591254563)
        ·
          refine ⟨688610316353207739886881845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459073544235471826591254563 688610316353207739886881845)
          ·
            refine ⟨64557217158113225614395173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 688610316353207739886881845 64557217158113225614395173)
            ·
              refine ⟨12104478217146229802699095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64557217158113225614395173 12104478217146229802699095)
              ·
                refine ⟨18156717325719344704048643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12104478217146229802699095 18156717325719344704048643)
                ·
                  refine ⟨27235075988579017056072965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18156717325719344704048643 27235075988579017056072965)
                  ·
                    refine ⟨5106576747858565698013681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27235075988579017056072965 5106576747858565698013681)
                    ·
                      refine ⟨3829932560893924273510261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5106576747858565698013681 3829932560893924273510261)
                      ·
                        rfl

theorem cell23_7458767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 4, 2].length) (baseStart_7458767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7458767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7458767 prefixEnd_7458767 := by exact prefixLift 7458767
  have htrace : WordTrace (prefixWord ++ tailWord_7458767) baseStart_7458767 baseEnd_7458767 := by
    simpa [prefixWord, tailWord_7458767, baseEnd_7458767] using wordTrace_append hprefix tailTrace_7458767
  have hstable : (prefixWord ++ tailWord_7458767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7458767).length < 2 ^ (prefixWord ++ tailWord_7458767).sum := by decide
  have hdescent : baseEnd_7458767 < baseStart_7458767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7458767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7458800 : List Nat := [2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 3]
def baseStart_7458800 : Nat := 118140960795 + 7458800 * 2 ^ 59
def prefixEnd_7458800 : Nat := 4983230072969 + 3 ^ 40 * 7458800 * 2
def baseEnd_7458800 : Nat := 3829949505755522644397609

theorem tailTrace_7458800 : CollatzResearch.WordTrace tailWord_7458800 prefixEnd_7458800 3829949505755522644397609 := by
  unfold tailWord_7458800
  simp only [CollatzResearch.WordTrace]
  refine ⟨136022392689024468233902927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181363190252032624311870569 136022392689024468233902927)
  ·
    refine ⟨204033589033536702350854391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136022392689024468233902927 204033589033536702350854391)
    ·
      refine ⟨306050383550305053526281587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204033589033536702350854391 306050383550305053526281587)
      ·
        refine ⟨459075575325457580289422381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306050383550305053526281587 459075575325457580289422381)
        ·
          refine ⟨172153340747046592608533393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 459075575325457580289422381 172153340747046592608533393)
          ·
            refine ⟨129115005560284944456400045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172153340747046592608533393 129115005560284944456400045)
            ·
              refine ⟨48418127085106854171150017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129115005560284944456400045 48418127085106854171150017)
              ·
                refine ⟨36313595313830140628362513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48418127085106854171150017 36313595313830140628362513)
                ·
                  refine ⟨27235196485372605471271885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36313595313830140628362513 27235196485372605471271885)
                  ·
                    refine ⟨10213198682014727051726957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27235196485372605471271885 10213198682014727051726957)
                    ·
                      refine ⟨3829949505755522644397609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10213198682014727051726957 3829949505755522644397609)
                      ·
                        rfl

theorem cell23_7458800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 3].length) (baseStart_7458800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7458800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7458800 prefixEnd_7458800 := by exact prefixLift 7458800
  have htrace : WordTrace (prefixWord ++ tailWord_7458800) baseStart_7458800 baseEnd_7458800 := by
    simpa [prefixWord, tailWord_7458800, baseEnd_7458800] using wordTrace_append hprefix tailTrace_7458800
  have hstable : (prefixWord ++ tailWord_7458800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7458800).length < 2 ^ (prefixWord ++ tailWord_7458800).sum := by decide
  have hdescent : baseEnd_7458800 < baseStart_7458800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7458800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7458822 : List Nat := [6, 2, 1, 2, 1, 1, 2, 2, 1, 3, 2]
def baseStart_7458822 : Nat := 118140960795 + 7458822 * 2 ^ 59
def prefixEnd_7458822 : Nat := 4983230072969 + 3 ^ 40 * 7458822 * 2
def baseEnd_7458822 : Nat := 3829960802329921558322509

theorem tailTrace_7458822 : CollatzResearch.WordTrace tailWord_7458822 prefixEnd_7458822 3829960802329921558322509 := by
  unfold tailWord_7458822
  simp only [CollatzResearch.WordTrace]
  refine ⟨8501424618249038569534585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 181363725189312822816737813 8501424618249038569534585)
  ·
    refine ⟨6376068463686778927150939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8501424618249038569534585 6376068463686778927150939)
    ·
      refine ⟨9564102695530168390726409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6376068463686778927150939 9564102695530168390726409)
      ·
        refine ⟨7173077021647626293044807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9564102695530168390726409 7173077021647626293044807)
        ·
          refine ⟨10759615532471439439567211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7173077021647626293044807 10759615532471439439567211)
          ·
            refine ⟨16139423298707159159350817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10759615532471439439567211 16139423298707159159350817)
            ·
              refine ⟨12104567474030369369513113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16139423298707159159350817 12104567474030369369513113)
              ·
                refine ⟨9078425605522777027134835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12104567474030369369513113 9078425605522777027134835)
                ·
                  refine ⟨13617638408284165540702253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9078425605522777027134835 13617638408284165540702253)
                  ·
                    refine ⟨5106614403106562077763345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13617638408284165540702253 5106614403106562077763345)
                    ·
                      refine ⟨3829960802329921558322509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5106614403106562077763345 3829960802329921558322509)
                      ·
                        rfl

theorem cell23_7458822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_7458822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7458822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7458822 prefixEnd_7458822 := by exact prefixLift 7458822
  have htrace : WordTrace (prefixWord ++ tailWord_7458822) baseStart_7458822 baseEnd_7458822 := by
    simpa [prefixWord, tailWord_7458822, baseEnd_7458822] using wordTrace_append hprefix tailTrace_7458822
  have hstable : (prefixWord ++ tailWord_7458822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7458822).length < 2 ^ (prefixWord ++ tailWord_7458822).sum := by decide
  have hdescent : baseEnd_7458822 < baseStart_7458822 := by decide
  rcases family_descends (prefixWord ++ tailWord_7458822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7458840 : List Nat := [2, 1, 2, 3, 2, 1, 1, 3, 1, 3, 4]
def baseStart_7458840 : Nat := 118140960795 + 7458840 * 2 ^ 59
def prefixEnd_7458840 : Nat := 4983230072969 + 3 ^ 40 * 7458840 * 2
def baseEnd_7458840 : Nat := 3829970044981702487897425

theorem tailTrace_7458840 : CollatzResearch.WordTrace tailWord_7458840 prefixEnd_7458840 3829970044981702487897425 := by
  unfold tailWord_7458840
  simp only [CollatzResearch.WordTrace]
  refine ⟨136023122148952011649630987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181364162865269348866174649 136023122148952011649630987)
  ·
    refine ⟨204034683223428017474446481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136023122148952011649630987 204034683223428017474446481)
    ·
      refine ⟨153026012417571013105834861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204034683223428017474446481 153026012417571013105834861)
      ·
        refine ⟨57384754656589129914688073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153026012417571013105834861 57384754656589129914688073)
        ·
          refine ⟨43038565992441847436016055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57384754656589129914688073 43038565992441847436016055)
          ·
            refine ⟨64557848988662771154024083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43038565992441847436016055 64557848988662771154024083)
            ·
              refine ⟨96836773482994156731036125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64557848988662771154024083 96836773482994156731036125)
              ·
                refine ⟨36313790056122808774138547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96836773482994156731036125 36313790056122808774138547)
                ·
                  refine ⟨54470685084184213161207821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36313790056122808774138547 54470685084184213161207821)
                  ·
                    refine ⟨20426506906569079935452933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54470685084184213161207821 20426506906569079935452933)
                    ·
                      refine ⟨3829970044981702487897425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20426506906569079935452933 3829970044981702487897425)
                      ·
                        rfl

theorem cell23_7458840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_7458840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7458840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7458840 prefixEnd_7458840 := by exact prefixLift 7458840
  have htrace : WordTrace (prefixWord ++ tailWord_7458840) baseStart_7458840 baseEnd_7458840 := by
    simpa [prefixWord, tailWord_7458840, baseEnd_7458840] using wordTrace_append hprefix tailTrace_7458840
  have hstable : (prefixWord ++ tailWord_7458840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7458840).length < 2 ^ (prefixWord ++ tailWord_7458840).sum := by decide
  have hdescent : baseEnd_7458840 < baseStart_7458840 := by decide
  rcases family_descends (prefixWord ++ tailWord_7458840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7458860 : List Nat := [2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 3]
def baseStart_7458860 : Nat := 118140960795 + 7458860 * 2 ^ 59
def prefixEnd_7458860 : Nat := 4983230072969 + 3 ^ 40 * 7458860 * 2
def baseEnd_7458860 : Nat := 3829980314594792409647333

theorem tailTrace_7458860 : CollatzResearch.WordTrace tailWord_7458860 prefixEnd_7458860 3829980314594792409647333 := by
  unfold tailWord_7458860
  simp only [CollatzResearch.WordTrace]
  refine ⟨136023486878915783357495017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181364649171887711143326689 136023486878915783357495017)
  ·
    refine ⟨102017615159186837518121263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136023486878915783357495017 102017615159186837518121263)
    ·
      refine ⟨153026422738780256277181895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102017615159186837518121263 153026422738780256277181895)
      ·
        refine ⟨229539634108170384415772843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153026422738780256277181895 229539634108170384415772843)
        ·
          refine ⟨344309451162255576623659265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229539634108170384415772843 344309451162255576623659265)
          ·
            refine ⟨258232088371691682467744449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 344309451162255576623659265 258232088371691682467744449)
            ·
              refine ⟨193674066278768761850808337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 258232088371691682467744449 193674066278768761850808337)
              ·
                refine ⟨145255549709076571388106253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193674066278768761850808337 145255549709076571388106253)
                ·
                  refine ⟨54470831140903714270539845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145255549709076571388106253 54470831140903714270539845)
                  ·
                    refine ⟨10213280838919446425726221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54470831140903714270539845 10213280838919446425726221)
                    ·
                      refine ⟨3829980314594792409647333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10213280838919446425726221 3829980314594792409647333)
                      ·
                        rfl

theorem cell23_7458860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 3].length) (baseStart_7458860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7458860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7458860 prefixEnd_7458860 := by exact prefixLift 7458860
  have htrace : WordTrace (prefixWord ++ tailWord_7458860) baseStart_7458860 baseEnd_7458860 := by
    simpa [prefixWord, tailWord_7458860, baseEnd_7458860] using wordTrace_append hprefix tailTrace_7458860
  have hstable : (prefixWord ++ tailWord_7458860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7458860).length < 2 ^ (prefixWord ++ tailWord_7458860).sum := by decide
  have hdescent : baseEnd_7458860 < baseStart_7458860 := by decide
  rcases family_descends (prefixWord ++ tailWord_7458860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7458867 : List Nat := [1, 1, 1, 2, 4, 1, 5, 1, 3, 4]
def baseStart_7458867 : Nat := 118140960795 + 7458867 * 2 ^ 59
def prefixEnd_7458867 : Nat := 4983230072969 + 3 ^ 40 * 7458867 * 2
def baseEnd_7458867 : Nat := 1276661302986457960753267

theorem tailTrace_7458867 : CollatzResearch.WordTrace tailWord_7458867 prefixEnd_7458867 1276661302986457960753267 := by
  unfold tailWord_7458867
  simp only [CollatzResearch.WordTrace]
  refine ⟨272047229068806206910494855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181364819379204137940329903 272047229068806206910494855)
  ·
    refine ⟨408070843603209310365742283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272047229068806206910494855 408070843603209310365742283)
    ·
      refine ⟨612106265404813965548613425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408070843603209310365742283 612106265404813965548613425)
      ·
        refine ⟨459079699053610474161460069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 612106265404813965548613425 459079699053610474161460069)
        ·
          refine ⟨86077443572551963905273763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 459079699053610474161460069 86077443572551963905273763)
          ·
            refine ⟨129116165358827945857910645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86077443572551963905273763 129116165358827945857910645)
            ·
              refine ⟨12104640502390119924179123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 129116165358827945857910645 12104640502390119924179123)
              ·
                refine ⟨18156960753585179886268685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12104640502390119924179123 18156960753585179886268685)
                ·
                  refine ⟨6808860282594442457350757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18156960753585179886268685 6808860282594442457350757)
                  ·
                    refine ⟨1276661302986457960753267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6808860282594442457350757 1276661302986457960753267)
                    ·
                      rfl

theorem cell23_7458867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 3, 4].length) (baseStart_7458867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7458867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7458867 prefixEnd_7458867 := by exact prefixLift 7458867
  have htrace : WordTrace (prefixWord ++ tailWord_7458867) baseStart_7458867 baseEnd_7458867 := by
    simpa [prefixWord, tailWord_7458867, baseEnd_7458867] using wordTrace_append hprefix tailTrace_7458867
  have hstable : (prefixWord ++ tailWord_7458867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7458867).length < 2 ^ (prefixWord ++ tailWord_7458867).sum := by decide
  have hdescent : baseEnd_7458867 < baseStart_7458867 := by decide
  rcases family_descends (prefixWord ++ tailWord_7458867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7458877 : List Nat := [1, 4, 1, 3, 1, 1, 1, 2, 4, 2, 3]
def baseStart_7458877 : Nat := 118140960795 + 7458877 * 2 ^ 59
def prefixEnd_7458877 : Nat := 4983230072969 + 3 ^ 40 * 7458877 * 2
def baseEnd_7458877 : Nat := 3829989043765918843134755

theorem tailTrace_7458877 : CollatzResearch.WordTrace tailWord_7458877 prefixEnd_7458877 3829989043765918843134755 := by
  unfold tailWord_7458877
  simp only [CollatzResearch.WordTrace]
  refine ⟨272047593798769978618358885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181365062532513319078905923 272047593798769978618358885)
  ·
    refine ⟨51008923837269370990942291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 272047593798769978618358885 51008923837269370990942291)
    ·
      refine ⟨76513385755904056486413437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51008923837269370990942291 76513385755904056486413437)
      ·
        refine ⟨28692519658464021182405039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76513385755904056486413437 28692519658464021182405039)
        ·
          refine ⟨43038779487696031773607559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28692519658464021182405039 43038779487696031773607559)
          ·
            refine ⟨64558169231544047660411339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43038779487696031773607559 64558169231544047660411339)
            ·
              refine ⟨96837253847316071490617009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64558169231544047660411339 96837253847316071490617009)
              ·
                refine ⟨72627940385487053617962757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96837253847316071490617009 72627940385487053617962757)
                ·
                  refine ⟨13617738822278822553368017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72627940385487053617962757 13617738822278822553368017)
                  ·
                    refine ⟨10213304116709116915026013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13617738822278822553368017 10213304116709116915026013)
                    ·
                      refine ⟨3829989043765918843134755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10213304116709116915026013 3829989043765918843134755)
                      ·
                        rfl

theorem cell23_7458877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_7458877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7458877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7458877 prefixEnd_7458877 := by exact prefixLift 7458877
  have htrace : WordTrace (prefixWord ++ tailWord_7458877) baseStart_7458877 baseEnd_7458877 := by
    simpa [prefixWord, tailWord_7458877, baseEnd_7458877] using wordTrace_append hprefix tailTrace_7458877
  have hstable : (prefixWord ++ tailWord_7458877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7458877).length < 2 ^ (prefixWord ++ tailWord_7458877).sum := by decide
  have hdescent : baseEnd_7458877 < baseStart_7458877 := by decide
  rcases family_descends (prefixWord ++ tailWord_7458877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7458894 : List Nat := [4, 1, 1, 1, 1, 5, 2, 1, 2, 2, 3]
def baseStart_7458894 : Nat := 118140960795 + 7458894 * 2 ^ 59
def prefixEnd_7458894 : Nat := 4983230072969 + 3 ^ 40 * 7458894 * 2
def baseEnd_7458894 : Nat := 3829997772937045276622177

theorem tailTrace_7458894 : CollatzResearch.WordTrace tailWord_7458894 prefixEnd_7458894 3829997772937045276622177 := by
  unfold tailWord_7458894
  simp only [CollatzResearch.WordTrace]
  refine ⟨34006026729963548815215967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181365475893138927014485157 34006026729963548815215967)
  ·
    refine ⟨51009040094945323222823951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34006026729963548815215967 51009040094945323222823951)
    ·
      refine ⟨76513560142417984834235927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51009040094945323222823951 76513560142417984834235927)
      ·
        refine ⟨114770340213626977251353891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76513560142417984834235927 114770340213626977251353891)
        ·
          refine ⟨172155510320440465877030837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114770340213626977251353891 172155510320440465877030837)
          ·
            refine ⟨16139579092541293675971641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 172155510320440465877030837 16139579092541293675971641)
            ·
              refine ⟨12104684319405970256978731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16139579092541293675971641 12104684319405970256978731)
              ·
                refine ⟨18157026479108955385468097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12104684319405970256978731 18157026479108955385468097)
                ·
                  refine ⟨13617769859331716539101073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18157026479108955385468097 13617769859331716539101073)
                  ·
                    refine ⟨10213327394498787404325805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13617769859331716539101073 10213327394498787404325805)
                    ·
                      refine ⟨3829997772937045276622177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10213327394498787404325805 3829997772937045276622177)
                      ·
                        rfl

theorem cell23_7458894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 2, 2, 3].length) (baseStart_7458894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7458894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7458894 prefixEnd_7458894 := by exact prefixLift 7458894
  have htrace : WordTrace (prefixWord ++ tailWord_7458894) baseStart_7458894 baseEnd_7458894 := by
    simpa [prefixWord, tailWord_7458894, baseEnd_7458894] using wordTrace_append hprefix tailTrace_7458894
  have hstable : (prefixWord ++ tailWord_7458894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7458894).length < 2 ^ (prefixWord ++ tailWord_7458894).sum := by decide
  have hdescent : baseEnd_7458894 < baseStart_7458894 := by decide
  rcases family_descends (prefixWord ++ tailWord_7458894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7458900 : List Nat := [2, 4, 1, 1, 1, 1, 1, 2, 1, 1, 8]
def baseStart_7458900 : Nat := 118140960795 + 7458900 * 2 ^ 59
def prefixEnd_7458900 : Nat := 4983230072969 + 3 ^ 40 * 7458900 * 2
def baseEnd_7458900 : Nat := 3830000853820972253147149

theorem tailTrace_7458900 : CollatzResearch.WordTrace tailWord_7458900 prefixEnd_7458900 3830000853820972253147149 := by
  unfold tailWord_7458900
  simp only [CollatzResearch.WordTrace]
  refine ⟨136024216338843326773223077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181365621785124435697630769 136024216338843326773223077)
  ·
    refine ⟨25504540563533123769979327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136024216338843326773223077 25504540563533123769979327)
    ·
      refine ⟨38256810845299685654968991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25504540563533123769979327 38256810845299685654968991)
      ·
        refine ⟨57385216267949528482453487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38256810845299685654968991 57385216267949528482453487)
        ·
          refine ⟨86077824401924292723680231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57385216267949528482453487 86077824401924292723680231)
          ·
            refine ⟨129116736602886439085520347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86077824401924292723680231 129116736602886439085520347)
            ·
              refine ⟨193675104904329658628280521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129116736602886439085520347 193675104904329658628280521)
              ·
                refine ⟨145256328678247243971210391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193675104904329658628280521 145256328678247243971210391)
                ·
                  refine ⟨217884493017370865956815587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145256328678247243971210391 217884493017370865956815587)
                  ·
                    refine ⟨326826739526056298935223381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 217884493017370865956815587 326826739526056298935223381)
                    ·
                      refine ⟨3830000853820972253147149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 326826739526056298935223381 3830000853820972253147149)
                      ·
                        rfl

theorem cell23_7458900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_7458900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7458900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7458900 prefixEnd_7458900 := by exact prefixLift 7458900
  have htrace : WordTrace (prefixWord ++ tailWord_7458900) baseStart_7458900 baseEnd_7458900 := by
    simpa [prefixWord, tailWord_7458900, baseEnd_7458900] using wordTrace_append hprefix tailTrace_7458900
  have hstable : (prefixWord ++ tailWord_7458900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7458900).length < 2 ^ (prefixWord ++ tailWord_7458900).sum := by decide
  have hdescent : baseEnd_7458900 < baseStart_7458900 := by decide
  rcases family_descends (prefixWord ++ tailWord_7458900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7458947 : List Nat := [1, 1, 1, 3, 3, 3, 2, 1, 3, 1, 4]
def baseStart_7458947 : Nat := 118140960795 + 7458947 * 2 ^ 59
def prefixEnd_7458947 : Nat := 4983230072969 + 3 ^ 40 * 7458947 * 2
def baseEnd_7458947 : Nat := 3830024987411733569259433

theorem tailTrace_7458947 : CollatzResearch.WordTrace tailWord_7458947 prefixEnd_7458947 3830024987411733569259433 := by
  unfold tailWord_7458947
  simp only [CollatzResearch.WordTrace]
  refine ⟨272050146908516380573407095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181366764605677587048938063 272050146908516380573407095)
  ·
    refine ⟨408075220362774570860110643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272050146908516380573407095 408075220362774570860110643)
    ·
      refine ⟨612112830544161856290165965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408075220362774570860110643 612112830544161856290165965)
      ·
        refine ⟨229542311454060696108812237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 612112830544161856290165965 229542311454060696108812237)
        ·
          refine ⟨86078366795272761040804589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229542311454060696108812237 86078366795272761040804589)
          ·
            refine ⟨32279387548227285390301721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86078366795272761040804589 32279387548227285390301721)
            ·
              refine ⟨24209540661170464042726291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32279387548227285390301721 24209540661170464042726291)
              ·
                refine ⟨36314310991755696064089437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24209540661170464042726291 36314310991755696064089437)
                ·
                  refine ⟨13617866621908386024033539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36314310991755696064089437 13617866621908386024033539)
                  ·
                    refine ⟨20426799932862579036050309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13617866621908386024033539 20426799932862579036050309)
                    ·
                      refine ⟨3830024987411733569259433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20426799932862579036050309 3830024987411733569259433)
                      ·
                        rfl

theorem cell23_7458947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 3, 1, 4].length) (baseStart_7458947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7458947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7458947 prefixEnd_7458947 := by exact prefixLift 7458947
  have htrace : WordTrace (prefixWord ++ tailWord_7458947) baseStart_7458947 baseEnd_7458947 := by
    simpa [prefixWord, tailWord_7458947, baseEnd_7458947] using wordTrace_append hprefix tailTrace_7458947
  have hstable : (prefixWord ++ tailWord_7458947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7458947).length < 2 ^ (prefixWord ++ tailWord_7458947).sum := by decide
  have hdescent : baseEnd_7458947 < baseStart_7458947 := by decide
  rcases family_descends (prefixWord ++ tailWord_7458947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7458981 : List Nat := [1, 3, 1, 2, 1, 3, 4, 1, 3, 2, 2]
def baseStart_7458981 : Nat := 118140960795 + 7458981 * 2 ^ 59
def prefixEnd_7458981 : Nat := 4983230072969 + 3 ^ 40 * 7458981 * 2
def baseEnd_7458981 : Nat := 3830042445753986436234277

theorem tailTrace_7458981 : CollatzResearch.WordTrace tailWord_7458981 prefixEnd_7458981 3830042445753986436234277 := by
  unfold tailWord_7458981
  simp only [CollatzResearch.WordTrace]
  refine ⟨272051386990393204380144797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181367591326928802920096531 272051386990393204380144797)
  ·
    refine ⟨102019270121397451642554299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272051386990393204380144797 102019270121397451642554299)
    ·
      refine ⟨153028905182096177463831449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102019270121397451642554299 153028905182096177463831449)
      ·
        refine ⟨114771678886572133097873587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153028905182096177463831449 114771678886572133097873587)
        ·
          refine ⟨172157518329858199646810381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114771678886572133097873587 172157518329858199646810381)
          ·
            refine ⟨64559069373696824867553893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172157518329858199646810381 64559069373696824867553893)
            ·
              refine ⟨12104825507568154662666355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64559069373696824867553893 12104825507568154662666355)
              ·
                refine ⟨18157238261352231993999533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12104825507568154662666355 18157238261352231993999533)
                ·
                  refine ⟨6808964348007086997749825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18157238261352231993999533 6808964348007086997749825)
                  ·
                    refine ⟨5106723261005315248312369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6808964348007086997749825 5106723261005315248312369)
                    ·
                      refine ⟨3830042445753986436234277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5106723261005315248312369 3830042445753986436234277)
                      ·
                        rfl

theorem cell23_7458981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 3, 2, 2].length) (baseStart_7458981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7458981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7458981 prefixEnd_7458981 := by exact prefixLift 7458981
  have htrace : WordTrace (prefixWord ++ tailWord_7458981) baseStart_7458981 baseEnd_7458981 := by
    simpa [prefixWord, tailWord_7458981, baseEnd_7458981] using wordTrace_append hprefix tailTrace_7458981
  have hstable : (prefixWord ++ tailWord_7458981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7458981).length < 2 ^ (prefixWord ++ tailWord_7458981).sum := by decide
  have hdescent : baseEnd_7458981 < baseStart_7458981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7458981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7459048 : List Nat := [2, 1, 4, 1, 2, 2, 4, 1, 2, 1, 3]
def baseStart_7459048 : Nat := 118140960795 + 7459048 * 2 ^ 59
def prefixEnd_7459048 : Nat := 4983230072969 + 3 ^ 40 * 7459048 * 2
def baseEnd_7459048 : Nat := 3830076848957837674096469

theorem tailTrace_7459048 : CollatzResearch.WordTrace tailWord_7459048 prefixEnd_7459048 3830076848957837674096469 := by
  unfold tailWord_7459048
  simp only [CollatzResearch.WordTrace]
  refine ⟨136026915340575237411416899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181369220454100316548555865 136026915340575237411416899)
  ·
    refine ⟨204040373010862856117125349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136026915340575237411416899 204040373010862856117125349)
    ·
      refine ⟨38257569939536785521961003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204040373010862856117125349 38257569939536785521961003)
      ·
        refine ⟨57386354909305178282941505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38257569939536785521961003 57386354909305178282941505)
        ·
          refine ⟨43039766181978883712206129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57386354909305178282941505 43039766181978883712206129)
          ·
            refine ⟨32279824636484162784154597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43039766181978883712206129 32279824636484162784154597)
            ·
              refine ⟨6052467119340780522028987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32279824636484162784154597 6052467119340780522028987)
              ·
                refine ⟨9078700679011170783043481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6052467119340780522028987 9078700679011170783043481)
                ·
                  refine ⟨6809025509258378087282611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9078700679011170783043481 6809025509258378087282611)
                  ·
                    refine ⟨10213538263887567130923917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6809025509258378087282611 10213538263887567130923917)
                    ·
                      refine ⟨3830076848957837674096469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10213538263887567130923917 3830076848957837674096469)
                      ·
                        rfl

theorem cell23_7459048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 1, 2, 1, 3].length) (baseStart_7459048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7459048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7459048 prefixEnd_7459048 := by exact prefixLift 7459048
  have htrace : WordTrace (prefixWord ++ tailWord_7459048) baseStart_7459048 baseEnd_7459048 := by
    simpa [prefixWord, tailWord_7459048, baseEnd_7459048] using wordTrace_append hprefix tailTrace_7459048
  have hstable : (prefixWord ++ tailWord_7459048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7459048).length < 2 ^ (prefixWord ++ tailWord_7459048).sum := by decide
  have hdescent : baseEnd_7459048 < baseStart_7459048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7459048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7459057 : List Nat := [1, 2, 2, 2, 2, 1, 3, 2, 2, 1, 5]
def baseStart_7459057 : Nat := 118140960795 + 7459057 * 2 ^ 59
def prefixEnd_7459057 : Nat := 4983230072969 + 3 ^ 40 * 7459057 * 2
def baseEnd_7459057 : Nat := 3830081470283728138883927

theorem tailTrace_7459057 : CollatzResearch.WordTrace tailWord_7459057 prefixEnd_7459057 3830081470283728138883927 := by
  unfold tailWord_7459057
  simp only [CollatzResearch.WordTrace]
  refine ⟨272054158938117869359911425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181369439292078579573274283 272054158938117869359911425)
  ·
    refine ⟨204040619203588402019933569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272054158938117869359911425 204040619203588402019933569)
    ·
      refine ⟨153030464402691301514950177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204040619203588402019933569 153030464402691301514950177)
      ·
        refine ⟨114772848302018476136212633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153030464402691301514950177 114772848302018476136212633)
        ·
          refine ⟨86079636226513857102159475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114772848302018476136212633 86079636226513857102159475)
          ·
            refine ⟨129119454339770785653239213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86079636226513857102159475 129119454339770785653239213)
            ·
              refine ⟨48419795377414044619964705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129119454339770785653239213 48419795377414044619964705)
              ·
                refine ⟨36314846533060533464973529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48419795377414044619964705 36314846533060533464973529)
                ·
                  refine ⟨27236134899795400098730147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36314846533060533464973529 27236134899795400098730147)
                  ·
                    refine ⟨40854202349693100148095221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27236134899795400098730147 40854202349693100148095221)
                    ·
                      refine ⟨3830081470283728138883927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40854202349693100148095221 3830081470283728138883927)
                      ·
                        rfl

theorem cell23_7459057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_7459057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7459057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7459057 prefixEnd_7459057 := by exact prefixLift 7459057
  have htrace : WordTrace (prefixWord ++ tailWord_7459057) baseStart_7459057 baseEnd_7459057 := by
    simpa [prefixWord, tailWord_7459057, baseEnd_7459057] using wordTrace_append hprefix tailTrace_7459057
  have hstable : (prefixWord ++ tailWord_7459057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7459057).length < 2 ^ (prefixWord ++ tailWord_7459057).sum := by decide
  have hdescent : baseEnd_7459057 < baseStart_7459057 := by decide
  rcases family_descends (prefixWord ++ tailWord_7459057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7459058 : List Nat := [3, 2, 1, 3, 2, 1, 3, 2, 1, 3, 2]
def baseStart_7459058 : Nat := 118140960795 + 7459058 * 2 ^ 59
def prefixEnd_7459058 : Nat := 4983230072969 + 3 ^ 40 * 7459058 * 2
def baseEnd_7459058 : Nat := 3830081983764382634971423

theorem tailTrace_7459058 : CollatzResearch.WordTrace tailWord_7459058 prefixEnd_7459058 3830081983764382634971423 := by
  unfold tailWord_7459058
  simp only [CollatzResearch.WordTrace]
  refine ⟨68013548852778561632674457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181369463607409497687131885 68013548852778561632674457)
  ·
    refine ⟨51010161639583921224505843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68013548852778561632674457 51010161639583921224505843)
    ·
      refine ⟨76515242459375881836758765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51010161639583921224505843 76515242459375881836758765)
      ·
        refine ⟨28693215922265955688784537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76515242459375881836758765 28693215922265955688784537)
        ·
          refine ⟨21519911941699466766588403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28693215922265955688784537 21519911941699466766588403)
          ·
            refine ⟨32279867912549200149882605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21519911941699466766588403 32279867912549200149882605)
            ·
              refine ⟨12104950467205950056205977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32279867912549200149882605 12104950467205950056205977)
              ·
                refine ⟨9078712850404462542154483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12104950467205950056205977 9078712850404462542154483)
                ·
                  refine ⟨13618069275606693813231725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9078712850404462542154483 13618069275606693813231725)
                  ·
                    refine ⟨5106775978352510179961897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13618069275606693813231725 5106775978352510179961897)
                    ·
                      refine ⟨3830081983764382634971423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5106775978352510179961897 3830081983764382634971423)
                      ·
                        rfl

theorem cell23_7459058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_7459058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7459058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7459058 prefixEnd_7459058 := by exact prefixLift 7459058
  have htrace : WordTrace (prefixWord ++ tailWord_7459058) baseStart_7459058 baseEnd_7459058 := by
    simpa [prefixWord, tailWord_7459058, baseEnd_7459058] using wordTrace_append hprefix tailTrace_7459058
  have hstable : (prefixWord ++ tailWord_7459058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7459058).length < 2 ^ (prefixWord ++ tailWord_7459058).sum := by decide
  have hdescent : baseEnd_7459058 < baseStart_7459058 := by decide
  rcases family_descends (prefixWord ++ tailWord_7459058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7459087 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 3, 5, 3]
def baseStart_7459087 : Nat := 118140960795 + 7459087 * 2 ^ 59
def prefixEnd_7459087 : Nat := 4983230072969 + 3 ^ 40 * 7459087 * 2
def baseEnd_7459087 : Nat := 3830096874703363021508789

theorem tailTrace_7459087 : CollatzResearch.WordTrace tailWord_7459087 prefixEnd_7459087 3830096874703363021508789 := by
  unfold tailWord_7459087
  simp only [CollatzResearch.WordTrace]
  refine ⟨272055253128009184483503515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181370168752006122989002343 272055253128009184483503515)
  ·
    refine ⟨408082879692013776725255273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272055253128009184483503515 408082879692013776725255273)
    ·
      refine ⟨306062159769010332543941455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408082879692013776725255273 306062159769010332543941455)
      ·
        refine ⟨459093239653515498815912183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306062159769010332543941455 459093239653515498815912183)
        ·
          refine ⟨688639859480273248223868275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459093239653515498815912183 688639859480273248223868275)
          ·
            refine ⟨1032959789220409872335802413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 688639859480273248223868275 1032959789220409872335802413)
            ·
              refine ⟨387359920957653702125925905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1032959789220409872335802413 387359920957653702125925905)
              ·
                refine ⟨290519940718240276594444429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 387359920957653702125925905 290519940718240276594444429)
                ·
                  refine ⟨108944977769340103722916661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 290519940718240276594444429 108944977769340103722916661)
                  ·
                    refine ⟨10213591665875634724023437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 108944977769340103722916661 10213591665875634724023437)
                    ·
                      refine ⟨3830096874703363021508789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10213591665875634724023437 3830096874703363021508789)
                      ·
                        rfl

theorem cell23_7459087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 5, 3].length) (baseStart_7459087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7459087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7459087 prefixEnd_7459087 := by exact prefixLift 7459087
  have htrace : WordTrace (prefixWord ++ tailWord_7459087) baseStart_7459087 baseEnd_7459087 := by
    simpa [prefixWord, tailWord_7459087, baseEnd_7459087] using wordTrace_append hprefix tailTrace_7459087
  have hstable : (prefixWord ++ tailWord_7459087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7459087).length < 2 ^ (prefixWord ++ tailWord_7459087).sum := by decide
  have hdescent : baseEnd_7459087 < baseStart_7459087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7459087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7459101 : List Nat := [1, 4, 2, 3, 2, 1, 1, 1, 2, 2, 4]
def baseStart_7459101 : Nat := 118140960795 + 7459101 * 2 ^ 59
def prefixEnd_7459101 : Nat := 4983230072969 + 3 ^ 40 * 7459101 * 2
def baseEnd_7459101 : Nat := 3830104063432525966733725

theorem tailTrace_7459101 : CollatzResearch.WordTrace tailWord_7459101 prefixEnd_7459101 3830104063432525966733725 := by
  unfold tailWord_7459101
  simp only [CollatzResearch.WordTrace]
  refine ⟨272055763749958464874513157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181370509166638976583008771 272055763749958464874513157)
  ·
    refine ⟨51010455703117212163971217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 272055763749958464874513157 51010455703117212163971217)
    ·
      refine ⟨38257841777337909122978413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51010455703117212163971217 38257841777337909122978413)
      ·
        refine ⟨14346690666501715921116905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38257841777337909122978413 14346690666501715921116905)
        ·
          refine ⟨10760017999876286940837679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14346690666501715921116905 10760017999876286940837679)
          ·
            refine ⟨16140026999814430411256519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10760017999876286940837679 16140026999814430411256519)
            ·
              refine ⟨24210040499721645616884779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16140026999814430411256519 24210040499721645616884779)
              ·
                refine ⟨36315060749582468425327169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24210040499721645616884779 36315060749582468425327169)
                ·
                  refine ⟨27236295562186851318995377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36315060749582468425327169 27236295562186851318995377)
                  ·
                    refine ⟨20427221671640138489246533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27236295562186851318995377 20427221671640138489246533)
                    ·
                      refine ⟨3830104063432525966733725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20427221671640138489246533 3830104063432525966733725)
                      ·
                        rfl

theorem cell23_7459101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_7459101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7459101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7459101 prefixEnd_7459101 := by exact prefixLift 7459101
  have htrace : WordTrace (prefixWord ++ tailWord_7459101) baseStart_7459101 baseEnd_7459101 := by
    simpa [prefixWord, tailWord_7459101, baseEnd_7459101] using wordTrace_append hprefix tailTrace_7459101
  have hstable : (prefixWord ++ tailWord_7459101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7459101).length < 2 ^ (prefixWord ++ tailWord_7459101).sum := by decide
  have hdescent : baseEnd_7459101 < baseStart_7459101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7459101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7459104 : List Nat := [2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 3]
def baseStart_7459104 : Nat := 118140960795 + 7459104 * 2 ^ 59
def prefixEnd_7459104 : Nat := 4983230072969 + 3 ^ 40 * 7459104 * 2
def baseEnd_7459104 : Nat := 3830105603874489454996211

theorem tailTrace_7459104 : CollatzResearch.WordTrace tailWord_7459104 prefixEnd_7459104 3830105603874489454996211 := by
  unfold tailWord_7459104
  simp only [CollatzResearch.WordTrace]
  refine ⟨136027936584473798193436183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181370582112631730924581577 136027936584473798193436183)
  ·
    refine ⟨204041904876710697290154275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136027936584473798193436183 204041904876710697290154275)
    ·
      refine ⟨306062857315066045935231413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204041904876710697290154275 306062857315066045935231413)
      ·
        refine ⟨28693392873287441806427945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 306062857315066045935231413 28693392873287441806427945)
        ·
          refine ⟨21520044654965581354820959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28693392873287441806427945 21520044654965581354820959)
          ·
            refine ⟨32280066982448372032231439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21520044654965581354820959 32280066982448372032231439)
            ·
              refine ⟨48420100473672558048347159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32280066982448372032231439 48420100473672558048347159)
              ·
                refine ⟨72630150710508837072520739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48420100473672558048347159 72630150710508837072520739)
                ·
                  refine ⟨108945226065763255608781109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72630150710508837072520739 108945226065763255608781109)
                  ·
                    refine ⟨10213614943665305213323229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 108945226065763255608781109 10213614943665305213323229)
                    ·
                      refine ⟨3830105603874489454996211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10213614943665305213323229 3830105603874489454996211)
                      ·
                        rfl

theorem cell23_7459104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_7459104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7459104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7459104 prefixEnd_7459104 := by exact prefixLift 7459104
  have htrace : WordTrace (prefixWord ++ tailWord_7459104) baseStart_7459104 baseEnd_7459104 := by
    simpa [prefixWord, tailWord_7459104, baseEnd_7459104] using wordTrace_append hprefix tailTrace_7459104
  have hstable : (prefixWord ++ tailWord_7459104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7459104).length < 2 ^ (prefixWord ++ tailWord_7459104).sum := by decide
  have hdescent : baseEnd_7459104 < baseStart_7459104 := by decide
  rcases family_descends (prefixWord ++ tailWord_7459104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7459107 : List Nat := [1, 1, 1, 4, 2, 2, 2, 2, 1, 7]
def baseStart_7459107 : Nat := 118140960795 + 7459107 * 2 ^ 59
def prefixEnd_7459107 : Nat := 4983230072969 + 3 ^ 40 * 7459107 * 2
def baseEnd_7459107 : Nat := 1276702381438817647752899

theorem tailTrace_7459107 : CollatzResearch.WordTrace tailWord_7459107 prefixEnd_7459107 1276702381438817647752899 := by
  unfold tailWord_7459107
  simp only [CollatzResearch.WordTrace]
  refine ⟨272055982587936727899231575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181370655058624485266154383 272055982587936727899231575)
  ·
    refine ⟨408083973881905091848847363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272055982587936727899231575 408083973881905091848847363)
    ·
      refine ⟨612125960822857637773271045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408083973881905091848847363 612125960822857637773271045)
      ·
        refine ⟨114773617654285807082488321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 612125960822857637773271045 114773617654285807082488321)
        ·
          refine ⟨86080213240714355311866241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114773617654285807082488321 86080213240714355311866241)
          ·
            refine ⟨64560159930535766483899681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86080213240714355311866241 64560159930535766483899681)
            ·
              refine ⟨48420119947901824862924761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64560159930535766483899681 48420119947901824862924761)
              ·
                refine ⟨36315089960926368647193571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48420119947901824862924761 36315089960926368647193571)
                ·
                  refine ⟨54472634941389552970790357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36315089960926368647193571 54472634941389552970790357)
                  ·
                    refine ⟨1276702381438817647752899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54472634941389552970790357 1276702381438817647752899)
                    ·
                      rfl

theorem cell23_7459107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 7].length) (baseStart_7459107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7459107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7459107 prefixEnd_7459107 := by exact prefixLift 7459107
  have htrace : WordTrace (prefixWord ++ tailWord_7459107) baseStart_7459107 baseEnd_7459107 := by
    simpa [prefixWord, tailWord_7459107, baseEnd_7459107] using wordTrace_append hprefix tailTrace_7459107
  have hstable : (prefixWord ++ tailWord_7459107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7459107).length < 2 ^ (prefixWord ++ tailWord_7459107).sum := by decide
  have hdescent : baseEnd_7459107 < baseStart_7459107 := by decide
  rcases family_descends (prefixWord ++ tailWord_7459107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7459144 : List Nat := [2, 1, 3, 1, 1, 2, 2, 4, 2, 1, 4]
def baseStart_7459144 : Nat := 118140960795 + 7459144 * 2 ^ 59
def prefixEnd_7459144 : Nat := 4983230072969 + 3 ^ 40 * 7459144 * 2
def baseEnd_7459144 : Nat := 3830126143100669298496027

theorem tailTrace_7459144 : CollatzResearch.WordTrace tailWord_7459144 prefixEnd_7459144 3830126143100669298496027 := by
  unfold tailWord_7459144
  simp only [CollatzResearch.WordTrace]
  refine ⟨136028666044401341609164243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181371554725868455478885657 136028666044401341609164243)
  ·
    refine ⟨204042999066602012413746365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136028666044401341609164243 204042999066602012413746365)
    ·
      refine ⟨76516124649975754655154887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204042999066602012413746365 76516124649975754655154887)
      ·
        refine ⟨114774186974963631982732331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76516124649975754655154887 114774186974963631982732331)
        ·
          refine ⟨172161280462445447974098497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114774186974963631982732331 172161280462445447974098497)
          ·
            refine ⟨129120960346834085980573873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172161280462445447974098497 129120960346834085980573873)
            ·
              refine ⟨96840720260125564485430405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129120960346834085980573873 96840720260125564485430405)
              ·
                refine ⟨18157635048773543341018201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96840720260125564485430405 18157635048773543341018201)
                ·
                  refine ⟨13618226286580157505763651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18157635048773543341018201 13618226286580157505763651)
                  ·
                    refine ⟨20427339429870236258645477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13618226286580157505763651 20427339429870236258645477)
                    ·
                      refine ⟨3830126143100669298496027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20427339429870236258645477 3830126143100669298496027)
                      ·
                        rfl

theorem cell23_7459144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_7459144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7459144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7459144 prefixEnd_7459144 := by exact prefixLift 7459144
  have htrace : WordTrace (prefixWord ++ tailWord_7459144) baseStart_7459144 baseEnd_7459144 := by
    simpa [prefixWord, tailWord_7459144, baseEnd_7459144] using wordTrace_append hprefix tailTrace_7459144
  have hstable : (prefixWord ++ tailWord_7459144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7459144).length < 2 ^ (prefixWord ++ tailWord_7459144).sum := by decide
  have hdescent : baseEnd_7459144 < baseStart_7459144 := by decide
  rcases family_descends (prefixWord ++ tailWord_7459144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7459181 : List Nat := [1, 5, 1, 1, 1, 2, 2, 3, 2, 2, 3]
def baseStart_7459181 : Nat := 118140960795 + 7459181 * 2 ^ 59
def prefixEnd_7459181 : Nat := 4983230072969 + 3 ^ 40 * 7459181 * 2
def baseEnd_7459181 : Nat := 3830145141884885653733357

theorem tailTrace_7459181 : CollatzResearch.WordTrace tailWord_7459181 prefixEnd_7459181 3830145141884885653733357 := by
  unfold tailWord_7459181
  simp only [CollatzResearch.WordTrace]
  refine ⟨272058681589668638537425397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181372454393112425691616931 272058681589668638537425397)
  ·
    refine ⟨25505501399031434862883631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 272058681589668638537425397 25505501399031434862883631)
    ·
      refine ⟨38258252098547152294325447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25505501399031434862883631 38258252098547152294325447)
      ·
        refine ⟨57387378147820728441488171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38258252098547152294325447 57387378147820728441488171)
        ·
          refine ⟨86081067221731092662232257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57387378147820728441488171 86081067221731092662232257)
          ·
            refine ⟨64560800416298319496674193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86081067221731092662232257 64560800416298319496674193)
            ·
              refine ⟨48420600312223739622505645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64560800416298319496674193 48420600312223739622505645)
              ·
                refine ⟨18157725117083902358439617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48420600312223739622505645 18157725117083902358439617)
                ·
                  refine ⟨13618293837812926768829713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18157725117083902358439617 13618293837812926768829713)
                  ·
                    refine ⟨10213720378359695076622285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13618293837812926768829713 10213720378359695076622285)
                    ·
                      refine ⟨3830145141884885653733357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10213720378359695076622285 3830145141884885653733357)
                      ·
                        rfl

theorem cell23_7459181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_7459181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7459181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7459181 prefixEnd_7459181 := by exact prefixLift 7459181
  have htrace : WordTrace (prefixWord ++ tailWord_7459181) baseStart_7459181 baseEnd_7459181 := by
    simpa [prefixWord, tailWord_7459181, baseEnd_7459181] using wordTrace_append hprefix tailTrace_7459181
  have hstable : (prefixWord ++ tailWord_7459181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7459181).length < 2 ^ (prefixWord ++ tailWord_7459181).sum := by decide
  have hdescent : baseEnd_7459181 < baseStart_7459181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7459181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7459187 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 6]
def baseStart_7459187 : Nat := 118140960795 + 7459187 * 2 ^ 59
def prefixEnd_7459187 : Nat := 4983230072969 + 3 ^ 40 * 7459187 * 2
def baseEnd_7459187 : Nat := 3830148222768812630258329

theorem tailTrace_7459187 : CollatzResearch.WordTrace tailWord_7459187 prefixEnd_7459187 3830148222768812630258329 := by
  unfold tailWord_7459187
  simp only [CollatzResearch.WordTrace]
  refine ⟨272058900427646901562143815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181372600285097934374762543 272058900427646901562143815)
  ·
    refine ⟨408088350641470352343215723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272058900427646901562143815 408088350641470352343215723)
    ·
      refine ⟨612132525962205528514823585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408088350641470352343215723 612132525962205528514823585)
      ·
        refine ⟨459099394471654146386117689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 612132525962205528514823585 459099394471654146386117689)
        ·
          refine ⟨344324545853740609789588267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 459099394471654146386117689 344324545853740609789588267)
          ·
            refine ⟨516486818780610914684382401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344324545853740609789588267 516486818780610914684382401)
            ·
              refine ⟨387365114085458186013286801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 516486818780610914684382401 387365114085458186013286801)
              ·
                refine ⟨290523835564093639509965101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 387365114085458186013286801 290523835564093639509965101)
                ·
                  refine ⟨108946438336535114816236913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 290523835564093639509965101 108946438336535114816236913)
                  ·
                    refine ⟨81709828752401336112177685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 108946438336535114816236913 81709828752401336112177685)
                    ·
                      refine ⟨3830148222768812630258329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81709828752401336112177685 3830148222768812630258329)
                      ·
                        rfl

theorem cell23_7459187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 6].length) (baseStart_7459187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7459187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7459187 prefixEnd_7459187 := by exact prefixLift 7459187
  have htrace : WordTrace (prefixWord ++ tailWord_7459187) baseStart_7459187 baseEnd_7459187 := by
    simpa [prefixWord, tailWord_7459187, baseEnd_7459187] using wordTrace_append hprefix tailTrace_7459187
  have hstable : (prefixWord ++ tailWord_7459187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7459187).length < 2 ^ (prefixWord ++ tailWord_7459187).sum := by decide
  have hdescent : baseEnd_7459187 < baseStart_7459187 := by decide
  rcases family_descends (prefixWord ++ tailWord_7459187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7459221 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 6, 3, 2]
def baseStart_7459221 : Nat := 118140960795 + 7459221 * 2 ^ 59
def prefixEnd_7459221 : Nat := 4983230072969 + 3 ^ 40 * 7459221 * 2
def baseEnd_7459221 : Nat := 3830165681111065497233173

theorem tailTrace_7459221 : CollatzResearch.WordTrace tailWord_7459221 prefixEnd_7459221 3830165681111065497233173 := by
  unfold tailWord_7459221
  simp only [CollatzResearch.WordTrace]
  refine ⟨272060140509523725368881517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181373427006349150245921011 272060140509523725368881517)
  ·
    refine ⟨102022552691071397013330569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272060140509523725368881517 102022552691071397013330569)
    ·
      refine ⟨76516914518303547759997927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102022552691071397013330569 76516914518303547759997927)
      ·
        refine ⟨114775371777455321639996891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76516914518303547759997927 114775371777455321639996891)
        ·
          refine ⟨172163057666182982459995337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114775371777455321639996891 172163057666182982459995337)
          ·
            refine ⟨129122293249637236844996503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172163057666182982459995337 129122293249637236844996503)
            ·
              refine ⟨193683439874455855267494755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129122293249637236844996503 193683439874455855267494755)
              ·
                refine ⟨290525159811683782901242133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193683439874455855267494755 290525159811683782901242133)
                ·
                  refine ⟨13618366866172677323495725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 290525159811683782901242133 13618366866172677323495725)
                  ·
                    refine ⟨5106887574814753996310897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13618366866172677323495725 5106887574814753996310897)
                    ·
                      refine ⟨3830165681111065497233173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5106887574814753996310897 3830165681111065497233173)
                      ·
                        rfl

theorem cell23_7459221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 6, 3, 2].length) (baseStart_7459221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7459221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7459221 prefixEnd_7459221 := by exact prefixLift 7459221
  have htrace : WordTrace (prefixWord ++ tailWord_7459221) baseStart_7459221 baseEnd_7459221 := by
    simpa [prefixWord, tailWord_7459221, baseEnd_7459221] using wordTrace_append hprefix tailTrace_7459221
  have hstable : (prefixWord ++ tailWord_7459221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7459221).length < 2 ^ (prefixWord ++ tailWord_7459221).sum := by decide
  have hdescent : baseEnd_7459221 < baseStart_7459221 := by decide
  rcases family_descends (prefixWord ++ tailWord_7459221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7459262 : List Nat := [4, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3]
def baseStart_7459262 : Nat := 118140960795 + 7459262 * 2 ^ 59
def prefixEnd_7459262 : Nat := 4983230072969 + 3 ^ 40 * 7459262 * 2
def baseEnd_7459262 : Nat := 3830186733817899836820485

theorem tailTrace_7459262 : CollatzResearch.WordTrace tailWord_7459262 prefixEnd_7459262 3830186733817899836820485 := by
  unfold tailWord_7459262
  simp only [CollatzResearch.WordTrace]
  refine ⟨34007704487796898671390505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181374423934916792914082693 34007704487796898671390505)
  ·
    refine ⟨25505778365847674003542879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34007704487796898671390505 25505778365847674003542879)
    ·
      refine ⟨38258667548771511005314319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25505778365847674003542879 38258667548771511005314319)
      ·
        refine ⟨57388001323157266507971479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38258667548771511005314319 57388001323157266507971479)
        ·
          refine ⟨86082001984735899761957219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57388001323157266507971479 86082001984735899761957219)
          ·
            refine ⟨129123002977103849642935829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86082001984735899761957219 129123002977103849642935829)
            ·
              refine ⟨6052640764551742952012617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 129123002977103849642935829 6052640764551742952012617)
              ·
                refine ⟨4539480573413807214009463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6052640764551742952012617 4539480573413807214009463)
                ·
                  refine ⟨6809220860120710821014195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4539480573413807214009463 6809220860120710821014195)
                  ·
                    refine ⟨10213831290181066231521293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6809220860120710821014195 10213831290181066231521293)
                    ·
                      refine ⟨3830186733817899836820485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10213831290181066231521293 3830186733817899836820485)
                      ·
                        rfl

theorem cell23_7459262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3].length) (baseStart_7459262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7459262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7459262 prefixEnd_7459262 := by exact prefixLift 7459262
  have htrace : WordTrace (prefixWord ++ tailWord_7459262) baseStart_7459262 baseEnd_7459262 := by
    simpa [prefixWord, tailWord_7459262, baseEnd_7459262] using wordTrace_append hprefix tailTrace_7459262
  have hstable : (prefixWord ++ tailWord_7459262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7459262).length < 2 ^ (prefixWord ++ tailWord_7459262).sum := by decide
  have hdescent : baseEnd_7459262 < baseStart_7459262 := by decide
  rcases family_descends (prefixWord ++ tailWord_7459262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7459264 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 4]
def baseStart_7459264 : Nat := 118140960795 + 7459264 * 2 ^ 59
def prefixEnd_7459264 : Nat := 4983230072969 + 3 ^ 40 * 7459264 * 2
def baseEnd_7459264 : Nat := 3830187760779208828995475

theorem tailTrace_7459264 : CollatzResearch.WordTrace tailWord_7459264 prefixEnd_7459264 3830187760779208828995475 := by
  unfold tailWord_7459264
  simp only [CollatzResearch.WordTrace]
  refine ⟨136030854424183971856348423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181374472565578629141797897 136030854424183971856348423)
  ·
    refine ⟨204046281636275957784522635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136030854424183971856348423 204046281636275957784522635)
    ·
      refine ⟨306069422454413936676783953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204046281636275957784522635 306069422454413936676783953)
      ·
        refine ⟨229552066840810452507587965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306069422454413936676783953 229552066840810452507587965)
        ·
          refine ⟨86082025065303919690345487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229552066840810452507587965 86082025065303919690345487)
          ·
            refine ⟨129123037597955879535518231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86082025065303919690345487 129123037597955879535518231)
            ·
              refine ⟨193684556396933819303277347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129123037597955879535518231 193684556396933819303277347)
              ·
                refine ⟨290526834595400728954916021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193684556396933819303277347 290526834595400728954916021)
                ·
                  refine ⟨27236890743318818339523377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 290526834595400728954916021 27236890743318818339523377)
                  ·
                    refine ⟨20427668057489113754642533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27236890743318818339523377 20427668057489113754642533)
                    ·
                      refine ⟨3830187760779208828995475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20427668057489113754642533 3830187760779208828995475)
                      ·
                        rfl

theorem cell23_7459264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 4].length) (baseStart_7459264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7459264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7459264 prefixEnd_7459264 := by exact prefixLift 7459264
  have htrace : WordTrace (prefixWord ++ tailWord_7459264) baseStart_7459264 baseEnd_7459264 := by
    simpa [prefixWord, tailWord_7459264, baseEnd_7459264] using wordTrace_append hprefix tailTrace_7459264
  have hstable : (prefixWord ++ tailWord_7459264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7459264).length < 2 ^ (prefixWord ++ tailWord_7459264).sum := by decide
  have hdescent : baseEnd_7459264 < baseStart_7459264 := by decide
  rcases family_descends (prefixWord ++ tailWord_7459264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7459271 : List Nat := [1, 1, 4, 1, 1, 4, 1, 2, 3, 2, 3]
def baseStart_7459271 : Nat := 118140960795 + 7459271 * 2 ^ 59
def prefixEnd_7459271 : Nat := 4983230072969 + 3 ^ 40 * 7459271 * 2
def baseEnd_7459271 : Nat := 3830191355143790301607943

theorem tailTrace_7459271 : CollatzResearch.WordTrace tailWord_7459271 prefixEnd_7459271 3830191355143790301607943 := by
  unfold tailWord_7459271
  simp only [CollatzResearch.WordTrace]
  refine ⟨272061964159342583908201667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181374642772895055938801111 272061964159342583908201667)
  ·
    refine ⟨408092946239013875862302501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272061964159342583908201667 408092946239013875862302501)
    ·
      refine ⟨76517427419815101724181719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 408092946239013875862302501 76517427419815101724181719)
      ·
        refine ⟨114776141129722652586272579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76517427419815101724181719 114776141129722652586272579)
        ·
          refine ⟨172164211694583978879408869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114776141129722652586272579 172164211694583978879408869)
          ·
            refine ⟨32280789692734496039889163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172164211694583978879408869 32280789692734496039889163)
            ·
              refine ⟨48421184539101744059833745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32280789692734496039889163 48421184539101744059833745)
              ·
                refine ⟨36315888404326308044875309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48421184539101744059833745 36315888404326308044875309)
                ·
                  refine ⟨13618458151622365516828241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36315888404326308044875309 13618458151622365516828241)
                  ·
                    refine ⟨10213843613716774137621181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13618458151622365516828241 10213843613716774137621181)
                    ·
                      refine ⟨3830191355143790301607943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10213843613716774137621181 3830191355143790301607943)
                      ·
                        rfl

theorem cell23_7459271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 3, 2, 3].length) (baseStart_7459271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7459271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7459271 prefixEnd_7459271 := by exact prefixLift 7459271
  have htrace : WordTrace (prefixWord ++ tailWord_7459271) baseStart_7459271 baseEnd_7459271 := by
    simpa [prefixWord, tailWord_7459271, baseEnd_7459271] using wordTrace_append hprefix tailTrace_7459271
  have hstable : (prefixWord ++ tailWord_7459271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7459271).length < 2 ^ (prefixWord ++ tailWord_7459271).sum := by decide
  have hdescent : baseEnd_7459271 < baseStart_7459271 := by decide
  rcases family_descends (prefixWord ++ tailWord_7459271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7459285 : List Nat := [1, 3, 2, 3, 1, 3, 1, 2, 3, 2, 2]
def baseStart_7459285 : Nat := 118140960795 + 7459285 * 2 ^ 59
def prefixEnd_7459285 : Nat := 4983230072969 + 3 ^ 40 * 7459285 * 2
def baseEnd_7459285 : Nat := 3830198543872953246832879

theorem tailTrace_7459285 : CollatzResearch.WordTrace tailWord_7459285 prefixEnd_7459285 3830198543872953246832879 := by
  unfold tailWord_7459285
  simp only [CollatzResearch.WordTrace]
  refine ⟨272062474781291864299211309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181374983187527909532807539 272062474781291864299211309)
  ·
    refine ⟨102023428042984449112204241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272062474781291864299211309 102023428042984449112204241)
    ·
      refine ⟨76517571032238336834153181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102023428042984449112204241 76517571032238336834153181)
      ·
        refine ⟨28694089137089376312807443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76517571032238336834153181 28694089137089376312807443)
        ·
          refine ⟨43041133705634064469211165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28694089137089376312807443 43041133705634064469211165)
          ·
            refine ⟨16140425139612774175954187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43041133705634064469211165 16140425139612774175954187)
            ·
              refine ⟨24210637709419161263931281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16140425139612774175954187 24210637709419161263931281)
              ·
                refine ⟨18157978282064370947948461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24210637709419161263931281 18157978282064370947948461)
                ·
                  refine ⟨6809241855774139105480673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18157978282064370947948461 6809241855774139105480673)
                  ·
                    refine ⟨5106931391830604329110505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6809241855774139105480673 5106931391830604329110505)
                    ·
                      refine ⟨3830198543872953246832879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5106931391830604329110505 3830198543872953246832879)
                      ·
                        rfl

theorem cell23_7459285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_7459285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7459285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7459285 prefixEnd_7459285 := by exact prefixLift 7459285
  have htrace : WordTrace (prefixWord ++ tailWord_7459285) baseStart_7459285 baseEnd_7459285 := by
    simpa [prefixWord, tailWord_7459285, baseEnd_7459285] using wordTrace_append hprefix tailTrace_7459285
  have hstable : (prefixWord ++ tailWord_7459285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7459285).length < 2 ^ (prefixWord ++ tailWord_7459285).sum := by decide
  have hdescent : baseEnd_7459285 < baseStart_7459285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7459285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7459335 : List Nat := [1, 1, 4, 3, 3, 2, 1, 1, 1, 3, 3]
def baseStart_7459335 : Nat := 118140960795 + 7459335 * 2 ^ 59
def prefixEnd_7459335 : Nat := 4983230072969 + 3 ^ 40 * 7459335 * 2
def baseEnd_7459335 : Nat := 3830224217905678051207649

theorem tailTrace_7459335 : CollatzResearch.WordTrace tailWord_7459335 prefixEnd_7459335 3830224217905678051207649 := by
  unfold tailWord_7459335
  simp only [CollatzResearch.WordTrace]
  refine ⟨272064298431110722838531459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181376198954073815225687639 272064298431110722838531459)
  ·
    refine ⟨408096447646666084257797189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272064298431110722838531459 408096447646666084257797189)
    ·
      refine ⟨76518083933749890798336973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 408096447646666084257797189 76518083933749890798336973)
      ·
        refine ⟨28694281475156209049376365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76518083933749890798336973 28694281475156209049376365)
        ·
          refine ⟨10760355553183578393516137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28694281475156209049376365 10760355553183578393516137)
          ·
            refine ⟨8070266664887683795137103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10760355553183578393516137 8070266664887683795137103)
            ·
              refine ⟨12105399997331525692705655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8070266664887683795137103 12105399997331525692705655)
              ·
                refine ⟨18158099995997288539058483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12105399997331525692705655 18158099995997288539058483)
                ·
                  refine ⟨27237149993995932808587725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18158099995997288539058483 27237149993995932808587725)
                  ·
                    refine ⟨10213931247748474803220397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27237149993995932808587725 10213931247748474803220397)
                    ·
                      refine ⟨3830224217905678051207649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10213931247748474803220397 3830224217905678051207649)
                      ·
                        rfl

theorem cell23_7459335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_7459335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7459335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7459335 prefixEnd_7459335 := by exact prefixLift 7459335
  have htrace : WordTrace (prefixWord ++ tailWord_7459335) baseStart_7459335 baseEnd_7459335 := by
    simpa [prefixWord, tailWord_7459335, baseEnd_7459335] using wordTrace_append hprefix tailTrace_7459335
  have hstable : (prefixWord ++ tailWord_7459335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7459335).length < 2 ^ (prefixWord ++ tailWord_7459335).sum := by decide
  have hdescent : baseEnd_7459335 < baseStart_7459335 := by decide
  rcases family_descends (prefixWord ++ tailWord_7459335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7459348 : List Nat := [2, 4, 3, 1, 1, 1, 1, 1, 2, 2, 5]
def baseStart_7459348 : Nat := 118140960795 + 7459348 * 2 ^ 59
def prefixEnd_7459348 : Nat := 4983230072969 + 3 ^ 40 * 7459348 * 2
def baseEnd_7459348 : Nat := 3830230893154186500345089

theorem tailTrace_7459348 : CollatzResearch.WordTrace tailWord_7459348 prefixEnd_7459348 3830230893154186500345089 := by
  unfold tailWord_7459348
  simp only [CollatzResearch.WordTrace]
  refine ⟨136032386290031813029377349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181376515053375750705836465 136032386290031813029377349)
  ·
    refine ⟨25506072429380964943008253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136032386290031813029377349 25506072429380964943008253)
    ·
      refine ⟨9564777161017861853628095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25506072429380964943008253 9564777161017861853628095)
      ·
        refine ⟨14347165741526792780442143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9564777161017861853628095 14347165741526792780442143)
        ·
          refine ⟨21520748612290189170663215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14347165741526792780442143 21520748612290189170663215)
          ·
            refine ⟨32281122918435283755994823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21520748612290189170663215 32281122918435283755994823)
            ·
              refine ⟨48421684377652925633992235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32281122918435283755994823 48421684377652925633992235)
              ·
                refine ⟨72632526566479388450988353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48421684377652925633992235 72632526566479388450988353)
                ·
                  refine ⟨54474394924859541338241265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72632526566479388450988353 54474394924859541338241265)
                  ·
                    refine ⟨40855796193644656003680949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54474394924859541338241265 40855796193644656003680949)
                    ·
                      refine ⟨3830230893154186500345089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40855796193644656003680949 3830230893154186500345089)
                      ·
                        rfl

theorem cell23_7459348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_7459348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7459348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7459348 prefixEnd_7459348 := by exact prefixLift 7459348
  have htrace : WordTrace (prefixWord ++ tailWord_7459348) baseStart_7459348 baseEnd_7459348 := by
    simpa [prefixWord, tailWord_7459348, baseEnd_7459348] using wordTrace_append hprefix tailTrace_7459348
  have hstable : (prefixWord ++ tailWord_7459348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7459348).length < 2 ^ (prefixWord ++ tailWord_7459348).sum := by decide
  have hdescent : baseEnd_7459348 < baseStart_7459348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7459348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7459361 : List Nat := [1, 2, 3, 2, 2, 1, 3, 1, 2, 1, 5]
def baseStart_7459361 : Nat := 118140960795 + 7459361 * 2 ^ 59
def prefixEnd_7459361 : Nat := 4983230072969 + 3 ^ 40 * 7459361 * 2
def baseEnd_7459361 : Nat := 3830237568402694949482529

theorem tailTrace_7459361 : CollatzResearch.WordTrace tailWord_7459361 prefixEnd_7459361 3830237568402694949482529 := by
  unfold tailWord_7459361
  simp only [CollatzResearch.WordTrace]
  refine ⟨272065246729016529278977937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181376831152677686185985291 272065246729016529278977937)
  ·
    refine ⟨204048935046762396959233453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272065246729016529278977937 204048935046762396959233453)
    ·
      refine ⟨76518350642535898859712545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204048935046762396959233453 76518350642535898859712545)
      ·
        refine ⟨57388762981901924144784409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76518350642535898859712545 57388762981901924144784409)
        ·
          refine ⟨43041572236426443108588307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57388762981901924144784409 43041572236426443108588307)
          ·
            refine ⟨64562358354639664662882461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43041572236426443108588307 64562358354639664662882461)
            ·
              refine ⟨24210884382989874248580923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64562358354639664662882461 24210884382989874248580923)
              ·
                refine ⟨36316326574484811372871385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24210884382989874248580923 36316326574484811372871385)
                ·
                  refine ⟨27237244930863608529653539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36316326574484811372871385 27237244930863608529653539)
                  ·
                    refine ⟨40855867396295412794480309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27237244930863608529653539 40855867396295412794480309)
                    ·
                      refine ⟨3830237568402694949482529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40855867396295412794480309 3830237568402694949482529)
                      ·
                        rfl

theorem cell23_7459361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_7459361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7459361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7459361 prefixEnd_7459361 := by exact prefixLift 7459361
  have htrace : WordTrace (prefixWord ++ tailWord_7459361) baseStart_7459361 baseEnd_7459361 := by
    simpa [prefixWord, tailWord_7459361, baseEnd_7459361] using wordTrace_append hprefix tailTrace_7459361
  have hstable : (prefixWord ++ tailWord_7459361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7459361).length < 2 ^ (prefixWord ++ tailWord_7459361).sum := by decide
  have hdescent : baseEnd_7459361 < baseStart_7459361 := by decide
  rcases family_descends (prefixWord ++ tailWord_7459361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7459391 : List Nat := [1, 1, 2, 2, 3, 2, 2, 1, 1, 5, 3]
def baseStart_7459391 : Nat := 118140960795 + 7459391 * 2 ^ 59
def prefixEnd_7459391 : Nat := 4983230072969 + 3 ^ 40 * 7459391 * 2
def baseEnd_7459391 : Nat := 3830252972822329832107391

theorem tailTrace_7459391 : CollatzResearch.WordTrace tailWord_7459391 prefixEnd_7459391 3830252972822329832107391 := by
  unfold tailWord_7459391
  simp only [CollatzResearch.WordTrace]
  refine ⟨272066340918907844402570027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181377560612605229601713351 272066340918907844402570027)
  ·
    refine ⟨408099511378361766603855041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272066340918907844402570027 408099511378361766603855041)
    ·
      refine ⟨306074633533771324952891281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408099511378361766603855041 306074633533771324952891281)
      ·
        refine ⟨229555975150328493714668461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306074633533771324952891281 229555975150328493714668461)
        ·
          refine ⟨86083490681373185143000673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229555975150328493714668461 86083490681373185143000673)
          ·
            refine ⟨64562618011029888857250505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86083490681373185143000673 64562618011029888857250505)
            ·
              refine ⟨48421963508272416642937879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64562618011029888857250505 48421963508272416642937879)
              ·
                refine ⟨72632945262408624964406819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48421963508272416642937879 72632945262408624964406819)
                ·
                  refine ⟨108949417893612937446610229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72632945262408624964406819 108949417893612937446610229)
                  ·
                    refine ⟨10214007927526212885619709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 108949417893612937446610229 10214007927526212885619709)
                    ·
                      refine ⟨3830252972822329832107391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10214007927526212885619709 3830252972822329832107391)
                      ·
                        rfl

theorem cell23_7459391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 5, 3].length) (baseStart_7459391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7459391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7459391 prefixEnd_7459391 := by exact prefixLift 7459391
  have htrace : WordTrace (prefixWord ++ tailWord_7459391) baseStart_7459391 baseEnd_7459391 := by
    simpa [prefixWord, tailWord_7459391, baseEnd_7459391] using wordTrace_append hprefix tailTrace_7459391
  have hstable : (prefixWord ++ tailWord_7459391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7459391).length < 2 ^ (prefixWord ++ tailWord_7459391).sum := by decide
  have hdescent : baseEnd_7459391 < baseStart_7459391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7459391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7459392 : List Nat := [2, 1, 1, 2, 2, 2, 6, 1, 2, 2, 2]
def baseStart_7459392 : Nat := 118140960795 + 7459392 * 2 ^ 59
def prefixEnd_7459392 : Nat := 4983230072969 + 3 ^ 40 * 7459392 * 2
def baseEnd_7459392 : Nat := 3830253486302984328194887

theorem tailTrace_7459392 : CollatzResearch.WordTrace tailWord_7459392 prefixEnd_7459392 3830253486302984328194887 := by
  unfold tailWord_7459392
  simp only [CollatzResearch.WordTrace]
  refine ⟨136033188695952110786678215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181377584927936147715570953 136033188695952110786678215)
  ·
    refine ⟨204049783043928166180017323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136033188695952110786678215 204049783043928166180017323)
    ·
      refine ⟨306074674565892249270025985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204049783043928166180017323 306074674565892249270025985)
      ·
        refine ⟨229556005924419186952519489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306074674565892249270025985 229556005924419186952519489)
        ·
          refine ⟨172167004443314390214389617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229556005924419186952519489 172167004443314390214389617)
          ·
            refine ⟨129125253332485792660792213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172167004443314390214389617 129125253332485792660792213)
            ·
              refine ⟨6052746249960271530974635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 129125253332485792660792213 6052746249960271530974635)
              ·
                refine ⟨9079119374940407296461953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6052746249960271530974635 9079119374940407296461953)
                ·
                  refine ⟨6809339531205305472346465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9079119374940407296461953 6809339531205305472346465)
                  ·
                    refine ⟨5107004648403979104259849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6809339531205305472346465 5107004648403979104259849)
                    ·
                      refine ⟨3830253486302984328194887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5107004648403979104259849 3830253486302984328194887)
                      ·
                        rfl

theorem cell23_7459392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 1, 2, 2, 2].length) (baseStart_7459392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7459392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7459392 prefixEnd_7459392 := by exact prefixLift 7459392
  have htrace : WordTrace (prefixWord ++ tailWord_7459392) baseStart_7459392 baseEnd_7459392 := by
    simpa [prefixWord, tailWord_7459392, baseEnd_7459392] using wordTrace_append hprefix tailTrace_7459392
  have hstable : (prefixWord ++ tailWord_7459392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7459392).length < 2 ^ (prefixWord ++ tailWord_7459392).sum := by decide
  have hdescent : baseEnd_7459392 < baseStart_7459392 := by decide
  rcases family_descends (prefixWord ++ tailWord_7459392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7459426 : List Nat := [3, 3, 2, 3, 1, 1, 2, 2, 2, 2, 2]
def baseStart_7459426 : Nat := 118140960795 + 7459426 * 2 ^ 59
def prefixEnd_7459426 : Nat := 4983230072969 + 3 ^ 40 * 7459426 * 2
def baseEnd_7459426 : Nat := 3830270944645237195169731

theorem tailTrace_7459426 : CollatzResearch.WordTrace tailWord_7459426 prefixEnd_7459426 3830270944645237195169731 := by
  unfold tailWord_7459426
  simp only [CollatzResearch.WordTrace]
  refine ⟨68016904368445261345023533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181378411649187363586729421 68016904368445261345023533)
  ·
    refine ⟨25506339138166973004383825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68016904368445261345023533 25506339138166973004383825)
    ·
      refine ⟨19129754353625229753287869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25506339138166973004383825 19129754353625229753287869)
      ·
        refine ⟨7173657882609461157482951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19129754353625229753287869 7173657882609461157482951)
        ·
          refine ⟨10760486823914191736224427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7173657882609461157482951 10760486823914191736224427)
          ·
            refine ⟨16140730235871287604336641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10760486823914191736224427 16140730235871287604336641)
            ·
              refine ⟨12105547676903465703252481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16140730235871287604336641 12105547676903465703252481)
              ·
                refine ⟨9079160757677599277439361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12105547676903465703252481 9079160757677599277439361)
                ·
                  refine ⟨6809370568258199458079521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9079160757677599277439361 6809370568258199458079521)
                  ·
                    refine ⟨5107027926193649593559641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6809370568258199458079521 5107027926193649593559641)
                    ·
                      refine ⟨3830270944645237195169731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5107027926193649593559641 3830270944645237195169731)
                      ·
                        rfl

theorem cell23_7459426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_7459426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7459426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7459426 prefixEnd_7459426 := by exact prefixLift 7459426
  have htrace : WordTrace (prefixWord ++ tailWord_7459426) baseStart_7459426 baseEnd_7459426 := by
    simpa [prefixWord, tailWord_7459426, baseEnd_7459426] using wordTrace_append hprefix tailTrace_7459426
  have hstable : (prefixWord ++ tailWord_7459426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7459426).length < 2 ^ (prefixWord ++ tailWord_7459426).sum := by decide
  have hdescent : baseEnd_7459426 < baseStart_7459426 := by decide
  rcases family_descends (prefixWord ++ tailWord_7459426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7459431 : List Nat := [1, 1, 5, 1, 1, 1, 1, 2, 3, 3, 4]
def baseStart_7459431 : Nat := 118140960795 + 7459431 * 2 ^ 59
def prefixEnd_7459431 : Nat := 4983230072969 + 3 ^ 40 * 7459431 * 2
def baseEnd_7459431 : Nat := 3830273512048509675607207

theorem tailTrace_7459431 : CollatzResearch.WordTrace tailWord_7459431 prefixEnd_7459431 3830273512048509675607207 := by
  unfold tailWord_7459431
  simp only [CollatzResearch.WordTrace]
  refine ⟨272067799838762931234026147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181378533225841954156017431 272067799838762931234026147)
  ·
    refine ⟨408101699758144396851039221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272067799838762931234026147 408101699758144396851039221)
    ·
      refine ⟨38259534352326037204784927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 408101699758144396851039221 38259534352326037204784927)
      ·
        refine ⟨57389301528489055807177391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38259534352326037204784927 57389301528489055807177391)
        ·
          refine ⟨86083952292733583710766087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57389301528489055807177391 86083952292733583710766087)
          ·
            refine ⟨129125928439100375566149131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86083952292733583710766087 129125928439100375566149131)
            ·
              refine ⟨193688892658650563349223697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129125928439100375566149131 193688892658650563349223697)
              ·
                refine ⟨145266669493987922511917773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193688892658650563349223697 145266669493987922511917773)
                ·
                  refine ⟨54475001060245470941969165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145266669493987922511917773 54475001060245470941969165)
                  ·
                    refine ⟨20428125397592051603238437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54475001060245470941969165 20428125397592051603238437)
                    ·
                      refine ⟨3830273512048509675607207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20428125397592051603238437 3830273512048509675607207)
                      ·
                        rfl

theorem cell23_7459431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_7459431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7459431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7459431 prefixEnd_7459431 := by exact prefixLift 7459431
  have htrace : WordTrace (prefixWord ++ tailWord_7459431) baseStart_7459431 baseEnd_7459431 := by
    simpa [prefixWord, tailWord_7459431, baseEnd_7459431] using wordTrace_append hprefix tailTrace_7459431
  have hstable : (prefixWord ++ tailWord_7459431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7459431).length < 2 ^ (prefixWord ++ tailWord_7459431).sum := by decide
  have hdescent : baseEnd_7459431 < baseStart_7459431 := by decide
  rcases family_descends (prefixWord ++ tailWord_7459431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7459438 : List Nat := [4, 1, 2, 2, 2, 1, 2, 1, 1, 2, 5]
def baseStart_7459438 : Nat := 118140960795 + 7459438 * 2 ^ 59
def prefixEnd_7459438 : Nat := 4983230072969 + 3 ^ 40 * 7459438 * 2
def baseEnd_7459438 : Nat := 3830277106413091148219675

theorem tailTrace_7459438 : CollatzResearch.WordTrace tailWord_7459438 prefixEnd_7459438 3830277106413091148219675 := by
  unfold tailWord_7459438
  simp only [CollatzResearch.WordTrace]
  refine ⟨34008506893717196428691371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181378703433158380953020645 34008506893717196428691371)
  ·
    refine ⟨51012760340575794643037057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34008506893717196428691371 51012760340575794643037057)
    ·
      refine ⟨38259570255431845982277793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51012760340575794643037057 38259570255431845982277793)
      ·
        refine ⟨28694677691573884486708345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38259570255431845982277793 28694677691573884486708345)
        ·
          refine ⟨21521008268680413365031259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28694677691573884486708345 21521008268680413365031259)
          ·
            refine ⟨32281512403020620047546889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21521008268680413365031259 32281512403020620047546889)
            ·
              refine ⟨24211134302265465035660167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32281512403020620047546889 24211134302265465035660167)
              ·
                refine ⟨36316701453398197553490251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24211134302265465035660167 36316701453398197553490251)
                ·
                  refine ⟨54475052180097296330235377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36316701453398197553490251 54475052180097296330235377)
                  ·
                    refine ⟨40856289135072972247676533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54475052180097296330235377 40856289135072972247676533)
                    ·
                      refine ⟨3830277106413091148219675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40856289135072972247676533 3830277106413091148219675)
                      ·
                        rfl

theorem cell23_7459438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_7459438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7459438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7459438 prefixEnd_7459438 := by exact prefixLift 7459438
  have htrace : WordTrace (prefixWord ++ tailWord_7459438) baseStart_7459438 baseEnd_7459438 := by
    simpa [prefixWord, tailWord_7459438, baseEnd_7459438] using wordTrace_append hprefix tailTrace_7459438
  have hstable : (prefixWord ++ tailWord_7459438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7459438).length < 2 ^ (prefixWord ++ tailWord_7459438).sum := by decide
  have hdescent : baseEnd_7459438 < baseStart_7459438 := by decide
  rcases family_descends (prefixWord ++ tailWord_7459438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7459448 : List Nat := [2, 1, 2, 1, 1, 1, 2, 5, 2, 4, 2]
def baseStart_7459448 : Nat := 118140960795 + 7459448 * 2 ^ 59
def prefixEnd_7459448 : Nat := 4983230072969 + 3 ^ 40 * 7459448 * 2
def baseEnd_7459448 : Nat := 3830282241219636109094629

theorem tailTrace_7459448 : CollatzResearch.WordTrace tailWord_7459448 prefixEnd_7459448 3830282241219636109094629 := by
  unfold tailWord_7459448
  simp only [CollatzResearch.WordTrace]
  refine ⟨136034209939850671568697499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181378946586467562091596665 136034209939850671568697499)
  ·
    refine ⟨204051314909776007353046249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136034209939850671568697499 204051314909776007353046249)
    ·
      refine ⟨153038486182332005514784687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204051314909776007353046249 153038486182332005514784687)
      ·
        refine ⟨229557729273498008272177031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153038486182332005514784687 229557729273498008272177031)
        ·
          refine ⟨344336593910247012408265547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229557729273498008272177031 344336593910247012408265547)
          ·
            refine ⟨516504890865370518612398321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344336593910247012408265547 516504890865370518612398321)
            ·
              refine ⟨387378668149027888959298741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 516504890865370518612398321 387378668149027888959298741)
              ·
                refine ⟨36316750138971364589934257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 387378668149027888959298741 36316750138971364589934257)
                ·
                  refine ⟨27237562604228523442450693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36316750138971364589934257 27237562604228523442450693)
                  ·
                    refine ⟨5107042988292848145459505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27237562604228523442450693 5107042988292848145459505)
                    ·
                      refine ⟨3830282241219636109094629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5107042988292848145459505 3830282241219636109094629)
                      ·
                        rfl

theorem cell23_7459448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 2, 4, 2].length) (baseStart_7459448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7459448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7459448 prefixEnd_7459448 := by exact prefixLift 7459448
  have htrace : WordTrace (prefixWord ++ tailWord_7459448) baseStart_7459448 baseEnd_7459448 := by
    simpa [prefixWord, tailWord_7459448, baseEnd_7459448] using wordTrace_append hprefix tailTrace_7459448
  have hstable : (prefixWord ++ tailWord_7459448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7459448).length < 2 ^ (prefixWord ++ tailWord_7459448).sum := by decide
  have hdescent : baseEnd_7459448 < baseStart_7459448 := by decide
  rcases family_descends (prefixWord ++ tailWord_7459448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7459468 : List Nat := [2, 2, 1, 2, 1, 1, 2, 5, 2, 2, 3]
def baseStart_7459468 : Nat := 118140960795 + 7459468 * 2 ^ 59
def prefixEnd_7459468 : Nat := 4983230072969 + 3 ^ 40 * 7459468 * 2
def baseEnd_7459468 : Nat := 3830292510832726030844537

theorem tailTrace_7459468 : CollatzResearch.WordTrace tailWord_7459468 prefixEnd_7459468 3830292510832726030844537 := by
  unfold tailWord_7459468
  simp only [CollatzResearch.WordTrace]
  refine ⟨136034574669814443276561529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181379432893085924368748705 136034574669814443276561529)
  ·
    refine ⟨102025931002360832457421147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136034574669814443276561529 102025931002360832457421147)
    ·
      refine ⟨153038896503541248686131721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102025931002360832457421147 153038896503541248686131721)
      ·
        refine ⟨114779172377655936514598791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153038896503541248686131721 114779172377655936514598791)
        ·
          refine ⟨172168758566483904771898187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114779172377655936514598791 172168758566483904771898187)
          ·
            refine ⟨258253137849725857157847281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172168758566483904771898187 258253137849725857157847281)
            ·
              refine ⟨193689853387294392868385461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 258253137849725857157847281 193689853387294392868385461)
              ·
                refine ⟨18158423755058849331411137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 193689853387294392868385461 18158423755058849331411137)
                ·
                  refine ⟨13618817816294136998558353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18158423755058849331411137 13618817816294136998558353)
                  ·
                    refine ⟨10214113362220602748918765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13618817816294136998558353 10214113362220602748918765)
                    ·
                      refine ⟨3830292510832726030844537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10214113362220602748918765 3830292510832726030844537)
                      ·
                        rfl

theorem cell23_7459468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 2, 2, 3].length) (baseStart_7459468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7459468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7459468 prefixEnd_7459468 := by exact prefixLift 7459468
  have htrace : WordTrace (prefixWord ++ tailWord_7459468) baseStart_7459468 baseEnd_7459468 := by
    simpa [prefixWord, tailWord_7459468, baseEnd_7459468] using wordTrace_append hprefix tailTrace_7459468
  have hstable : (prefixWord ++ tailWord_7459468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7459468).length < 2 ^ (prefixWord ++ tailWord_7459468).sum := by decide
  have hdescent : baseEnd_7459468 < baseStart_7459468 := by decide
  rcases family_descends (prefixWord ++ tailWord_7459468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7459488 : List Nat := [2, 1, 1, 4, 4, 1, 1, 1, 8]
def baseStart_7459488 : Nat := 118140960795 + 7459488 * 2 ^ 59
def prefixEnd_7459488 : Nat := 4983230072969 + 3 ^ 40 * 7459488 * 2
def baseEnd_7459488 : Nat := 425589197827312883621605

theorem tailTrace_7459488 : CollatzResearch.WordTrace tailWord_7459488 prefixEnd_7459488 425589197827312883621605 := by
  unfold tailWord_7459488
  simp only [CollatzResearch.WordTrace]
  refine ⟨136034939399778214984425559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181379919199704286645900745 136034939399778214984425559)
  ·
    refine ⟨204052409099667322476638339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136034939399778214984425559 204052409099667322476638339)
    ·
      refine ⟨306078613649500983714957509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204052409099667322476638339 306078613649500983714957509)
      ·
        refine ⟨57389740059281434446554533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 306078613649500983714957509 57389740059281434446554533)
        ·
          refine ⟨10760576261115268958728975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57389740059281434446554533 10760576261115268958728975)
          ·
            refine ⟨16140864391672903438093463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10760576261115268958728975 16140864391672903438093463)
            ·
              refine ⟨24211296587509355157140195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16140864391672903438093463 24211296587509355157140195)
              ·
                refine ⟨36316944881264032735710293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24211296587509355157140195 36316944881264032735710293)
                ·
                  refine ⟨425589197827312883621605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36316944881264032735710293 425589197827312883621605)
                  ·
                    rfl

theorem cell23_7459488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 8].length) (baseStart_7459488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7459488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7459488 prefixEnd_7459488 := by exact prefixLift 7459488
  have htrace : WordTrace (prefixWord ++ tailWord_7459488) baseStart_7459488 baseEnd_7459488 := by
    simpa [prefixWord, tailWord_7459488, baseEnd_7459488] using wordTrace_append hprefix tailTrace_7459488
  have hstable : (prefixWord ++ tailWord_7459488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7459488).length < 2 ^ (prefixWord ++ tailWord_7459488).sum := by decide
  have hdescent : baseEnd_7459488 < baseStart_7459488 := by decide
  rcases family_descends (prefixWord ++ tailWord_7459488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7459561 : List Nat := [1, 2, 1, 1, 1, 2, 5, 10]
def baseStart_7459561 : Nat := 118140960795 + 7459561 * 2 ^ 59
def prefixEnd_7459561 : Nat := 4983230072969 + 3 ^ 40 * 7459561 * 2
def baseEnd_7459561 : Nat := 141864454241984969147467

theorem tailTrace_7459561 : CollatzResearch.WordTrace tailWord_7459561 prefixEnd_7459561 141864454241984969147467 := by
  unfold tailWord_7459561
  simp only [CollatzResearch.WordTrace]
  refine ⟨272072541328291963436258537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181381694218861308957505691 272072541328291963436258537)
  ·
    refine ⟨204054405996218972577193903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272072541328291963436258537 204054405996218972577193903)
    ·
      refine ⟨306081608994328458865790855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204054405996218972577193903 306081608994328458865790855)
      ·
        refine ⟨459122413491492688298686283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306081608994328458865790855 459122413491492688298686283)
        ·
          refine ⟨688683620237239032448029425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459122413491492688298686283 688683620237239032448029425)
          ·
            refine ⟨516512715177929274336022069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 688683620237239032448029425 516512715177929274336022069)
            ·
              refine ⟨48423067047930869469002069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 516512715177929274336022069 48423067047930869469002069)
              ·
                refine ⟨141864454241984969147467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 48423067047930869469002069 141864454241984969147467)
                ·
                  rfl

theorem cell23_7459561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 10].length) (baseStart_7459561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7459561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7459561 prefixEnd_7459561 := by exact prefixLift 7459561
  have htrace : WordTrace (prefixWord ++ tailWord_7459561) baseStart_7459561 baseEnd_7459561 := by
    simpa [prefixWord, tailWord_7459561, baseEnd_7459561] using wordTrace_append hprefix tailTrace_7459561
  have hstable : (prefixWord ++ tailWord_7459561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7459561).length < 2 ^ (prefixWord ++ tailWord_7459561).sum := by decide
  have hdescent : baseEnd_7459561 < baseStart_7459561 := by decide
  rcases family_descends (prefixWord ++ tailWord_7459561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7459568 : List Nat := [2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 4]
def baseStart_7459568 : Nat := 118140960795 + 7459568 * 2 ^ 59
def prefixEnd_7459568 : Nat := 4983230072969 + 3 ^ 40 * 7459568 * 2
def baseEnd_7459568 : Nat := 3830343858898175639594077

theorem tailTrace_7459568 : CollatzResearch.WordTrace tailWord_7459568 prefixEnd_7459568 3830343858898175639594077 := by
  unfold tailWord_7459568
  simp only [CollatzResearch.WordTrace]
  refine ⟨136036398319633301815881679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181381864426177735754508905 136036398319633301815881679)
  ·
    refine ⟨204054597479449952723822519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136036398319633301815881679 204054597479449952723822519)
    ·
      refine ⟨306081896219174929085733779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204054597479449952723822519 306081896219174929085733779)
      ·
        refine ⟨459122844328762393628600669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306081896219174929085733779 459122844328762393628600669)
        ·
          refine ⟨172171066623285897610725251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 459122844328762393628600669 172171066623285897610725251)
          ·
            refine ⟨258256599934928846416087877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172171066623285897610725251 258256599934928846416087877)
            ·
              refine ⟨48423112487799158703016477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 258256599934928846416087877 48423112487799158703016477)
              ·
                refine ⟨18158667182924684513631179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48423112487799158703016477 18158667182924684513631179)
                ·
                  refine ⟨27238000774387026770446769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18158667182924684513631179 27238000774387026770446769)
                  ·
                    refine ⟨20428500580790270077835077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27238000774387026770446769 20428500580790270077835077)
                    ·
                      refine ⟨3830343858898175639594077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20428500580790270077835077 3830343858898175639594077)
                      ·
                        rfl

theorem cell23_7459568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 4].length) (baseStart_7459568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7459568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7459568 prefixEnd_7459568 := by exact prefixLift 7459568
  have htrace : WordTrace (prefixWord ++ tailWord_7459568) baseStart_7459568 baseEnd_7459568 := by
    simpa [prefixWord, tailWord_7459568, baseEnd_7459568] using wordTrace_append hprefix tailTrace_7459568
  have hstable : (prefixWord ++ tailWord_7459568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7459568).length < 2 ^ (prefixWord ++ tailWord_7459568).sum := by decide
  have hdescent : baseEnd_7459568 < baseStart_7459568 := by decide
  rcases family_descends (prefixWord ++ tailWord_7459568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7459628 : List Nat := [2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 4]
def baseStart_7459628 : Nat := 118140960795 + 7459628 * 2 ^ 59
def prefixEnd_7459628 : Nat := 4983230072969 + 3 ^ 40 * 7459628 * 2
def baseEnd_7459628 : Nat := 3830374667737445404843801

theorem tailTrace_7459628 : CollatzResearch.WordTrace tailWord_7459628 prefixEnd_7459628 3830374667737445404843801 := by
  unfold tailWord_7459628
  simp only [CollatzResearch.WordTrace]
  refine ⟨136037492509524616939473769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181383323346032822585965025 136037492509524616939473769)
  ·
    refine ⟨102028119382143462704605327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136037492509524616939473769 102028119382143462704605327)
    ·
      refine ⟨153042179073215194056907991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102028119382143462704605327 153042179073215194056907991)
      ·
        refine ⟨229563268609822791085361987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153042179073215194056907991 229563268609822791085361987)
        ·
          refine ⟨344344902914734186628042981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229563268609822791085361987 344344902914734186628042981)
          ·
            refine ⟨64564669296512659992758059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 344344902914734186628042981 64564669296512659992758059)
            ·
              refine ⟨96847003944768989989137089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64564669296512659992758059 96847003944768989989137089)
              ·
                refine ⟨72635252958576742491852817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96847003944768989989137089 72635252958576742491852817)
                ·
                  refine ⟨54476439718932556868889613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72635252958576742491852817 54476439718932556868889613)
                  ·
                    refine ⟨20428664894599708825833605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54476439718932556868889613 20428664894599708825833605)
                    ·
                      refine ⟨3830374667737445404843801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20428664894599708825833605 3830374667737445404843801)
                      ·
                        rfl

theorem cell23_7459628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 4].length) (baseStart_7459628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7459628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7459628 prefixEnd_7459628 := by exact prefixLift 7459628
  have htrace : WordTrace (prefixWord ++ tailWord_7459628) baseStart_7459628 baseEnd_7459628 := by
    simpa [prefixWord, tailWord_7459628, baseEnd_7459628] using wordTrace_append hprefix tailTrace_7459628
  have hstable : (prefixWord ++ tailWord_7459628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7459628).length < 2 ^ (prefixWord ++ tailWord_7459628).sum := by decide
  have hdescent : baseEnd_7459628 < baseStart_7459628 := by decide
  rcases family_descends (prefixWord ++ tailWord_7459628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7459629 : List Nat := [1, 5, 3, 2, 1, 1, 3, 7]
def baseStart_7459629 : Nat := 118140960795 + 7459629 * 2 ^ 59
def prefixEnd_7459629 : Nat := 4983230072969 + 3 ^ 40 * 7459629 * 2
def baseEnd_7459629 : Nat := 141865747452522218553011

theorem tailTrace_7459629 : CollatzResearch.WordTrace tailWord_7459629 prefixEnd_7459629 141865747452522218553011 := by
  unfold tailWord_7459629
  simp only [CollatzResearch.WordTrace]
  refine ⟨272075021492045611049733941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181383347661363740699822627 272075021492045611049733941)
  ·
    refine ⟨25507033264879276035912557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 272075021492045611049733941 25507033264879276035912557)
    ·
      refine ⟨9565137474329728513467209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25507033264879276035912557 9565137474329728513467209)
      ·
        refine ⟨7173853105747296385100407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9565137474329728513467209 7173853105747296385100407)
        ·
          refine ⟨10760779658620944577650611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7173853105747296385100407 10760779658620944577650611)
          ·
            refine ⟨16141169487931416866475917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10760779658620944577650611 16141169487931416866475917)
            ·
              refine ⟨6052938557974281324928469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16141169487931416866475917 6052938557974281324928469)
              ·
                refine ⟨141865747452522218553011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6052938557974281324928469 141865747452522218553011)
                ·
                  rfl

theorem cell23_7459629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 7].length) (baseStart_7459629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7459629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7459629 prefixEnd_7459629 := by exact prefixLift 7459629
  have htrace : WordTrace (prefixWord ++ tailWord_7459629) baseStart_7459629 baseEnd_7459629 := by
    simpa [prefixWord, tailWord_7459629, baseEnd_7459629] using wordTrace_append hprefix tailTrace_7459629
  have hstable : (prefixWord ++ tailWord_7459629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7459629).length < 2 ^ (prefixWord ++ tailWord_7459629).sum := by decide
  have hdescent : baseEnd_7459629 < baseStart_7459629 := by decide
  rcases family_descends (prefixWord ++ tailWord_7459629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7459648 : List Nat := [2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 5]
def baseStart_7459648 : Nat := 118140960795 + 7459648 * 2 ^ 59
def prefixEnd_7459648 : Nat := 4983230072969 + 3 ^ 40 * 7459648 * 2
def baseEnd_7459648 : Nat := 3830384937350535326593709

theorem tailTrace_7459648 : CollatzResearch.WordTrace tailWord_7459648 prefixEnd_7459648 3830384937350535326593709 := by
  unfold tailWord_7459648
  simp only [CollatzResearch.WordTrace]
  refine ⟨136037857239488388647337799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181383809652651184863117065 136037857239488388647337799)
  ·
    refine ⟨204056785859232582971006699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136037857239488388647337799 204056785859232582971006699)
    ·
      refine ⟨306085178788848874456510049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204056785859232582971006699 306085178788848874456510049)
      ·
        refine ⟨229563884091636655842382537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306085178788848874456510049 229563884091636655842382537)
        ·
          refine ⟨172172913068727491881786903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229563884091636655842382537 172172913068727491881786903)
          ·
            refine ⟨258259369603091237822680355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172172913068727491881786903 258259369603091237822680355)
            ·
              refine ⟨387389054404636856734020533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258259369603091237822680355 387389054404636856734020533)
              ·
                refine ⟨36317723850434705318814425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 387389054404636856734020533 36317723850434705318814425)
                ·
                  refine ⟨27238292887826028989110819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36317723850434705318814425 27238292887826028989110819)
                  ·
                    refine ⟨40857439331739043483666229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27238292887826028989110819 40857439331739043483666229)
                    ·
                      refine ⟨3830384937350535326593709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40857439331739043483666229 3830384937350535326593709)
                      ·
                        rfl

theorem cell23_7459648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 5].length) (baseStart_7459648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7459648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7459648 prefixEnd_7459648 := by exact prefixLift 7459648
  have htrace : WordTrace (prefixWord ++ tailWord_7459648) baseStart_7459648 baseEnd_7459648 := by
    simpa [prefixWord, tailWord_7459648, baseEnd_7459648] using wordTrace_append hprefix tailTrace_7459648
  have hstable : (prefixWord ++ tailWord_7459648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7459648).length < 2 ^ (prefixWord ++ tailWord_7459648).sum := by decide
  have hdescent : baseEnd_7459648 < baseStart_7459648 := by decide
  rcases family_descends (prefixWord ++ tailWord_7459648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7459708 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 3, 1, 7]
def baseStart_7459708 : Nat := 118140960795 + 7459708 * 2 ^ 59
def prefixEnd_7459708 : Nat := 4983230072969 + 3 ^ 40 * 7459708 * 2
def baseEnd_7459708 : Nat := 3830415746189805091843433

theorem tailTrace_7459708 : CollatzResearch.WordTrace tailWord_7459708 prefixEnd_7459708 3830415746189805091843433 := by
  unfold tailWord_7459708
  simp only [CollatzResearch.WordTrace]
  refine ⟨136038951429379703770929889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181385268572506271694573185 136038951429379703770929889)
  ·
    refine ⟨102029213572034777828197417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136038951429379703770929889 102029213572034777828197417)
    ·
      refine ⟨76521910179026083371148063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102029213572034777828197417 76521910179026083371148063)
      ·
        refine ⟨114782865268539125056722095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76521910179026083371148063 114782865268539125056722095)
        ·
          refine ⟨172174297902808687585083143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114782865268539125056722095 172174297902808687585083143)
          ·
            refine ⟨258261446854213031377624715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172174297902808687585083143 258261446854213031377624715)
            ·
              refine ⟨387392170281319547066437073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258261446854213031377624715 387392170281319547066437073)
              ·
                refine ⟨290544127710989660299827805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 387392170281319547066437073 290544127710989660299827805)
                ·
                  refine ⟨108954047891621122612435427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 290544127710989660299827805 108954047891621122612435427)
                  ·
                    refine ⟨163431071837431683918653141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 108954047891621122612435427 163431071837431683918653141)
                    ·
                      refine ⟨3830415746189805091843433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 163431071837431683918653141 3830415746189805091843433)
                      ·
                        rfl

theorem cell23_7459708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_7459708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7459708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7459708 prefixEnd_7459708 := by exact prefixLift 7459708
  have htrace : WordTrace (prefixWord ++ tailWord_7459708) baseStart_7459708 baseEnd_7459708 := by
    simpa [prefixWord, tailWord_7459708, baseEnd_7459708] using wordTrace_append hprefix tailTrace_7459708
  have hstable : (prefixWord ++ tailWord_7459708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7459708).length < 2 ^ (prefixWord ++ tailWord_7459708).sum := by decide
  have hdescent : baseEnd_7459708 < baseStart_7459708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7459708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7459715 : List Nat := [1, 1, 1, 3, 4, 1, 3, 2, 2, 5]
def baseStart_7459715 : Nat := 118140960795 + 7459715 * 2 ^ 59
def prefixEnd_7459715 : Nat := 4983230072969 + 3 ^ 40 * 7459715 * 2
def baseEnd_7459715 : Nat := 1276806446851462188151967

theorem tailTrace_7459715 : CollatzResearch.WordTrace tailWord_7459715 prefixEnd_7459715 1276806446851462188151967 := by
  unfold tailWord_7459715
  simp only [CollatzResearch.WordTrace]
  refine ⟨272078158169734047737364599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181385438779822698491576399 272078158169734047737364599)
  ·
    refine ⟨408117237254601071606046899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272078158169734047737364599 408117237254601071606046899)
    ·
      refine ⟨612175855881901607409070349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408117237254601071606046899 612175855881901607409070349)
      ·
        refine ⟨229565945955713102778401381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 612175855881901607409070349 229565945955713102778401381)
        ·
          refine ⟨43043614866696206770950259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 229565945955713102778401381 43043614866696206770950259)
          ·
            refine ⟨64565422300044310156425389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43043614866696206770950259 64565422300044310156425389)
            ·
              refine ⟨24212033362516616308659521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64565422300044310156425389 24212033362516616308659521)
              ·
                refine ⟨18159025021887462231494641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24212033362516616308659521 18159025021887462231494641)
                ·
                  refine ⟨13619268766415596673620981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18159025021887462231494641 13619268766415596673620981)
                  ·
                    refine ⟨1276806446851462188151967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13619268766415596673620981 1276806446851462188151967)
                    ·
                      rfl

theorem cell23_7459715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 2, 5].length) (baseStart_7459715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7459715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7459715 prefixEnd_7459715 := by exact prefixLift 7459715
  have htrace : WordTrace (prefixWord ++ tailWord_7459715) baseStart_7459715 baseEnd_7459715 := by
    simpa [prefixWord, tailWord_7459715, baseEnd_7459715] using wordTrace_append hprefix tailTrace_7459715
  have hstable : (prefixWord ++ tailWord_7459715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7459715).length < 2 ^ (prefixWord ++ tailWord_7459715).sum := by decide
  have hdescent : baseEnd_7459715 < baseStart_7459715 := by decide
  rcases family_descends (prefixWord ++ tailWord_7459715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7459719 : List Nat := [1, 1, 4, 2, 3, 2, 3, 2, 5]
def baseStart_7459719 : Nat := 118140960795 + 7459719 * 2 ^ 59
def prefixEnd_7459719 : Nat := 4983230072969 + 3 ^ 40 * 7459719 * 2
def baseEnd_7459719 : Nat := 425602377164111616533987

theorem tailTrace_7459719 : CollatzResearch.WordTrace tailWord_7459719 prefixEnd_7459719 425602377164111616533987 := by
  unfold tailWord_7459719
  simp only [CollatzResearch.WordTrace]
  refine ⟨272078304061719556420510211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181385536041146370947006807 272078304061719556420510211)
  ·
    refine ⟨408117456092579334630765317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272078304061719556420510211 408117456092579334630765317)
    ·
      refine ⟨76522023017358625243268497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 408117456092579334630765317 76522023017358625243268497)
      ·
        refine ⟨57391517263018968932451373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76522023017358625243268497 57391517263018968932451373)
        ·
          refine ⟨21521818973632113349669265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57391517263018968932451373 21521818973632113349669265)
          ·
            refine ⟨16141364230224085012251949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21521818973632113349669265 16141364230224085012251949)
            ·
              refine ⟨6053011586334031879594481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16141364230224085012251949 6053011586334031879594481)
              ·
                refine ⟨4539758689750523909695861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6053011586334031879594481 4539758689750523909695861)
                ·
                  refine ⟨425602377164111616533987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4539758689750523909695861 425602377164111616533987)
                  ·
                    rfl

theorem cell23_7459719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 2, 5].length) (baseStart_7459719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7459719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7459719 prefixEnd_7459719 := by exact prefixLift 7459719
  have htrace : WordTrace (prefixWord ++ tailWord_7459719) baseStart_7459719 baseEnd_7459719 := by
    simpa [prefixWord, tailWord_7459719, baseEnd_7459719] using wordTrace_append hprefix tailTrace_7459719
  have hstable : (prefixWord ++ tailWord_7459719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7459719).length < 2 ^ (prefixWord ++ tailWord_7459719).sum := by decide
  have hdescent : baseEnd_7459719 < baseStart_7459719 := by decide
  rcases family_descends (prefixWord ++ tailWord_7459719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7459730 : List Nat := [3, 2, 3, 2, 2, 2, 2, 1, 2, 2, 2]
def baseStart_7459730 : Nat := 118140960795 + 7459730 * 2 ^ 59
def prefixEnd_7459730 : Nat := 4983230072969 + 3 ^ 40 * 7459730 * 2
def baseEnd_7459730 : Nat := 3830427042764204005768333

theorem tailTrace_7459730 : CollatzResearch.WordTrace tailWord_7459730 prefixEnd_7459730 3830427042764204005768333 := by
  unfold tailWord_7459730
  simp only [CollatzResearch.WordTrace]
  refine ⟨68019676316169926324790161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181385803509786470199440429 68019676316169926324790161)
  ·
    refine ⟨51014757237127444743592621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68019676316169926324790161 51014757237127444743592621)
    ·
      refine ⟨19130533963922791778847233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51014757237127444743592621 19130533963922791778847233)
      ·
        refine ⟨14347900472942093834135425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19130533963922791778847233 14347900472942093834135425)
        ·
          refine ⟨10760925354706570375601569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14347900472942093834135425 10760925354706570375601569)
          ·
            refine ⟨8070694016029927781701177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10760925354706570375601569 8070694016029927781701177)
            ·
              refine ⟨6053020512022445836275883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8070694016029927781701177 6053020512022445836275883)
              ·
                refine ⟨9079530768033668754413825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6053020512022445836275883 9079530768033668754413825)
                ·
                  refine ⟨6809648076025251565810369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9079530768033668754413825 6809648076025251565810369)
                  ·
                    refine ⟨5107236057018938674357777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6809648076025251565810369 5107236057018938674357777)
                    ·
                      refine ⟨3830427042764204005768333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5107236057018938674357777 3830427042764204005768333)
                      ·
                        rfl

theorem cell23_7459730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_7459730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7459730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7459730 prefixEnd_7459730 := by exact prefixLift 7459730
  have htrace : WordTrace (prefixWord ++ tailWord_7459730) baseStart_7459730 baseEnd_7459730 := by
    simpa [prefixWord, tailWord_7459730, baseEnd_7459730] using wordTrace_append hprefix tailTrace_7459730
  have hstable : (prefixWord ++ tailWord_7459730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7459730).length < 2 ^ (prefixWord ++ tailWord_7459730).sum := by decide
  have hdescent : baseEnd_7459730 < baseStart_7459730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7459730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7459735 : List Nat := [1, 1, 3, 3, 1, 2, 1, 2, 4, 1, 4]
def baseStart_7459735 : Nat := 118140960795 + 7459735 * 2 ^ 59
def prefixEnd_7459735 : Nat := 4983230072969 + 3 ^ 40 * 7459735 * 2
def baseEnd_7459735 : Nat := 3830429610167476486205809

theorem tailTrace_7459735 : CollatzResearch.WordTrace tailWord_7459735 prefixEnd_7459735 3830429610167476486205809 := by
  unfold tailWord_7459735
  simp only [CollatzResearch.WordTrace]
  refine ⟨272078887629661591153092659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181385925086441060768728439 272078887629661591153092659)
  ·
    refine ⟨408118331444492386729638989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272078887629661591153092659 408118331444492386729638989)
    ·
      refine ⟨153044374291684645023614621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 408118331444492386729638989 153044374291684645023614621)
      ·
        refine ⟨57391640359381741883855483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153044374291684645023614621 57391640359381741883855483)
        ·
          refine ⟨86087460539072612825783225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57391640359381741883855483 86087460539072612825783225)
          ·
            refine ⟨64565595404304459619337419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86087460539072612825783225 64565595404304459619337419)
            ·
              refine ⟨96848393106456689429006129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64565595404304459619337419 96848393106456689429006129)
              ·
                refine ⟨72636294829842517071754597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96848393106456689429006129 72636294829842517071754597)
                ·
                  refine ⟨13619305280595471950953987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72636294829842517071754597 13619305280595471950953987)
                  ·
                    refine ⟨20428957920893207926430981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13619305280595471950953987 20428957920893207926430981)
                    ·
                      refine ⟨3830429610167476486205809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20428957920893207926430981 3830429610167476486205809)
                      ·
                        rfl

theorem cell23_7459735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_7459735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7459735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7459735 prefixEnd_7459735 := by exact prefixLift 7459735
  have htrace : WordTrace (prefixWord ++ tailWord_7459735) baseStart_7459735 baseEnd_7459735 := by
    simpa [prefixWord, tailWord_7459735, baseEnd_7459735] using wordTrace_append hprefix tailTrace_7459735
  have hstable : (prefixWord ++ tailWord_7459735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7459735).length < 2 ^ (prefixWord ++ tailWord_7459735).sum := by decide
  have hdescent : baseEnd_7459735 < baseStart_7459735 := by decide
  rcases family_descends (prefixWord ++ tailWord_7459735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7459755 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 6, 2, 3]
def baseStart_7459755 : Nat := 118140960795 + 7459755 * 2 ^ 59
def prefixEnd_7459755 : Nat := 4983230072969 + 3 ^ 40 * 7459755 * 2
def baseEnd_7459755 : Nat := 3830439879780566407955717

theorem tailTrace_7459755 : CollatzResearch.WordTrace tailWord_7459755 prefixEnd_7459755 3830439879780566407955717 := by
  unfold tailWord_7459755
  simp only [CollatzResearch.WordTrace]
  refine ⟨272079617089589134568820719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181386411393059423045880479 272079617089589134568820719)
  ·
    refine ⟨408119425634383701853231079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272079617089589134568820719 408119425634383701853231079)
    ·
      refine ⟨612179138451575552779846619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408119425634383701853231079 612179138451575552779846619)
      ·
        refine ⟨918268707677363329169769929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 612179138451575552779846619 918268707677363329169769929)
        ·
          refine ⟨688701530758022496877327447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 918268707677363329169769929 688701530758022496877327447)
          ·
            refine ⟨1033052296137033745315991171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 688701530758022496877327447 1033052296137033745315991171)
            ·
              refine ⟨1549578444205550617973986757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1033052296137033745315991171 1549578444205550617973986757)
              ·
                refine ⟨290545958288540740870122517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1549578444205550617973986757 290545958288540740870122517)
                ·
                  refine ⟨13619341794775347228286993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 290545958288540740870122517 13619341794775347228286993)
                  ·
                    refine ⟨10214506346081510421215245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13619341794775347228286993 10214506346081510421215245)
                    ·
                      refine ⟨3830439879780566407955717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10214506346081510421215245 3830439879780566407955717)
                      ·
                        rfl

theorem cell23_7459755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 6, 2, 3].length) (baseStart_7459755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7459755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7459755 prefixEnd_7459755 := by exact prefixLift 7459755
  have htrace : WordTrace (prefixWord ++ tailWord_7459755) baseStart_7459755 baseEnd_7459755 := by
    simpa [prefixWord, tailWord_7459755, baseEnd_7459755] using wordTrace_append hprefix tailTrace_7459755
  have hstable : (prefixWord ++ tailWord_7459755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7459755).length < 2 ^ (prefixWord ++ tailWord_7459755).sum := by decide
  have hdescent : baseEnd_7459755 < baseStart_7459755 := by decide
  rcases family_descends (prefixWord ++ tailWord_7459755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7459765 : List Nat := [1, 3, 3, 2, 1, 1, 2, 1, 2, 1, 6]
def baseStart_7459765 : Nat := 118140960795 + 7459765 * 2 ^ 59
def prefixEnd_7459765 : Nat := 4983230072969 + 3 ^ 40 * 7459765 * 2
def baseEnd_7459765 : Nat := 3830445014587111368830671

theorem tailTrace_7459765 : CollatzResearch.WordTrace tailWord_7459765 prefixEnd_7459765 3830445014587111368830671 := by
  unfold tailWord_7459765
  simp only [CollatzResearch.WordTrace]
  refine ⟨272079981819552906276684749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181386654546368604184456499 272079981819552906276684749)
  ·
    refine ⟨102029993182332339853756781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272079981819552906276684749 102029993182332339853756781)
    ·
      refine ⟨38261247443374627445158793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102029993182332339853756781 38261247443374627445158793)
      ·
        refine ⟨28695935582530970583869095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38261247443374627445158793 28695935582530970583869095)
        ·
          refine ⟨43043903373796455875803643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28695935582530970583869095 43043903373796455875803643)
          ·
            refine ⟨64565855060694683813705465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43043903373796455875803643 64565855060694683813705465)
            ·
              refine ⟨48424391295521012860279099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64565855060694683813705465 48424391295521012860279099)
              ·
                refine ⟨72636586943281519290418649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48424391295521012860279099 72636586943281519290418649)
                ·
                  refine ⟨54477440207461139467813987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72636586943281519290418649 54477440207461139467813987)
                  ·
                    refine ⟨81716160311191709201720981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54477440207461139467813987 81716160311191709201720981)
                    ·
                      refine ⟨3830445014587111368830671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81716160311191709201720981 3830445014587111368830671)
                      ·
                        rfl

theorem cell23_7459765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_7459765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7459765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7459765 prefixEnd_7459765 := by exact prefixLift 7459765
  have htrace : WordTrace (prefixWord ++ tailWord_7459765) baseStart_7459765 baseEnd_7459765 := by
    simpa [prefixWord, tailWord_7459765, baseEnd_7459765] using wordTrace_append hprefix tailTrace_7459765
  have hstable : (prefixWord ++ tailWord_7459765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7459765).length < 2 ^ (prefixWord ++ tailWord_7459765).sum := by decide
  have hdescent : baseEnd_7459765 < baseStart_7459765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7459765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7459813 : List Nat := [1, 3, 1, 6, 1, 1, 2, 3, 1, 4]
def baseStart_7459813 : Nat := 118140960795 + 7459813 * 2 ^ 59
def prefixEnd_7459813 : Nat := 4983230072969 + 3 ^ 40 * 7459813 * 2
def baseEnd_7459813 : Nat := 1276823220552842393676817

theorem tailTrace_7459813 : CollatzResearch.WordTrace tailWord_7459813 prefixEnd_7459813 1276823220552842393676817 := by
  unfold tailWord_7459813
  simp only [CollatzResearch.WordTrace]
  refine ⟨272081732523379010474432093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181387821682252673649621395 272081732523379010474432093)
  ·
    refine ⟨102030649696267128927912035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272081732523379010474432093 102030649696267128927912035)
    ·
      refine ⟨153045974544400693391868053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102030649696267128927912035 153045974544400693391868053)
      ·
        refine ⟨7174030056768782502743815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 153045974544400693391868053 7174030056768782502743815)
        ·
          refine ⟨10761045085153173754115723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7174030056768782502743815 10761045085153173754115723)
          ·
            refine ⟨16141567627729760631173585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10761045085153173754115723 16141567627729760631173585)
            ·
              refine ⟨12106175720797320473380189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16141567627729760631173585 12106175720797320473380189)
              ·
                refine ⟨4539815895298995177517571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12106175720797320473380189 4539815895298995177517571)
                ·
                  refine ⟨6809723842948492766276357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4539815895298995177517571 6809723842948492766276357)
                  ·
                    refine ⟨1276823220552842393676817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6809723842948492766276357 1276823220552842393676817)
                    ·
                      rfl

theorem cell23_7459813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 3, 1, 4].length) (baseStart_7459813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7459813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7459813 prefixEnd_7459813 := by exact prefixLift 7459813
  have htrace : WordTrace (prefixWord ++ tailWord_7459813) baseStart_7459813 baseEnd_7459813 := by
    simpa [prefixWord, tailWord_7459813, baseEnd_7459813] using wordTrace_append hprefix tailTrace_7459813
  have hstable : (prefixWord ++ tailWord_7459813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7459813).length < 2 ^ (prefixWord ++ tailWord_7459813).sum := by decide
  have hdescent : baseEnd_7459813 < baseStart_7459813 := by decide
  rcases family_descends (prefixWord ++ tailWord_7459813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7459826 : List Nat := [3, 2, 1, 5, 1, 2, 1, 2, 6]
def baseStart_7459826 : Nat := 118140960795 + 7459826 * 2 ^ 59
def prefixEnd_7459826 : Nat := 4983230072969 + 3 ^ 40 * 7459826 * 2
def baseEnd_7459826 : Nat := 425608481878559514463099

theorem tailTrace_7459826 : CollatzResearch.WordTrace tailWord_7459826 prefixEnd_7459826 425608481878559514463099 := by
  unfold tailWord_7459826
  simp only [CollatzResearch.WordTrace]
  refine ⟨68020551668082978423663833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181388137781554609129770221 68020551668082978423663833)
  ·
    refine ⟨51015413751062233817747875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68020551668082978423663833 51015413751062233817747875)
    ·
      refine ⟨76523120626593350726621813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51015413751062233817747875 76523120626593350726621813)
      ·
        refine ⟨7174042558743126630620795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76523120626593350726621813 7174042558743126630620795)
        ·
          refine ⟨10761063838114689945931193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7174042558743126630620795 10761063838114689945931193)
          ·
            refine ⟨8070797878586017459448395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10761063838114689945931193 8070797878586017459448395)
            ·
              refine ⟨12106196817879026189172593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8070797878586017459448395 12106196817879026189172593)
              ·
                refine ⟨9079647613409269641879445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12106196817879026189172593 9079647613409269641879445)
                ·
                  refine ⟨425608481878559514463099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9079647613409269641879445 425608481878559514463099)
                  ·
                    rfl

theorem cell23_7459826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 2, 6].length) (baseStart_7459826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7459826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7459826 prefixEnd_7459826 := by exact prefixLift 7459826
  have htrace : WordTrace (prefixWord ++ tailWord_7459826) baseStart_7459826 baseEnd_7459826 := by
    simpa [prefixWord, tailWord_7459826, baseEnd_7459826] using wordTrace_append hprefix tailTrace_7459826
  have hstable : (prefixWord ++ tailWord_7459826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7459826).length < 2 ^ (prefixWord ++ tailWord_7459826).sum := by decide
  have hdescent : baseEnd_7459826 < baseStart_7459826 := by decide
  rcases family_descends (prefixWord ++ tailWord_7459826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7459836 : List Nat := [2, 2, 2, 1, 2, 3, 2, 4, 1, 1, 3]
def baseStart_7459836 : Nat := 118140960795 + 7459836 * 2 ^ 59
def prefixEnd_7459836 : Nat := 4983230072969 + 3 ^ 40 * 7459836 * 2
def baseEnd_7459836 : Nat := 3830481471713580591042845

theorem tailTrace_7459836 : CollatzResearch.WordTrace tailWord_7459836 prefixEnd_7459836 3830481471713580591042845 := by
  unfold tailWord_7459836
  simp only [CollatzResearch.WordTrace]
  refine ⟨136041285701147842701259681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181388380934863790268346241 136041285701147842701259681)
  ·
    refine ⟨102030964275860882025944761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136041285701147842701259681 102030964275860882025944761)
    ·
      refine ⟨76523223206895661519458571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102030964275860882025944761 76523223206895661519458571)
      ·
        refine ⟨114784834810343492279187857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76523223206895661519458571 114784834810343492279187857)
        ·
          refine ⟨86088626107757619209390893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114784834810343492279187857 86088626107757619209390893)
          ·
            refine ⟨32283234790409107203521585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86088626107757619209390893 32283234790409107203521585)
            ·
              refine ⟨24212426092806830402641189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32283234790409107203521585 24212426092806830402641189)
              ·
                refine ⟨4539829892401280700495223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24212426092806830402641189 4539829892401280700495223)
                ·
                  refine ⟨6809744838601921050742835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4539829892401280700495223 6809744838601921050742835)
                  ·
                    refine ⟨10214617257902881576114253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6809744838601921050742835 10214617257902881576114253)
                    ·
                      refine ⟨3830481471713580591042845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10214617257902881576114253 3830481471713580591042845)
                      ·
                        rfl

theorem cell23_7459836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 4, 1, 1, 3].length) (baseStart_7459836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7459836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7459836 prefixEnd_7459836 := by exact prefixLift 7459836
  have htrace : WordTrace (prefixWord ++ tailWord_7459836) baseStart_7459836 baseEnd_7459836 := by
    simpa [prefixWord, tailWord_7459836, baseEnd_7459836] using wordTrace_append hprefix tailTrace_7459836
  have hstable : (prefixWord ++ tailWord_7459836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7459836).length < 2 ^ (prefixWord ++ tailWord_7459836).sum := by decide
  have hdescent : baseEnd_7459836 < baseStart_7459836 := by decide
  rcases family_descends (prefixWord ++ tailWord_7459836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7459852 : List Nat := [2, 2, 1, 2, 3, 2, 3, 1, 1, 6]
def baseStart_7459852 : Nat := 118140960795 + 7459852 * 2 ^ 59
def prefixEnd_7459852 : Nat := 4983230072969 + 3 ^ 40 * 7459852 * 2
def baseEnd_7459852 : Nat := 1276829895801350842814257

theorem tailTrace_7459852 : CollatzResearch.WordTrace tailWord_7459852 prefixEnd_7459852 1276829895801350842814257 := by
  unfold tailWord_7459852
  simp only [CollatzResearch.WordTrace]
  refine ⟨136041577485118860067550905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181388769980158480090067873 136041577485118860067550905)
  ·
    refine ⟨102031183113839145050663179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136041577485118860067550905 102031183113839145050663179)
    ·
      refine ⟨153046774670758717575994769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102031183113839145050663179 153046774670758717575994769)
      ·
        refine ⟨114785081003069038181996077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153046774670758717575994769 114785081003069038181996077)
        ·
          refine ⟨43044405376150889318248529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114785081003069038181996077 43044405376150889318248529)
          ·
            refine ⟨32283304032113166988686397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43044405376150889318248529 32283304032113166988686397)
            ·
              refine ⟨12106239012042437620757399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32283304032113166988686397 12106239012042437620757399)
              ·
                refine ⟨18159358518063656431136099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12106239012042437620757399 18159358518063656431136099)
                ·
                  refine ⟨27239037777095484646704149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18159358518063656431136099 27239037777095484646704149)
                  ·
                    refine ⟨1276829895801350842814257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27239037777095484646704149 1276829895801350842814257)
                    ·
                      rfl

theorem cell23_7459852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 1, 6].length) (baseStart_7459852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7459852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7459852 prefixEnd_7459852 := by exact prefixLift 7459852
  have htrace : WordTrace (prefixWord ++ tailWord_7459852) baseStart_7459852 baseEnd_7459852 := by
    simpa [prefixWord, tailWord_7459852, baseEnd_7459852] using wordTrace_append hprefix tailTrace_7459852
  have hstable : (prefixWord ++ tailWord_7459852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7459852).length < 2 ^ (prefixWord ++ tailWord_7459852).sum := by decide
  have hdescent : baseEnd_7459852 < baseStart_7459852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7459852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7459855 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 7, 2, 4]
def baseStart_7459855 : Nat := 118140960795 + 7459855 * 2 ^ 59
def prefixEnd_7459855 : Nat := 4983230072969 + 3 ^ 40 * 7459855 * 2
def baseEnd_7459855 : Nat := 3830491227846016016705257

theorem tailTrace_7459855 : CollatzResearch.WordTrace tailWord_7459855 prefixEnd_7459855 3830491227846016016705257 := by
  unfold tailWord_7459855
  simp only [CollatzResearch.WordTrace]
  refine ⟨272083264389226851647461019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181388842926151234431640679 272083264389226851647461019)
  ·
    refine ⟨408124896583840277471191529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272083264389226851647461019 408124896583840277471191529)
    ·
      refine ⟨306093672437880208103393647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408124896583840277471191529 306093672437880208103393647)
      ·
        refine ⟨459140508656820312155090471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306093672437880208103393647 459140508656820312155090471)
        ·
          refine ⟨688710762985230468232635707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459140508656820312155090471 688710762985230468232635707)
          ·
            refine ⟨1033066144477845702348953561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 688710762985230468232635707 1033066144477845702348953561)
            ·
              refine ⟨774799608358384276761715171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1033066144477845702348953561 774799608358384276761715171)
              ·
                refine ⟨1162199412537576415142572757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 774799608358384276761715171 1162199412537576415142572757)
                ·
                  refine ⟨27239048731349447229904049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1162199412537576415142572757 27239048731349447229904049)
                  ·
                    refine ⟨20429286548512085422428037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27239048731349447229904049 20429286548512085422428037)
                    ·
                      refine ⟨3830491227846016016705257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20429286548512085422428037 3830491227846016016705257)
                      ·
                        rfl

theorem cell23_7459855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 2, 4].length) (baseStart_7459855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7459855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7459855 prefixEnd_7459855 := by exact prefixLift 7459855
  have htrace : WordTrace (prefixWord ++ tailWord_7459855) baseStart_7459855 baseEnd_7459855 := by
    simpa [prefixWord, tailWord_7459855, baseEnd_7459855] using wordTrace_append hprefix tailTrace_7459855
  have hstable : (prefixWord ++ tailWord_7459855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7459855).length < 2 ^ (prefixWord ++ tailWord_7459855).sum := by decide
  have hdescent : baseEnd_7459855 < baseStart_7459855 := by decide
  rcases family_descends (prefixWord ++ tailWord_7459855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7459879 : List Nat := [1, 1, 7, 1, 1, 1, 1, 3, 1, 1, 5]
def baseStart_7459879 : Nat := 118140960795 + 7459879 * 2 ^ 59
def prefixEnd_7459879 : Nat := 4983230072969 + 3 ^ 40 * 7459879 * 2
def baseEnd_7459879 : Nat := 3830503551381723922805147

theorem tailTrace_7459879 : CollatzResearch.WordTrace tailWord_7459879 prefixEnd_7459879 3830503551381723922805147 := by
  unfold tailWord_7459879
  simp only [CollatzResearch.WordTrace]
  refine ⟨272084139741139903746334691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181389426494093269164223127 272084139741139903746334691)
  ·
    refine ⟨408126209611709855619502037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272084139741139903746334691 408126209611709855619502037)
    ·
      refine ⟨9565458037774449741082079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 408126209611709855619502037 9565458037774449741082079)
      ·
        refine ⟨14348187056661674611623119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9565458037774449741082079 14348187056661674611623119)
        ·
          refine ⟨21522280584992511917434679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14348187056661674611623119 21522280584992511917434679)
          ·
            refine ⟨32283420877488767876152019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21522280584992511917434679 32283420877488767876152019)
            ·
              refine ⟨48425131316233151814228029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32283420877488767876152019 48425131316233151814228029)
              ·
                refine ⟨18159424243587431930335511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48425131316233151814228029 18159424243587431930335511)
                ·
                  refine ⟨27239136365381147895503267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18159424243587431930335511 27239136365381147895503267)
                  ·
                    refine ⟨40858704548071721843254901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27239136365381147895503267 40858704548071721843254901)
                    ·
                      refine ⟨3830503551381723922805147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40858704548071721843254901 3830503551381723922805147)
                      ·
                        rfl

theorem cell23_7459879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_7459879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7459879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7459879 prefixEnd_7459879 := by exact prefixLift 7459879
  have htrace : WordTrace (prefixWord ++ tailWord_7459879) baseStart_7459879 baseEnd_7459879 := by
    simpa [prefixWord, tailWord_7459879, baseEnd_7459879] using wordTrace_append hprefix tailTrace_7459879
  have hstable : (prefixWord ++ tailWord_7459879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7459879).length < 2 ^ (prefixWord ++ tailWord_7459879).sum := by decide
  have hdescent : baseEnd_7459879 < baseStart_7459879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7459879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7459895 : List Nat := [1, 1, 3, 1, 2, 2, 1, 3, 2, 7]
def baseStart_7459895 : Nat := 118140960795 + 7459895 * 2 ^ 59
def prefixEnd_7459895 : Nat := 4983230072969 + 3 ^ 40 * 7459895 * 2
def baseEnd_7459895 : Nat := 1276837255690731953401691

theorem tailTrace_7459895 : CollatzResearch.WordTrace tailWord_7459895 prefixEnd_7459895 1276837255690731953401691 := by
  unfold tailWord_7459895
  simp only [CollatzResearch.WordTrace]
  refine ⟨272084723309081938478917139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181389815539387958985944759 272084723309081938478917139)
  ·
    refine ⟨408127084963622907718375709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272084723309081938478917139 408127084963622907718375709)
    ·
      refine ⟨153047656861358590394390891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 408127084963622907718375709 153047656861358590394390891)
      ·
        refine ⟨229571485292037885591586337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153047656861358590394390891 229571485292037885591586337)
        ·
          refine ⟨172178613969028414193689753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229571485292037885591586337 172178613969028414193689753)
          ·
            refine ⟨129133960476771310645267315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172178613969028414193689753 129133960476771310645267315)
            ·
              refine ⟨193700940715156965967900973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129133960476771310645267315 193700940715156965967900973)
              ·
                refine ⟨72637852768183862237962865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 193700940715156965967900973 72637852768183862237962865)
                ·
                  refine ⟨54478389576137896678472149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72637852768183862237962865 54478389576137896678472149)
                  ·
                    refine ⟨1276837255690731953401691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54478389576137896678472149 1276837255690731953401691)
                    ·
                      rfl

theorem cell23_7459895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 7].length) (baseStart_7459895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7459895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7459895 prefixEnd_7459895 := by exact prefixLift 7459895
  have htrace : WordTrace (prefixWord ++ tailWord_7459895) baseStart_7459895 baseEnd_7459895 := by
    simpa [prefixWord, tailWord_7459895, baseEnd_7459895] using wordTrace_append hprefix tailTrace_7459895
  have hstable : (prefixWord ++ tailWord_7459895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7459895).length < 2 ^ (prefixWord ++ tailWord_7459895).sum := by decide
  have hdescent : baseEnd_7459895 < baseStart_7459895 := by decide
  rcases family_descends (prefixWord ++ tailWord_7459895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7459944 : List Nat := [2, 1, 4, 4, 1, 2, 2, 2, 1, 2, 2]
def baseStart_7459944 : Nat := 118140960795 + 7459944 * 2 ^ 59
def prefixEnd_7459944 : Nat := 4983230072969 + 3 ^ 40 * 7459944 * 2
def baseEnd_7459944 : Nat := 3830536927624266168492349

theorem tailTrace_7459944 : CollatzResearch.WordTrace tailWord_7459944 prefixEnd_7459944 3830536927624266168492349 := by
  unfold tailWord_7459944
  simp only [CollatzResearch.WordTrace]
  refine ⟨136043255242952209923725443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181391006990602946564967257 136043255242952209923725443)
  ·
    refine ⟨204064882864428314885588165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136043255242952209923725443 204064882864428314885588165)
    ·
      refine ⟨38262165537080309041047781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204064882864428314885588165 38262165537080309041047781)
      ·
        refine ⟨7174156038202557945196459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38262165537080309041047781 7174156038202557945196459)
        ·
          refine ⟨10761234057303836917794689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7174156038202557945196459 10761234057303836917794689)
          ·
            refine ⟨8070925542977877688346017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10761234057303836917794689 8070925542977877688346017)
            ·
              refine ⟨6053194157233408266259513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8070925542977877688346017 6053194157233408266259513)
              ·
                refine ⟨4539895617925056199694635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6053194157233408266259513 4539895617925056199694635)
                ·
                  refine ⟨6809843426887584299541953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4539895617925056199694635 6809843426887584299541953)
                  ·
                    refine ⟨5107382570165688224656465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6809843426887584299541953 5107382570165688224656465)
                    ·
                      refine ⟨3830536927624266168492349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5107382570165688224656465 3830536927624266168492349)
                      ·
                        rfl

theorem cell23_7459944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_7459944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7459944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7459944 prefixEnd_7459944 := by exact prefixLift 7459944
  have htrace : WordTrace (prefixWord ++ tailWord_7459944) baseStart_7459944 baseEnd_7459944 := by
    simpa [prefixWord, tailWord_7459944, baseEnd_7459944] using wordTrace_append hprefix tailTrace_7459944
  have hstable : (prefixWord ++ tailWord_7459944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7459944).length < 2 ^ (prefixWord ++ tailWord_7459944).sum := by decide
  have hdescent : baseEnd_7459944 < baseStart_7459944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7459944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7459952 : List Nat := [2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 3]
def baseStart_7459952 : Nat := 118140960795 + 7459952 * 2 ^ 59
def prefixEnd_7459952 : Nat := 4983230072969 + 3 ^ 40 * 7459952 * 2
def baseEnd_7459952 : Nat := 3830541035469502137192311

theorem tailTrace_7459952 : CollatzResearch.WordTrace tailWord_7459952 prefixEnd_7459952 3830541035469502137192311 := by
  unfold tailWord_7459952
  simp only [CollatzResearch.WordTrace]
  refine ⟨136043401134937718606871055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181391201513250291475828073 136043401134937718606871055)
  ·
    refine ⟨204065101702406577910306583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136043401134937718606871055 204065101702406577910306583)
    ·
      refine ⟨306097652553609866865459875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204065101702406577910306583 306097652553609866865459875)
      ·
        refine ⟨459146478830414800298189813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306097652553609866865459875 459146478830414800298189813)
        ·
          refine ⟨43044982390351387527955295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 459146478830414800298189813 43044982390351387527955295)
          ·
            refine ⟨64567473585527081291932943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43044982390351387527955295 64567473585527081291932943)
            ·
              refine ⟨96851210378290621937899415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64567473585527081291932943 96851210378290621937899415)
              ·
                refine ⟨145276815567435932906849123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96851210378290621937899415 145276815567435932906849123)
                ·
                  refine ⟨217915223351153899360273685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145276815567435932906849123 217915223351153899360273685)
                  ·
                    refine ⟨10214776094585339032512829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 217915223351153899360273685 10214776094585339032512829)
                    ·
                      refine ⟨3830541035469502137192311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10214776094585339032512829 3830541035469502137192311)
                      ·
                        rfl

theorem cell23_7459952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 3].length) (baseStart_7459952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7459952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7459952 prefixEnd_7459952 := by exact prefixLift 7459952
  have htrace : WordTrace (prefixWord ++ tailWord_7459952) baseStart_7459952 baseEnd_7459952 := by
    simpa [prefixWord, tailWord_7459952, baseEnd_7459952] using wordTrace_append hprefix tailTrace_7459952
  have hstable : (prefixWord ++ tailWord_7459952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7459952).length < 2 ^ (prefixWord ++ tailWord_7459952).sum := by decide
  have hdescent : baseEnd_7459952 < baseStart_7459952 := by decide
  rcases family_descends (prefixWord ++ tailWord_7459952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7459955 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 13]
def baseStart_7459955 : Nat := 118140960795 + 7459955 * 2 ^ 59
def prefixEnd_7459955 : Nat := 4983230072969 + 3 ^ 40 * 7459955 * 2
def baseEnd_7459955 : Nat := 425615841767940625050533

theorem tailTrace_7459955 : CollatzResearch.WordTrace tailWord_7459955 prefixEnd_7459955 425615841767940625050533 := by
  unfold tailWord_7459955
  simp only [CollatzResearch.WordTrace]
  refine ⟨272086911688864568726101319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181391274459243045817400879 272086911688864568726101319)
  ·
    refine ⟨408130367533296853089151979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272086911688864568726101319 408130367533296853089151979)
    ·
      refine ⟨612195551299945279633727969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408130367533296853089151979 612195551299945279633727969)
      ·
        refine ⟨459146663474958959725295977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 612195551299945279633727969 459146663474958959725295977)
        ·
          refine ⟨344359997606219219793971983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 459146663474958959725295977 344359997606219219793971983)
          ·
            refine ⟨516539996409328829690957975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344359997606219219793971983 516539996409328829690957975)
            ·
              refine ⟨774809994613993244536436963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 516539996409328829690957975 774809994613993244536436963)
              ·
                refine ⟨1162214991920989866804655445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 774809994613993244536436963 1162214991920989866804655445)
                ·
                  refine ⟨425615841767940625050533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 13 1162214991920989866804655445 425615841767940625050533)
                  ·
                    rfl

theorem cell23_7459955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 13].length) (baseStart_7459955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7459955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7459955 prefixEnd_7459955 := by exact prefixLift 7459955
  have htrace : WordTrace (prefixWord ++ tailWord_7459955) baseStart_7459955 baseEnd_7459955 := by
    simpa [prefixWord, tailWord_7459955, baseEnd_7459955] using wordTrace_append hprefix tailTrace_7459955
  have hstable : (prefixWord ++ tailWord_7459955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7459955).length < 2 ^ (prefixWord ++ tailWord_7459955).sum := by decide
  have hdescent : baseEnd_7459955 < baseStart_7459955 := by decide
  rcases family_descends (prefixWord ++ tailWord_7459955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7459972 : List Nat := [2, 3, 2, 1, 2, 2, 1, 1, 9]
def baseStart_7459972 : Nat := 118140960795 + 7459972 * 2 ^ 59
def prefixEnd_7459972 : Nat := 4983230072969 + 3 ^ 40 * 7459972 * 2
def baseEnd_7459972 : Nat := 425616811675843562104691

theorem tailTrace_7459972 : CollatzResearch.WordTrace tailWord_7459972 prefixEnd_7459972 425616811675843562104691 := by
  unfold tailWord_7459972
  simp only [CollatzResearch.WordTrace]
  refine ⟨136043765864901490314735085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181391687819868653752980113 136043765864901490314735085)
  ·
    refine ⟨51016412199338058868025657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136043765864901490314735085 51016412199338058868025657)
    ·
      refine ⟨38262309149503544151019243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51016412199338058868025657 38262309149503544151019243)
      ·
        refine ⟨57393463724255316226528865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38262309149503544151019243 57393463724255316226528865)
        ·
          refine ⟨43045097793191487169896649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57393463724255316226528865 43045097793191487169896649)
          ·
            refine ⟨32283823344893615377422487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43045097793191487169896649 32283823344893615377422487)
            ·
              refine ⟨48425735017340423066133731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32283823344893615377422487 48425735017340423066133731)
              ·
                refine ⟨72638602526010634599200597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48425735017340423066133731 72638602526010634599200597)
                ·
                  refine ⟨425616811675843562104691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 72638602526010634599200597 425616811675843562104691)
                  ·
                    rfl

theorem cell23_7459972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 9].length) (baseStart_7459972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7459972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7459972 prefixEnd_7459972 := by exact prefixLift 7459972
  have htrace : WordTrace (prefixWord ++ tailWord_7459972) baseStart_7459972 baseEnd_7459972 := by
    simpa [prefixWord, tailWord_7459972, baseEnd_7459972] using wordTrace_append hprefix tailTrace_7459972
  have hstable : (prefixWord ++ tailWord_7459972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7459972).length < 2 ^ (prefixWord ++ tailWord_7459972).sum := by decide
  have hdescent : baseEnd_7459972 < baseStart_7459972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7459972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7460039 : List Nat := [1, 1, 4, 1, 1, 1, 1, 4, 1, 6, 2]
def baseStart_7460039 : Nat := 118140960795 + 7460039 * 2 ^ 59
def prefixEnd_7460039 : Nat := 4983230072969 + 3 ^ 40 * 7460039 * 2
def baseEnd_7460039 : Nat := 3830585708286443296804411

theorem tailTrace_7460039 : CollatzResearch.WordTrace tailWord_7460039 prefixEnd_7460039 3830585708286443296804411 := by
  unfold tailWord_7460039
  simp only [CollatzResearch.WordTrace]
  refine ⟨272089975420560251072159171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181393316947040167381439447 272089975420560251072159171)
  ·
    refine ⟨408134963130840376608238757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272089975420560251072159171 408134963130840376608238757)
    ·
      refine ⟨76525305587032570614044767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 408134963130840376608238757 76525305587032570614044767)
      ·
        refine ⟨114787958380548855921067151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76525305587032570614044767 114787958380548855921067151)
        ·
          refine ⟨172181937570823283881600727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114787958380548855921067151 172181937570823283881600727)
          ·
            refine ⟨258272906356234925822401091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172181937570823283881600727 258272906356234925822401091)
            ·
              refine ⟨387409359534352388733601637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258272906356234925822401091 387409359534352388733601637)
              ·
                refine ⟨72639254912691072887550307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 387409359534352388733601637 72639254912691072887550307)
                ·
                  refine ⟨108958882369036609331325461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72639254912691072887550307 108958882369036609331325461)
                  ·
                    refine ⟨5107447611048591062405881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 108958882369036609331325461 5107447611048591062405881)
                    ·
                      refine ⟨3830585708286443296804411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5107447611048591062405881 3830585708286443296804411)
                      ·
                        rfl

theorem cell23_7460039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 6, 2].length) (baseStart_7460039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7460039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7460039 prefixEnd_7460039 := by exact prefixLift 7460039
  have htrace : WordTrace (prefixWord ++ tailWord_7460039) baseStart_7460039 baseEnd_7460039 := by
    simpa [prefixWord, tailWord_7460039, baseEnd_7460039] using wordTrace_append hprefix tailTrace_7460039
  have hstable : (prefixWord ++ tailWord_7460039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7460039).length < 2 ^ (prefixWord ++ tailWord_7460039).sum := by decide
  have hdescent : baseEnd_7460039 < baseStart_7460039 := by decide
  rcases family_descends (prefixWord ++ tailWord_7460039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7460056 : List Nat := [2, 1, 2, 2, 5, 1, 1, 2, 2, 1, 4]
def baseStart_7460056 : Nat := 118140960795 + 7460056 * 2 ^ 59
def prefixEnd_7460056 : Nat := 4983230072969 + 3 ^ 40 * 7460056 * 2
def baseEnd_7460056 : Nat := 3830594437457569730291833

theorem tailTrace_7460056 : CollatzResearch.WordTrace tailWord_7460056 prefixEnd_7460056 3830594437457569730291833 := by
  unfold tailWord_7460056
  simp only [CollatzResearch.WordTrace]
  refine ⟨136045297730749331487764011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181393730307665775317018681 136045297730749331487764011)
  ·
    refine ⟨204067946596123997231646017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136045297730749331487764011 204067946596123997231646017)
    ·
      refine ⟨153050959947092997923734513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204067946596123997231646017 153050959947092997923734513)
      ·
        refine ⟨114788219960319748442800885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153050959947092997923734513 114788219960319748442800885)
        ·
          refine ⟨10761395621279976416512583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 114788219960319748442800885 10761395621279976416512583)
          ·
            refine ⟨16142093431919964624768875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10761395621279976416512583 16142093431919964624768875)
            ·
              refine ⟨24213140147879946937153313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16142093431919964624768875 24213140147879946937153313)
              ·
                refine ⟨18159855110909960202864985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24213140147879946937153313 18159855110909960202864985)
                ·
                  refine ⟨13619891333182470152148739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18159855110909960202864985 13619891333182470152148739)
                  ·
                    refine ⟨20429836999773705228223109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13619891333182470152148739 20429836999773705228223109)
                    ·
                      refine ⟨3830594437457569730291833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20429836999773705228223109 3830594437457569730291833)
                      ·
                        rfl

theorem cell23_7460056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 2, 1, 4].length) (baseStart_7460056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7460056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7460056 prefixEnd_7460056 := by exact prefixLift 7460056
  have htrace : WordTrace (prefixWord ++ tailWord_7460056) baseStart_7460056 baseEnd_7460056 := by
    simpa [prefixWord, tailWord_7460056, baseEnd_7460056] using wordTrace_append hprefix tailTrace_7460056
  have hstable : (prefixWord ++ tailWord_7460056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7460056).length < 2 ^ (prefixWord ++ tailWord_7460056).sum := by decide
  have hdescent : baseEnd_7460056 < baseStart_7460056 := by decide
  rcases family_descends (prefixWord ++ tailWord_7460056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7460146 : List Nat := [3, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4]
def baseStart_7460146 : Nat := 118140960795 + 7460146 * 2 ^ 59
def prefixEnd_7460146 : Nat := 4983230072969 + 3 ^ 40 * 7460146 * 2
def baseEnd_7460146 : Nat := 3830640650716474378166419

theorem tailTrace_7460146 : CollatzResearch.WordTrace tailWord_7460146 prefixEnd_7460146 3830640650716474378166419 := by
  unfold tailWord_7460146
  simp only [CollatzResearch.WordTrace]
  refine ⟨68023469507793152086576073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181395918687448405564202861 68023469507793152086576073)
  ·
    refine ⟨51017602130844864064932055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68023469507793152086576073 51017602130844864064932055)
    ·
      refine ⟨76526403196267296097398083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51017602130844864064932055 76526403196267296097398083)
      ·
        refine ⟨114789604794400944146097125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76526403196267296097398083 114789604794400944146097125)
        ·
          refine ⟨21523050898950177027393211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114789604794400944146097125 21523050898950177027393211)
          ·
            refine ⟨32284576348425265541089817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21523050898950177027393211 32284576348425265541089817)
            ·
              refine ⟨24213432261318949155817363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32284576348425265541089817 24213432261318949155817363)
              ·
                refine ⟨36320148391978423733726045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24213432261318949155817363 36320148391978423733726045)
                ·
                  refine ⟨13620055646991908900147267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36320148391978423733726045 13620055646991908900147267)
                  ·
                    refine ⟨20430083470487863350220901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13620055646991908900147267 20430083470487863350220901)
                    ·
                      refine ⟨3830640650716474378166419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20430083470487863350220901 3830640650716474378166419)
                      ·
                        rfl

theorem cell23_7460146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_7460146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7460146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7460146 prefixEnd_7460146 := by exact prefixLift 7460146
  have htrace : WordTrace (prefixWord ++ tailWord_7460146) baseStart_7460146 baseEnd_7460146 := by
    simpa [prefixWord, tailWord_7460146, baseEnd_7460146] using wordTrace_append hprefix tailTrace_7460146
  have hstable : (prefixWord ++ tailWord_7460146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7460146).length < 2 ^ (prefixWord ++ tailWord_7460146).sum := by decide
  have hdescent : baseEnd_7460146 < baseStart_7460146 := by decide
  rcases family_descends (prefixWord ++ tailWord_7460146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7460180 : List Nat := [2, 4, 1, 1, 2, 1, 4, 1, 3, 2, 2]
def baseStart_7460180 : Nat := 118140960795 + 7460180 * 2 ^ 59
def prefixEnd_7460180 : Nat := 4983230072969 + 3 ^ 40 * 7460180 * 2
def baseEnd_7460180 : Nat := 3830658109058727245141263

theorem tailTrace_7460180 : CollatzResearch.WordTrace tailWord_7460180 prefixEnd_7460180 3830658109058727245141263 := by
  unfold tailWord_7460180
  simp only [CollatzResearch.WordTrace]
  refine ⟨136047559056524716076520997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181396745408699621435361329 136047559056524716076520997)
  ·
    refine ⟨25508917323098384264347687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136047559056524716076520997 25508917323098384264347687)
    ·
      refine ⟨38263375984647576396521531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25508917323098384264347687 38263375984647576396521531)
      ·
        refine ⟨57395063976971364594782297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38263375984647576396521531 57395063976971364594782297)
        ·
          refine ⟨43046297982728523446086723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57395063976971364594782297 43046297982728523446086723)
          ·
            refine ⟨64569446974092785169130085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43046297982728523446086723 64569446974092785169130085)
            ·
              refine ⟨12106771307642397219211891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64569446974092785169130085 12106771307642397219211891)
              ·
                refine ⟨18160156961463595828817837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12106771307642397219211891 18160156961463595828817837)
                ·
                  refine ⟨6810058860548848435806689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18160156961463595828817837 6810058860548848435806689)
                  ·
                    refine ⟨5107544145411636326855017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6810058860548848435806689 5107544145411636326855017)
                    ·
                      refine ⟨3830658109058727245141263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5107544145411636326855017 3830658109058727245141263)
                      ·
                        rfl

theorem cell23_7460180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 3, 2, 2].length) (baseStart_7460180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7460180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7460180 prefixEnd_7460180 := by exact prefixLift 7460180
  have htrace : WordTrace (prefixWord ++ tailWord_7460180) baseStart_7460180 baseEnd_7460180 := by
    simpa [prefixWord, tailWord_7460180, baseEnd_7460180] using wordTrace_append hprefix tailTrace_7460180
  have hstable : (prefixWord ++ tailWord_7460180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7460180).length < 2 ^ (prefixWord ++ tailWord_7460180).sum := by decide
  have hdescent : baseEnd_7460180 < baseStart_7460180 := by decide
  rcases family_descends (prefixWord ++ tailWord_7460180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7460200 : List Nat := [2, 1, 4, 2, 3, 1, 2, 2, 1, 2, 3]
def baseStart_7460200 : Nat := 118140960795 + 7460200 * 2 ^ 59
def prefixEnd_7460200 : Nat := 4983230072969 + 3 ^ 40 * 7460200 * 2
def baseEnd_7460200 : Nat := 3830668378671817166891171

theorem tailTrace_7460200 : CollatzResearch.WordTrace tailWord_7460200 prefixEnd_7460200 3830668378671817166891171 := by
  unfold tailWord_7460200
  simp only [CollatzResearch.WordTrace]
  refine ⟨136047923786488487784385027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181397231715317983712513369 136047923786488487784385027)
  ·
    refine ⟨204071885679732731676577541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136047923786488487784385027 204071885679732731676577541)
    ·
      refine ⟨38263478564949887189358289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204071885679732731676577541 38263478564949887189358289)
      ·
        refine ⟨28697608923712415392018717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38263478564949887189358289 28697608923712415392018717)
        ·
          refine ⟨10761603346392155772007019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28697608923712415392018717 10761603346392155772007019)
          ·
            refine ⟨16142405019588233658010529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10761603346392155772007019 16142405019588233658010529)
            ·
              refine ⟨12106803764691175243507897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16142405019588233658010529 12106803764691175243507897)
              ·
                refine ⟨9080102823518381432630923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12106803764691175243507897 9080102823518381432630923)
                ·
                  refine ⟨13620154235277572148946385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9080102823518381432630923 13620154235277572148946385)
                  ·
                    refine ⟨10215115676458179111709789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13620154235277572148946385 10215115676458179111709789)
                    ·
                      refine ⟨3830668378671817166891171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10215115676458179111709789 3830668378671817166891171)
                      ·
                        rfl

theorem cell23_7460200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_7460200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7460200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7460200 prefixEnd_7460200 := by exact prefixLift 7460200
  have htrace : WordTrace (prefixWord ++ tailWord_7460200) baseStart_7460200 baseEnd_7460200 := by
    simpa [prefixWord, tailWord_7460200, baseEnd_7460200] using wordTrace_append hprefix tailTrace_7460200
  have hstable : (prefixWord ++ tailWord_7460200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7460200).length < 2 ^ (prefixWord ++ tailWord_7460200).sum := by decide
  have hdescent : baseEnd_7460200 < baseStart_7460200 := by decide
  rcases family_descends (prefixWord ++ tailWord_7460200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7460209 : List Nat := [1, 2, 2, 2, 1, 2, 3, 1, 2, 2, 5]
def baseStart_7460209 : Nat := 118140960795 + 7460209 * 2 ^ 59
def prefixEnd_7460209 : Nat := 4983230072969 + 3 ^ 40 * 7460209 * 2
def baseEnd_7460209 : Nat := 3830672999997707631678629

theorem tailTrace_7460209 : CollatzResearch.WordTrace tailWord_7460209 prefixEnd_7460209 3830672999997707631678629 := by
  unfold tailWord_7460209
  simp only [CollatzResearch.WordTrace]
  refine ⟨272096175829944370105847681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181397450553296246737231787 272096175829944370105847681)
  ·
    refine ⟨204072131872458277579385761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272096175829944370105847681 204072131872458277579385761)
    ·
      refine ⟨153054098904343708184539321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204072131872458277579385761 153054098904343708184539321)
      ·
        refine ⟨114790574178257781138404491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153054098904343708184539321 114790574178257781138404491)
        ·
          refine ⟨172185861267386671707606737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114790574178257781138404491 172185861267386671707606737)
          ·
            refine ⟨129139395950540003780705053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172185861267386671707606737 129139395950540003780705053)
            ·
              refine ⟨48427273481452501417764395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129139395950540003780705053 48427273481452501417764395)
              ·
                refine ⟨72640910222178752126646593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48427273481452501417764395 72640910222178752126646593)
                ·
                  refine ⟨54480682666634064094984945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72640910222178752126646593 54480682666634064094984945)
                  ·
                    refine ⟨40860511999975548071238709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54480682666634064094984945 40860511999975548071238709)
                    ·
                      refine ⟨3830672999997707631678629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40860511999975548071238709 3830672999997707631678629)
                      ·
                        rfl

theorem cell23_7460209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_7460209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7460209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7460209 prefixEnd_7460209 := by exact prefixLift 7460209
  have htrace : WordTrace (prefixWord ++ tailWord_7460209) baseStart_7460209 baseEnd_7460209 := by
    simpa [prefixWord, tailWord_7460209, baseEnd_7460209] using wordTrace_append hprefix tailTrace_7460209
  have hstable : (prefixWord ++ tailWord_7460209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7460209).length < 2 ^ (prefixWord ++ tailWord_7460209).sum := by decide
  have hdescent : baseEnd_7460209 < baseStart_7460209 := by decide
  rcases family_descends (prefixWord ++ tailWord_7460209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7460229 : List Nat := [1, 3, 1, 1, 3, 1, 2, 1, 4, 6]
def baseStart_7460229 : Nat := 118140960795 + 7460229 * 2 ^ 59
def prefixEnd_7460229 : Nat := 4983230072969 + 3 ^ 40 * 7460229 * 2
def baseEnd_7460229 : Nat := 1276894423203599184476179

theorem tailTrace_7460229 : CollatzResearch.WordTrace tailWord_7460229 prefixEnd_7460229 1276894423203599184476179 := by
  unfold tailWord_7460229
  simp only [CollatzResearch.WordTrace]
  refine ⟨272096905289871913521575741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181397936859914609014383827 272096905289871913521575741)
  ·
    refine ⟨102036339483701967570590903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272096905289871913521575741 102036339483701967570590903)
    ·
      refine ⟨153054509225552951355886355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102036339483701967570590903 153054509225552951355886355)
      ·
        refine ⟨229581763838329427033829533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153054509225552951355886355 229581763838329427033829533)
        ·
          refine ⟨86093161439373535137686075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229581763838329427033829533 86093161439373535137686075)
          ·
            refine ⟨129139742159060302706529113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86093161439373535137686075 129139742159060302706529113)
            ·
              refine ⟨96854806619295227029896835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129139742159060302706529113 96854806619295227029896835)
              ·
                refine ⟨145282209928942840544845253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96854806619295227029896835 145282209928942840544845253)
                ·
                  refine ⟨27240414361676782602158485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145282209928942840544845253 27240414361676782602158485)
                  ·
                    refine ⟨1276894423203599184476179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27240414361676782602158485 1276894423203599184476179)
                    ·
                      rfl

theorem cell23_7460229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 6].length) (baseStart_7460229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7460229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7460229 prefixEnd_7460229 := by exact prefixLift 7460229
  have htrace : WordTrace (prefixWord ++ tailWord_7460229) baseStart_7460229 baseEnd_7460229 := by
    simpa [prefixWord, tailWord_7460229, baseEnd_7460229] using wordTrace_append hprefix tailTrace_7460229
  have hstable : (prefixWord ++ tailWord_7460229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7460229).length < 2 ^ (prefixWord ++ tailWord_7460229).sum := by decide
  have hdescent : baseEnd_7460229 < baseStart_7460229 := by decide
  rcases family_descends (prefixWord ++ tailWord_7460229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7460259 : List Nat := [1, 1, 1, 4, 1, 3, 2, 1, 9]
def baseStart_7460259 : Nat := 118140960795 + 7460259 * 2 ^ 59
def prefixEnd_7460259 : Nat := 4983230072969 + 3 ^ 40 * 7460259 * 2
def baseEnd_7460259 : Nat := 425633186003381381783711

theorem tailTrace_7460259 : CollatzResearch.WordTrace tailWord_7460259 prefixEnd_7460259 425633186003381381783711 := by
  unfold tailWord_7460259
  simp only [CollatzResearch.WordTrace]
  refine ⟨272097999479763228645167831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181398666319842152430111887 272097999479763228645167831)
  ·
    refine ⟨408146999219644842967751747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272097999479763228645167831 408146999219644842967751747)
    ·
      refine ⟨612220498829467264451627621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408146999219644842967751747 612220498829467264451627621)
      ·
        refine ⟨114791343530525112084680179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 612220498829467264451627621 114791343530525112084680179)
        ·
          refine ⟨172187015295787668127020269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114791343530525112084680179 172187015295787668127020269)
          ·
            refine ⟨64570130735920375547632601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172187015295787668127020269 64570130735920375547632601)
            ·
              refine ⟨48427598051940281660724451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64570130735920375547632601 48427598051940281660724451)
              ·
                refine ⟨72641397077910422491086677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48427598051940281660724451 72641397077910422491086677)
                ·
                  refine ⟨425633186003381381783711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 72641397077910422491086677 425633186003381381783711)
                  ·
                    rfl

theorem cell23_7460259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 9].length) (baseStart_7460259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7460259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7460259 prefixEnd_7460259 := by exact prefixLift 7460259
  have htrace : WordTrace (prefixWord ++ tailWord_7460259) baseStart_7460259 baseEnd_7460259 := by
    simpa [prefixWord, tailWord_7460259, baseEnd_7460259] using wordTrace_append hprefix tailTrace_7460259
  have hstable : (prefixWord ++ tailWord_7460259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7460259).length < 2 ^ (prefixWord ++ tailWord_7460259).sum := by decide
  have hdescent : baseEnd_7460259 < baseStart_7460259 := by decide
  rcases family_descends (prefixWord ++ tailWord_7460259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7460323 : List Nat := [1, 1, 1, 6, 2, 1, 3, 1, 2, 5]
def baseStart_7460323 : Nat := 118140960795 + 7460323 * 2 ^ 59
def prefixEnd_7460323 : Nat := 4983230072969 + 3 ^ 40 * 7460323 * 2
def baseEnd_7460323 : Nat := 1276910512264106728551035

theorem tailTrace_7460323 : CollatzResearch.WordTrace tailWord_7460323 prefixEnd_7460323 1276910512264106728551035 := by
  unfold tailWord_7460323
  simp only [CollatzResearch.WordTrace]
  refine ⟨272100333751531367575497623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181400222501020911716998415 272100333751531367575497623)
  ·
    refine ⟨408150500627297051363246435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272100333751531367575497623 408150500627297051363246435)
    ·
      refine ⟨612225750940945577044869653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408150500627297051363246435 612225750940945577044869653)
      ·
        refine ⟨28698082075356823923978265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 612225750940945577044869653 28698082075356823923978265)
        ·
          refine ⟨21523561556517617942983699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28698082075356823923978265 21523561556517617942983699)
          ·
            refine ⟨32285342334776426914475549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21523561556517617942983699 32285342334776426914475549)
            ·
              refine ⟨12107003375541160092928331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32285342334776426914475549 12107003375541160092928331)
              ·
                refine ⟨18160505063311740139392497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12107003375541160092928331 18160505063311740139392497)
                ·
                  refine ⟨13620378797483805104544373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18160505063311740139392497 13620378797483805104544373)
                  ·
                    refine ⟨1276910512264106728551035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13620378797483805104544373 1276910512264106728551035)
                    ·
                      rfl

theorem cell23_7460323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 2, 5].length) (baseStart_7460323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7460323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7460323 prefixEnd_7460323 := by exact prefixLift 7460323
  have htrace : WordTrace (prefixWord ++ tailWord_7460323) baseStart_7460323 baseEnd_7460323 := by
    simpa [prefixWord, tailWord_7460323, baseEnd_7460323] using wordTrace_append hprefix tailTrace_7460323
  have hstable : (prefixWord ++ tailWord_7460323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7460323).length < 2 ^ (prefixWord ++ tailWord_7460323).sum := by decide
  have hdescent : baseEnd_7460323 < baseStart_7460323 := by decide
  rcases family_descends (prefixWord ++ tailWord_7460323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7460396 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 7, 5]
def baseStart_7460396 : Nat := 118140960795 + 7460396 * 2 ^ 59
def prefixEnd_7460396 : Nat := 4983230072969 + 3 ^ 40 * 7460396 * 2
def baseEnd_7460396 : Nat := 1276923006960032800013423

theorem tailTrace_7460396 : CollatzResearch.WordTrace tailWord_7460396 prefixEnd_7460396 1276923006960032800013423 := by
  unfold tailWord_7460396
  simp only [CollatzResearch.WordTrace]
  refine ⟨136051498140133450521452521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181401997520177934028603361 136051498140133450521452521)
  ·
    refine ⟨102038623605100087891089391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136051498140133450521452521 102038623605100087891089391)
    ·
      refine ⟨153057935407650131836634087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102038623605100087891089391 153057935407650131836634087)
      ·
        refine ⟨229586903111475197754951131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153057935407650131836634087 229586903111475197754951131)
        ·
          refine ⟨344380354667212796632426697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229586903111475197754951131 344380354667212796632426697)
          ·
            refine ⟨258285266000409597474320023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 344380354667212796632426697 258285266000409597474320023)
            ·
              refine ⟨387427899000614396211480035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258285266000409597474320023 387427899000614396211480035)
              ·
                refine ⟨581141848500921594317220053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 387427899000614396211480035 581141848500921594317220053)
                ·
                  refine ⟨13620512074240349866809845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 581141848500921594317220053 13620512074240349866809845)
                  ·
                    refine ⟨1276923006960032800013423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13620512074240349866809845 1276923006960032800013423)
                    ·
                      rfl

theorem cell23_7460396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 5].length) (baseStart_7460396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7460396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7460396 prefixEnd_7460396 := by exact prefixLift 7460396
  have htrace : WordTrace (prefixWord ++ tailWord_7460396) baseStart_7460396 baseEnd_7460396 := by
    simpa [prefixWord, tailWord_7460396, baseEnd_7460396] using wordTrace_append hprefix tailTrace_7460396
  have hstable : (prefixWord ++ tailWord_7460396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7460396).length < 2 ^ (prefixWord ++ tailWord_7460396).sum := by decide
  have hdescent : baseEnd_7460396 < baseStart_7460396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7460396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7460416 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 4]
def baseStart_7460416 : Nat := 118140960795 + 7460416 * 2 ^ 59
def prefixEnd_7460416 : Nat := 4983230072969 + 3 ^ 40 * 7460416 * 2
def baseEnd_7460416 : Nat := 3830779290493188321790177

theorem tailTrace_7460416 : CollatzResearch.WordTrace tailWord_7460416 prefixEnd_7460416 3830779290493188321790177 := by
  unfold tailWord_7460416
  simp only [CollatzResearch.WordTrace]
  refine ⟨136051862870097222229316551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181402483826796296305755401 136051862870097222229316551)
  ·
    refine ⟨204077794305145833343974827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136051862870097222229316551 204077794305145833343974827)
    ·
      refine ⟨306116691457718750015962241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204077794305145833343974827 306116691457718750015962241)
      ·
        refine ⟨229587518593289062511971681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306116691457718750015962241 229587518593289062511971681)
        ·
          refine ⟨172190638944966796883978761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229587518593289062511971681 172190638944966796883978761)
          ·
            refine ⟨129142979208725097662984071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172190638944966796883978761 129142979208725097662984071)
            ·
              refine ⟨193714468813087646494476107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129142979208725097662984071 193714468813087646494476107)
              ·
                refine ⟨290571703219631469741714161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193714468813087646494476107 290571703219631469741714161)
                ·
                  refine ⟨217928777414723602306285621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 290571703219631469741714161 217928777414723602306285621)
                  ·
                    refine ⟨20430822882630337716214277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 217928777414723602306285621 20430822882630337716214277)
                    ·
                      refine ⟨3830779290493188321790177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20430822882630337716214277 3830779290493188321790177)
                      ·
                        rfl

theorem cell23_7460416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 4].length) (baseStart_7460416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7460416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7460416 prefixEnd_7460416 := by exact prefixLift 7460416
  have htrace : WordTrace (prefixWord ++ tailWord_7460416) baseStart_7460416 baseEnd_7460416 := by
    simpa [prefixWord, tailWord_7460416, baseEnd_7460416] using wordTrace_append hprefix tailTrace_7460416
  have hstable : (prefixWord ++ tailWord_7460416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7460416).length < 2 ^ (prefixWord ++ tailWord_7460416).sum := by decide
  have hdescent : baseEnd_7460416 < baseStart_7460416 := by decide
  rcases family_descends (prefixWord ++ tailWord_7460416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7460433 : List Nat := [1, 2, 2, 1, 3, 2, 3, 1, 3, 1, 4]
def baseStart_7460433 : Nat := 118140960795 + 7460433 * 2 ^ 59
def prefixEnd_7460433 : Nat := 4983230072969 + 3 ^ 40 * 7460433 * 2
def baseEnd_7460433 : Nat := 3830788019664314755277599

theorem tailTrace_7460433 : CollatzResearch.WordTrace tailWord_7460433 prefixEnd_7460433 3830788019664314755277599 := by
  unfold tailWord_7460433
  simp only [CollatzResearch.WordTrace]
  refine ⟨272104345781132856362001953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181402897187421904241334635 272104345781132856362001953)
  ·
    refine ⟨204078259335849642271501465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272104345781132856362001953 204078259335849642271501465)
    ·
      refine ⟨153058694501887231703626099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204078259335849642271501465 153058694501887231703626099)
      ·
        refine ⟨229588041752830847555439149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153058694501887231703626099 229588041752830847555439149)
        ·
          refine ⟨86095515657311567833289681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229588041752830847555439149 86095515657311567833289681)
          ·
            refine ⟨64571636742983675874967261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86095515657311567833289681 64571636742983675874967261)
            ·
              refine ⟨24214363778618878453112723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64571636742983675874967261 24214363778618878453112723)
              ·
                refine ⟨36321545667928317679669085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24214363778618878453112723 36321545667928317679669085)
                ·
                  refine ⟨13620579625473119129875907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36321545667928317679669085 13620579625473119129875907)
                  ·
                    refine ⟨20430869438209678694813861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13620579625473119129875907 20430869438209678694813861)
                    ·
                      refine ⟨3830788019664314755277599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20430869438209678694813861 3830788019664314755277599)
                      ·
                        rfl

theorem cell23_7460433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 3, 1, 4].length) (baseStart_7460433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7460433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7460433 prefixEnd_7460433 := by exact prefixLift 7460433
  have htrace : WordTrace (prefixWord ++ tailWord_7460433) baseStart_7460433 baseEnd_7460433 := by
    simpa [prefixWord, tailWord_7460433, baseEnd_7460433] using wordTrace_append hprefix tailTrace_7460433
  have hstable : (prefixWord ++ tailWord_7460433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7460433).length < 2 ^ (prefixWord ++ tailWord_7460433).sum := by decide
  have hdescent : baseEnd_7460433 < baseStart_7460433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7460433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7460484 : List Nat := [2, 3, 2, 1, 4, 1, 1, 2, 3, 2, 2]
def baseStart_7460484 : Nat := 118140960795 + 7460484 * 2 ^ 59
def prefixEnd_7460484 : Nat := 4983230072969 + 3 ^ 40 * 7460484 * 2
def baseEnd_7460484 : Nat := 3830814207177694055739865

theorem tailTrace_7460484 : CollatzResearch.WordTrace tailWord_7460484 prefixEnd_7460484 3830814207177694055739865 := by
  unfold tailWord_7460484
  simp only [CollatzResearch.WordTrace]
  refine ⟨136053102951974046036054253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181404137269298728048072337 136053102951974046036054253)
  ·
    refine ⟨51019913606990267263520345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136053102951974046036054253 51019913606990267263520345)
    ·
      refine ⟨38264935205242700447640259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51019913606990267263520345 38264935205242700447640259)
      ·
        refine ⟨57397402807864050671460389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38264935205242700447640259 57397402807864050671460389)
        ·
          refine ⟨10762013026474509500898823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57397402807864050671460389 10762013026474509500898823)
          ·
            refine ⟨16143019539711764251348235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10762013026474509500898823 16143019539711764251348235)
            ·
              refine ⟨24214529309567646377022353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16143019539711764251348235 24214529309567646377022353)
              ·
                refine ⟨18160896982175734782766765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24214529309567646377022353 18160896982175734782766765)
                ·
                  refine ⟨6810336368315900543537537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18160896982175734782766765 6810336368315900543537537)
                  ·
                    refine ⟨5107752276236925407653153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6810336368315900543537537 5107752276236925407653153)
                    ·
                      refine ⟨3830814207177694055739865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5107752276236925407653153 3830814207177694055739865)
                      ·
                        rfl

theorem cell23_7460484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 3, 2, 2].length) (baseStart_7460484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7460484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7460484 prefixEnd_7460484 := by exact prefixLift 7460484
  have htrace : WordTrace (prefixWord ++ tailWord_7460484) baseStart_7460484 baseEnd_7460484 := by
    simpa [prefixWord, tailWord_7460484, baseEnd_7460484] using wordTrace_append hprefix tailTrace_7460484
  have hstable : (prefixWord ++ tailWord_7460484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7460484).length < 2 ^ (prefixWord ++ tailWord_7460484).sum := by decide
  have hdescent : baseEnd_7460484 < baseStart_7460484 := by decide
  rcases family_descends (prefixWord ++ tailWord_7460484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7460490 : List Nat := [3, 1, 2, 3, 2, 2, 3, 7]
def baseStart_7460490 : Nat := 118140960795 + 7460490 * 2 ^ 59
def prefixEnd_7460490 : Nat := 4983230072969 + 3 ^ 40 * 7460490 * 2
def baseEnd_7460490 : Nat := 141882121780060038232031

theorem tailTrace_7460490 : CollatzResearch.WordTrace tailWord_7460490 prefixEnd_7460490 141882121780060038232031 := by
  unfold tailWord_7460490
  simp only [CollatzResearch.WordTrace]
  refine ⟨68026606185481588774206731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181404283161284236731217949 68026606185481588774206731)
  ·
    refine ⟨102039909278222383161310097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68026606185481588774206731 102039909278222383161310097)
    ·
      refine ⟨76529931958666787370982573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102039909278222383161310097 76529931958666787370982573)
      ·
        refine ⟨28698724484500045264118465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76529931958666787370982573 28698724484500045264118465)
        ·
          refine ⟨21524043363375033948088849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28698724484500045264118465 21524043363375033948088849)
          ·
            refine ⟨16143032522531275461066637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21524043363375033948088849 16143032522531275461066637)
            ·
              refine ⟨6053637195949228297899989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16143032522531275461066637 6053637195949228297899989)
              ·
                refine ⟨141882121780060038232031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6053637195949228297899989 141882121780060038232031)
                ·
                  rfl

theorem cell23_7460490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 7].length) (baseStart_7460490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7460490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7460490 prefixEnd_7460490 := by exact prefixLift 7460490
  have htrace : WordTrace (prefixWord ++ tailWord_7460490) baseStart_7460490 baseEnd_7460490 := by
    simpa [prefixWord, tailWord_7460490, baseEnd_7460490] using wordTrace_append hprefix tailTrace_7460490
  have hstable : (prefixWord ++ tailWord_7460490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7460490).length < 2 ^ (prefixWord ++ tailWord_7460490).sum := by decide
  have hdescent : baseEnd_7460490 < baseStart_7460490 := by decide
  rcases family_descends (prefixWord ++ tailWord_7460490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7460504 : List Nat := [2, 1, 2, 4, 1, 4, 2, 1, 1, 2, 3]
def baseStart_7460504 : Nat := 118140960795 + 7460504 * 2 ^ 59
def prefixEnd_7460504 : Nat := 4983230072969 + 3 ^ 40 * 7460504 * 2
def baseEnd_7460504 : Nat := 3830824476790783977489773

theorem tailTrace_7460504 : CollatzResearch.WordTrace tailWord_7460504 prefixEnd_7460504 3830824476790783977489773 := by
  unfold tailWord_7460504
  simp only [CollatzResearch.WordTrace]
  refine ⟨136053467681937817743918283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181404623575917090325224377 136053467681937817743918283)
  ·
    refine ⟨204080201522906726615877425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136053467681937817743918283 204080201522906726615877425)
    ·
      refine ⟨153060151142180044961908069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204080201522906726615877425 153060151142180044961908069)
      ·
        refine ⟨28698778339158758430357763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153060151142180044961908069 28698778339158758430357763)
        ·
          refine ⟨43048167508738137645536645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28698778339158758430357763 43048167508738137645536645)
          ·
            refine ⟨8071531407888400808538121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43048167508738137645536645 8071531407888400808538121)
            ·
              refine ⟨6053648555916300606403591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8071531407888400808538121 6053648555916300606403591)
              ·
                refine ⟨9080472833874450909605387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6053648555916300606403591 9080472833874450909605387)
                ·
                  refine ⟨13620709250811676364408081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9080472833874450909605387 13620709250811676364408081)
                  ·
                    refine ⟨10215531938108757273306061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13620709250811676364408081 10215531938108757273306061)
                    ·
                      refine ⟨3830824476790783977489773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10215531938108757273306061 3830824476790783977489773)
                      ·
                        rfl

theorem cell23_7460504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_7460504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7460504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7460504 prefixEnd_7460504 := by exact prefixLift 7460504
  have htrace : WordTrace (prefixWord ++ tailWord_7460504) baseStart_7460504 baseEnd_7460504 := by
    simpa [prefixWord, tailWord_7460504, baseEnd_7460504] using wordTrace_append hprefix tailTrace_7460504
  have hstable : (prefixWord ++ tailWord_7460504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7460504).length < 2 ^ (prefixWord ++ tailWord_7460504).sum := by decide
  have hdescent : baseEnd_7460504 < baseStart_7460504 := by decide
  rcases family_descends (prefixWord ++ tailWord_7460504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7460511 : List Nat := [1, 1, 2, 7, 2, 1, 1, 2, 2, 4]
def baseStart_7460511 : Nat := 118140960795 + 7460511 * 2 ^ 59
def prefixEnd_7460511 : Nat := 4983230072969 + 3 ^ 40 * 7460511 * 2
def baseEnd_7460511 : Nat := 1276942690385121816700747

theorem tailTrace_7460511 : CollatzResearch.WordTrace tailWord_7460511 prefixEnd_7460511 1276942690385121816700747 := by
  unfold tailWord_7460511
  simp only [CollatzResearch.WordTrace]
  refine ⟨272107190674850275683341387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181404793783233517122227591 272107190674850275683341387)
  ·
    refine ⟨408160786012275413525012081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272107190674850275683341387 408160786012275413525012081)
    ·
      refine ⟨306120589509206560143759061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408160786012275413525012081 306120589509206560143759061)
      ·
        refine ⟨7174701316622028753369353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 306120589509206560143759061 7174701316622028753369353)
        ·
          refine ⟨5381025987466521565027015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7174701316622028753369353 5381025987466521565027015)
          ·
            refine ⟨8071538981199782347540523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5381025987466521565027015 8071538981199782347540523)
            ·
              refine ⟨12107308471799673521310785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8071538981199782347540523 12107308471799673521310785)
              ·
                refine ⟨9080481353849755140983089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12107308471799673521310785 9080481353849755140983089)
                ·
                  refine ⟨6810361015387316355737317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9080481353849755140983089 6810361015387316355737317)
                  ·
                    refine ⟨1276942690385121816700747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6810361015387316355737317 1276942690385121816700747)
                    ·
                      rfl

theorem cell23_7460511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 2, 2, 4].length) (baseStart_7460511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7460511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7460511 prefixEnd_7460511 := by exact prefixLift 7460511
  have htrace : WordTrace (prefixWord ++ tailWord_7460511) baseStart_7460511 baseEnd_7460511 := by
    simpa [prefixWord, tailWord_7460511, baseEnd_7460511] using wordTrace_append hprefix tailTrace_7460511
  have hstable : (prefixWord ++ tailWord_7460511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7460511).length < 2 ^ (prefixWord ++ tailWord_7460511).sum := by decide
  have hdescent : baseEnd_7460511 < baseStart_7460511 := by decide
  rcases family_descends (prefixWord ++ tailWord_7460511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7460517 : List Nat := [1, 3, 1, 2, 1, 2, 5, 2, 2, 1, 3]
def baseStart_7460517 : Nat := 118140960795 + 7460517 * 2 ^ 59
def prefixEnd_7460517 : Nat := 4983230072969 + 3 ^ 40 * 7460517 * 2
def baseEnd_7460517 : Nat := 3830831152039292426627213

theorem tailTrace_7460517 : CollatzResearch.WordTrace tailWord_7460517 prefixEnd_7460517 3830831152039292426627213 := by
  unfold tailWord_7460517
  simp only [CollatzResearch.WordTrace]
  refine ⟨272107409512828538708059805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181404939675219025805373203 272107409512828538708059805)
  ·
    refine ⟨102040278567310702015522427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272107409512828538708059805 102040278567310702015522427)
    ·
      refine ⟨153060417850966053023283641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102040278567310702015522427 153060417850966053023283641)
      ·
        refine ⟨114795313388224539767462731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153060417850966053023283641 114795313388224539767462731)
        ·
          refine ⟨172192970082336809651194097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114795313388224539767462731 172192970082336809651194097)
          ·
            refine ⟨129144727561752607238395573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172192970082336809651194097 129144727561752607238395573)
            ·
              refine ⟨12107318208914306928599585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 129144727561752607238395573 12107318208914306928599585)
              ·
                refine ⟨9080488656685730196449689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12107318208914306928599585 9080488656685730196449689)
                ·
                  refine ⟨6810366492514297647337267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9080488656685730196449689 6810366492514297647337267)
                  ·
                    refine ⟨10215549738771446471005901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6810366492514297647337267 10215549738771446471005901)
                    ·
                      refine ⟨3830831152039292426627213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10215549738771446471005901 3830831152039292426627213)
                      ·
                        rfl

theorem cell23_7460517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 2, 2, 1, 3].length) (baseStart_7460517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7460517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7460517 prefixEnd_7460517 := by exact prefixLift 7460517
  have htrace : WordTrace (prefixWord ++ tailWord_7460517) baseStart_7460517 baseEnd_7460517 := by
    simpa [prefixWord, tailWord_7460517, baseEnd_7460517] using wordTrace_append hprefix tailTrace_7460517
  have hstable : (prefixWord ++ tailWord_7460517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7460517).length < 2 ^ (prefixWord ++ tailWord_7460517).sum := by decide
  have hdescent : baseEnd_7460517 < baseStart_7460517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7460517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7460534 : List Nat := [5, 1, 3, 1, 1, 1, 3, 1, 1, 3, 3]
def baseStart_7460534 : Nat := 118140960795 + 7460534 * 2 ^ 59
def prefixEnd_7460534 : Nat := 4983230072969 + 3 ^ 40 * 7460534 * 2
def baseEnd_7460534 : Nat := 3830839881210418860114635

theorem tailTrace_7460534 : CollatzResearch.WordTrace tailWord_7460534 prefixEnd_7460534 3830839881210418860114635 := by
  unfold tailWord_7460534
  simp only [CollatzResearch.WordTrace]
  refine ⟨17006751847110434413214291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 181405353035844633740952437 17006751847110434413214291)
  ·
    refine ⟨25510127770665651619821437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17006751847110434413214291 25510127770665651619821437)
    ·
      refine ⟨9566297913999619357433039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25510127770665651619821437 9566297913999619357433039)
      ·
        refine ⟨14349446870999429036149559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9566297913999619357433039 14349446870999429036149559)
        ·
          refine ⟨21524170306499143554224339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14349446870999429036149559 21524170306499143554224339)
          ·
            refine ⟨32286255459748715331336509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21524170306499143554224339 32286255459748715331336509)
            ·
              refine ⟨12107345797405768249251191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32286255459748715331336509 12107345797405768249251191)
              ·
                refine ⟨18161018696108652373876787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12107345797405768249251191 18161018696108652373876787)
                ·
                  refine ⟨27241528044162978560815181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18161018696108652373876787 27241528044162978560815181)
                  ·
                    refine ⟨10215573016561116960305693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27241528044162978560815181 10215573016561116960305693)
                    ·
                      refine ⟨3830839881210418860114635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10215573016561116960305693 3830839881210418860114635)
                      ·
                        rfl

theorem cell23_7460534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_7460534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7460534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7460534 prefixEnd_7460534 := by exact prefixLift 7460534
  have htrace : WordTrace (prefixWord ++ tailWord_7460534) baseStart_7460534 baseEnd_7460534 := by
    simpa [prefixWord, tailWord_7460534, baseEnd_7460534] using wordTrace_append hprefix tailTrace_7460534
  have hstable : (prefixWord ++ tailWord_7460534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7460534).length < 2 ^ (prefixWord ++ tailWord_7460534).sum := by decide
  have hdescent : baseEnd_7460534 < baseStart_7460534 := by decide
  rcases family_descends (prefixWord ++ tailWord_7460534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7460543 : List Nat := [1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 5]
def baseStart_7460543 : Nat := 118140960795 + 7460543 * 2 ^ 59
def prefixEnd_7460543 : Nat := 4983230072969 + 3 ^ 40 * 7460543 * 2
def baseEnd_7460543 : Nat := 3830844502536309324902093

theorem tailTrace_7460543 : CollatzResearch.WordTrace tailWord_7460543 prefixEnd_7460543 3830844502536309324902093 := by
  unfold tailWord_7460543
  simp only [CollatzResearch.WordTrace]
  refine ⟨272108357810734345148506283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181405571873822896765670855 272108357810734345148506283)
  ·
    refine ⟨408162536716101517722759425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272108357810734345148506283 408162536716101517722759425)
    ·
      refine ⟨306121902537076138292069569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408162536716101517722759425 306121902537076138292069569)
      ·
        refine ⟨229591426902807103719052177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306121902537076138292069569 229591426902807103719052177)
        ·
          refine ⟨172193570177105327789289133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229591426902807103719052177 172193570177105327789289133)
          ·
            refine ⟨64572588816414497920983425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172193570177105327789289133 64572588816414497920983425)
            ·
              refine ⟨48429441612310873440737569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64572588816414497920983425 48429441612310873440737569)
              ·
                refine ⟨36322081209233155080553177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48429441612310873440737569 36322081209233155080553177)
                ·
                  refine ⟨27241560906924866310414883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36322081209233155080553177 27241560906924866310414883)
                  ·
                    refine ⟨40862341360387299465622325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27241560906924866310414883 40862341360387299465622325)
                    ·
                      refine ⟨3830844502536309324902093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40862341360387299465622325 3830844502536309324902093)
                      ·
                        rfl

theorem cell23_7460543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 5].length) (baseStart_7460543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7460543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7460543 prefixEnd_7460543 := by exact prefixLift 7460543
  have htrace : WordTrace (prefixWord ++ tailWord_7460543) baseStart_7460543 baseEnd_7460543 := by
    simpa [prefixWord, tailWord_7460543, baseEnd_7460543] using wordTrace_append hprefix tailTrace_7460543
  have hstable : (prefixWord ++ tailWord_7460543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7460543).length < 2 ^ (prefixWord ++ tailWord_7460543).sum := by decide
  have hdescent : baseEnd_7460543 < baseStart_7460543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7460543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7460590 : List Nat := [4, 1, 2, 1, 1, 2, 2, 1, 1, 5, 3]
def baseStart_7460590 : Nat := 118140960795 + 7460590 * 2 ^ 59
def prefixEnd_7460590 : Nat := 4983230072969 + 3 ^ 40 * 7460590 * 2
def baseEnd_7460590 : Nat := 3830868636127070641014377

theorem tailTrace_7460590 : CollatzResearch.WordTrace tailWord_7460590 prefixEnd_7460590 3830868636127070641014377 := by
  unfold tailWord_7460590
  simp only [CollatzResearch.WordTrace]
  refine ⟨34013759005195509021933403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181406714694376048116978149 34013759005195509021933403)
  ·
    refine ⟨51020638507793263532900105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34013759005195509021933403 51020638507793263532900105)
    ·
      refine ⟨38265478880844947649675079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51020638507793263532900105 38265478880844947649675079)
      ·
        refine ⟨57398218321267421474512619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38265478880844947649675079 57398218321267421474512619)
        ·
          refine ⟨86097327481901132211768929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57398218321267421474512619 86097327481901132211768929)
          ·
            refine ⟨64572995611425849158826697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86097327481901132211768929 64572995611425849158826697)
            ·
              refine ⟨48429746708569386869120023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64572995611425849158826697 48429746708569386869120023)
              ·
                refine ⟨72644620062854080303680035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48429746708569386869120023 72644620062854080303680035)
                ·
                  refine ⟨108966930094281120455520053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72644620062854080303680035 108966930094281120455520053)
                  ·
                    refine ⟨10215649696338855042705005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 108966930094281120455520053 10215649696338855042705005)
                    ·
                      refine ⟨3830868636127070641014377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10215649696338855042705005 3830868636127070641014377)
                      ·
                        rfl

theorem cell23_7460590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_7460590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7460590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7460590 prefixEnd_7460590 := by exact prefixLift 7460590
  have htrace : WordTrace (prefixWord ++ tailWord_7460590) baseStart_7460590 baseEnd_7460590 := by
    simpa [prefixWord, tailWord_7460590, baseEnd_7460590] using wordTrace_append hprefix tailTrace_7460590
  have hstable : (prefixWord ++ tailWord_7460590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7460590).length < 2 ^ (prefixWord ++ tailWord_7460590).sum := by decide
  have hdescent : baseEnd_7460590 < baseStart_7460590 := by decide
  rcases family_descends (prefixWord ++ tailWord_7460590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7460600 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 4, 5, 2]
def baseStart_7460600 : Nat := 118140960795 + 7460600 * 2 ^ 59
def prefixEnd_7460600 : Nat := 4983230072969 + 3 ^ 40 * 7460600 * 2
def baseEnd_7460600 : Nat := 3830873770933615601889331

theorem tailTrace_7460600 : CollatzResearch.WordTrace tailWord_7460600 prefixEnd_7460600 3830873770933615601889331 := by
  unfold tailWord_7460600
  simp only [CollatzResearch.WordTrace]
  refine ⟨136055218385763921941665627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181406957847685229255554169 136055218385763921941665627)
  ·
    refine ⟨204082827578645882912498441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136055218385763921941665627 204082827578645882912498441)
    ·
      refine ⟨153062120683984412184373831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204082827578645882912498441 153062120683984412184373831)
      ·
        refine ⟨229593181025976618276560747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153062120683984412184373831 229593181025976618276560747)
        ·
          refine ⟨344389771538964927414841121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229593181025976618276560747 344389771538964927414841121)
          ·
            refine ⟨258292328654223695561130841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 344389771538964927414841121 258292328654223695561130841)
            ·
              refine ⟨193719246490667771670848131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 258292328654223695561130841 193719246490667771670848131)
              ·
                refine ⟨290578869736001657506272197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193719246490667771670848131 290578869736001657506272197)
                ·
                  refine ⟨54483538075500310782426037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 290578869736001657506272197 54483538075500310782426037)
                  ·
                    refine ⟨5107831694578154135852441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54483538075500310782426037 5107831694578154135852441)
                    ·
                      refine ⟨3830873770933615601889331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5107831694578154135852441 3830873770933615601889331)
                      ·
                        rfl

theorem cell23_7460600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 4, 5, 2].length) (baseStart_7460600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7460600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7460600 prefixEnd_7460600 := by exact prefixLift 7460600
  have htrace : WordTrace (prefixWord ++ tailWord_7460600) baseStart_7460600 baseEnd_7460600 := by
    simpa [prefixWord, tailWord_7460600, baseEnd_7460600] using wordTrace_append hprefix tailTrace_7460600
  have hstable : (prefixWord ++ tailWord_7460600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7460600).length < 2 ^ (prefixWord ++ tailWord_7460600).sum := by decide
  have hdescent : baseEnd_7460600 < baseStart_7460600 := by decide
  rcases family_descends (prefixWord ++ tailWord_7460600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7460657 : List Nat := [1, 2, 2, 3, 2, 3, 1, 2, 3, 4]
def baseStart_7460657 : Nat := 118140960795 + 7460657 * 2 ^ 59
def prefixEnd_7460657 : Nat := 4983230072969 + 3 ^ 40 * 7460657 * 2
def baseEnd_7460657 : Nat := 1276967679776973959625523

theorem tailTrace_7460657 : CollatzResearch.WordTrace tailWord_7460657 prefixEnd_7460657 1276967679776973959625523 := by
  unfold tailWord_7460657
  simp only [CollatzResearch.WordTrace]
  refine ⟨272112515732321342618156225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181408343821547561745437483 272112515732321342618156225)
  ·
    refine ⟨204084386799241006963617169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272112515732321342618156225 204084386799241006963617169)
    ·
      refine ⟨153063290099430755222712877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204084386799241006963617169 153063290099430755222712877)
      ·
        refine ⟨57398733787286533208517329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153063290099430755222712877 57398733787286533208517329)
        ·
          refine ⟨43049050340464899906387997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57398733787286533208517329 43049050340464899906387997)
          ·
            refine ⟨16143393877674337464895499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43049050340464899906387997 16143393877674337464895499)
            ·
              refine ⟨24215090816511506197343249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16143393877674337464895499 24215090816511506197343249)
              ·
                refine ⟨18161318112383629648007437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24215090816511506197343249 18161318112383629648007437)
                ·
                  refine ⟨6810494292143861118002789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18161318112383629648007437 6810494292143861118002789)
                  ·
                    refine ⟨1276967679776973959625523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6810494292143861118002789 1276967679776973959625523)
                    ·
                      rfl

theorem cell23_7460657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 3, 4].length) (baseStart_7460657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7460657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7460657 prefixEnd_7460657 := by exact prefixLift 7460657
  have htrace : WordTrace (prefixWord ++ tailWord_7460657) baseStart_7460657 baseEnd_7460657 := by
    simpa [prefixWord, tailWord_7460657, baseEnd_7460657] using wordTrace_append hprefix tailTrace_7460657
  have hstable : (prefixWord ++ tailWord_7460657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7460657).length < 2 ^ (prefixWord ++ tailWord_7460657).sum := by decide
  have hdescent : baseEnd_7460657 < baseStart_7460657 := by decide
  rcases family_descends (prefixWord ++ tailWord_7460657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7460690 : List Nat := [3, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6]
def baseStart_7460690 : Nat := 118140960795 + 7460690 * 2 ^ 59
def prefixEnd_7460690 : Nat := 4983230072969 + 3 ^ 40 * 7460690 * 2
def baseEnd_7460690 : Nat := 3830919984192520249763917

theorem tailTrace_7460690 : CollatzResearch.WordTrace tailWord_7460690 prefixEnd_7460690 3830919984192520249763917 := by
  unfold tailWord_7460690
  simp only [CollatzResearch.WordTrace]
  refine ⟨68028429835300447313526881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181409146227467859502738349 68028429835300447313526881)
  ·
    refine ⟨51021322376475335485145161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68028429835300447313526881 51021322376475335485145161)
    ·
      refine ⟨38265991782356501613858871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51021322376475335485145161 38265991782356501613858871)
      ·
        refine ⟨57398987673534752420788307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38265991782356501613858871 57398987673534752420788307)
        ·
          refine ⟨86098481510302128631182461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57398987673534752420788307 86098481510302128631182461)
          ·
            refine ⟨32286930566363298236693423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86098481510302128631182461 32286930566363298236693423)
            ·
              refine ⟨48430395849544947355040135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32286930566363298236693423 48430395849544947355040135)
              ·
                refine ⟨72645593774317421032560203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48430395849544947355040135 72645593774317421032560203)
                ·
                  refine ⟨108968390661476131548840305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72645593774317421032560203 108968390661476131548840305)
                  ·
                    refine ⟨81726292996107098661630229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 108968390661476131548840305 81726292996107098661630229)
                    ·
                      refine ⟨3830919984192520249763917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81726292996107098661630229 3830919984192520249763917)
                      ·
                        rfl

theorem cell23_7460690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_7460690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7460690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7460690 prefixEnd_7460690 := by exact prefixLift 7460690
  have htrace : WordTrace (prefixWord ++ tailWord_7460690) baseStart_7460690 baseEnd_7460690 := by
    simpa [prefixWord, tailWord_7460690, baseEnd_7460690] using wordTrace_append hprefix tailTrace_7460690
  have hstable : (prefixWord ++ tailWord_7460690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7460690).length < 2 ^ (prefixWord ++ tailWord_7460690).sum := by decide
  have hdescent : baseEnd_7460690 < baseStart_7460690 := by decide
  rcases family_descends (prefixWord ++ tailWord_7460690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7460717 : List Nat := [1, 5, 1, 1, 1, 1, 3, 4, 1, 5]
def baseStart_7460717 : Nat := 118140960795 + 7460717 * 2 ^ 59
def prefixEnd_7460717 : Nat := 4983230072969 + 3 ^ 40 * 7460717 * 2
def baseEnd_7460717 : Nat := 1276977949390063881375431

theorem tailTrace_7460717 : CollatzResearch.WordTrace tailWord_7460717 prefixEnd_7460717 1276977949390063881375431 := by
  unfold tailWord_7460717
  simp only [CollatzResearch.WordTrace]
  refine ⟨272114704112103972865340405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181409802741402648576893603 272114704112103972865340405)
  ·
    refine ⟨25510753510509747456125663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 272114704112103972865340405 25510753510509747456125663)
    ·
      refine ⟨38266130265764621184188495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25510753510509747456125663 38266130265764621184188495)
      ·
        refine ⟨57399195398646931776282743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38266130265764621184188495 57399195398646931776282743)
        ·
          refine ⟨86098793097970397664424115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57399195398646931776282743 86098793097970397664424115)
          ·
            refine ⟨129148189646955596496636173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86098793097970397664424115 129148189646955596496636173)
            ·
              refine ⟨48430571117608348686238565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129148189646955596496636173 48430571117608348686238565)
              ·
                refine ⟨9080732084551565378669731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48430571117608348686238565 9080732084551565378669731)
                ·
                  refine ⟨13621098126827348068004597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9080732084551565378669731 13621098126827348068004597)
                  ·
                    refine ⟨1276977949390063881375431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13621098126827348068004597 1276977949390063881375431)
                    ·
                      rfl

theorem cell23_7460717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_7460717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7460717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7460717 prefixEnd_7460717 := by exact prefixLift 7460717
  have htrace : WordTrace (prefixWord ++ tailWord_7460717) baseStart_7460717 baseEnd_7460717 := by
    simpa [prefixWord, tailWord_7460717, baseEnd_7460717] using wordTrace_append hprefix tailTrace_7460717
  have hstable : (prefixWord ++ tailWord_7460717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7460717).length < 2 ^ (prefixWord ++ tailWord_7460717).sum := by decide
  have hdescent : baseEnd_7460717 < baseStart_7460717 := by decide
  rcases family_descends (prefixWord ++ tailWord_7460717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7460730 : List Nat := [3, 1, 1, 1, 1, 1, 4, 4, 1, 6]
def baseStart_7460730 : Nat := 118140960795 + 7460730 * 2 ^ 59
def prefixEnd_7460730 : Nat := 4983230072969 + 3 ^ 40 * 7460730 * 2
def baseEnd_7460730 : Nat := 1276980174472900031087911

theorem tailTrace_7460730 : CollatzResearch.WordTrace tailWord_7460730 prefixEnd_7460730 1276980174472900031087911 := by
  unfold tailWord_7460730
  simp only [CollatzResearch.WordTrace]
  refine ⟨68028794565264219021390911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181410118840704584057042429 68028794565264219021390911)
  ·
    refine ⟨102043191847896328532086367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68028794565264219021390911 102043191847896328532086367)
    ·
      refine ⟨153064787771844492798129551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102043191847896328532086367 153064787771844492798129551)
      ·
        refine ⟨229597181657766739197194327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153064787771844492798129551 229597181657766739197194327)
        ·
          refine ⟨344395772486650108795791491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229597181657766739197194327 344395772486650108795791491)
          ·
            refine ⟨516593658729975163193687237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344395772486650108795791491 516593658729975163193687237)
            ·
              refine ⟨96861311011870343098816357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 516593658729975163193687237 96861311011870343098816357)
              ·
                refine ⟨18161495814725689331028067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96861311011870343098816357 18161495814725689331028067)
                ·
                  refine ⟨27242243722088533996542101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18161495814725689331028067 27242243722088533996542101)
                  ·
                    refine ⟨1276980174472900031087911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27242243722088533996542101 1276980174472900031087911)
                    ·
                      rfl

theorem cell23_7460730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 1, 6].length) (baseStart_7460730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7460730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7460730 prefixEnd_7460730 := by exact prefixLift 7460730
  have htrace : WordTrace (prefixWord ++ tailWord_7460730) baseStart_7460730 baseEnd_7460730 := by
    simpa [prefixWord, tailWord_7460730, baseEnd_7460730] using wordTrace_append hprefix tailTrace_7460730
  have hstable : (prefixWord ++ tailWord_7460730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7460730).length < 2 ^ (prefixWord ++ tailWord_7460730).sum := by decide
  have hdescent : baseEnd_7460730 < baseStart_7460730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7460730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7460747 : List Nat := [1, 1, 1, 1, 4, 2, 1, 6, 2, 4]
def baseStart_7460747 : Nat := 118140960795 + 7460747 * 2 ^ 59
def prefixEnd_7460747 : Nat := 4983230072969 + 3 ^ 40 * 7460747 * 2
def baseEnd_7460747 : Nat := 1276983084196608842250385

theorem tailTrace_7460747 : CollatzResearch.WordTrace tailWord_7460747 prefixEnd_7460747 1276983084196608842250385 := by
  unfold tailWord_7460747
  simp only [CollatzResearch.WordTrace]
  refine ⟨272115798301995287988932495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181410532201330191992621663 272115798301995287988932495)
  ·
    refine ⟨408173697452992931983398743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272115798301995287988932495 408173697452992931983398743)
    ·
      refine ⟨612260546179489397975098115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408173697452992931983398743 612260546179489397975098115)
      ·
        refine ⟨918390819269234096962647173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 612260546179489397975098115 918390819269234096962647173)
        ·
          refine ⟨172198278612981393180496345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 918390819269234096962647173 172198278612981393180496345)
          ·
            refine ⟨129148708959736044885372259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172198278612981393180496345 129148708959736044885372259)
            ·
              refine ⟨193723063439604067328058389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129148708959736044885372259 193723063439604067328058389)
              ·
                refine ⟨9080768598731440656002737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 193723063439604067328058389 9080768598731440656002737)
                ·
                  refine ⟨6810576449048580492002053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9080768598731440656002737 6810576449048580492002053)
                  ·
                    refine ⟨1276983084196608842250385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6810576449048580492002053 1276983084196608842250385)
                    ·
                      rfl

theorem cell23_7460747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 6, 2, 4].length) (baseStart_7460747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7460747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7460747 prefixEnd_7460747 := by exact prefixLift 7460747
  have htrace : WordTrace (prefixWord ++ tailWord_7460747) baseStart_7460747 baseEnd_7460747 := by
    simpa [prefixWord, tailWord_7460747, baseEnd_7460747] using wordTrace_append hprefix tailTrace_7460747
  have hstable : (prefixWord ++ tailWord_7460747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7460747).length < 2 ^ (prefixWord ++ tailWord_7460747).sum := by decide
  have hdescent : baseEnd_7460747 < baseStart_7460747 := by decide
  rcases family_descends (prefixWord ++ tailWord_7460747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7460757 : List Nat := [1, 3, 2, 1, 1, 3, 2, 2, 3, 2, 3]
def baseStart_7460757 : Nat := 118140960795 + 7460757 * 2 ^ 59
def prefixEnd_7460757 : Nat := 4983230072969 + 3 ^ 40 * 7460757 * 2
def baseEnd_7460757 : Nat := 3830954387396371487626109

theorem tailTrace_7460757 : CollatzResearch.WordTrace tailWord_7460757 prefixEnd_7460757 3830954387396371487626109 := by
  unfold tailWord_7460757
  simp only [CollatzResearch.WordTrace]
  refine ⟨272116163031959059696796525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181410775354639373131197683 272116163031959059696796525)
  ·
    refine ⟨102043561136984647386298697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272116163031959059696796525 102043561136984647386298697)
    ·
      refine ⟨76532670852738485539724023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102043561136984647386298697 76532670852738485539724023)
      ·
        refine ⟨114799006279107728309586035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76532670852738485539724023 114799006279107728309586035)
        ·
          refine ⟨172198509418661592464379053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114799006279107728309586035 172198509418661592464379053)
          ·
            refine ⟨64574441031998097174142145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172198509418661592464379053 64574441031998097174142145)
            ·
              refine ⟨48430830773998572880606609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64574441031998097174142145 48430830773998572880606609)
              ·
                refine ⟨36323123080498929660454957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48430830773998572880606609 36323123080498929660454957)
                ·
                  refine ⟨13621171155187098622670609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36323123080498929660454957 13621171155187098622670609)
                  ·
                    refine ⟨10215878366390323967002957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13621171155187098622670609 10215878366390323967002957)
                    ·
                      refine ⟨3830954387396371487626109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10215878366390323967002957 3830954387396371487626109)
                      ·
                        rfl

theorem cell23_7460757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 3, 2, 3].length) (baseStart_7460757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7460757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7460757 prefixEnd_7460757 := by exact prefixLift 7460757
  have htrace : WordTrace (prefixWord ++ tailWord_7460757) baseStart_7460757 baseEnd_7460757 := by
    simpa [prefixWord, tailWord_7460757, baseEnd_7460757] using wordTrace_append hprefix tailTrace_7460757
  have hstable : (prefixWord ++ tailWord_7460757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7460757).length < 2 ^ (prefixWord ++ tailWord_7460757).sum := by decide
  have hdescent : baseEnd_7460757 < baseStart_7460757 := by decide
  rcases family_descends (prefixWord ++ tailWord_7460757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7460787 : List Nat := [1, 1, 1, 2, 3, 1, 5, 2, 1, 3, 3]
def baseStart_7460787 : Nat := 118140960795 + 7460787 * 2 ^ 59
def prefixEnd_7460787 : Nat := 4983230072969 + 3 ^ 40 * 7460787 * 2
def baseEnd_7460787 : Nat := 3830969791816006370250971

theorem tailTrace_7460787 : CollatzResearch.WordTrace tailWord_7460787 prefixEnd_7460787 3830969791816006370250971 := by
  unfold tailWord_7460787
  simp only [CollatzResearch.WordTrace]
  refine ⟨272117257221850374820388615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181411504814566916546925743 272117257221850374820388615)
  ·
    refine ⟨408175885832775562230582923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272117257221850374820388615 408175885832775562230582923)
    ·
      refine ⟨612263828749163343345874385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408175885832775562230582923 612263828749163343345874385)
      ·
        refine ⟨459197871561872507509405789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 612263828749163343345874385 459197871561872507509405789)
        ·
          refine ⟨172199201835702190316027171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 459197871561872507509405789 172199201835702190316027171)
          ·
            refine ⟨258298802753553285474040757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172199201835702190316027171 258298802753553285474040757)
            ·
              refine ⟨24215512758145620513191321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 258298802753553285474040757 24215512758145620513191321)
              ·
                refine ⟨18161634568609215384893491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24215512758145620513191321 18161634568609215384893491)
                ·
                  refine ⟨27242451852913823077340237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18161634568609215384893491 27242451852913823077340237)
                  ·
                    refine ⟨10215919444842683654002589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27242451852913823077340237 10215919444842683654002589)
                    ·
                      refine ⟨3830969791816006370250971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10215919444842683654002589 3830969791816006370250971)
                      ·
                        rfl

theorem cell23_7460787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 3, 3].length) (baseStart_7460787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7460787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7460787 prefixEnd_7460787 := by exact prefixLift 7460787
  have htrace : WordTrace (prefixWord ++ tailWord_7460787) baseStart_7460787 baseEnd_7460787 := by
    simpa [prefixWord, tailWord_7460787, baseEnd_7460787] using wordTrace_append hprefix tailTrace_7460787
  have hstable : (prefixWord ++ tailWord_7460787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7460787).length < 2 ^ (prefixWord ++ tailWord_7460787).sum := by decide
  have hdescent : baseEnd_7460787 < baseStart_7460787 := by decide
  rcases family_descends (prefixWord ++ tailWord_7460787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7460814 : List Nat := [4, 1, 1, 1, 2, 2, 1, 1, 5, 3, 2]
def baseStart_7460814 : Nat := 118140960795 + 7460814 * 2 ^ 59
def prefixEnd_7460814 : Nat := 4983230072969 + 3 ^ 40 * 7460814 * 2
def baseEnd_7460814 : Nat := 3830983655793677764613347

theorem tailTrace_7460814 : CollatzResearch.WordTrace tailWord_7460814 prefixEnd_7460814 3830983655793677764613347 := by
  unfold tailWord_7460814
  simp only [CollatzResearch.WordTrace]
  refine ⟨34014780249094069803952687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181412161328501705621080997 34014780249094069803952687)
  ·
    refine ⟨51022170373641104705929031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34014780249094069803952687 51022170373641104705929031)
    ·
      refine ⟨76533255560461657058893547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51022170373641104705929031 76533255560461657058893547)
      ·
        refine ⟨114799883340692485588340321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76533255560461657058893547 114799883340692485588340321)
        ·
          refine ⟨86099912505519364191255241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114799883340692485588340321 86099912505519364191255241)
          ·
            refine ⟨64574934379139523143441431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86099912505519364191255241 64574934379139523143441431)
            ·
              refine ⟨96862401568709284715162147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64574934379139523143441431 96862401568709284715162147)
              ·
                refine ⟨145293602353063927072743221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96862401568709284715162147 145293602353063927072743221)
                ·
                  refine ⟨13621275220599743163069677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 145293602353063927072743221 13621275220599743163069677)
                  ·
                    refine ⟨5107978207724903686151129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13621275220599743163069677 5107978207724903686151129)
                    ·
                      refine ⟨3830983655793677764613347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5107978207724903686151129 3830983655793677764613347)
                      ·
                        rfl

theorem cell23_7460814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 5, 3, 2].length) (baseStart_7460814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7460814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7460814 prefixEnd_7460814 := by exact prefixLift 7460814
  have htrace : WordTrace (prefixWord ++ tailWord_7460814) baseStart_7460814 baseEnd_7460814 := by
    simpa [prefixWord, tailWord_7460814, baseEnd_7460814] using wordTrace_append hprefix tailTrace_7460814
  have hstable : (prefixWord ++ tailWord_7460814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7460814).length < 2 ^ (prefixWord ++ tailWord_7460814).sum := by decide
  have hdescent : baseEnd_7460814 < baseStart_7460814 := by decide
  rcases family_descends (prefixWord ++ tailWord_7460814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7460821 : List Nat := [1, 3, 2, 3, 2, 1, 2, 3, 2, 1, 3]
def baseStart_7460821 : Nat := 118140960795 + 7460821 * 2 ^ 59
def prefixEnd_7460821 : Nat := 4983230072969 + 3 ^ 40 * 7460821 * 2
def baseEnd_7460821 : Nat := 3830987250158259237225815

theorem tailTrace_7460821 : CollatzResearch.WordTrace tailWord_7460821 prefixEnd_7460821 3830987250158259237225815 := by
  unfold tailWord_7460821
  simp only [CollatzResearch.WordTrace]
  refine ⟨272118497303727198627126317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181412331535818132418084211 272118497303727198627126317)
  ·
    refine ⟨102044436488897699485172369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272118497303727198627126317 102044436488897699485172369)
    ·
      refine ⟨76533327366673274613879277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102044436488897699485172369 76533327366673274613879277)
      ·
        refine ⟨28699997762502477980204729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76533327366673274613879277 28699997762502477980204729)
        ·
          refine ⟨21524998321876858485153547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28699997762502477980204729 21524998321876858485153547)
          ·
            refine ⟨32287497482815287727730321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21524998321876858485153547 32287497482815287727730321)
            ·
              refine ⟨24215623112111465795797741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32287497482815287727730321 24215623112111465795797741)
              ·
                refine ⟨9080858667041799673424153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24215623112111465795797741 9080858667041799673424153)
                ·
                  refine ⟨6810644000281349755068115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9080858667041799673424153 6810644000281349755068115)
                  ·
                    refine ⟨10215966000422024632602173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6810644000281349755068115 10215966000422024632602173)
                    ·
                      refine ⟨3830987250158259237225815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10215966000422024632602173 3830987250158259237225815)
                      ·
                        rfl

theorem cell23_7460821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_7460821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7460821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7460821 prefixEnd_7460821 := by exact prefixLift 7460821
  have htrace : WordTrace (prefixWord ++ tailWord_7460821) baseStart_7460821 baseEnd_7460821 := by
    simpa [prefixWord, tailWord_7460821, baseEnd_7460821] using wordTrace_append hprefix tailTrace_7460821
  have hstable : (prefixWord ++ tailWord_7460821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7460821).length < 2 ^ (prefixWord ++ tailWord_7460821).sum := by decide
  have hdescent : baseEnd_7460821 < baseStart_7460821 := by decide
  rcases family_descends (prefixWord ++ tailWord_7460821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7460828 : List Nat := [2, 2, 6, 1, 1, 1, 3, 7]
def baseStart_7460828 : Nat := 118140960795 + 7460828 * 2 ^ 59
def prefixEnd_7460828 : Nat := 4983230072969 + 3 ^ 40 * 7460828 * 2
def baseEnd_7460828 : Nat := 141888549797142248512529

theorem tailTrace_7460828 : CollatzResearch.WordTrace tailWord_7460828 prefixEnd_7460828 141888549797142248512529 := by
  unfold tailWord_7460828
  simp only [CollatzResearch.WordTrace]
  refine ⟨136059376307350919411315569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181412501743134559215087425 136059376307350919411315569)
  ·
    refine ⟨102044532230513189558486677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136059376307350919411315569 102044532230513189558486677)
    ·
      refine ⟨4783337448305305760554063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 102044532230513189558486677 4783337448305305760554063)
      ·
        refine ⟨7175006172457958640831095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4783337448305305760554063 7175006172457958640831095)
        ·
          refine ⟨10762509258686937961246643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7175006172457958640831095 10762509258686937961246643)
          ·
            refine ⟨16143763888030406941869965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10762509258686937961246643 16143763888030406941869965)
            ·
              refine ⟨6053911458011402603201237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16143763888030406941869965 6053911458011402603201237)
              ·
                refine ⟨141888549797142248512529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6053911458011402603201237 141888549797142248512529)
                ·
                  rfl

theorem cell23_7460828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 7].length) (baseStart_7460828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7460828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7460828 prefixEnd_7460828 := by exact prefixLift 7460828
  have htrace : WordTrace (prefixWord ++ tailWord_7460828) baseStart_7460828 baseEnd_7460828 := by
    simpa [prefixWord, tailWord_7460828, baseEnd_7460828] using wordTrace_append hprefix tailTrace_7460828
  have hstable : (prefixWord ++ tailWord_7460828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7460828).length < 2 ^ (prefixWord ++ tailWord_7460828).sum := by decide
  have hdescent : baseEnd_7460828 < baseStart_7460828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7460828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7460857 : List Nat := [1, 2, 1, 3, 1, 4, 1, 2, 2, 2, 4]
def baseStart_7460857 : Nat := 118140960795 + 7460857 * 2 ^ 59
def prefixEnd_7460857 : Nat := 4983230072969 + 3 ^ 40 * 7460857 * 2
def baseEnd_7460857 : Nat := 3831005735461821096375649

theorem tailTrace_7460857 : CollatzResearch.WordTrace tailWord_7460857 prefixEnd_7460857 3831005735461821096375649 := by
  unfold tailWord_7460857
  simp only [CollatzResearch.WordTrace]
  refine ⟨272119810331596776775436825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181413206887731184516957883 272119810331596776775436825)
  ·
    refine ⟨204089857748697582581577619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272119810331596776775436825 204089857748697582581577619)
    ·
      refine ⟨306134786623046373872366429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204089857748697582581577619 306134786623046373872366429)
      ·
        refine ⟨114800544983642390202137411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 306134786623046373872366429 114800544983642390202137411)
        ·
          refine ⟨172200817475463585303206117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114800544983642390202137411 172200817475463585303206117)
          ·
            refine ⟨32287653276649422244351147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172200817475463585303206117 32287653276649422244351147)
            ·
              refine ⟨48431479914974133366526721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32287653276649422244351147 48431479914974133366526721)
              ·
                refine ⟨36323609936230600024895041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48431479914974133366526721 36323609936230600024895041)
                ·
                  refine ⟨27242707452172950018671281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36323609936230600024895041 27242707452172950018671281)
                  ·
                    refine ⟨20432030589129712514003461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27242707452172950018671281 20432030589129712514003461)
                    ·
                      refine ⟨3831005735461821096375649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20432030589129712514003461 3831005735461821096375649)
                      ·
                        rfl

theorem cell23_7460857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_7460857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7460857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7460857 prefixEnd_7460857 := by exact prefixLift 7460857
  have htrace : WordTrace (prefixWord ++ tailWord_7460857) baseStart_7460857 baseEnd_7460857 := by
    simpa [prefixWord, tailWord_7460857, baseEnd_7460857] using wordTrace_append hprefix tailTrace_7460857
  have hstable : (prefixWord ++ tailWord_7460857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7460857).length < 2 ^ (prefixWord ++ tailWord_7460857).sum := by decide
  have hdescent : baseEnd_7460857 < baseStart_7460857 := by decide
  rcases family_descends (prefixWord ++ tailWord_7460857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7460901 : List Nat := [1, 3, 1, 2, 2, 5, 1, 3, 5]
def baseStart_7460901 : Nat := 118140960795 + 7460901 * 2 ^ 59
def prefixEnd_7460901 : Nat := 4983230072969 + 3 ^ 40 * 7460901 * 2
def baseEnd_7460901 : Nat := 425669814290068769358383

theorem tailTrace_7460901 : CollatzResearch.WordTrace tailWord_7460901 prefixEnd_7460901 425669814290068769358383 := by
  unfold tailWord_7460901
  simp only [CollatzResearch.WordTrace]
  refine ⟨272121415143437372290038557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181414276762291581526692371 272121415143437372290038557)
  ·
    refine ⟨102045530678789014608764459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272121415143437372290038557 102045530678789014608764459)
    ·
      refine ⟨153068296018183521913146689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102045530678789014608764459 153068296018183521913146689)
      ·
        refine ⟨114801222013637641434860017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153068296018183521913146689 114801222013637641434860017)
        ·
          refine ⟨86100916510228231076145013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114801222013637641434860017 86100916510228231076145013)
          ·
            refine ⟨8071960922833896663388595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86100916510228231076145013 8071960922833896663388595)
            ·
              refine ⟨12107941384250844995082893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8071960922833896663388595 12107941384250844995082893)
              ·
                refine ⟨4540478019094066873156085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12107941384250844995082893 4540478019094066873156085)
                ·
                  refine ⟨425669814290068769358383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4540478019094066873156085 425669814290068769358383)
                  ·
                    rfl

theorem cell23_7460901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 3, 5].length) (baseStart_7460901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7460901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7460901 prefixEnd_7460901 := by exact prefixLift 7460901
  have htrace : WordTrace (prefixWord ++ tailWord_7460901) baseStart_7460901 baseEnd_7460901 := by
    simpa [prefixWord, tailWord_7460901, baseEnd_7460901] using wordTrace_append hprefix tailTrace_7460901
  have hstable : (prefixWord ++ tailWord_7460901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7460901).length < 2 ^ (prefixWord ++ tailWord_7460901).sum := by decide
  have hdescent : baseEnd_7460901 < baseStart_7460901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7460901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7460914 : List Nat := [3, 2, 1, 1, 2, 4, 1, 2, 2, 5]
def baseStart_7460914 : Nat := 118140960795 + 7460914 * 2 ^ 59
def prefixEnd_7460914 : Nat := 4983230072969 + 3 ^ 40 * 7460914 * 2
def baseEnd_7460914 : Nat := 1277011667953042457787629

theorem tailTrace_7460914 : CollatzResearch.WordTrace tailWord_7460914 prefixEnd_7460914 1277011667953042457787629 := by
  unfold tailWord_7460914
  simp only [CollatzResearch.WordTrace]
  refine ⟨68030472323097568877565449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181414592861593517006841197 68030472323097568877565449)
  ·
    refine ⟨51022854242323176658174087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68030472323097568877565449 51022854242323176658174087)
    ·
      refine ⟨76534281363484764987261131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51022854242323176658174087 76534281363484764987261131)
      ·
        refine ⟨114801422045227147480891697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76534281363484764987261131 114801422045227147480891697)
        ·
          refine ⟨86101066533920360610668773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114801422045227147480891697 86101066533920360610668773)
          ·
            refine ⟨16143949975110067614500395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86101066533920360610668773 16143949975110067614500395)
            ·
              refine ⟨24215924962665101421750593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16143949975110067614500395 24215924962665101421750593)
              ·
                refine ⟨18161943721998826066312945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24215924962665101421750593 18161943721998826066312945)
                ·
                  refine ⟨13621457791499119549734709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18161943721998826066312945 13621457791499119549734709)
                  ·
                    refine ⟨1277011667953042457787629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13621457791499119549734709 1277011667953042457787629)
                    ·
                      rfl

theorem cell23_7460914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 2, 5].length) (baseStart_7460914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7460914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7460914 prefixEnd_7460914 := by exact prefixLift 7460914
  have htrace : WordTrace (prefixWord ++ tailWord_7460914) baseStart_7460914 baseEnd_7460914 := by
    simpa [prefixWord, tailWord_7460914, baseEnd_7460914] using wordTrace_append hprefix tailTrace_7460914
  have hstable : (prefixWord ++ tailWord_7460914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7460914).length < 2 ^ (prefixWord ++ tailWord_7460914).sum := by decide
  have hdescent : baseEnd_7460914 < baseStart_7460914 := by decide
  rcases family_descends (prefixWord ++ tailWord_7460914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7460918 : List Nat := [5, 1, 2, 1, 1, 1, 5, 2, 5]
def baseStart_7460918 : Nat := 118140960795 + 7460918 * 2 ^ 59
def prefixEnd_7460918 : Nat := 4983230072969 + 3 ^ 40 * 7460918 * 2
def baseEnd_7460918 : Nat := 425670784197971706412541

theorem tailTrace_7460918 : CollatzResearch.WordTrace tailWord_7460918 prefixEnd_7460918 425670784197971706412541 := by
  unfold tailWord_7460918
  simp only [CollatzResearch.WordTrace]
  refine ⟨17007627199023486512087963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 181414690122917189462271605 17007627199023486512087963)
  ·
    refine ⟨25511440798535229768131945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17007627199023486512087963 25511440798535229768131945)
    ·
      refine ⟨19133580598901422326098959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25511440798535229768131945 19133580598901422326098959)
      ·
        refine ⟨28700370898352133489148439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19133580598901422326098959 28700370898352133489148439)
        ·
          refine ⟨43050556347528200233722659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28700370898352133489148439 43050556347528200233722659)
          ·
            refine ⟨64575834521292300350583989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43050556347528200233722659 64575834521292300350583989)
            ·
              refine ⟨6053984486371153157867249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64575834521292300350583989 6053984486371153157867249)
              ·
                refine ⟨4540488364778364868400437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6053984486371153157867249 4540488364778364868400437)
                ·
                  refine ⟨425670784197971706412541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4540488364778364868400437 425670784197971706412541)
                  ·
                    rfl

theorem cell23_7460918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 2, 5].length) (baseStart_7460918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7460918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7460918 prefixEnd_7460918 := by exact prefixLift 7460918
  have htrace : WordTrace (prefixWord ++ tailWord_7460918) baseStart_7460918 baseEnd_7460918 := by
    simpa [prefixWord, tailWord_7460918, baseEnd_7460918] using wordTrace_append hprefix tailTrace_7460918
  have hstable : (prefixWord ++ tailWord_7460918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7460918).length < 2 ^ (prefixWord ++ tailWord_7460918).sum := by decide
  have hdescent : baseEnd_7460918 < baseStart_7460918 := by decide
  rcases family_descends (prefixWord ++ tailWord_7460918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7460961 : List Nat := [1, 2, 3, 1, 1, 2, 1, 7, 1, 4]
def baseStart_7460961 : Nat := 118140960795 + 7460961 * 2 ^ 59
def prefixEnd_7460961 : Nat := 4983230072969 + 3 ^ 40 * 7460961 * 2
def baseEnd_7460961 : Nat := 1277019712483296229825057

theorem tailTrace_7460961 : CollatzResearch.WordTrace tailWord_7460961 prefixEnd_7460961 1277019712483296229825057 := by
  unfold tailWord_7460961
  simp only [CollatzResearch.WordTrace]
  refine ⟨272123603523220002537222737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181415735682146668358148491 272123603523220002537222737)
  ·
    refine ⟨204092702642415001902917053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272123603523220002537222737 204092702642415001902917053)
    ·
      refine ⟨76534763490905625713593895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204092702642415001902917053 76534763490905625713593895)
      ·
        refine ⟨114802145236358438570390843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76534763490905625713593895 114802145236358438570390843)
        ·
          refine ⟨172203217854537657855586265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114802145236358438570390843 172203217854537657855586265)
          ·
            refine ⟨129152413390903243391689699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172203217854537657855586265 129152413390903243391689699)
            ·
              refine ⟨193728620086354865087534549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129152413390903243391689699 193728620086354865087534549)
              ·
                refine ⟨4540514533273942150489091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 193728620086354865087534549 4540514533273942150489091)
                ·
                  refine ⟨6810771799910913225733637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4540514533273942150489091 6810771799910913225733637)
                  ·
                    refine ⟨1277019712483296229825057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6810771799910913225733637 1277019712483296229825057)
                    ·
                      rfl

theorem cell23_7460961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 7, 1, 4].length) (baseStart_7460961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7460961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7460961 prefixEnd_7460961 := by exact prefixLift 7460961
  have htrace : WordTrace (prefixWord ++ tailWord_7460961) baseStart_7460961 baseEnd_7460961 := by
    simpa [prefixWord, tailWord_7460961, baseEnd_7460961] using wordTrace_append hprefix tailTrace_7460961
  have hstable : (prefixWord ++ tailWord_7460961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7460961).length < 2 ^ (prefixWord ++ tailWord_7460961).sum := by decide
  have hdescent : baseEnd_7460961 < baseStart_7460961 := by decide
  rcases family_descends (prefixWord ++ tailWord_7460961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7460977 : List Nat := [1, 2, 2, 2, 1, 1, 4, 1, 1, 2, 6]
def baseStart_7460977 : Nat := 118140960795 + 7460977 * 2 ^ 59
def prefixEnd_7460977 : Nat := 4983230072969 + 3 ^ 40 * 7460977 * 2
def baseEnd_7460977 : Nat := 3831067353140360626875097

theorem tailTrace_7460977 : CollatzResearch.WordTrace tailWord_7460977 prefixEnd_7460977 3831067353140360626875097 := by
  unfold tailWord_7460977
  simp only [CollatzResearch.WordTrace]
  refine ⟨272124187091162037269805185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181416124727441358179870123 272124187091162037269805185)
  ·
    refine ⟨204093140318371527952353889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272124187091162037269805185 204093140318371527952353889)
    ·
      refine ⟨153069855238778645964265417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204093140318371527952353889 153069855238778645964265417)
      ·
        refine ⟨114802391429083984473199063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153069855238778645964265417 114802391429083984473199063)
        ·
          refine ⟨172203587143625976709798595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114802391429083984473199063 172203587143625976709798595)
          ·
            refine ⟨258305380715438965064697893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172203587143625976709798595 258305380715438965064697893)
            ·
              refine ⟨48432258884144805949630855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 258305380715438965064697893 48432258884144805949630855)
              ·
                refine ⟨72648388326217208924446283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48432258884144805949630855 72648388326217208924446283)
                ·
                  refine ⟨108972582489325813386669425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72648388326217208924446283 108972582489325813386669425)
                  ·
                    refine ⟨81729436866994360040002069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 108972582489325813386669425 81729436866994360040002069)
                    ·
                      refine ⟨3831067353140360626875097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81729436866994360040002069 3831067353140360626875097)
                      ·
                        rfl

theorem cell23_7460977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_7460977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7460977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7460977 prefixEnd_7460977 := by exact prefixLift 7460977
  have htrace : WordTrace (prefixWord ++ tailWord_7460977) baseStart_7460977 baseEnd_7460977 := by
    simpa [prefixWord, tailWord_7460977, baseEnd_7460977] using wordTrace_append hprefix tailTrace_7460977
  have hstable : (prefixWord ++ tailWord_7460977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7460977).length < 2 ^ (prefixWord ++ tailWord_7460977).sum := by decide
  have hdescent : baseEnd_7460977 < baseStart_7460977 := by decide
  rcases family_descends (prefixWord ++ tailWord_7460977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7460978 : List Nat := [3, 2, 1, 2, 2, 3, 1, 4, 1, 4]
def baseStart_7460978 : Nat := 118140960795 + 7460978 * 2 ^ 59
def prefixEnd_7460978 : Nat := 4983230072969 + 3 ^ 40 * 7460978 * 2
def baseEnd_7460978 : Nat := 1277022622207005040987531

theorem tailTrace_7460978 : CollatzResearch.WordTrace tailWord_7460978 prefixEnd_7460978 1277022622207005040987531 := by
  unfold tailWord_7460978
  simp only [CollatzResearch.WordTrace]
  refine ⟨68031055891039603610147897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181416149042772276293727725 68031055891039603610147897)
  ·
    refine ⟨51023291918279702707610923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68031055891039603610147897 51023291918279702707610923)
    ·
      refine ⟨76534937877419554061416385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51023291918279702707610923 76534937877419554061416385)
      ·
        refine ⟨57401203408064665546062289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76534937877419554061416385 57401203408064665546062289)
        ·
          refine ⟨43050902556048499159546717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57401203408064665546062289 43050902556048499159546717)
          ·
            refine ⟨16144088458518187184830019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43050902556048499159546717 16144088458518187184830019)
            ·
              refine ⟨24216132687777280777245029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16144088458518187184830019 24216132687777280777245029)
              ·
                refine ⟨4540524878958240145733443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24216132687777280777245029 4540524878958240145733443)
                ·
                  refine ⟨6810787318437360218600165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4540524878958240145733443 6810787318437360218600165)
                  ·
                    refine ⟨1277022622207005040987531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6810787318437360218600165 1277022622207005040987531)
                    ·
                      rfl

theorem cell23_7460978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 4, 1, 4].length) (baseStart_7460978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7460978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7460978 prefixEnd_7460978 := by exact prefixLift 7460978
  have htrace : WordTrace (prefixWord ++ tailWord_7460978) baseStart_7460978 baseEnd_7460978 := by
    simpa [prefixWord, tailWord_7460978, baseEnd_7460978] using wordTrace_append hprefix tailTrace_7460978
  have hstable : (prefixWord ++ tailWord_7460978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7460978).length < 2 ^ (prefixWord ++ tailWord_7460978).sum := by decide
  have hdescent : baseEnd_7460978 < baseStart_7460978 := by decide
  rcases family_descends (prefixWord ++ tailWord_7460978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7461001 : List Nat := [1, 2, 1, 1, 4, 2, 3, 2, 3, 1, 3]
def baseStart_7461001 : Nat := 118140960795 + 7461001 * 2 ^ 59
def prefixEnd_7461001 : Nat := 4983230072969 + 3 ^ 40 * 7461001 * 2
def baseEnd_7461001 : Nat := 3831079676676068532974987

theorem tailTrace_7461001 : CollatzResearch.WordTrace tailWord_7461001 prefixEnd_7461001 3831079676676068532974987 := by
  unfold tailWord_7461001
  simp only [CollatzResearch.WordTrace]
  refine ⟨272125062443075089368678857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181416708295383392912452571 272125062443075089368678857)
  ·
    refine ⟨204093796832306317026509143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272125062443075089368678857 204093796832306317026509143)
    ·
      refine ⟨306140695248459475539763715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204093796832306317026509143 306140695248459475539763715)
      ·
        refine ⟨459211042872689213309645573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306140695248459475539763715 459211042872689213309645573)
        ·
          refine ⟨86102070538629227495558545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 459211042872689213309645573 86102070538629227495558545)
          ·
            refine ⟨64576552903971920621668909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86102070538629227495558545 64576552903971920621668909)
            ·
              refine ⟨24216207338989470233125841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64576552903971920621668909 24216207338989470233125841)
              ·
                refine ⟨18162155504242102674844381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24216207338989470233125841 18162155504242102674844381)
                ·
                  refine ⟨6810808314090788503066643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18162155504242102674844381 6810808314090788503066643)
                  ·
                    refine ⟨10216212471136182754599965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6810808314090788503066643 10216212471136182754599965)
                    ·
                      refine ⟨3831079676676068532974987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10216212471136182754599965 3831079676676068532974987)
                      ·
                        rfl

theorem cell23_7461001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 3, 1, 3].length) (baseStart_7461001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7461001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7461001 prefixEnd_7461001 := by exact prefixLift 7461001
  have htrace : WordTrace (prefixWord ++ tailWord_7461001) baseStart_7461001 baseEnd_7461001 := by
    simpa [prefixWord, tailWord_7461001, baseEnd_7461001] using wordTrace_append hprefix tailTrace_7461001
  have hstable : (prefixWord ++ tailWord_7461001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7461001).length < 2 ^ (prefixWord ++ tailWord_7461001).sum := by decide
  have hdescent : baseEnd_7461001 < baseStart_7461001 := by decide
  rcases family_descends (prefixWord ++ tailWord_7461001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7461012 : List Nat := [2, 4, 2, 3, 1, 1, 2, 3, 1, 4]
def baseStart_7461012 : Nat := 118140960795 + 7461012 * 2 ^ 59
def prefixEnd_7461012 : Nat := 4983230072969 + 3 ^ 40 * 7461012 * 2
def baseEnd_7461012 : Nat := 1277028441654422663312479

theorem tailTrace_7461012 : CollatzResearch.WordTrace tailWord_7461012 prefixEnd_7461012 1277028441654422663312479 := by
  unfold tailWord_7461012
  simp only [CollatzResearch.WordTrace]
  refine ⟨136062731823017619123664645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181416975764023492164886193 136062731823017619123664645)
  ·
    refine ⟨25511762216815803585687121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136062731823017619123664645 25511762216815803585687121)
    ·
      refine ⟨19133821662611852689265341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25511762216815803585687121 19133821662611852689265341)
      ·
        refine ⟨7175183123479444758474503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19133821662611852689265341 7175183123479444758474503)
        ·
          refine ⟨10762774685219167137711755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7175183123479444758474503 10762774685219167137711755)
          ·
            refine ⟨16144162027828750706567633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10762774685219167137711755 16144162027828750706567633)
            ·
              refine ⟨12108121520871563029925725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16144162027828750706567633 12108121520871563029925725)
              ·
                refine ⟨4540545570326836136222147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12108121520871563029925725 4540545570326836136222147)
                ·
                  refine ⟨6810818355490254204333221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4540545570326836136222147 6810818355490254204333221)
                  ·
                    refine ⟨1277028441654422663312479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6810818355490254204333221 1277028441654422663312479)
                    ·
                      rfl

theorem cell23_7461012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_7461012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7461012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7461012 prefixEnd_7461012 := by exact prefixLift 7461012
  have htrace : WordTrace (prefixWord ++ tailWord_7461012) baseStart_7461012 baseEnd_7461012 := by
    simpa [prefixWord, tailWord_7461012, baseEnd_7461012] using wordTrace_append hprefix tailTrace_7461012
  have hstable : (prefixWord ++ tailWord_7461012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7461012).length < 2 ^ (prefixWord ++ tailWord_7461012).sum := by decide
  have hdescent : baseEnd_7461012 < baseStart_7461012 := by decide
  rcases family_descends (prefixWord ++ tailWord_7461012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7461021 : List Nat := [1, 4, 2, 1, 1, 4, 1, 3, 1, 5]
def baseStart_7461021 : Nat := 118140960795 + 7461021 * 2 ^ 59
def prefixEnd_7461021 : Nat := 4983230072969 + 3 ^ 40 * 7461021 * 2
def baseEnd_7461021 : Nat := 1277029982096386151574965

theorem tailTrace_7461021 : CollatzResearch.WordTrace tailWord_7461021 prefixEnd_7461021 1277029982096386151574965 := by
  unfold tailWord_7461021
  simp only [CollatzResearch.WordTrace]
  refine ⟨272125791903002632784406917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181417194602001755189604611 272125791903002632784406917)
  ·
    refine ⟨51023585981812993647076297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 272125791903002632784406917 51023585981812993647076297)
    ·
      refine ⟨38267689486359745235307223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51023585981812993647076297 38267689486359745235307223)
      ·
        refine ⟨57401534229539617852960835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38267689486359745235307223 57401534229539617852960835)
        ·
          refine ⟨86102301344309426779441253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57401534229539617852960835 86102301344309426779441253)
          ·
            refine ⟨16144181502058017521145235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86102301344309426779441253 16144181502058017521145235)
            ·
              refine ⟨24216272253087026281717853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16144181502058017521145235 24216272253087026281717853)
              ·
                refine ⟨9081102094907634855644195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24216272253087026281717853 9081102094907634855644195)
                ·
                  refine ⟨13621653142361452283466293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9081102094907634855644195 13621653142361452283466293)
                  ·
                    refine ⟨1277029982096386151574965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13621653142361452283466293 1277029982096386151574965)
                    ·
                      rfl

theorem cell23_7461021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_7461021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7461021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7461021 prefixEnd_7461021 := by exact prefixLift 7461021
  have htrace : WordTrace (prefixWord ++ tailWord_7461021) baseStart_7461021 baseEnd_7461021 := by
    simpa [prefixWord, tailWord_7461021, baseEnd_7461021] using wordTrace_append hprefix tailTrace_7461021
  have hstable : (prefixWord ++ tailWord_7461021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7461021).length < 2 ^ (prefixWord ++ tailWord_7461021).sum := by decide
  have hdescent : baseEnd_7461021 < baseStart_7461021 := by decide
  rcases family_descends (prefixWord ++ tailWord_7461021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7461061 : List Nat := [1, 3, 1, 1, 1, 1, 5, 4, 1, 2, 3]
def baseStart_7461061 : Nat := 118140960795 + 7461061 * 2 ^ 59
def prefixEnd_7461061 : Nat := 4983230072969 + 3 ^ 40 * 7461061 * 2
def baseEnd_7461061 : Nat := 3831110485515338298224711

theorem tailTrace_7461061 : CollatzResearch.WordTrace tailWord_7461061 prefixEnd_7461061 3831110485515338298224711 := by
  unfold tailWord_7461061
  simp only [CollatzResearch.WordTrace]
  refine ⟨272127250822857719615863037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181418167215238479743908691 272127250822857719615863037)
  ·
    refine ⟨102047719058571644855948639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272127250822857719615863037 102047719058571644855948639)
    ·
      refine ⟨153071578587857467283922959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102047719058571644855948639 153071578587857467283922959)
      ·
        refine ⟨229607367881786200925884439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153071578587857467283922959 229607367881786200925884439)
        ·
          refine ⟨344411051822679301388826659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229607367881786200925884439 344411051822679301388826659)
          ·
            refine ⟨516616577734018952083239989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344411051822679301388826659 516616577734018952083239989)
            ·
              refine ⟨48432804162564276757803749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 516616577734018952083239989 48432804162564276757803749)
              ·
                refine ⟨9081150780480801892088203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48432804162564276757803749 9081150780480801892088203)
                ·
                  refine ⟨13621726170721202838132305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9081150780480801892088203 13621726170721202838132305)
                  ·
                    refine ⟨10216294628040902128599229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13621726170721202838132305 10216294628040902128599229)
                    ·
                      refine ⟨3831110485515338298224711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10216294628040902128599229 3831110485515338298224711)
                      ·
                        rfl

theorem cell23_7461061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 4, 1, 2, 3].length) (baseStart_7461061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7461061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7461061 prefixEnd_7461061 := by exact prefixLift 7461061
  have htrace : WordTrace (prefixWord ++ tailWord_7461061) baseStart_7461061 baseEnd_7461061 := by
    simpa [prefixWord, tailWord_7461061, baseEnd_7461061] using wordTrace_append hprefix tailTrace_7461061
  have hstable : (prefixWord ++ tailWord_7461061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7461061).length < 2 ^ (prefixWord ++ tailWord_7461061).sum := by decide
  have hdescent : baseEnd_7461061 < baseStart_7461061 := by decide
  rcases family_descends (prefixWord ++ tailWord_7461061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7461078 : List Nat := [5, 2, 1, 2, 1, 1, 1, 3, 1, 1, 5]
def baseStart_7461078 : Nat := 118140960795 + 7461078 * 2 ^ 59
def prefixEnd_7461078 : Nat := 4983230072969 + 3 ^ 40 * 7461078 * 2
def baseEnd_7461078 : Nat := 3831119214686464731712133

theorem tailTrace_7461078 : CollatzResearch.WordTrace tailWord_7461078 prefixEnd_7461078 3831119214686464731712133 := by
  unfold tailWord_7461078
  simp only [CollatzResearch.WordTrace]
  refine ⟨17007991928987258219951993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 181418580575864087679487925 17007991928987258219951993)
  ·
    refine ⟨12755993946740443664963995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17007991928987258219951993 12755993946740443664963995)
    ·
      refine ⟨19133990920110665497445993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12755993946740443664963995 19133990920110665497445993)
      ·
        refine ⟨14350493190082999123084495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19133990920110665497445993 14350493190082999123084495)
        ·
          refine ⟨21525739785124498684626743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14350493190082999123084495 21525739785124498684626743)
          ·
            refine ⟨32288609677686748026940115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21525739785124498684626743 32288609677686748026940115)
            ·
              refine ⟨48432914516530122040410173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32288609677686748026940115 48432914516530122040410173)
              ·
                refine ⟨18162342943698795765153815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48432914516530122040410173 18162342943698795765153815)
                ·
                  refine ⟨27243514415548193647730723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18162342943698795765153815 27243514415548193647730723)
                  ·
                    refine ⟨40865271623322290471596085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27243514415548193647730723 40865271623322290471596085)
                    ·
                      refine ⟨3831119214686464731712133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40865271623322290471596085 3831119214686464731712133)
                      ·
                        rfl

theorem cell23_7461078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_7461078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7461078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7461078 prefixEnd_7461078 := by exact prefixLift 7461078
  have htrace : WordTrace (prefixWord ++ tailWord_7461078) baseStart_7461078 baseEnd_7461078 := by
    simpa [prefixWord, tailWord_7461078, baseEnd_7461078] using wordTrace_append hprefix tailTrace_7461078
  have hstable : (prefixWord ++ tailWord_7461078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7461078).length < 2 ^ (prefixWord ++ tailWord_7461078).sum := by decide
  have hdescent : baseEnd_7461078 < baseStart_7461078 := by decide
  rcases family_descends (prefixWord ++ tailWord_7461078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7461151 : List Nat := [1, 1, 2, 4, 3, 1, 1, 1, 2, 4, 3]
def baseStart_7461151 : Nat := 118140960795 + 7461151 * 2 ^ 59
def prefixEnd_7461151 : Nat := 4983230072969 + 3 ^ 40 * 7461151 * 2
def baseEnd_7461151 : Nat := 3831156698774242946099297

theorem tailTrace_7461151 : CollatzResearch.WordTrace tailWord_7461151 prefixEnd_7461151 3831156698774242946099297 := by
  unfold tailWord_7461151
  simp only [CollatzResearch.WordTrace]
  refine ⟨272130533392531664986639307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181420355595021109991092871 272130533392531664986639307)
  ·
    refine ⟨408195800088797497479958961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272130533392531664986639307 408195800088797497479958961)
    ·
      refine ⟨306146850066598123109969221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408195800088797497479958961 306146850066598123109969221)
      ·
        refine ⟨57402534387487148083119229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 306146850066598123109969221 57402534387487148083119229)
        ·
          refine ⟨21525950395307680531169711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57402534387487148083119229 21525950395307680531169711)
          ·
            refine ⟨32288925592961520796754567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21525950395307680531169711 32288925592961520796754567)
            ·
              refine ⟨48433388389442281195131851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32288925592961520796754567 48433388389442281195131851)
              ·
                refine ⟨72650082584163421792697777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48433388389442281195131851 72650082584163421792697777)
                ·
                  refine ⟨54487561938122566344523333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72650082584163421792697777 54487561938122566344523333)
                  ·
                    refine ⟨10216417863397981189598125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54487561938122566344523333 10216417863397981189598125)
                    ·
                      refine ⟨3831156698774242946099297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10216417863397981189598125 3831156698774242946099297)
                      ·
                        rfl

theorem cell23_7461151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_7461151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7461151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7461151 prefixEnd_7461151 := by exact prefixLift 7461151
  have htrace : WordTrace (prefixWord ++ tailWord_7461151) baseStart_7461151 baseEnd_7461151 := by
    simpa [prefixWord, tailWord_7461151, baseEnd_7461151] using wordTrace_append hprefix tailTrace_7461151
  have hstable : (prefixWord ++ tailWord_7461151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7461151).length < 2 ^ (prefixWord ++ tailWord_7461151).sum := by decide
  have hdescent : baseEnd_7461151 < baseStart_7461151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7461151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7461221 : List Nat := [1, 3, 1, 3, 1, 3, 1, 2, 1, 3, 4]
def baseStart_7461221 : Nat := 118140960795 + 7461221 * 2 ^ 59
def prefixEnd_7461221 : Nat := 4983230072969 + 3 ^ 40 * 7461221 * 2
def baseEnd_7461221 : Nat := 3831192642420057672223975

theorem tailTrace_7461221 : CollatzResearch.WordTrace tailWord_7461221 prefixEnd_7461221 3831192642420057672223975 := by
  unfold tailWord_7461221
  simp only [CollatzResearch.WordTrace]
  refine ⟨272133086502278066941687517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181422057668185377961125011 272133086502278066941687517)
  ·
    refine ⟨102049907438354275103132819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272133086502278066941687517 102049907438354275103132819)
    ·
      refine ⟨153074861157531412654699229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102049907438354275103132819 153074861157531412654699229)
      ·
        refine ⟨57403072934074279745512211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153074861157531412654699229 57403072934074279745512211)
        ·
          refine ⟨86104609401111419618268317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57403072934074279745512211 86104609401111419618268317)
          ·
            refine ⟨32289228525416782356850619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86104609401111419618268317 32289228525416782356850619)
            ·
              refine ⟨48433842788125173535275929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32289228525416782356850619 48433842788125173535275929)
              ·
                refine ⟨36325382091093880151456947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48433842788125173535275929 36325382091093880151456947)
                ·
                  refine ⟨54488073136640820227185421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36325382091093880151456947 54488073136640820227185421)
                  ·
                    refine ⟨20433027426240307585194533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54488073136640820227185421 20433027426240307585194533)
                    ·
                      refine ⟨3831192642420057672223975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20433027426240307585194533 3831192642420057672223975)
                      ·
                        rfl

theorem cell23_7461221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_7461221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7461221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7461221 prefixEnd_7461221 := by exact prefixLift 7461221
  have htrace : WordTrace (prefixWord ++ tailWord_7461221) baseStart_7461221 baseEnd_7461221 := by
    simpa [prefixWord, tailWord_7461221, baseEnd_7461221] using wordTrace_append hprefix tailTrace_7461221
  have hstable : (prefixWord ++ tailWord_7461221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7461221).length < 2 ^ (prefixWord ++ tailWord_7461221).sum := by decide
  have hdescent : baseEnd_7461221 < baseStart_7461221 := by decide
  rcases family_descends (prefixWord ++ tailWord_7461221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7461231 : List Nat := [1, 1, 2, 1, 3, 1, 2, 3, 5, 4]
def baseStart_7461231 : Nat := 118140960795 + 7461231 * 2 ^ 59
def prefixEnd_7461231 : Nat := 4983230072969 + 3 ^ 40 * 7461231 * 2
def baseEnd_7461231 : Nat := 1277065925742200877699643

theorem tailTrace_7461231 : CollatzResearch.WordTrace tailWord_7461231 prefixEnd_7461231 1277065925742200877699643 := by
  unfold tailWord_7461231
  simp only [CollatzResearch.WordTrace]
  refine ⟨272133451232241838649551547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181422300821494559099701031 272133451232241838649551547)
  ·
    refine ⟨408200176848362757974327321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272133451232241838649551547 408200176848362757974327321)
    ·
      refine ⟨306150132636272068480745491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408200176848362757974327321 306150132636272068480745491)
      ·
        refine ⟨459225198954408102721118237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306150132636272068480745491 459225198954408102721118237)
        ·
          refine ⟨172209449607903038520419339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 459225198954408102721118237 172209449607903038520419339)
          ·
            refine ⟨258314174411854557780629009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172209449607903038520419339 258314174411854557780629009)
            ·
              refine ⟨193735630808890918335471757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 258314174411854557780629009 193735630808890918335471757)
              ·
                refine ⟨72650861553334094375801909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 193735630808890918335471757 72650861553334094375801909)
                ·
                  refine ⟨6811018270625071347731429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72650861553334094375801909 6811018270625071347731429)
                  ·
                    refine ⟨1277065925742200877699643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6811018270625071347731429 1277065925742200877699643)
                    ·
                      rfl

theorem cell23_7461231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 5, 4].length) (baseStart_7461231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7461231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7461231 prefixEnd_7461231 := by exact prefixLift 7461231
  have htrace : WordTrace (prefixWord ++ tailWord_7461231) baseStart_7461231 baseEnd_7461231 := by
    simpa [prefixWord, tailWord_7461231, baseEnd_7461231] using wordTrace_append hprefix tailTrace_7461231
  have hstable : (prefixWord ++ tailWord_7461231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7461231).length < 2 ^ (prefixWord ++ tailWord_7461231).sum := by decide
  have hdescent : baseEnd_7461231 < baseStart_7461231 := by decide
  rcases family_descends (prefixWord ++ tailWord_7461231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7461316 : List Nat := [2, 3, 3, 2, 2, 2, 2, 2, 1, 4]
def baseStart_7461316 : Nat := 118140960795 + 7461316 * 2 ^ 59
def prefixEnd_7461316 : Nat := 4983230072969 + 3 ^ 40 * 7461316 * 2
def baseEnd_7461316 : Nat := 1277080474360744933512013

theorem tailTrace_7461316 : CollatzResearch.WordTrace tailWord_7461316 prefixEnd_7461316 1277080474360744933512013 := by
  unfold tailWord_7461316
  simp only [CollatzResearch.WordTrace]
  refine ⟨136068275718466949083197901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181424367624622598777597201 136068275718466949083197901)
  ·
    refine ⟨51025603394425105906199213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136068275718466949083197901 51025603394425105906199213)
    ·
      refine ⟨19134601272909414714824705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51025603394425105906199213 19134601272909414714824705)
      ·
        refine ⟨14350950954682061036118529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19134601272909414714824705 14350950954682061036118529)
        ·
          refine ⟨10763213216011545777088897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14350950954682061036118529 10763213216011545777088897)
          ·
            refine ⟨8072409912008659332816673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10763213216011545777088897 8072409912008659332816673)
            ·
              refine ⟨6054307434006494499612505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8072409912008659332816673 6054307434006494499612505)
              ·
                refine ⟨4540730575504870874709379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6054307434006494499612505 4540730575504870874709379)
                ·
                  refine ⟨6811095863257306312064069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4540730575504870874709379 6811095863257306312064069)
                  ·
                    refine ⟨1277080474360744933512013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6811095863257306312064069 1277080474360744933512013)
                    ·
                      rfl

theorem cell23_7461316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_7461316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7461316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7461316 prefixEnd_7461316 := by exact prefixLift 7461316
  have htrace : WordTrace (prefixWord ++ tailWord_7461316) baseStart_7461316 baseEnd_7461316 := by
    simpa [prefixWord, tailWord_7461316, baseEnd_7461316] using wordTrace_append hprefix tailTrace_7461316
  have hstable : (prefixWord ++ tailWord_7461316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7461316).length < 2 ^ (prefixWord ++ tailWord_7461316).sum := by decide
  have hdescent : baseEnd_7461316 < baseStart_7461316 := by decide
  rcases family_descends (prefixWord ++ tailWord_7461316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7461322 : List Nat := [3, 1, 2, 1, 2, 2, 3, 4, 1, 1, 3]
def baseStart_7461322 : Nat := 118140960795 + 7461322 * 2 ^ 59
def prefixEnd_7461322 : Nat := 4983230072969 + 3 ^ 40 * 7461322 * 2
def baseEnd_7461322 : Nat := 3831244503966161777061011

theorem tailTrace_7461322 : CollatzResearch.WordTrace tailWord_7461322 prefixEnd_7461322 3831244503966161777061011 := by
  unfold tailWord_7461322
  simp only [CollatzResearch.WordTrace]
  refine ⟨68034192568728040297778555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181424513516608107460742813 68034192568728040297778555)
  ·
    refine ⟨102051288853092060446667833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68034192568728040297778555 102051288853092060446667833)
    ·
      refine ⟨76538466639819045335000875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102051288853092060446667833 76538466639819045335000875)
      ·
        refine ⟨114807699959728568002501313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76538466639819045335000875 114807699959728568002501313)
        ·
          refine ⟨86105774969796426001875985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114807699959728568002501313 86105774969796426001875985)
          ·
            refine ⟨64579331227347319501406989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86105774969796426001875985 64579331227347319501406989)
            ·
              refine ⟨24217249210255244813027621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64579331227347319501406989 24217249210255244813027621)
              ·
                refine ⟨4540734226922858402442679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24217249210255244813027621 4540734226922858402442679)
                ·
                  refine ⟨6811101340384287603664019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4540734226922858402442679 6811101340384287603664019)
                  ·
                    refine ⟨10216652010576431405496029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6811101340384287603664019 10216652010576431405496029)
                    ·
                      refine ⟨3831244503966161777061011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10216652010576431405496029 3831244503966161777061011)
                      ·
                        rfl

theorem cell23_7461322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 4, 1, 1, 3].length) (baseStart_7461322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7461322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7461322 prefixEnd_7461322 := by exact prefixLift 7461322
  have htrace : WordTrace (prefixWord ++ tailWord_7461322) baseStart_7461322 baseEnd_7461322 := by
    simpa [prefixWord, tailWord_7461322, baseEnd_7461322] using wordTrace_append hprefix tailTrace_7461322
  have hstable : (prefixWord ++ tailWord_7461322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7461322).length < 2 ^ (prefixWord ++ tailWord_7461322).sum := by decide
  have hdescent : baseEnd_7461322 < baseStart_7461322 := by decide
  rcases family_descends (prefixWord ++ tailWord_7461322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7461338 : List Nat := [3, 1, 1, 2, 3, 1, 4, 1, 1, 6]
def baseStart_7461338 : Nat := 118140960795 + 7461338 * 2 ^ 59
def prefixEnd_7461338 : Nat := 4983230072969 + 3 ^ 40 * 7461338 * 2
def baseEnd_7461338 : Nat := 1277084239885544571486979

theorem tailTrace_7461338 : CollatzResearch.WordTrace tailWord_7461338 prefixEnd_7461338 1277084239885544571486979 := by
  unfold tailWord_7461338
  simp only [CollatzResearch.WordTrace]
  refine ⟨68034338460713548980924167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181424902561902797282464445 68034338460713548980924167)
  ·
    refine ⟨102051507691070323471386251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68034338460713548980924167 102051507691070323471386251)
    ·
      refine ⟨153077261536605485207079377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102051507691070323471386251 153077261536605485207079377)
      ·
        refine ⟨114807946152454113905309533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153077261536605485207079377 114807946152454113905309533)
        ·
          refine ⟨43052979807170292714491075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114807946152454113905309533 43052979807170292714491075)
          ·
            refine ⟨64579469710755439071736613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43052979807170292714491075 64579469710755439071736613)
            ·
              refine ⟨12108650570766644825950615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64579469710755439071736613 12108650570766644825950615)
              ·
                refine ⟨18162975856149967238925923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12108650570766644825950615 18162975856149967238925923)
                ·
                  refine ⟨27244463784224950858388885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18162975856149967238925923 27244463784224950858388885)
                  ·
                    refine ⟨1277084239885544571486979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27244463784224950858388885 1277084239885544571486979)
                    ·
                      rfl

theorem cell23_7461338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 1, 6].length) (baseStart_7461338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7461338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7461338 prefixEnd_7461338 := by exact prefixLift 7461338
  have htrace : WordTrace (prefixWord ++ tailWord_7461338) baseStart_7461338 baseEnd_7461338 := by
    simpa [prefixWord, tailWord_7461338, baseEnd_7461338] using wordTrace_append hprefix tailTrace_7461338
  have hstable : (prefixWord ++ tailWord_7461338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7461338).length < 2 ^ (prefixWord ++ tailWord_7461338).sum := by decide
  have hdescent : baseEnd_7461338 < baseStart_7461338 := by decide
  rcases family_descends (prefixWord ++ tailWord_7461338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7461349 : List Nat := [1, 3, 1, 5, 2, 2, 1, 1, 2, 3, 2]
def baseStart_7461349 : Nat := 118140960795 + 7461349 * 2 ^ 59
def prefixEnd_7461349 : Nat := 4983230072969 + 3 ^ 40 * 7461349 * 2
def baseEnd_7461349 : Nat := 3831258367943833171423387

theorem tailTrace_7461349 : CollatzResearch.WordTrace tailWord_7461349 prefixEnd_7461349 3831258367943833171423387 := by
  unfold tailWord_7461349
  simp only [CollatzResearch.WordTrace]
  refine ⟨272137755045814344802347101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181425170030542896534898067 272137755045814344802347101)
  ·
    refine ⟨102051658142180379300880163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272137755045814344802347101 102051658142180379300880163)
    ·
      refine ⟨153077487213270568951320245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102051658142180379300880163 153077487213270568951320245)
      ·
        refine ⟨14351014426244115839186273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 153077487213270568951320245 14351014426244115839186273)
        ·
          refine ⟨10763260819683086879389705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14351014426244115839186273 10763260819683086879389705)
          ·
            refine ⟨8072445614762315159542279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10763260819683086879389705 8072445614762315159542279)
            ·
              refine ⟨12108668422143472739313419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8072445614762315159542279 12108668422143472739313419)
              ·
                refine ⟨18163002633215209108970129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12108668422143472739313419 18163002633215209108970129)
                ·
                  refine ⟨13622251974911406831727597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18163002633215209108970129 13622251974911406831727597)
                  ·
                    refine ⟨5108344490591777561897849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13622251974911406831727597 5108344490591777561897849)
                    ·
                      refine ⟨3831258367943833171423387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5108344490591777561897849 3831258367943833171423387)
                      ·
                        rfl

theorem cell23_7461349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_7461349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7461349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7461349 prefixEnd_7461349 := by exact prefixLift 7461349
  have htrace : WordTrace (prefixWord ++ tailWord_7461349) baseStart_7461349 baseEnd_7461349 := by
    simpa [prefixWord, tailWord_7461349, baseEnd_7461349] using wordTrace_append hprefix tailTrace_7461349
  have hstable : (prefixWord ++ tailWord_7461349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7461349).length < 2 ^ (prefixWord ++ tailWord_7461349).sum := by decide
  have hdescent : baseEnd_7461349 < baseStart_7461349 := by decide
  rcases family_descends (prefixWord ++ tailWord_7461349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7461362 : List Nat := [3, 2, 1, 4, 2, 1, 1, 3, 1, 1, 4]
def baseStart_7461362 : Nat := 118140960795 + 7461362 * 2 ^ 59
def prefixEnd_7461362 : Nat := 4983230072969 + 3 ^ 40 * 7461362 * 2
def baseEnd_7461362 : Nat := 3831265043192341620560827

theorem tailTrace_7461362 : CollatzResearch.WordTrace tailWord_7461362 prefixEnd_7461362 3831265043192341620560827 := by
  unfold tailWord_7461362
  simp only [CollatzResearch.WordTrace]
  refine ⟨68034557298691812005642585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181425486129844832015046893 68034557298691812005642585)
  ·
    refine ⟨51025917974018859004231939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68034557298691812005642585 51025917974018859004231939)
    ·
      refine ⟨76538876961028288506347909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51025917974018859004231939 76538876961028288506347909)
      ·
        refine ⟨14351039430192804094940233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76538876961028288506347909 14351039430192804094940233)
        ·
          refine ⟨10763279572644603071205175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14351039430192804094940233 10763279572644603071205175)
          ·
            refine ⟨16144919358966904606807763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10763279572644603071205175 16144919358966904606807763)
            ·
              refine ⟨24217379038450356910211645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16144919358966904606807763 24217379038450356910211645)
              ·
                refine ⟨9081517139418883841329367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24217379038450356910211645 9081517139418883841329367)
                ·
                  refine ⟨13622275709128325761994051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9081517139418883841329367 13622275709128325761994051)
                  ·
                    refine ⟨20433413563692488642991077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13622275709128325761994051 20433413563692488642991077)
                    ·
                      refine ⟨3831265043192341620560827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20433413563692488642991077 3831265043192341620560827)
                      ·
                        rfl

theorem cell23_7461362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_7461362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7461362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7461362 prefixEnd_7461362 := by exact prefixLift 7461362
  have htrace : WordTrace (prefixWord ++ tailWord_7461362) baseStart_7461362 baseEnd_7461362 := by
    simpa [prefixWord, tailWord_7461362, baseEnd_7461362] using wordTrace_append hprefix tailTrace_7461362
  have hstable : (prefixWord ++ tailWord_7461362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7461362).length < 2 ^ (prefixWord ++ tailWord_7461362).sum := by decide
  have hdescent : baseEnd_7461362 < baseStart_7461362 := by decide
  rcases family_descends (prefixWord ++ tailWord_7461362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7461381 : List Nat := [1, 3, 1, 1, 2, 2, 2, 1, 1, 9]
def baseStart_7461381 : Nat := 118140960795 + 7461381 * 2 ^ 59
def prefixEnd_7461381 : Nat := 4983230072969 + 3 ^ 40 * 7461381 * 2
def baseEnd_7461381 : Nat := 1277091599774925682074413

theorem tailTrace_7461381 : CollatzResearch.WordTrace tailWord_7461381 prefixEnd_7461381 1277091599774925682074413 := by
  unfold tailWord_7461381
  simp only [CollatzResearch.WordTrace]
  refine ⟨272138922181698414267511997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181425948121132276178341331 272138922181698414267511997)
  ·
    refine ⟨102052095818136905350316999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272138922181698414267511997 102052095818136905350316999)
    ·
      refine ⟨153078143727205358025475499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102052095818136905350316999 153078143727205358025475499)
      ·
        refine ⟨229617215590808037038213249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153078143727205358025475499 229617215590808037038213249)
        ·
          refine ⟨172212911693106027778659937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229617215590808037038213249 172212911693106027778659937)
          ·
            refine ⟨129159683769829520833994953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172212911693106027778659937 129159683769829520833994953)
            ·
              refine ⟨96869762827372140625496215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129159683769829520833994953 96869762827372140625496215)
              ·
                refine ⟨145304644241058210938244323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96869762827372140625496215 145304644241058210938244323)
                ·
                  refine ⟨217956966361587316407366485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145304644241058210938244323 217956966361587316407366485)
                  ·
                    refine ⟨1277091599774925682074413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 217956966361587316407366485 1277091599774925682074413)
                    ·
                      rfl

theorem cell23_7461381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 9].length) (baseStart_7461381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7461381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7461381 prefixEnd_7461381 := by exact prefixLift 7461381
  have htrace : WordTrace (prefixWord ++ tailWord_7461381) baseStart_7461381 baseEnd_7461381 := by
    simpa [prefixWord, tailWord_7461381, baseEnd_7461381] using wordTrace_append hprefix tailTrace_7461381
  have hstable : (prefixWord ++ tailWord_7461381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7461381).length < 2 ^ (prefixWord ++ tailWord_7461381).sum := by decide
  have hdescent : baseEnd_7461381 < baseStart_7461381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7461381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7461389 : List Nat := [1, 7, 1, 1, 1, 3, 1, 1, 1, 6]
def baseStart_7461389 : Nat := 118140960795 + 7461389 * 2 ^ 59
def prefixEnd_7461389 : Nat := 4983230072969 + 3 ^ 40 * 7461389 * 2
def baseEnd_7461389 : Nat := 1277092969056671004974401

theorem tailTrace_7461389 : CollatzResearch.WordTrace tailWord_7461389 prefixEnd_7461389 1277092969056671004974401 := by
  unfold tailWord_7461389
  simp only [CollatzResearch.WordTrace]
  refine ⟨272139213965669431633803221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181426142643779621089202147 272139213965669431633803221)
  ·
    refine ⟨6378262827320377303917263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 272139213965669431633803221 6378262827320377303917263)
    ·
      refine ⟨9567394240980565955875895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6378262827320377303917263 9567394240980565955875895)
      ·
        refine ⟨14351091361470848933813843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9567394240980565955875895 14351091361470848933813843)
        ·
          refine ⟨21526637042206273400720765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14351091361470848933813843 21526637042206273400720765)
          ·
            refine ⟨8072488890827352525270287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21526637042206273400720765 8072488890827352525270287)
            ·
              refine ⟨12108733336241028787905431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8072488890827352525270287 12108733336241028787905431)
              ·
                refine ⟨18163100004361543181858147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12108733336241028787905431 18163100004361543181858147)
                ·
                  refine ⟨27244650006542314772787221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18163100004361543181858147 27244650006542314772787221)
                  ·
                    refine ⟨1277092969056671004974401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27244650006542314772787221 1277092969056671004974401)
                    ·
                      rfl

theorem cell23_7461389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_7461389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7461389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7461389 prefixEnd_7461389 := by exact prefixLift 7461389
  have htrace : WordTrace (prefixWord ++ tailWord_7461389) baseStart_7461389 baseEnd_7461389 := by
    simpa [prefixWord, tailWord_7461389, baseEnd_7461389] using wordTrace_append hprefix tailTrace_7461389
  have hstable : (prefixWord ++ tailWord_7461389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7461389).length < 2 ^ (prefixWord ++ tailWord_7461389).sum := by decide
  have hdescent : baseEnd_7461389 < baseStart_7461389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7461389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7461391 : List Nat := [1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 5]
def baseStart_7461391 : Nat := 118140960795 + 7461391 * 2 ^ 59
def prefixEnd_7461391 : Nat := 4983230072969 + 3 ^ 40 * 7461391 * 2
def baseEnd_7461391 : Nat := 3831279934131322007098193

theorem tailTrace_7461391 : CollatzResearch.WordTrace tailWord_7461391 prefixEnd_7461391 3831279934131322007098193 := by
  unfold tailWord_7461391
  simp only [CollatzResearch.WordTrace]
  refine ⟨272139286911662185975376027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181426191274441457316917351 272139286911662185975376027)
  ·
    refine ⟨408208930367493278963064041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272139286911662185975376027 408208930367493278963064041)
    ·
      refine ⟨306156697775619959222298031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408208930367493278963064041 306156697775619959222298031)
      ·
        refine ⟨459235046663429938833447047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306156697775619959222298031 459235046663429938833447047)
        ·
          refine ⟨688852569995144908250170571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459235046663429938833447047 688852569995144908250170571)
          ·
            refine ⟨1033278854992717362375255857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 688852569995144908250170571 1033278854992717362375255857)
            ·
              refine ⟨774959141244538021781441893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1033278854992717362375255857 774959141244538021781441893)
              ·
                refine ⟨145304838983350879084020355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 774959141244538021781441893 145304838983350879084020355)
                ·
                  refine ⟨217957258475026318626030533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145304838983350879084020355 217957258475026318626030533)
                  ·
                    refine ⟨40866985964067434742380725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 217957258475026318626030533 40866985964067434742380725)
                    ·
                      refine ⟨3831279934131322007098193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40866985964067434742380725 3831279934131322007098193)
                      ·
                        rfl

theorem cell23_7461391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 5].length) (baseStart_7461391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7461391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7461391 prefixEnd_7461391 := by exact prefixLift 7461391
  have htrace : WordTrace (prefixWord ++ tailWord_7461391) baseStart_7461391 baseEnd_7461391 := by
    simpa [prefixWord, tailWord_7461391, baseEnd_7461391] using wordTrace_append hprefix tailTrace_7461391
  have hstable : (prefixWord ++ tailWord_7461391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7461391).length < 2 ^ (prefixWord ++ tailWord_7461391).sum := by decide
  have hdescent : baseEnd_7461391 < baseStart_7461391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7461391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7461399 : List Nat := [1, 1, 3, 6, 1, 1, 2, 2, 1, 2, 3]
def baseStart_7461399 : Nat := 118140960795 + 7461399 * 2 ^ 59
def prefixEnd_7461399 : Nat := 4983230072969 + 3 ^ 40 * 7461399 * 2
def baseEnd_7461399 : Nat := 3831284041976557975798157

theorem tailTrace_7461399 : CollatzResearch.WordTrace tailWord_7461399 prefixEnd_7461399 3831284041976557975798157 := by
  unfold tailWord_7461399
  simp only [CollatzResearch.WordTrace]
  refine ⟨272139578695633203341667251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181426385797088802227778167 272139578695633203341667251)
  ·
    refine ⟨408209368043449805012500877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272139578695633203341667251 408209368043449805012500877)
    ·
      refine ⟨153078513016293676879687829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 408209368043449805012500877 153078513016293676879687829)
      ·
        refine ⟨7175555297638766103735367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 153078513016293676879687829 7175555297638766103735367)
        ·
          refine ⟨10763332946458149155603051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7175555297638766103735367 10763332946458149155603051)
          ·
            refine ⟨16144999419687223733404577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10763332946458149155603051 16144999419687223733404577)
            ·
              refine ⟨12108749564765417800053433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16144999419687223733404577 12108749564765417800053433)
              ·
                refine ⟨9081562173574063350040075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12108749564765417800053433 9081562173574063350040075)
                ·
                  refine ⟨13622343260361095025060113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9081562173574063350040075 13622343260361095025060113)
                  ·
                    refine ⟨10216757445270821268795085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13622343260361095025060113 10216757445270821268795085)
                    ·
                      refine ⟨3831284041976557975798157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10216757445270821268795085 3831284041976557975798157)
                      ·
                        rfl

theorem cell23_7461399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_7461399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7461399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7461399 prefixEnd_7461399 := by exact prefixLift 7461399
  have htrace : WordTrace (prefixWord ++ tailWord_7461399) baseStart_7461399 baseEnd_7461399 := by
    simpa [prefixWord, tailWord_7461399, baseEnd_7461399] using wordTrace_append hprefix tailTrace_7461399
  have hstable : (prefixWord ++ tailWord_7461399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7461399).length < 2 ^ (prefixWord ++ tailWord_7461399).sum := by decide
  have hdescent : baseEnd_7461399 < baseStart_7461399 := by decide
  rcases family_descends (prefixWord ++ tailWord_7461399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7461446 : List Nat := [6, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3]
def baseStart_7461446 : Nat := 118140960795 + 7461446 * 2 ^ 59
def prefixEnd_7461446 : Nat := 4983230072969 + 3 ^ 40 * 7461446 * 2
def baseEnd_7461446 : Nat := 3831308175567319291910441

theorem tailTrace_7461446 : CollatzResearch.WordTrace tailWord_7461446 prefixEnd_7461446 3831308175567319291910441 := by
  unfold tailWord_7461446
  simp only [CollatzResearch.WordTrace]
  refine ⟨8504415403951966574019631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 181427528617641953579085461 8504415403951966574019631)
  ·
    refine ⟨12756623105927949861029447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8504415403951966574019631 12756623105927949861029447)
    ·
      refine ⟨19134934658891924791544171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12756623105927949861029447 19134934658891924791544171)
      ·
        refine ⟨28702401988337887187316257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19134934658891924791544171 28702401988337887187316257)
        ·
          refine ⟨21526801491253415390487193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28702401988337887187316257 21526801491253415390487193)
          ·
            refine ⟨16145101118440061542865395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21526801491253415390487193 16145101118440061542865395)
            ·
              refine ⟨24217651677660092314298093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16145101118440061542865395 24217651677660092314298093)
              ·
                refine ⟨9081619379122534617861785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24217651677660092314298093 9081619379122534617861785)
                ·
                  refine ⟨6811214534341900963396339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9081619379122534617861785 6811214534341900963396339)
                  ·
                    refine ⟨10216821801512851445094509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6811214534341900963396339 10216821801512851445094509)
                    ·
                      refine ⟨3831308175567319291910441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10216821801512851445094509 3831308175567319291910441)
                      ·
                        rfl

theorem cell23_7461446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_7461446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7461446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7461446 prefixEnd_7461446 := by exact prefixLift 7461446
  have htrace : WordTrace (prefixWord ++ tailWord_7461446) baseStart_7461446 baseEnd_7461446 := by
    simpa [prefixWord, tailWord_7461446, baseEnd_7461446] using wordTrace_append hprefix tailTrace_7461446
  have hstable : (prefixWord ++ tailWord_7461446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7461446).length < 2 ^ (prefixWord ++ tailWord_7461446).sum := by decide
  have hdescent : baseEnd_7461446 < baseStart_7461446 := by decide
  rcases family_descends (prefixWord ++ tailWord_7461446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7461448 : List Nat := [2, 1, 3, 1, 1, 1, 1, 5, 2, 2, 4]
def baseStart_7461448 : Nat := 118140960795 + 7461448 * 2 ^ 59
def prefixEnd_7461448 : Nat := 4983230072969 + 3 ^ 40 * 7461448 * 2
def baseEnd_7461448 : Nat := 3831309202528628284085431

theorem tailTrace_7461448 : CollatzResearch.WordTrace tailWord_7461448 prefixEnd_7461448 3831309202528628284085431 := by
  unfold tailWord_7461448
  simp only [CollatzResearch.WordTrace]
  refine ⟨136070682936227842355100499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181427577248303789806800665 136070682936227842355100499)
  ·
    refine ⟨204106024404341763532650749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136070682936227842355100499 204106024404341763532650749)
    ·
      refine ⟨76539759151628161324744031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204106024404341763532650749 76539759151628161324744031)
      ·
        refine ⟨114809638727442241987116047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76539759151628161324744031 114809638727442241987116047)
        ·
          refine ⟨172214458091163362980674071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114809638727442241987116047 172214458091163362980674071)
          ·
            refine ⟨258321687136745044471011107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172214458091163362980674071 258321687136745044471011107)
            ·
              refine ⟨387482530705117566706516661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258321687136745044471011107 387482530705117566706516661)
              ·
                refine ⟨36326487253604771878735937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 387482530705117566706516661 36326487253604771878735937)
                ·
                  refine ⟨27244865440203578909051953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36326487253604771878735937 27244865440203578909051953)
                  ·
                    refine ⟨20433649080152684181788965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27244865440203578909051953 20433649080152684181788965)
                    ·
                      refine ⟨3831309202528628284085431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20433649080152684181788965 3831309202528628284085431)
                      ·
                        rfl

theorem cell23_7461448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_7461448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7461448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7461448 prefixEnd_7461448 := by exact prefixLift 7461448
  have htrace : WordTrace (prefixWord ++ tailWord_7461448) baseStart_7461448 baseEnd_7461448 := by
    simpa [prefixWord, tailWord_7461448, baseEnd_7461448] using wordTrace_append hprefix tailTrace_7461448
  have hstable : (prefixWord ++ tailWord_7461448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7461448).length < 2 ^ (prefixWord ++ tailWord_7461448).sum := by decide
  have hdescent : baseEnd_7461448 < baseStart_7461448 := by decide
  rcases family_descends (prefixWord ++ tailWord_7461448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7461458 : List Nat := [3, 2, 2, 1, 2, 1, 2, 1, 9]
def baseStart_7461458 : Nat := 118140960795 + 7461458 * 2 ^ 59
def prefixEnd_7461458 : Nat := 4983230072969 + 3 ^ 40 * 7461458 * 2
def baseEnd_7461458 : Nat := 425701593037241471662265

theorem tailTrace_7461458 : CollatzResearch.WordTrace tailWord_7461458 prefixEnd_7461458 425701593037241471662265 := by
  unfold tailWord_7461458
  simp only [CollatzResearch.WordTrace]
  refine ⟨68035432650604864104516257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181427820401612970945376685 68035432650604864104516257)
  ·
    refine ⟨51026574487953648078387193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68035432650604864104516257 51026574487953648078387193)
    ·
      refine ⟨38269930865965236058790395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51026574487953648078387193 38269930865965236058790395)
      ·
        refine ⟨57404896298947854088185593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38269930865965236058790395 57404896298947854088185593)
        ·
          refine ⟨43053672224210890566139195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57404896298947854088185593 43053672224210890566139195)
          ·
            refine ⟨64580508336316335849208793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43053672224210890566139195 64580508336316335849208793)
            ·
              refine ⟨48435381252237251886906595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64580508336316335849208793 48435381252237251886906595)
              ·
                refine ⟨72653071878355877830359893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48435381252237251886906595 72653071878355877830359893)
                ·
                  refine ⟨425701593037241471662265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 72653071878355877830359893 425701593037241471662265)
                  ·
                    rfl

theorem cell23_7461458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 9].length) (baseStart_7461458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7461458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7461458 prefixEnd_7461458 := by exact prefixLift 7461458
  have htrace : WordTrace (prefixWord ++ tailWord_7461458) baseStart_7461458 baseEnd_7461458 := by
    simpa [prefixWord, tailWord_7461458, baseEnd_7461458] using wordTrace_append hprefix tailTrace_7461458
  have hstable : (prefixWord ++ tailWord_7461458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7461458).length < 2 ^ (prefixWord ++ tailWord_7461458).sum := by decide
  have hdescent : baseEnd_7461458 < baseStart_7461458 := by decide
  rcases family_descends (prefixWord ++ tailWord_7461458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7461475 : List Nat := [1, 1, 1, 5, 1, 2, 2, 5, 5]
def baseStart_7461475 : Nat := 118140960795 + 7461475 * 2 ^ 59
def prefixEnd_7461475 : Nat := 4983230072969 + 3 ^ 40 * 7461475 * 2
def baseEnd_7461475 : Nat := 425702562945144408716423

theorem tailTrace_7461475 : CollatzResearch.WordTrace tailWord_7461475 prefixEnd_7461475 425702562945144408716423 := by
  unfold tailWord_7461475
  simp only [CollatzResearch.WordTrace]
  refine ⟨272142350643357868321433879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181428233762238578880955919 272142350643357868321433879)
  ·
    refine ⟨408213525965036802482150819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272142350643357868321433879 408213525965036802482150819)
    ·
      refine ⟨612320288947555203723226229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408213525965036802482150819 612320288947555203723226229)
      ·
        refine ⟨57405027088833300349052459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 612320288947555203723226229 57405027088833300349052459)
        ·
          refine ⟨86107540633249950523578689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57405027088833300349052459 86107540633249950523578689)
          ·
            refine ⟨64580655474937462892684017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86107540633249950523578689 64580655474937462892684017)
            ·
              refine ⟨48435491606203097169513013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64580655474937462892684017 48435491606203097169513013)
              ·
                refine ⟨4540827338081540359641845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48435491606203097169513013 4540827338081540359641845)
                ·
                  refine ⟨425702562945144408716423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4540827338081540359641845 425702562945144408716423)
                  ·
                    rfl

theorem cell23_7461475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 5, 5].length) (baseStart_7461475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7461475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7461475 prefixEnd_7461475 := by exact prefixLift 7461475
  have htrace : WordTrace (prefixWord ++ tailWord_7461475) baseStart_7461475 baseEnd_7461475 := by
    simpa [prefixWord, tailWord_7461475, baseEnd_7461475] using wordTrace_append hprefix tailTrace_7461475
  have hstable : (prefixWord ++ tailWord_7461475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7461475).length < 2 ^ (prefixWord ++ tailWord_7461475).sum := by decide
  have hdescent : baseEnd_7461475 < baseStart_7461475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7461475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7461486 : List Nat := [4, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2]
def baseStart_7461486 : Nat := 118140960795 + 7461486 * 2 ^ 59
def prefixEnd_7461486 : Nat := 4983230072969 + 3 ^ 40 * 7461486 * 2
def baseEnd_7461486 : Nat := 3831328714793499135410257

theorem tailTrace_7461486 : CollatzResearch.WordTrace tailWord_7461486 prefixEnd_7461486 3831328714793499135410257 := by
  unfold tailWord_7461486
  simp only [CollatzResearch.WordTrace]
  refine ⟨34017843980789752150010539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181428501230878678133389541 34017843980789752150010539)
  ·
    refine ⟨51026765971184628225015809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34017843980789752150010539 51026765971184628225015809)
    ·
      refine ⟨38270074478388471168761857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51026765971184628225015809 38270074478388471168761857)
      ·
        refine ⟨28702555858791353376571393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38270074478388471168761857 28702555858791353376571393)
        ·
          refine ⟨21526916894093515032428545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28702555858791353376571393 21526916894093515032428545)
          ·
            refine ⟨16145187670570136274321409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21526916894093515032428545 16145187670570136274321409)
            ·
              refine ⟨12108890752927602205741057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16145187670570136274321409 12108890752927602205741057)
              ·
                refine ⟨9081668064695701654305793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12108890752927602205741057 9081668064695701654305793)
                ·
                  refine ⟨6811251048521776240729345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9081668064695701654305793 6811251048521776240729345)
                  ·
                    refine ⟨5108438286391332180547009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6811251048521776240729345 5108438286391332180547009)
                    ·
                      refine ⟨3831328714793499135410257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5108438286391332180547009 3831328714793499135410257)
                      ·
                        rfl

theorem cell23_7461486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_7461486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7461486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7461486 prefixEnd_7461486 := by exact prefixLift 7461486
  have htrace : WordTrace (prefixWord ++ tailWord_7461486) baseStart_7461486 baseEnd_7461486 := by
    simpa [prefixWord, tailWord_7461486, baseEnd_7461486] using wordTrace_append hprefix tailTrace_7461486
  have hstable : (prefixWord ++ tailWord_7461486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7461486).length < 2 ^ (prefixWord ++ tailWord_7461486).sum := by decide
  have hdescent : baseEnd_7461486 < baseStart_7461486 := by decide
  rcases family_descends (prefixWord ++ tailWord_7461486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7461495 : List Nat := [1, 1, 3, 1, 1, 3, 3, 1, 2, 5, 2]
def baseStart_7461495 : Nat := 118140960795 + 7461495 * 2 ^ 59
def prefixEnd_7461495 : Nat := 4983230072969 + 3 ^ 40 * 7461495 * 2
def baseEnd_7461495 : Nat := 3831333336119389600197715

theorem tailTrace_7461495 : CollatzResearch.WordTrace tailWord_7461495 prefixEnd_7461495 3831333336119389600197715 := by
  unfold tailWord_7461495
  simp only [CollatzResearch.WordTrace]
  refine ⟨272143080103285411737161939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181428720068856941158107959 272143080103285411737161939)
  ·
    refine ⟨408214620154928117605742909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272143080103285411737161939 408214620154928117605742909)
    ·
      refine ⟨153080482558098044102153591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 408214620154928117605742909 153080482558098044102153591)
      ·
        refine ⟨229620723837147066153230387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153080482558098044102153591 229620723837147066153230387)
        ·
          refine ⟨344431085755720599229845581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229620723837147066153230387 344431085755720599229845581)
          ·
            refine ⟨129161657158395224711192093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 344431085755720599229845581 129161657158395224711192093)
            ·
              refine ⟨48435621434398209266697035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129161657158395224711192093 48435621434398209266697035)
              ·
                refine ⟨72653432151597313900045553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48435621434398209266697035 72653432151597313900045553)
                ·
                  refine ⟨54490074113697985425034165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72653432151597313900045553 54490074113697985425034165)
                  ·
                    refine ⟨5108444448159186133596953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54490074113697985425034165 5108444448159186133596953)
                    ·
                      refine ⟨3831333336119389600197715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5108444448159186133596953 3831333336119389600197715)
                      ·
                        rfl

theorem cell23_7461495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 5, 2].length) (baseStart_7461495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7461495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7461495 prefixEnd_7461495 := by exact prefixLift 7461495
  have htrace : WordTrace (prefixWord ++ tailWord_7461495) baseStart_7461495 baseEnd_7461495 := by
    simpa [prefixWord, tailWord_7461495, baseEnd_7461495] using wordTrace_append hprefix tailTrace_7461495
  have hstable : (prefixWord ++ tailWord_7461495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7461495).length < 2 ^ (prefixWord ++ tailWord_7461495).sum := by decide
  have hdescent : baseEnd_7461495 < baseStart_7461495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7461495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7461522 : List Nat := [3, 2, 3, 1, 2, 1, 3, 1, 2, 5]
def baseStart_7461522 : Nat := 118140960795 + 7461522 * 2 ^ 59
def prefixEnd_7461522 : Nat := 4983230072969 + 3 ^ 40 * 7461522 * 2
def baseEnd_7461522 : Nat := 1277115733365686998186697

theorem tailTrace_7461522 : CollatzResearch.WordTrace tailWord_7461522 prefixEnd_7461522 1277115733365686998186697 := by
  unfold tailWord_7461522
  simp only [CollatzResearch.WordTrace]
  refine ⟨68036016218546898837098705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181429376582791730232263213 68036016218546898837098705)
  ·
    refine ⟨51027012163910174127824029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68036016218546898837098705 51027012163910174127824029)
    ·
      refine ⟨19135129561466315297934011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51027012163910174127824029 19135129561466315297934011)
      ·
        refine ⟨28702694342199472946901017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19135129561466315297934011 28702694342199472946901017)
        ·
          refine ⟨21527020756649604710175763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28702694342199472946901017 21527020756649604710175763)
          ·
            refine ⟨32290531134974407065263645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21527020756649604710175763 32290531134974407065263645)
            ·
              refine ⟨12108949175615402649473867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32290531134974407065263645 12108949175615402649473867)
              ·
                refine ⟨18163423763423103974210801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12108949175615402649473867 18163423763423103974210801)
                ·
                  refine ⟨13622567822567327980658101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18163423763423103974210801 13622567822567327980658101)
                  ·
                    refine ⟨1277115733365686998186697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13622567822567327980658101 1277115733365686998186697)
                    ·
                      rfl

theorem cell23_7461522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_7461522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7461522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7461522 prefixEnd_7461522 := by exact prefixLift 7461522
  have htrace : WordTrace (prefixWord ++ tailWord_7461522) baseStart_7461522 baseEnd_7461522 := by
    simpa [prefixWord, tailWord_7461522, baseEnd_7461522] using wordTrace_append hprefix tailTrace_7461522
  have hstable : (prefixWord ++ tailWord_7461522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7461522).length < 2 ^ (prefixWord ++ tailWord_7461522).sum := by decide
  have hdescent : baseEnd_7461522 < baseStart_7461522 := by decide
  rcases family_descends (prefixWord ++ tailWord_7461522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7461609 : List Nat := [1, 2, 1, 1, 1, 2, 4, 6, 1, 1, 3]
def baseStart_7461609 : Nat := 118140960795 + 7461609 * 2 ^ 59
def prefixEnd_7461609 : Nat := 4983230072969 + 3 ^ 40 * 7461609 * 2
def baseEnd_7461609 : Nat := 3831391872914002154172191

theorem tailTrace_7461609 : CollatzResearch.WordTrace tailWord_7461609 prefixEnd_7461609 3831391872914002154172191 := by
  unfold tailWord_7461609
  simp only [CollatzResearch.WordTrace]
  refine ⟨272147238024872409206811881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181431492016581606137874587 272147238024872409206811881)
  ·
    refine ⟨204110428518654306905108911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272147238024872409206811881 204110428518654306905108911)
    ·
      refine ⟨306165642777981460357663367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204110428518654306905108911 306165642777981460357663367)
      ·
        refine ⟨459248464166972190536495051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306165642777981460357663367 459248464166972190536495051)
        ·
          refine ⟨688872696250458285804742577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459248464166972190536495051 688872696250458285804742577)
          ·
            refine ⟨516654522187843714353556933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 688872696250458285804742577 516654522187843714353556933)
            ·
              refine ⟨96872722910220696441291925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 516654522187843714353556933 96872722910220696441291925)
              ·
                refine ⟨4540908886416595145685559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 96872722910220696441291925 4540908886416595145685559)
                ·
                  refine ⟨6811363329624892718528339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4540908886416595145685559 6811363329624892718528339)
                  ·
                    refine ⟨10217044994437339077792509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6811363329624892718528339 10217044994437339077792509)
                    ·
                      refine ⟨3831391872914002154172191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10217044994437339077792509 3831391872914002154172191)
                      ·
                        rfl

theorem cell23_7461609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 6, 1, 1, 3].length) (baseStart_7461609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7461609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7461609 prefixEnd_7461609 := by exact prefixLift 7461609
  have htrace : WordTrace (prefixWord ++ tailWord_7461609) baseStart_7461609 baseEnd_7461609 := by
    simpa [prefixWord, tailWord_7461609, baseEnd_7461609] using wordTrace_append hprefix tailTrace_7461609
  have hstable : (prefixWord ++ tailWord_7461609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7461609).length < 2 ^ (prefixWord ++ tailWord_7461609).sum := by decide
  have hdescent : baseEnd_7461609 < baseStart_7461609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7461609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7461655 : List Nat := [1, 1, 3, 4, 3, 11]
def baseStart_7461655 : Nat := 118140960795 + 7461655 * 2 ^ 59
def prefixEnd_7461655 : Nat := 4983230072969 + 3 ^ 40 * 7461655 * 2
def baseEnd_7461655 : Nat := 15767141946601271498753

theorem tailTrace_7461655 : CollatzResearch.WordTrace tailWord_7461655 prefixEnd_7461655 15767141946601271498753 := by
  unfold tailWord_7461655
  simp only [CollatzResearch.WordTrace]
  refine ⟨272148915782705759062986419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181432610521803839375324279 272148915782705759062986419)
  ·
    refine ⟨408223373674058638594479629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272148915782705759062986419 408223373674058638594479629)
    ·
      refine ⟨153083765127771989472929861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 408223373674058638594479629 153083765127771989472929861)
      ·
        refine ⟨28703205961457248026174349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153083765127771989472929861 28703205961457248026174349)
        ·
          refine ⟨10763702235546468009815381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28703205961457248026174349 10763702235546468009815381)
          ·
            refine ⟨15767141946601271498753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10763702235546468009815381 15767141946601271498753)
            ·
              rfl

theorem cell23_7461655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 11].length) (baseStart_7461655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7461655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7461655 prefixEnd_7461655 := by exact prefixLift 7461655
  have htrace : WordTrace (prefixWord ++ tailWord_7461655) baseStart_7461655 baseEnd_7461655 := by
    simpa [prefixWord, tailWord_7461655, baseEnd_7461655] using wordTrace_append hprefix tailTrace_7461655
  have hstable : (prefixWord ++ tailWord_7461655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7461655).length < 2 ^ (prefixWord ++ tailWord_7461655).sum := by decide
  have hdescent : baseEnd_7461655 < baseStart_7461655 := by decide
  rcases family_descends (prefixWord ++ tailWord_7461655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7461700 : List Nat := [2, 3, 4, 2, 1, 2, 2, 1, 1, 1, 4]
def baseStart_7461700 : Nat := 118140960795 + 7461700 * 2 ^ 59
def prefixEnd_7461700 : Nat := 4983230072969 + 3 ^ 40 * 7461700 * 2
def baseEnd_7461700 : Nat := 3831438599653561298134273

theorem tailTrace_7461700 : CollatzResearch.WordTrace tailWord_7461700 prefixEnd_7461700 3831438599653561298134273 := by
  unfold tailWord_7461700
  simp only [CollatzResearch.WordTrace]
  refine ⟨136075278533771365874187277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181433704711695154498916369 136075278533771365874187277)
  ·
    refine ⟨51028229450164262202820229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136075278533771365874187277 51028229450164262202820229)
    ·
      refine ⟨9567793021905799163028793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51028229450164262202820229 9567793021905799163028793)
      ·
        refine ⟨7175844766429349372271595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9567793021905799163028793 7175844766429349372271595)
        ·
          refine ⟨10763767149644024058407393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7175844766429349372271595 10763767149644024058407393)
          ·
            refine ⟨8072825362233018043805545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10763767149644024058407393 8072825362233018043805545)
            ·
              refine ⟨6054619021674763532854159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8072825362233018043805545 6054619021674763532854159)
              ·
                refine ⟨9081928532512145299281239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6054619021674763532854159 9081928532512145299281239)
                ·
                  refine ⟨13622892798768217948921859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9081928532512145299281239 13622892798768217948921859)
                  ·
                    refine ⟨20434339198152326923382789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13622892798768217948921859 20434339198152326923382789)
                    ·
                      refine ⟨3831438599653561298134273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20434339198152326923382789 3831438599653561298134273)
                      ·
                        rfl

theorem cell23_7461700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_7461700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7461700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7461700 prefixEnd_7461700 := by exact prefixLift 7461700
  have htrace : WordTrace (prefixWord ++ tailWord_7461700) baseStart_7461700 baseEnd_7461700 := by
    simpa [prefixWord, tailWord_7461700, baseEnd_7461700] using wordTrace_append hprefix tailTrace_7461700
  have hstable : (prefixWord ++ tailWord_7461700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7461700).length < 2 ^ (prefixWord ++ tailWord_7461700).sum := by decide
  have hdescent : baseEnd_7461700 < baseStart_7461700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7461700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7461716 : List Nat := [2, 4, 1, 1, 4, 1, 1, 1, 4, 1, 3]
def baseStart_7461716 : Nat := 118140960795 + 7461716 * 2 ^ 59
def prefixEnd_7461716 : Nat := 4983230072969 + 3 ^ 40 * 7461716 * 2
def baseEnd_7461716 : Nat := 3831446815344033235534199

theorem tailTrace_7461716 : CollatzResearch.WordTrace tailWord_7461716 prefixEnd_7461716 3831446815344033235534199 := by
  unfold tailWord_7461716
  simp only [CollatzResearch.WordTrace]
  refine ⟨136075570317742383240478501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181434093756989844320638001 136075570317742383240478501)
  ·
    refine ⟨25514169434576696857589719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136075570317742383240478501 25514169434576696857589719)
    ·
      refine ⟨38271254151865045286384579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25514169434576696857589719 38271254151865045286384579)
      ·
        refine ⟨57406881227797567929576869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38271254151865045286384579 57406881227797567929576869)
        ·
          refine ⟨10763790230212043986795663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57406881227797567929576869 10763790230212043986795663)
          ·
            refine ⟨16145685345318065980193495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10763790230212043986795663 16145685345318065980193495)
            ·
              refine ⟨24218528017977098970290243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16145685345318065980193495 24218528017977098970290243)
              ·
                refine ⟨36327792026965648455435365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24218528017977098970290243 36327792026965648455435365)
                ·
                  refine ⟨6811461005056059085394131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36327792026965648455435365 6811461005056059085394131)
                  ·
                    refine ⟨10217191507584088628091197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6811461005056059085394131 10217191507584088628091197)
                    ·
                      refine ⟨3831446815344033235534199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10217191507584088628091197 3831446815344033235534199)
                      ·
                        rfl

theorem cell23_7461716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_7461716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7461716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7461716 prefixEnd_7461716 := by exact prefixLift 7461716
  have htrace : WordTrace (prefixWord ++ tailWord_7461716) baseStart_7461716 baseEnd_7461716 := by
    simpa [prefixWord, tailWord_7461716, baseEnd_7461716] using wordTrace_append hprefix tailTrace_7461716
  have hstable : (prefixWord ++ tailWord_7461716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7461716).length < 2 ^ (prefixWord ++ tailWord_7461716).sum := by decide
  have hdescent : baseEnd_7461716 < baseStart_7461716 := by decide
  rcases family_descends (prefixWord ++ tailWord_7461716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7461732 : List Nat := [2, 3, 1, 1, 4, 1, 2, 1, 2, 6]
def baseStart_7461732 : Nat := 118140960795 + 7461732 * 2 ^ 59
def prefixEnd_7461732 : Nat := 4983230072969 + 3 ^ 40 * 7461732 * 2
def baseEnd_7461732 : Nat := 1277151677011501724311375

theorem tailTrace_7461732 : CollatzResearch.WordTrace tailWord_7461732 prefixEnd_7461732 1277151677011501724311375 := by
  unfold tailWord_7461732
  simp only [CollatzResearch.WordTrace]
  refine ⟨136075862101713400606769725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181434482802284534142359633 136075862101713400606769725)
  ·
    refine ⟨51028448288142525227538647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136075862101713400606769725 51028448288142525227538647)
    ·
      refine ⟨76542672432213787841307971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51028448288142525227538647 76542672432213787841307971)
      ·
        refine ⟨114814008648320681761961957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76542672432213787841307971 114814008648320681761961957)
        ·
          refine ⟨21527626621560127830367867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114814008648320681761961957 21527626621560127830367867)
          ·
            refine ⟨32291439932340191745551801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21527626621560127830367867 32291439932340191745551801)
            ·
              refine ⟨24218579949255143809163851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32291439932340191745551801 24218579949255143809163851)
              ·
                refine ⟨36327869923882715713745777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24218579949255143809163851 36327869923882715713745777)
                ·
                  refine ⟨27245902442912036785309333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36327869923882715713745777 27245902442912036785309333)
                  ·
                    refine ⟨1277151677011501724311375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27245902442912036785309333 1277151677011501724311375)
                    ·
                      rfl

theorem cell23_7461732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 2, 6].length) (baseStart_7461732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7461732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7461732 prefixEnd_7461732 := by exact prefixLift 7461732
  have htrace : WordTrace (prefixWord ++ tailWord_7461732) baseStart_7461732 baseEnd_7461732 := by
    simpa [prefixWord, tailWord_7461732, baseEnd_7461732] using wordTrace_append hprefix tailTrace_7461732
  have hstable : (prefixWord ++ tailWord_7461732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7461732).length < 2 ^ (prefixWord ++ tailWord_7461732).sum := by decide
  have hdescent : baseEnd_7461732 < baseStart_7461732 := by decide
  rcases family_descends (prefixWord ++ tailWord_7461732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7461739 : List Nat := [1, 1, 1, 1, 2, 2, 7, 1, 1, 4, 2]
def baseStart_7461739 : Nat := 118140960795 + 7461739 * 2 ^ 59
def prefixEnd_7461739 : Nat := 4983230072969 + 3 ^ 40 * 7461739 * 2
def baseEnd_7461739 : Nat := 3831458625399086645546593

theorem tailTrace_7461739 : CollatzResearch.WordTrace tailWord_7461739 prefixEnd_7461739 3831458625399086645546593 := by
  unfold tailWord_7461739
  simp only [CollatzResearch.WordTrace]
  refine ⟨272151979514401441409044271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181434653009600960939362847 272151979514401441409044271)
  ·
    refine ⟨408227969271602162113566407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272151979514401441409044271 408227969271602162113566407)
    ·
      refine ⟨612341953907403243170349611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408227969271602162113566407 612341953907403243170349611)
      ·
        refine ⟨918512930861104864755524417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 612341953907403243170349611 918512930861104864755524417)
        ·
          refine ⟨688884698145828648566643313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 918512930861104864755524417 688884698145828648566643313)
          ·
            refine ⟨516663523609371486424982485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 688884698145828648566643313 516663523609371486424982485)
            ·
              refine ⟨12109301334594644213085527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 516663523609371486424982485 12109301334594644213085527)
              ·
                refine ⟨18163952001891966319628291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12109301334594644213085527 18163952001891966319628291)
                ·
                  refine ⟨27245928002837949479442437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18163952001891966319628291 27245928002837949479442437)
                  ·
                    refine ⟨5108611500532115527395457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27245928002837949479442437 5108611500532115527395457)
                    ·
                      refine ⟨3831458625399086645546593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5108611500532115527395457 3831458625399086645546593)
                      ·
                        rfl

theorem cell23_7461739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 4, 2].length) (baseStart_7461739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7461739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7461739 prefixEnd_7461739 := by exact prefixLift 7461739
  have htrace : WordTrace (prefixWord ++ tailWord_7461739) baseStart_7461739 baseEnd_7461739 := by
    simpa [prefixWord, tailWord_7461739, baseEnd_7461739] using wordTrace_append hprefix tailTrace_7461739
  have hstable : (prefixWord ++ tailWord_7461739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7461739).length < 2 ^ (prefixWord ++ tailWord_7461739).sum := by decide
  have hdescent : baseEnd_7461739 < baseStart_7461739 := by decide
  rcases family_descends (prefixWord ++ tailWord_7461739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7461772 : List Nat := [2, 2, 1, 2, 1, 2, 2, 1, 4, 3, 3]
def baseStart_7461772 : Nat := 118140960795 + 7461772 * 2 ^ 59
def prefixEnd_7461772 : Nat := 4983230072969 + 3 ^ 40 * 7461772 * 2
def baseEnd_7461772 : Nat := 3831475570260685016433941

theorem tailTrace_7461772 : CollatzResearch.WordTrace tailWord_7461772 prefixEnd_7461772 3831475570260685016433941 := by
  unfold tailWord_7461772
  simp only [CollatzResearch.WordTrace]
  refine ⟨136076591561640944022497785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181435455415521258696663713 136076591561640944022497785)
  ·
    refine ⟨102057443671230708016873339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136076591561640944022497785 102057443671230708016873339)
    ·
      refine ⟨153086165506846062025310009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102057443671230708016873339 153086165506846062025310009)
      ·
        refine ⟨114814624130134546518982507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153086165506846062025310009 114814624130134546518982507)
        ·
          refine ⟨172221936195201819778473761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114814624130134546518982507 172221936195201819778473761)
          ·
            refine ⟨129166452146401364833855321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172221936195201819778473761 129166452146401364833855321)
            ·
              refine ⟨96874839109801023625391491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129166452146401364833855321 96874839109801023625391491)
              ·
                refine ⟨145312258664701535438087237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96874839109801023625391491 145312258664701535438087237)
                ·
                  refine ⟨27246048499631537894641357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145312258664701535438087237 27246048499631537894641357)
                  ·
                    refine ⟨10217268187361826710490509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27246048499631537894641357 10217268187361826710490509)
                    ·
                      refine ⟨3831475570260685016433941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10217268187361826710490509 3831475570260685016433941)
                      ·
                        rfl

theorem cell23_7461772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 4, 3, 3].length) (baseStart_7461772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7461772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7461772 prefixEnd_7461772 := by exact prefixLift 7461772
  have htrace : WordTrace (prefixWord ++ tailWord_7461772) baseStart_7461772 baseEnd_7461772 := by
    simpa [prefixWord, tailWord_7461772, baseEnd_7461772] using wordTrace_append hprefix tailTrace_7461772
  have hstable : (prefixWord ++ tailWord_7461772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7461772).length < 2 ^ (prefixWord ++ tailWord_7461772).sum := by decide
  have hdescent : baseEnd_7461772 < baseStart_7461772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7461772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7461866 : List Nat := [3, 1, 3, 1, 2, 2, 3, 1, 2, 2, 3]
def baseStart_7461866 : Nat := 118140960795 + 7461866 * 2 ^ 59
def prefixEnd_7461866 : Nat := 4983230072969 + 3 ^ 40 * 7461866 * 2
def baseEnd_7461866 : Nat := 3831523837442207648658509

theorem tailTrace_7461866 : CollatzResearch.WordTrace tailWord_7461866 prefixEnd_7461866 3831523837442207648658509 := by
  unfold tailWord_7461866
  simp only [CollatzResearch.WordTrace]
  refine ⟨68039152896235335524729363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181437741056627561399278301 68039152896235335524729363)
  ·
    refine ⟨102058729344353003287094045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68039152896235335524729363 102058729344353003287094045)
    ·
      refine ⟨38272023504132376232660267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102058729344353003287094045 38272023504132376232660267)
      ·
        refine ⟨57408035256198564348990401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38272023504132376232660267 57408035256198564348990401)
        ·
          refine ⟨43056026442148923261742801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57408035256198564348990401 43056026442148923261742801)
          ·
            refine ⟨32292019831611692446307101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43056026442148923261742801 32292019831611692446307101)
            ·
              refine ⟨12109507436854384667365163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32292019831611692446307101 12109507436854384667365163)
              ·
                refine ⟨18164261155281577001047745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12109507436854384667365163 18164261155281577001047745)
                ·
                  refine ⟨13623195866461182750785809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18164261155281577001047745 13623195866461182750785809)
                  ·
                    refine ⟨10217396899845887063089357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13623195866461182750785809 10217396899845887063089357)
                    ·
                      refine ⟨3831523837442207648658509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10217396899845887063089357 3831523837442207648658509)
                      ·
                        rfl

theorem cell23_7461866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_7461866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7461866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7461866 prefixEnd_7461866 := by exact prefixLift 7461866
  have htrace : WordTrace (prefixWord ++ tailWord_7461866) baseStart_7461866 baseEnd_7461866 := by
    simpa [prefixWord, tailWord_7461866, baseEnd_7461866] using wordTrace_append hprefix tailTrace_7461866
  have hstable : (prefixWord ++ tailWord_7461866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7461866).length < 2 ^ (prefixWord ++ tailWord_7461866).sum := by decide
  have hdescent : baseEnd_7461866 < baseStart_7461866 := by decide
  rcases family_descends (prefixWord ++ tailWord_7461866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7461873 : List Nat := [1, 2, 2, 2, 4, 2, 2, 3, 1, 4]
def baseStart_7461873 : Nat := 118140960795 + 7461873 * 2 ^ 59
def prefixEnd_7461873 : Nat := 4983230072969 + 3 ^ 40 * 7461873 * 2
def baseEnd_7461873 : Nat := 1277175810602263040423659

theorem tailTrace_7461873 : CollatzResearch.WordTrace tailWord_7461873 prefixEnd_7461873 1277175810602263040423659 := by
  unfold tailWord_7461873
  simp only [CollatzResearch.WordTrace]
  refine ⟨272156866895915982294422273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181437911263943988196281515 272156866895915982294422273)
  ·
    refine ⟨204117650171936986720816705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272156866895915982294422273 204117650171936986720816705)
    ·
      refine ⟨153088237628952740040612529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204117650171936986720816705 153088237628952740040612529)
      ·
        refine ⟨114816178221714555030459397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153088237628952740040612529 114816178221714555030459397)
        ·
          refine ⟨21528033416571479068211137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114816178221714555030459397 21528033416571479068211137)
          ·
            refine ⟨16146025062428609301158353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21528033416571479068211137 16146025062428609301158353)
            ·
              refine ⟨12109518796821456975868765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16146025062428609301158353 12109518796821456975868765)
              ·
                refine ⟨4541069548808046365950787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12109518796821456975868765 4541069548808046365950787)
                ·
                  refine ⟨6811604323212069548926181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4541069548808046365950787 6811604323212069548926181)
                  ·
                    refine ⟨1277175810602263040423659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6811604323212069548926181 1277175810602263040423659)
                    ·
                      rfl

theorem cell23_7461873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 3, 1, 4].length) (baseStart_7461873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7461873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7461873 prefixEnd_7461873 := by exact prefixLift 7461873
  have htrace : WordTrace (prefixWord ++ tailWord_7461873) baseStart_7461873 baseEnd_7461873 := by
    simpa [prefixWord, tailWord_7461873, baseEnd_7461873] using wordTrace_append hprefix tailTrace_7461873
  have hstable : (prefixWord ++ tailWord_7461873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7461873).length < 2 ^ (prefixWord ++ tailWord_7461873).sum := by decide
  have hdescent : baseEnd_7461873 < baseStart_7461873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7461873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7461886 : List Nat := [4, 2, 2, 2, 2, 1, 1, 1, 8]
def baseStart_7461886 : Nat := 118140960795 + 7461886 * 2 ^ 59
def prefixEnd_7461886 : Nat := 4983230072969 + 3 ^ 40 * 7461886 * 2
def baseEnd_7461886 : Nat := 425726011895033063378713

theorem tailTrace_7461886 : CollatzResearch.WordTrace tailWord_7461886 prefixEnd_7461886 425726011895033063378713 := by
  unfold tailWord_7461886
  simp only [CollatzResearch.WordTrace]
  refine ⟨34019667630608610689330689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181438227363245923676430341 34019667630608610689330689)
  ·
    refine ⟨25514750722956458016998017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34019667630608610689330689 25514750722956458016998017)
    ·
      refine ⟨19136063042217343512748513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25514750722956458016998017 19136063042217343512748513)
      ·
        refine ⟨14352047281663007634561385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19136063042217343512748513 14352047281663007634561385)
        ·
          refine ⟨10764035461247255725921039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14352047281663007634561385 10764035461247255725921039)
          ·
            refine ⟨16146053191870883588881559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10764035461247255725921039 16146053191870883588881559)
            ·
              refine ⟨24219079787806325383322339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16146053191870883588881559 24219079787806325383322339)
              ·
                refine ⟨36328619681709488074983509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24219079787806325383322339 36328619681709488074983509)
                ·
                  refine ⟨425726011895033063378713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36328619681709488074983509 425726011895033063378713)
                  ·
                    rfl

theorem cell23_7461886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 8].length) (baseStart_7461886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7461886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7461886 prefixEnd_7461886 := by exact prefixLift 7461886
  have htrace : WordTrace (prefixWord ++ tailWord_7461886) baseStart_7461886 baseEnd_7461886 := by
    simpa [prefixWord, tailWord_7461886, baseEnd_7461886] using wordTrace_append hprefix tailTrace_7461886
  have hstable : (prefixWord ++ tailWord_7461886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7461886).length < 2 ^ (prefixWord ++ tailWord_7461886).sum := by decide
  have hdescent : baseEnd_7461886 < baseStart_7461886 := by decide
  rcases family_descends (prefixWord ++ tailWord_7461886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7461890 : List Nat := [3, 4, 1, 3, 1, 1, 2, 1, 3, 4]
def baseStart_7461890 : Nat := 118140960795 + 7461890 * 2 ^ 59
def prefixEnd_7461890 : Nat := 4983230072969 + 3 ^ 40 * 7461890 * 2
def baseEnd_7461890 : Nat := 1277178720325971851586133

theorem tailTrace_7461890 : CollatzResearch.WordTrace tailWord_7461890 prefixEnd_7461890 1277178720325971851586133 := by
  unfold tailWord_7461890
  simp only [CollatzResearch.WordTrace]
  refine ⟨68039371734213598549447781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181438324624569596131860749 68039371734213598549447781)
  ·
    refine ⟨12757382200165049728021459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68039371734213598549447781 12757382200165049728021459)
    ·
      refine ⟨19136073300247574592032189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12757382200165049728021459 19136073300247574592032189)
      ·
        refine ⟨7176027487592840472012071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19136073300247574592032189 7176027487592840472012071)
        ·
          refine ⟨10764041231389260708018107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7176027487592840472012071 10764041231389260708018107)
          ·
            refine ⟨16146061847083891062027161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10764041231389260708018107 16146061847083891062027161)
            ·
              refine ⟨12109546385312918296520371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16146061847083891062027161 12109546385312918296520371)
              ·
                refine ⟨18164319577969377444780557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12109546385312918296520371 18164319577969377444780557)
                ·
                  refine ⟨6811619841738516541792709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18164319577969377444780557 6811619841738516541792709)
                  ·
                    refine ⟨1277178720325971851586133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6811619841738516541792709 1277178720325971851586133)
                    ·
                      rfl

theorem cell23_7461890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_7461890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7461890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7461890 prefixEnd_7461890 := by exact prefixLift 7461890
  have htrace : WordTrace (prefixWord ++ tailWord_7461890) baseStart_7461890 baseEnd_7461890 := by
    simpa [prefixWord, tailWord_7461890, baseEnd_7461890] using wordTrace_append hprefix tailTrace_7461890
  have hstable : (prefixWord ++ tailWord_7461890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7461890).length < 2 ^ (prefixWord ++ tailWord_7461890).sum := by decide
  have hdescent : baseEnd_7461890 < baseStart_7461890 := by decide
  rcases family_descends (prefixWord ++ tailWord_7461890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7461896 : List Nat := [2, 1, 3, 2, 1, 3, 1, 3, 3, 1, 3]
def baseStart_7461896 : Nat := 118140960795 + 7461896 * 2 ^ 59
def prefixEnd_7461896 : Nat := 4983230072969 + 3 ^ 40 * 7461896 * 2
def baseEnd_7461896 : Nat := 3831539241861842531283371

theorem tailTrace_7461896 : CollatzResearch.WordTrace tailWord_7461896 prefixEnd_7461896 3831539241861842531283371 := by
  unfold tailWord_7461896
  simp only [CollatzResearch.WordTrace]
  refine ⟨136078852887416328611254771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181438470516555104815006361 136078852887416328611254771)
  ·
    refine ⟨204118279331124492916882157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136078852887416328611254771 204118279331124492916882157)
    ·
      refine ⟨76544354749171684843830809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204118279331124492916882157 76544354749171684843830809)
      ·
        refine ⟨57408266061878763632873107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76544354749171684843830809 57408266061878763632873107)
        ·
          refine ⟨86112399092818145449309661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57408266061878763632873107 86112399092818145449309661)
          ·
            refine ⟨32292149659806804543491123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86112399092818145449309661 32292149659806804543491123)
            ·
              refine ⟨48438224489710206815236685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32292149659806804543491123 48438224489710206815236685)
              ·
                refine ⟨18164334183641327555713757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48438224489710206815236685 18164334183641327555713757)
                ·
                  refine ⟨6811625318865497833392659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18164334183641327555713757 6811625318865497833392659)
                  ·
                    refine ⟨10217437978298246750088989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6811625318865497833392659 10217437978298246750088989)
                    ·
                      refine ⟨3831539241861842531283371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10217437978298246750088989 3831539241861842531283371)
                      ·
                        rfl

theorem cell23_7461896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_7461896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7461896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7461896 prefixEnd_7461896 := by exact prefixLift 7461896
  have htrace : WordTrace (prefixWord ++ tailWord_7461896) baseStart_7461896 baseEnd_7461896 := by
    simpa [prefixWord, tailWord_7461896, baseEnd_7461896] using wordTrace_append hprefix tailTrace_7461896
  have hstable : (prefixWord ++ tailWord_7461896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7461896).length < 2 ^ (prefixWord ++ tailWord_7461896).sum := by decide
  have hdescent : baseEnd_7461896 < baseStart_7461896 := by decide
  rcases family_descends (prefixWord ++ tailWord_7461896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7461939 : List Nat := [1, 1, 1, 2, 4, 1, 1, 2, 5, 2, 3]
def baseStart_7461939 : Nat := 118140960795 + 7461939 * 2 ^ 59
def prefixEnd_7461939 : Nat := 4983230072969 + 3 ^ 40 * 7461939 * 2
def baseEnd_7461939 : Nat := 3831561321529985863045673

theorem tailTrace_7461939 : CollatzResearch.WordTrace tailWord_7461939 prefixEnd_7461939 3831561321529985863045673 := by
  unfold tailWord_7461939
  simp only [CollatzResearch.WordTrace]
  refine ⟨272159274113676875566324871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181439516075784583710883247 272159274113676875566324871)
  ·
    refine ⟨408238911170515313349487307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272159274113676875566324871 408238911170515313349487307)
    ·
      refine ⟨612358366755772970024230961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408238911170515313349487307 612358366755772970024230961)
      ·
        refine ⟨459268775066829727518173221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 612358366755772970024230961 459268775066829727518173221)
        ·
          refine ⟨86112895325030573909657479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 459268775066829727518173221 86112895325030573909657479)
          ·
            refine ⟨129169342987545860864486219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86112895325030573909657479 129169342987545860864486219)
            ·
              refine ⟨193754014481318791296729329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129169342987545860864486219 193754014481318791296729329)
              ·
                refine ⟨145315510860989093472546997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193754014481318791296729329 145315510860989093472546997)
                ·
                  refine ⟨13623329143217727513051281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 145315510860989093472546997 13623329143217727513051281)
                  ·
                    refine ⟨10217496857413295634788461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13623329143217727513051281 10217496857413295634788461)
                    ·
                      refine ⟨3831561321529985863045673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10217496857413295634788461 3831561321529985863045673)
                      ·
                        rfl

theorem cell23_7461939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 5, 2, 3].length) (baseStart_7461939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7461939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7461939 prefixEnd_7461939 := by exact prefixLift 7461939
  have htrace : WordTrace (prefixWord ++ tailWord_7461939) baseStart_7461939 baseEnd_7461939 := by
    simpa [prefixWord, tailWord_7461939, baseEnd_7461939] using wordTrace_append hprefix tailTrace_7461939
  have hstable : (prefixWord ++ tailWord_7461939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7461939).length < 2 ^ (prefixWord ++ tailWord_7461939).sum := by decide
  have hdescent : baseEnd_7461939 < baseStart_7461939 := by decide
  rcases family_descends (prefixWord ++ tailWord_7461939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7461940 : List Nat := [2, 5, 1, 2, 1, 2, 1, 2, 2, 3, 2]
def baseStart_7461940 : Nat := 118140960795 + 7461940 * 2 ^ 59
def prefixEnd_7461940 : Nat := 4983230072969 + 3 ^ 40 * 7461940 * 2
def baseEnd_7461940 : Nat := 3831561835010640359133169

theorem tailTrace_7461940 : CollatzResearch.WordTrace tailWord_7461940 prefixEnd_7461940 3831561835010640359133169 := by
  unfold tailWord_7461940
  simp only [CollatzResearch.WordTrace]
  refine ⟨136079655293336626368555637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181439540391115501824740849 136079655293336626368555637)
  ·
    refine ⟨12757467683750308722052091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 136079655293336626368555637 12757467683750308722052091)
    ·
      refine ⟨19136201525625463083078137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12757467683750308722052091 19136201525625463083078137)
      ·
        refine ⟨14352151144219097312308603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19136201525625463083078137 14352151144219097312308603)
        ·
          refine ⟨21528226716328645968462905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14352151144219097312308603 21528226716328645968462905)
          ·
            refine ⟨16146170037246484476347179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21528226716328645968462905 16146170037246484476347179)
            ·
              refine ⟨24219255055869726714520769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16146170037246484476347179 24219255055869726714520769)
              ·
                refine ⟨18164441291902295035890577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24219255055869726714520769 18164441291902295035890577)
                ·
                  refine ⟨13623330968926721276917933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18164441291902295035890577 13623330968926721276917933)
                  ·
                    refine ⟨5108749113347520478844225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13623330968926721276917933 5108749113347520478844225)
                    ·
                      refine ⟨3831561835010640359133169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5108749113347520478844225 3831561835010640359133169)
                      ·
                        rfl

theorem cell23_7461940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_7461940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7461940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7461940 prefixEnd_7461940 := by exact prefixLift 7461940
  have htrace : WordTrace (prefixWord ++ tailWord_7461940) baseStart_7461940 baseEnd_7461940 := by
    simpa [prefixWord, tailWord_7461940, baseEnd_7461940] using wordTrace_append hprefix tailTrace_7461940
  have hstable : (prefixWord ++ tailWord_7461940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7461940).length < 2 ^ (prefixWord ++ tailWord_7461940).sum := by decide
  have hdescent : baseEnd_7461940 < baseStart_7461940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7461940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7461949 : List Nat := [1, 4, 1, 3, 1, 2, 1, 2, 1, 1, 6]
def baseStart_7461949 : Nat := 118140960795 + 7461949 * 2 ^ 59
def prefixEnd_7461949 : Nat := 4983230072969 + 3 ^ 40 * 7461949 * 2
def baseEnd_7461949 : Nat := 3831566456336530823920627

theorem tailTrace_7461949 : CollatzResearch.WordTrace tailWord_7461949 prefixEnd_7461949 3831566456336530823920627 := by
  unfold tailWord_7461949
  simp only [CollatzResearch.WordTrace]
  refine ⟨272159638843640647274188901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181439759229093764849459267 272159638843640647274188901)
  ·
    refine ⟨51029932283182621363910419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 272159638843640647274188901 51029932283182621363910419)
    ·
      refine ⟨76544898424773932045865629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51029932283182621363910419 76544898424773932045865629)
      ·
        refine ⟨28704336909290224517199611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76544898424773932045865629 28704336909290224517199611)
        ·
          refine ⟨43056505363935336775799417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28704336909290224517199611 43056505363935336775799417)
          ·
            refine ⟨32292379022951502581849563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43056505363935336775799417 32292379022951502581849563)
            ·
              refine ⟨48438568534427253872774345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32292379022951502581849563 48438568534427253872774345)
              ·
                refine ⟨36328926400820440404580759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48438568534427253872774345 36328926400820440404580759)
                ·
                  refine ⟨54493389601230660606871139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36328926400820440404580759 54493389601230660606871139)
                  ·
                    refine ⟨81740084401845990910306709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54493389601230660606871139 81740084401845990910306709)
                    ·
                      refine ⟨3831566456336530823920627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81740084401845990910306709 3831566456336530823920627)
                      ·
                        rfl

theorem cell23_7461949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_7461949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7461949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7461949 prefixEnd_7461949 := by exact prefixLift 7461949
  have htrace : WordTrace (prefixWord ++ tailWord_7461949) baseStart_7461949 baseEnd_7461949 := by
    simpa [prefixWord, tailWord_7461949, baseEnd_7461949] using wordTrace_append hprefix tailTrace_7461949
  have hstable : (prefixWord ++ tailWord_7461949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7461949).length < 2 ^ (prefixWord ++ tailWord_7461949).sum := by decide
  have hdescent : baseEnd_7461949 < baseStart_7461949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7461949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7461959 : List Nat := [1, 1, 4, 1, 3, 3, 2, 8]
def baseStart_7461959 : Nat := 118140960795 + 7461959 * 2 ^ 59
def prefixEnd_7461959 : Nat := 4983230072969 + 3 ^ 40 * 7461959 * 2
def baseEnd_7461959 : Nat := 141910058931225029066503

theorem tailTrace_7461959 : CollatzResearch.WordTrace tailWord_7461959 prefixEnd_7461959 141910058931225029066503 := by
  unfold tailWord_7461959
  simp only [CollatzResearch.WordTrace]
  refine ⟨272160003573604418982052931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181440002382402945988035287 272160003573604418982052931)
  ·
    refine ⟨408240005360406628473079397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272160003573604418982052931 408240005360406628473079397)
    ·
      refine ⟨76545001005076242838702387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 408240005360406628473079397 76545001005076242838702387)
      ·
        refine ⟨114817501507614364258053581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76545001005076242838702387 114817501507614364258053581)
        ·
          refine ⟨43056563065355386596770093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114817501507614364258053581 43056563065355386596770093)
          ·
            refine ⟨16146211149508269973788785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43056563065355386596770093 16146211149508269973788785)
            ·
              refine ⟨12109658362131202480341589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16146211149508269973788785 12109658362131202480341589)
              ·
                refine ⟨141910058931225029066503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12109658362131202480341589 141910058931225029066503)
                ·
                  rfl

theorem cell23_7461959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 8].length) (baseStart_7461959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7461959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7461959 prefixEnd_7461959 := by exact prefixLift 7461959
  have htrace : WordTrace (prefixWord ++ tailWord_7461959) baseStart_7461959 baseEnd_7461959 := by
    simpa [prefixWord, tailWord_7461959, baseEnd_7461959] using wordTrace_append hprefix tailTrace_7461959
  have hstable : (prefixWord ++ tailWord_7461959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7461959).length < 2 ^ (prefixWord ++ tailWord_7461959).sum := by decide
  have hdescent : baseEnd_7461959 < baseStart_7461959 := by decide
  rcases family_descends (prefixWord ++ tailWord_7461959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7462019 : List Nat := [1, 1, 1, 3, 3, 2, 3, 1, 2, 6]
def baseStart_7462019 : Nat := 118140960795 + 7462019 * 2 ^ 59
def prefixEnd_7462019 : Nat := 4983230072969 + 3 ^ 40 * 7462019 * 2
def baseEnd_7462019 : Nat := 1277200799994115183348435

theorem tailTrace_7462019 : CollatzResearch.WordTrace tailWord_7462019 prefixEnd_7462019 1277200799994115183348435 := by
  unfold tailWord_7462019
  simp only [CollatzResearch.WordTrace]
  refine ⟨272162191953387049229237111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181441461302258032819491407 272162191953387049229237111)
  ·
    refine ⟨408243287930080573843855667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272162191953387049229237111 408243287930080573843855667)
    ·
      refine ⟨612364931895120860765783501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408243287930080573843855667 612364931895120860765783501)
      ·
        refine ⟨229636849460670322787168813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 612364931895120860765783501 229636849460670322787168813)
        ·
          refine ⟨86113818547751371045188305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229636849460670322787168813 86113818547751371045188305)
          ·
            refine ⟨64585363910813528283891229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86113818547751371045188305 64585363910813528283891229)
            ·
              refine ⟨24219511466555073106459211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64585363910813528283891229 24219511466555073106459211)
              ·
                refine ⟨36329267199832609659688817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24219511466555073106459211 36329267199832609659688817)
                ·
                  refine ⟨27246950399874457244766613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36329267199832609659688817 27246950399874457244766613)
                  ·
                    refine ⟨1277200799994115183348435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27246950399874457244766613 1277200799994115183348435)
                    ·
                      rfl

theorem cell23_7462019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 6].length) (baseStart_7462019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7462019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7462019 prefixEnd_7462019 := by exact prefixLift 7462019
  have htrace : WordTrace (prefixWord ++ tailWord_7462019) baseStart_7462019 baseEnd_7462019 := by
    simpa [prefixWord, tailWord_7462019, baseEnd_7462019] using wordTrace_append hprefix tailTrace_7462019
  have hstable : (prefixWord ++ tailWord_7462019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7462019).length < 2 ^ (prefixWord ++ tailWord_7462019).sum := by decide
  have hdescent : baseEnd_7462019 < baseStart_7462019 := by decide
  rcases family_descends (prefixWord ++ tailWord_7462019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7462049 : List Nat := [1, 2, 3, 3, 1, 1, 1, 2, 9]
def baseStart_7462049 : Nat := 118140960795 + 7462049 * 2 ^ 59
def prefixEnd_7462049 : Nat := 4983230072969 + 3 ^ 40 * 7462049 * 2
def baseEnd_7462049 : Nat := 425735311600220048074463

theorem tailTrace_7462049 : CollatzResearch.WordTrace tailWord_7462049 prefixEnd_7462049 425735311600220048074463 := by
  unfold tailWord_7462049
  simp only [CollatzResearch.WordTrace]
  refine ⟨272163286143278364352829201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181442190762185576235219467 272163286143278364352829201)
  ·
    refine ⟨204122464607458773264621901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272163286143278364352829201 204122464607458773264621901)
    ·
      refine ⟨76545924227797039974233213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204122464607458773264621901 76545924227797039974233213)
      ·
        refine ⟨28704721585423889990337455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76545924227797039974233213 28704721585423889990337455)
        ·
          refine ⟨43057082378135834985506183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28704721585423889990337455 43057082378135834985506183)
          ·
            refine ⟨64585623567203752478259275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43057082378135834985506183 64585623567203752478259275)
            ·
              refine ⟨96878435350805628717388913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64585623567203752478259275 96878435350805628717388913)
              ·
                refine ⟨72658826513104221538041685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96878435350805628717388913 72658826513104221538041685)
                ·
                  refine ⟨425735311600220048074463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 72658826513104221538041685 425735311600220048074463)
                  ·
                    rfl

theorem cell23_7462049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 9].length) (baseStart_7462049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7462049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7462049 prefixEnd_7462049 := by exact prefixLift 7462049
  have htrace : WordTrace (prefixWord ++ tailWord_7462049) baseStart_7462049 baseEnd_7462049 := by
    simpa [prefixWord, tailWord_7462049, baseEnd_7462049] using wordTrace_append hprefix tailTrace_7462049
  have hstable : (prefixWord ++ tailWord_7462049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7462049).length < 2 ^ (prefixWord ++ tailWord_7462049).sum := by decide
  have hdescent : baseEnd_7462049 < baseStart_7462049 := by decide
  rcases family_descends (prefixWord ++ tailWord_7462049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7462059 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 2, 9, 3]
def baseStart_7462059 : Nat := 118140960795 + 7462059 * 2 ^ 59
def prefixEnd_7462059 : Nat := 4983230072969 + 3 ^ 40 * 7462059 * 2
def baseEnd_7462059 : Nat := 3831622939208525393545121

theorem tailTrace_7462059 : CollatzResearch.WordTrace tailWord_7462059 prefixEnd_7462059 3831622939208525393545121 := by
  unfold tailWord_7462059
  simp only [CollatzResearch.WordTrace]
  refine ⟨272163650873242136060693231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181442433915494757373795487 272163650873242136060693231)
  ·
    refine ⟨408245476309863204091039847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272163650873242136060693231 408245476309863204091039847)
    ·
      refine ⟨612368214464794806136559771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408245476309863204091039847 612368214464794806136559771)
      ·
        refine ⟨918552321697192209204839657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 612368214464794806136559771 918552321697192209204839657)
        ·
          refine ⟨688914241272894156903629743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 918552321697192209204839657 688914241272894156903629743)
          ·
            refine ⟨1033371361909341235355444615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 688914241272894156903629743 1033371361909341235355444615)
            ·
              refine ⟨1550057042864011853033166923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1033371361909341235355444615 1550057042864011853033166923)
              ·
                refine ⟨2325085564296017779549750385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1550057042864011853033166923 2325085564296017779549750385)
                ·
                  refine ⟨1743814173222013334662312789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2325085564296017779549750385 1743814173222013334662312789)
                  ·
                    refine ⟨10217661171222734382786989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 1743814173222013334662312789 10217661171222734382786989)
                    ·
                      refine ⟨3831622939208525393545121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10217661171222734382786989 3831622939208525393545121)
                      ·
                        rfl

theorem cell23_7462059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 9, 3].length) (baseStart_7462059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7462059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7462059 prefixEnd_7462059 := by exact prefixLift 7462059
  have htrace : WordTrace (prefixWord ++ tailWord_7462059) baseStart_7462059 baseEnd_7462059 := by
    simpa [prefixWord, tailWord_7462059, baseEnd_7462059] using wordTrace_append hprefix tailTrace_7462059
  have hstable : (prefixWord ++ tailWord_7462059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7462059).length < 2 ^ (prefixWord ++ tailWord_7462059).sum := by decide
  have hdescent : baseEnd_7462059 < baseStart_7462059 := by decide
  rcases family_descends (prefixWord ++ tailWord_7462059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7462066 : List Nat := [3, 2, 1, 1, 1, 5, 2, 1, 7]
def baseStart_7462066 : Nat := 118140960795 + 7462066 * 2 ^ 59
def prefixEnd_7462066 : Nat := 4983230072969 + 3 ^ 40 * 7462066 * 2
def baseEnd_7462066 : Nat := 425736281508122985128621

theorem tailTrace_7462066 : CollatzResearch.WordTrace tailWord_7462066 prefixEnd_7462066 425736281508122985128621 := by
  unfold tailWord_7462066
  simp only [CollatzResearch.WordTrace]
  refine ⟨68040976546054194064049513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181442604122811184170798701 68040976546054194064049513)
  ·
    refine ⟨51030732409540645548037135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68040976546054194064049513 51030732409540645548037135)
    ·
      refine ⟨76546098614310968322055703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51030732409540645548037135 76546098614310968322055703)
      ·
        refine ⟨114819147921466452483083555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76546098614310968322055703 114819147921466452483083555)
        ·
          refine ⟨172228721882199678724625333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114819147921466452483083555 172228721882199678724625333)
          ·
            refine ⟨16146442676456219880433625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 172228721882199678724625333 16146442676456219880433625)
            ·
              refine ⟨12109832007342164910325219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16146442676456219880433625 12109832007342164910325219)
              ·
                refine ⟨18164748011013247365487829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12109832007342164910325219 18164748011013247365487829)
                ·
                  refine ⟨425736281508122985128621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18164748011013247365487829 425736281508122985128621)
                  ·
                    rfl

theorem cell23_7462066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 7].length) (baseStart_7462066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7462066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7462066 prefixEnd_7462066 := by exact prefixLift 7462066
  have htrace : WordTrace (prefixWord ++ tailWord_7462066) baseStart_7462066 baseEnd_7462066 := by
    simpa [prefixWord, tailWord_7462066, baseEnd_7462066] using wordTrace_append hprefix tailTrace_7462066
  have hstable : (prefixWord ++ tailWord_7462066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7462066).length < 2 ^ (prefixWord ++ tailWord_7462066).sum := by decide
  have hdescent : baseEnd_7462066 < baseStart_7462066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7462066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7462079 : List Nat := [1, 1, 2, 2, 2, 2, 3, 2, 1, 7]
def baseStart_7462079 : Nat := 118140960795 + 7462079 * 2 ^ 59
def prefixEnd_7462079 : Nat := 4983230072969 + 3 ^ 40 * 7462079 * 2
def baseEnd_7462079 : Nat := 1277211069607205105098343

theorem tailTrace_7462079 : CollatzResearch.WordTrace tailWord_7462079 prefixEnd_7462079 1277211069607205105098343 := by
  unfold tailWord_7462079
  simp only [CollatzResearch.WordTrace]
  refine ⟨272164380333169679476421291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181442920222113119650947527 272164380333169679476421291)
  ·
    refine ⟨408246570499754519214631937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272164380333169679476421291 408246570499754519214631937)
    ·
      refine ⟨306184927874815889410973953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408246570499754519214631937 306184927874815889410973953)
      ·
        refine ⟨229638695906111917058230465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306184927874815889410973953 229638695906111917058230465)
        ·
          refine ⟨172229021929583937793672849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229638695906111917058230465 172229021929583937793672849)
          ·
            refine ⟨129171766447187953345254637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172229021929583937793672849 129171766447187953345254637)
            ·
              refine ⟨48439412417695482504470489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129171766447187953345254637 48439412417695482504470489)
              ·
                refine ⟨36329559313271611878352867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48439412417695482504470489 36329559313271611878352867)
                ·
                  refine ⟨54494338969907417817529301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36329559313271611878352867 54494338969907417817529301)
                  ·
                    refine ⟨1277211069607205105098343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54494338969907417817529301 1277211069607205105098343)
                    ·
                      rfl

theorem cell23_7462079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 7].length) (baseStart_7462079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7462079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7462079 prefixEnd_7462079 := by exact prefixLift 7462079
  have htrace : WordTrace (prefixWord ++ tailWord_7462079) baseStart_7462079 baseEnd_7462079 := by
    simpa [prefixWord, tailWord_7462079, baseEnd_7462079] using wordTrace_append hprefix tailTrace_7462079
  have hstable : (prefixWord ++ tailWord_7462079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7462079).length < 2 ^ (prefixWord ++ tailWord_7462079).sum := by decide
  have hdescent : baseEnd_7462079 < baseStart_7462079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7462079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7462116 : List Nat := [2, 3, 1, 1, 1, 2, 3, 1, 4, 1, 4]
def baseStart_7462116 : Nat := 118140960795 + 7462116 * 2 ^ 59
def prefixEnd_7462116 : Nat := 4983230072969 + 3 ^ 40 * 7462116 * 2
def baseEnd_7462116 : Nat := 3831652207605831670532359

theorem tailTrace_7462116 : CollatzResearch.WordTrace tailWord_7462116 prefixEnd_7462116 3831652207605831670532359 := by
  unfold tailWord_7462116
  simp only [CollatzResearch.WordTrace]
  refine ⟨136082864917017817397759101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181443819889357089863678801 136082864917017817397759101)
  ·
    refine ⟨51031074343881681524159663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136082864917017817397759101 51031074343881681524159663)
    ·
      refine ⟨76546611515822522286239495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51031074343881681524159663 76546611515822522286239495)
      ·
        refine ⟨114819917273733783429359243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76546611515822522286239495 114819917273733783429359243)
        ·
          refine ⟨172229875910600675144038865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114819917273733783429359243 172229875910600675144038865)
          ·
            refine ⟨129172406932950506358029149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172229875910600675144038865 129172406932950506358029149)
            ·
              refine ⟨48439652599856439884260931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129172406932950506358029149 48439652599856439884260931)
              ·
                refine ⟨72659478899784659826391397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48439652599856439884260931 72659478899784659826391397)
                ·
                  refine ⟨13623652293709623717448387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72659478899784659826391397 13623652293709623717448387)
                  ·
                    refine ⟨20435478440564435576172581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13623652293709623717448387 20435478440564435576172581)
                    ·
                      refine ⟨3831652207605831670532359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20435478440564435576172581 3831652207605831670532359)
                      ·
                        rfl

theorem cell23_7462116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_7462116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7462116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7462116 prefixEnd_7462116 := by exact prefixLift 7462116
  have htrace : WordTrace (prefixWord ++ tailWord_7462116) baseStart_7462116 baseEnd_7462116 := by
    simpa [prefixWord, tailWord_7462116, baseEnd_7462116] using wordTrace_append hprefix tailTrace_7462116
  have hstable : (prefixWord ++ tailWord_7462116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7462116).length < 2 ^ (prefixWord ++ tailWord_7462116).sum := by decide
  have hdescent : baseEnd_7462116 < baseStart_7462116 := by decide
  rcases family_descends (prefixWord ++ tailWord_7462116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7462153 : List Nat := [1, 2, 1, 1, 3, 3, 4, 1, 2, 2, 3]
def baseStart_7462153 : Nat := 118140960795 + 7462153 * 2 ^ 59
def prefixEnd_7462153 : Nat := 4983230072969 + 3 ^ 40 * 7462153 * 2
def baseEnd_7462153 : Nat := 3831671206390048025769689

theorem tailTrace_7462153 : CollatzResearch.WordTrace tailWord_7462153 prefixEnd_7462153 3831671206390048025769689 := by
  unfold tailWord_7462153
  simp only [CollatzResearch.WordTrace]
  refine ⟨272167079334901590114615113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181444719556601060076410075 272167079334901590114615113)
  ·
    refine ⟨204125309501176192585961335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272167079334901590114615113 204125309501176192585961335)
    ·
      refine ⟨306187964251764288878942003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204125309501176192585961335 306187964251764288878942003)
      ·
        refine ⟨459281946377646433318413005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306187964251764288878942003 459281946377646433318413005)
        ·
          refine ⟨172230729891617412494404877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 459281946377646433318413005 172230729891617412494404877)
          ·
            refine ⟨64586523709356529685401829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172230729891617412494404877 64586523709356529685401829)
            ·
              refine ⟨12109973195504349316012843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64586523709356529685401829 12109973195504349316012843)
              ·
                refine ⟨18164959793256523974019265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12109973195504349316012843 18164959793256523974019265)
                ·
                  refine ⟨13623719844942392980514449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18164959793256523974019265 13623719844942392980514449)
                  ·
                    refine ⟨10217789883706794735385837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13623719844942392980514449 10217789883706794735385837)
                    ·
                      refine ⟨3831671206390048025769689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10217789883706794735385837 3831671206390048025769689)
                      ·
                        rfl

theorem cell23_7462153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 2, 2, 3].length) (baseStart_7462153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7462153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7462153 prefixEnd_7462153 := by exact prefixLift 7462153
  have htrace : WordTrace (prefixWord ++ tailWord_7462153) baseStart_7462153 baseEnd_7462153 := by
    simpa [prefixWord, tailWord_7462153, baseEnd_7462153] using wordTrace_append hprefix tailTrace_7462153
  have hstable : (prefixWord ++ tailWord_7462153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7462153).length < 2 ^ (prefixWord ++ tailWord_7462153).sum := by decide
  have hdescent : baseEnd_7462153 < baseStart_7462153 := by decide
  rcases family_descends (prefixWord ++ tailWord_7462153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7462159 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 8]
def baseStart_7462159 : Nat := 118140960795 + 7462159 * 2 ^ 59
def prefixEnd_7462159 : Nat := 4983230072969 + 3 ^ 40 * 7462159 * 2
def baseEnd_7462159 : Nat := 3831674287273975002294661

theorem tailTrace_7462159 : CollatzResearch.WordTrace tailWord_7462159 prefixEnd_7462159 3831674287273975002294661 := by
  unfold tailWord_7462159
  simp only [CollatzResearch.WordTrace]
  refine ⟨272167298172879853139333531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181444865448586568759555687 272167298172879853139333531)
  ·
    refine ⟨408250947259319779709000297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272167298172879853139333531 408250947259319779709000297)
    ·
      refine ⟨306188210444489834781750223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408250947259319779709000297 306188210444489834781750223)
      ·
        refine ⟨459282315666734752172625335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306188210444489834781750223 459282315666734752172625335)
        ·
          refine ⟨688923473500102128258938003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459282315666734752172625335 688923473500102128258938003)
          ·
            refine ⟨1033385210250153192388407005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 688923473500102128258938003 1033385210250153192388407005)
            ·
              refine ⟨387519453843807447145652627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1033385210250153192388407005 387519453843807447145652627)
              ·
                refine ⟨581279180765711170718478941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 387519453843807447145652627 581279180765711170718478941)
                ·
                  refine ⟨217979692787141689019429603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 581279180765711170718478941 217979692787141689019429603)
                  ·
                    refine ⟨326969539180712533529144405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 217979692787141689019429603 326969539180712533529144405)
                    ·
                      refine ⟨3831674287273975002294661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 326969539180712533529144405 3831674287273975002294661)
                      ·
                        rfl

theorem cell23_7462159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 8].length) (baseStart_7462159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7462159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7462159 prefixEnd_7462159 := by exact prefixLift 7462159
  have htrace : WordTrace (prefixWord ++ tailWord_7462159) baseStart_7462159 baseEnd_7462159 := by
    simpa [prefixWord, tailWord_7462159, baseEnd_7462159] using wordTrace_append hprefix tailTrace_7462159
  have hstable : (prefixWord ++ tailWord_7462159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7462159).length < 2 ^ (prefixWord ++ tailWord_7462159).sum := by decide
  have hdescent : baseEnd_7462159 < baseStart_7462159 := by decide
  rcases family_descends (prefixWord ++ tailWord_7462159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7462173 : List Nat := [1, 4, 2, 3, 1, 1, 1, 4, 6]
def baseStart_7462173 : Nat := 118140960795 + 7462173 * 2 ^ 59
def prefixEnd_7462173 : Nat := 4983230072969 + 3 ^ 40 * 7462173 * 2
def baseEnd_7462173 : Nat := 425742386222570883057733

theorem tailTrace_7462173 : CollatzResearch.WordTrace tailWord_7462173 prefixEnd_7462173 425742386222570883057733 := by
  unfold tailWord_7462173
  simp only [CollatzResearch.WordTrace]
  refine ⟨272167808794829133530343173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181445205863219422353562115 272167808794829133530343173)
  ·
    refine ⟨51031464149030462536939345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 272167808794829133530343173 51031464149030462536939345)
    ·
      refine ⟨38273598111772846902704509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51031464149030462536939345 38273598111772846902704509)
      ·
        refine ⟨14352599291914817588514191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38273598111772846902704509 14352599291914817588514191)
        ·
          refine ⟨21528898937872226382771287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14352599291914817588514191 21528898937872226382771287)
          ·
            refine ⟨32293348406808339574156931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21528898937872226382771287 32293348406808339574156931)
            ·
              refine ⟨48440022610212509361235397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32293348406808339574156931 48440022610212509361235397)
              ·
                refine ⟨9082504239414845505231637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48440022610212509361235397 9082504239414845505231637)
                ·
                  refine ⟨425742386222570883057733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9082504239414845505231637 425742386222570883057733)
                  ·
                    rfl

theorem cell23_7462173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 4, 6].length) (baseStart_7462173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7462173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7462173 prefixEnd_7462173 := by exact prefixLift 7462173
  have htrace : WordTrace (prefixWord ++ tailWord_7462173) baseStart_7462173 baseEnd_7462173 := by
    simpa [prefixWord, tailWord_7462173, baseEnd_7462173] using wordTrace_append hprefix tailTrace_7462173
  have hstable : (prefixWord ++ tailWord_7462173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7462173).length < 2 ^ (prefixWord ++ tailWord_7462173).sum := by decide
  have hdescent : baseEnd_7462173 < baseStart_7462173 := by decide
  rcases family_descends (prefixWord ++ tailWord_7462173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7462220 : List Nat := [2, 2, 1, 3, 2, 2, 4, 1, 1, 5]
def baseStart_7462220 : Nat := 118140960795 + 7462220 * 2 ^ 59
def prefixEnd_7462220 : Nat := 4983230072969 + 3 ^ 40 * 7462220 * 2
def baseEnd_7462220 : Nat := 1277235203197966421210627

theorem tailTrace_7462220 : CollatzResearch.WordTrace tailWord_7462220 prefixEnd_7462220 1277235203197966421210627 := by
  unfold tailWord_7462220
  simp only [CollatzResearch.WordTrace]
  refine ⟨136084761512829430278652057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181446348683772573704869409 136084761512829430278652057)
  ·
    refine ⟨102063571134622072708989043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136084761512829430278652057 102063571134622072708989043)
    ·
      refine ⟨153095356701933109063483565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102063571134622072708989043 153095356701933109063483565)
      ·
        refine ⟨57410758763224915898806337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153095356701933109063483565 57410758763224915898806337)
        ·
          refine ⟨43058069072418686924104753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57410758763224915898806337 43058069072418686924104753)
          ·
            refine ⟨32293551804314015193078565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43058069072418686924104753 32293551804314015193078565)
            ·
              refine ⟨6055040963308877848702231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32293551804314015193078565 6055040963308877848702231)
              ·
                refine ⟨9082561444963316773053347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6055040963308877848702231 9082561444963316773053347)
                ·
                  refine ⟨13623842167444975159580021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9082561444963316773053347 13623842167444975159580021)
                  ·
                    refine ⟨1277235203197966421210627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13623842167444975159580021 1277235203197966421210627)
                    ·
                      rfl

theorem cell23_7462220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 1, 1, 5].length) (baseStart_7462220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7462220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7462220 prefixEnd_7462220 := by exact prefixLift 7462220
  have htrace : WordTrace (prefixWord ++ tailWord_7462220) baseStart_7462220 baseEnd_7462220 := by
    simpa [prefixWord, tailWord_7462220, baseEnd_7462220] using wordTrace_append hprefix tailTrace_7462220
  have hstable : (prefixWord ++ tailWord_7462220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7462220).length < 2 ^ (prefixWord ++ tailWord_7462220).sum := by decide
  have hdescent : baseEnd_7462220 < baseStart_7462220 := by decide
  rcases family_descends (prefixWord ++ tailWord_7462220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7462243 : List Nat := [1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 5]
def baseStart_7462243 : Nat := 118140960795 + 7462243 * 2 ^ 59
def prefixEnd_7462243 : Nat := 4983230072969 + 3 ^ 40 * 7462243 * 2
def baseEnd_7462243 : Nat := 3831717419648952673644275

theorem tailTrace_7462243 : CollatzResearch.WordTrace tailWord_7462243 prefixEnd_7462243 3831717419648952673644275 := by
  unfold tailWord_7462243
  simp only [CollatzResearch.WordTrace]
  refine ⟨272170361904575535485391383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181446907936383690323594255 272170361904575535485391383)
  ·
    refine ⟨408255542856863303228087075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272170361904575535485391383 408255542856863303228087075)
    ·
      refine ⟨612383314285294954842130613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408255542856863303228087075 612383314285294954842130613)
      ·
        refine ⟨57410935714246402016449745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 612383314285294954842130613 57410935714246402016449745)
        ·
          refine ⟨43058201785684801512337309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57410935714246402016449745 43058201785684801512337309)
          ·
            refine ⟨16146825669631800567126491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43058201785684801512337309 16146825669631800567126491)
            ·
              refine ⟨24220238504447700850689737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16146825669631800567126491 24220238504447700850689737)
              ·
                refine ⟨18165178878335775638017303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24220238504447700850689737 18165178878335775638017303)
                ·
                  refine ⟨27247768317503663457025955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18165178878335775638017303 27247768317503663457025955)
                  ·
                    refine ⟨40871652476255495185538933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27247768317503663457025955 40871652476255495185538933)
                    ·
                      refine ⟨3831717419648952673644275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40871652476255495185538933 3831717419648952673644275)
                      ·
                        rfl

theorem cell23_7462243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_7462243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7462243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7462243 prefixEnd_7462243 := by exact prefixLift 7462243
  have htrace : WordTrace (prefixWord ++ tailWord_7462243) baseStart_7462243 baseEnd_7462243 := by
    simpa [prefixWord, tailWord_7462243, baseEnd_7462243] using wordTrace_append hprefix tailTrace_7462243
  have hstable : (prefixWord ++ tailWord_7462243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7462243).length < 2 ^ (prefixWord ++ tailWord_7462243).sum := by decide
  have hdescent : baseEnd_7462243 < baseStart_7462243 := by decide
  rcases family_descends (prefixWord ++ tailWord_7462243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7462253 : List Nat := [1, 5, 1, 1, 1, 4, 1, 1, 1, 1, 6]
def baseStart_7462253 : Nat := 118140960795 + 7462253 * 2 ^ 59
def prefixEnd_7462253 : Nat := 4983230072969 + 3 ^ 40 * 7462253 * 2
def baseEnd_7462253 : Nat := 3831722554455497634519229

theorem tailTrace_7462253 : CollatzResearch.WordTrace tailWord_7462253 prefixEnd_7462253 3831722554455497634519229 := by
  unfold tailWord_7462253
  simp only [CollatzResearch.WordTrace]
  refine ⟨272170726634539307193255413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181447151089692871462170275 272170726634539307193255413)
  ·
    refine ⟨25516005621988060049367695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 272170726634539307193255413 25516005621988060049367695)
    ·
      refine ⟨38274008432982090074051543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25516005621988060049367695 38274008432982090074051543)
      ·
        refine ⟨57411012649473135111077315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38274008432982090074051543 57411012649473135111077315)
        ·
          refine ⟨86116518974209702666615973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57411012649473135111077315 86116518974209702666615973)
          ·
            refine ⟨16146847307664319249990495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86116518974209702666615973 16146847307664319249990495)
            ·
              refine ⟨24220270961496478874985743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16146847307664319249990495 24220270961496478874985743)
              ·
                refine ⟨36330406442244718312478615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24220270961496478874985743 36330406442244718312478615)
                ·
                  refine ⟨54495609663367077468717923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36330406442244718312478615 54495609663367077468717923)
                  ·
                    refine ⟨81743414495050616203076885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54495609663367077468717923 81743414495050616203076885)
                    ·
                      refine ⟨3831722554455497634519229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81743414495050616203076885 3831722554455497634519229)
                      ·
                        rfl

theorem cell23_7462253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_7462253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7462253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7462253 prefixEnd_7462253 := by exact prefixLift 7462253
  have htrace : WordTrace (prefixWord ++ tailWord_7462253) baseStart_7462253 baseEnd_7462253 := by
    simpa [prefixWord, tailWord_7462253, baseEnd_7462253] using wordTrace_append hprefix tailTrace_7462253
  have hstable : (prefixWord ++ tailWord_7462253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7462253).length < 2 ^ (prefixWord ++ tailWord_7462253).sum := by decide
  have hdescent : baseEnd_7462253 < baseStart_7462253 := by decide
  rcases family_descends (prefixWord ++ tailWord_7462253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7462333 : List Nat := [1, 4, 1, 2, 2, 1, 1, 3, 2, 1, 5]
def baseStart_7462333 : Nat := 118140960795 + 7462333 * 2 ^ 59
def prefixEnd_7462333 : Nat := 4983230072969 + 3 ^ 40 * 7462333 * 2
def baseEnd_7462333 : Nat := 3831763632907857321518861

theorem tailTrace_7462333 : CollatzResearch.WordTrace tailWord_7462333 prefixEnd_7462333 3831763632907857321518861 := by
  unfold tailWord_7462333
  simp only [CollatzResearch.WordTrace]
  refine ⟨272173644474249480856167653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181449096316166320570778435 272173644474249480856167653)
  ·
    refine ⟨51032558338921777660531435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 272173644474249480856167653 51032558338921777660531435)
    ·
      refine ⟨76548837508382666490797153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51032558338921777660531435 76548837508382666490797153)
      ·
        refine ⟨57411628131286999868097865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76548837508382666490797153 57411628131286999868097865)
        ·
          refine ⟨43058721098465249901073399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57411628131286999868097865 43058721098465249901073399)
          ·
            refine ⟨64588081647697874851610099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43058721098465249901073399 64588081647697874851610099)
            ·
              refine ⟨96882122471546812277415149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64588081647697874851610099 96882122471546812277415149)
              ·
                refine ⟨36330795926830054604030681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96882122471546812277415149 36330795926830054604030681)
                ·
                  refine ⟨27248096945122540953023011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36330795926830054604030681 27248096945122540953023011)
                  ·
                    refine ⟨40872145417683811429534517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27248096945122540953023011 40872145417683811429534517)
                    ·
                      refine ⟨3831763632907857321518861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40872145417683811429534517 3831763632907857321518861)
                      ·
                        rfl

theorem cell23_7462333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_7462333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7462333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7462333 prefixEnd_7462333 := by exact prefixLift 7462333
  have htrace : WordTrace (prefixWord ++ tailWord_7462333) baseStart_7462333 baseEnd_7462333 := by
    simpa [prefixWord, tailWord_7462333, baseEnd_7462333] using wordTrace_append hprefix tailTrace_7462333
  have hstable : (prefixWord ++ tailWord_7462333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7462333).length < 2 ^ (prefixWord ++ tailWord_7462333).sum := by decide
  have hdescent : baseEnd_7462333 < baseStart_7462333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7462333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7462343 : List Nat := [1, 1, 4, 1, 1, 3, 2, 2, 2, 2, 4]
def baseStart_7462343 : Nat := 118140960795 + 7462343 * 2 ^ 59
def prefixEnd_7462343 : Nat := 4983230072969 + 3 ^ 40 * 7462343 * 2
def baseEnd_7462343 : Nat := 3831768767714402282393815

theorem tailTrace_7462343 : CollatzResearch.WordTrace tailWord_7462343 prefixEnd_7462343 3831768767714402282393815 := by
  unfold tailWord_7462343
  simp only [CollatzResearch.WordTrace]
  refine ⟨272174009204213252564031683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181449339469475501709354455 272174009204213252564031683)
  ·
    refine ⟨408261013806319878846047525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272174009204213252564031683 408261013806319878846047525)
    ·
      refine ⟨76548940088684977283633911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 408261013806319878846047525 76548940088684977283633911)
      ·
        refine ⟨114823410133027465925450867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76548940088684977283633911 114823410133027465925450867)
        ·
          refine ⟨172235115199541198888176301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114823410133027465925450867 172235115199541198888176301)
          ·
            refine ⟨64588168199827949583066113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172235115199541198888176301 64588168199827949583066113)
            ·
              refine ⟨48441126149870962187299585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64588168199827949583066113 48441126149870962187299585)
              ·
                refine ⟨36330844612403221640474689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48441126149870962187299585 36330844612403221640474689)
                ·
                  refine ⟨27248133459302416230356017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36330844612403221640474689 27248133459302416230356017)
                  ·
                    refine ⟨20436100094476812172767013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27248133459302416230356017 20436100094476812172767013)
                    ·
                      refine ⟨3831768767714402282393815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20436100094476812172767013 3831768767714402282393815)
                      ·
                        rfl

theorem cell23_7462343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_7462343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7462343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7462343 prefixEnd_7462343 := by exact prefixLift 7462343
  have htrace : WordTrace (prefixWord ++ tailWord_7462343) baseStart_7462343 baseEnd_7462343 := by
    simpa [prefixWord, tailWord_7462343, baseEnd_7462343] using wordTrace_append hprefix tailTrace_7462343
  have hstable : (prefixWord ++ tailWord_7462343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7462343).length < 2 ^ (prefixWord ++ tailWord_7462343).sum := by decide
  have hdescent : baseEnd_7462343 < baseStart_7462343 := by decide
  rcases family_descends (prefixWord ++ tailWord_7462343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7462347 : List Nat := [1, 1, 1, 1, 3, 3, 3, 4, 2, 2, 2]
def baseStart_7462347 : Nat := 118140960795 + 7462347 * 2 ^ 59
def prefixEnd_7462347 : Nat := 4983230072969 + 3 ^ 40 * 7462347 * 2
def baseEnd_7462347 : Nat := 3831770821637020266743797

theorem tailTrace_7462347 : CollatzResearch.WordTrace tailWord_7462347 prefixEnd_7462347 3831770821637020266743797 := by
  unfold tailWord_7462347
  simp only [CollatzResearch.WordTrace]
  refine ⟨272174155096198761247177295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181449436730799174164784863 272174155096198761247177295)
  ·
    refine ⟨408261232644298141870765943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272174155096198761247177295 408261232644298141870765943)
    ·
      refine ⟨612391848966447212806148915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408261232644298141870765943 612391848966447212806148915)
      ·
        refine ⟨918587773449670819209223373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 612391848966447212806148915 918587773449670819209223373)
        ·
          refine ⟨344470415043626557203458765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 918587773449670819209223373 344470415043626557203458765)
          ·
            refine ⟨129176405641359958951297037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 344470415043626557203458765 129176405641359958951297037)
            ·
              refine ⟨48441152115509984606736389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129176405641359958951297037 48441152115509984606736389)
              ·
                refine ⟨9082716021658122113763073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48441152115509984606736389 9082716021658122113763073)
                ·
                  refine ⟨6812037016243591585322305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9082716021658122113763073 6812037016243591585322305)
                  ·
                    refine ⟨5109027762182693688991729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6812037016243591585322305 5109027762182693688991729)
                    ·
                      refine ⟨3831770821637020266743797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5109027762182693688991729 3831770821637020266743797)
                      ·
                        rfl

theorem cell23_7462347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 4, 2, 2, 2].length) (baseStart_7462347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7462347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7462347 prefixEnd_7462347 := by exact prefixLift 7462347
  have htrace : WordTrace (prefixWord ++ tailWord_7462347) baseStart_7462347 baseEnd_7462347 := by
    simpa [prefixWord, tailWord_7462347, baseEnd_7462347] using wordTrace_append hprefix tailTrace_7462347
  have hstable : (prefixWord ++ tailWord_7462347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7462347).length < 2 ^ (prefixWord ++ tailWord_7462347).sum := by decide
  have hdescent : baseEnd_7462347 < baseStart_7462347 := by decide
  rcases family_descends (prefixWord ++ tailWord_7462347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7462454 : List Nat := [5, 1, 2, 1, 3, 1, 1, 2, 2, 1, 4]
def baseStart_7462454 : Nat := 118140960795 + 7462454 * 2 ^ 59
def prefixEnd_7462454 : Nat := 4983230072969 + 3 ^ 40 * 7462454 * 2
def baseEnd_7462454 : Nat := 3831825764067051348105805

theorem tailTrace_7462454 : CollatzResearch.WordTrace tailWord_7462454 prefixEnd_7462454 3831825764067051348105805 := by
  unfold tailWord_7462454
  simp only [CollatzResearch.WordTrace]
  refine ⟨17011128606675694907582651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 181452038471207412347548277 17011128606675694907582651)
  ·
    refine ⟨25516692910013542361373977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17011128606675694907582651 25516692910013542361373977)
    ·
      refine ⟨19137519682510156771030483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25516692910013542361373977 19137519682510156771030483)
      ·
        refine ⟨28706279523765235156545725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19137519682510156771030483 28706279523765235156545725)
        ·
          refine ⟨10764854821411963183704647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28706279523765235156545725 10764854821411963183704647)
          ·
            refine ⟨16147282232117944775556971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10764854821411963183704647 16147282232117944775556971)
            ·
              refine ⟨24220923348176917163335457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16147282232117944775556971 24220923348176917163335457)
              ·
                refine ⟨18165692511132687872501593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24220923348176917163335457 18165692511132687872501593)
                ·
                  refine ⟨13624269383349515904376195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18165692511132687872501593 13624269383349515904376195)
                  ·
                    refine ⟨20436404075024273856564293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13624269383349515904376195 20436404075024273856564293)
                    ·
                      refine ⟨3831825764067051348105805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20436404075024273856564293 3831825764067051348105805)
                      ·
                        rfl

theorem cell23_7462454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_7462454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7462454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7462454 prefixEnd_7462454 := by exact prefixLift 7462454
  have htrace : WordTrace (prefixWord ++ tailWord_7462454) baseStart_7462454 baseEnd_7462454 := by
    simpa [prefixWord, tailWord_7462454, baseEnd_7462454] using wordTrace_append hprefix tailTrace_7462454
  have hstable : (prefixWord ++ tailWord_7462454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7462454).length < 2 ^ (prefixWord ++ tailWord_7462454).sum := by decide
  have hdescent : baseEnd_7462454 < baseStart_7462454 := by decide
  rcases family_descends (prefixWord ++ tailWord_7462454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7462457 : List Nat := [1, 2, 1, 5, 1, 3, 1, 2, 2, 2, 3]
def baseStart_7462457 : Nat := 118140960795 + 7462457 * 2 ^ 59
def prefixEnd_7462457 : Nat := 4983230072969 + 3 ^ 40 * 7462457 * 2
def baseEnd_7462457 : Nat := 3831827304509014836368291

theorem tailTrace_7462457 : CollatzResearch.WordTrace tailWord_7462457 prefixEnd_7462457 3831827304509014836368291 := by
  unfold tailWord_7462457
  simp only [CollatzResearch.WordTrace]
  refine ⟨272178167125800250033681625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181452111417200166689121083 272178167125800250033681625)
  ·
    refine ⟨204133625344350187525261219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272178167125800250033681625 204133625344350187525261219)
    ·
      refine ⟨306200438016525281287891829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204133625344350187525261219 306200438016525281287891829)
      ·
        refine ⟨28706291064049245120739859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 306200438016525281287891829 28706291064049245120739859)
        ·
          refine ⟨43059436596073867681109789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28706291064049245120739859 43059436596073867681109789)
          ·
            refine ⟨16147288723527700380416171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43059436596073867681109789 16147288723527700380416171)
            ·
              refine ⟨24220933085291550570624257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16147288723527700380416171 24220933085291550570624257)
              ·
                refine ⟨18165699813968662927968193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24220933085291550570624257 18165699813968662927968193)
                ·
                  refine ⟨13624274860476497195976145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18165699813968662927968193 13624274860476497195976145)
                  ·
                    refine ⟨10218206145357372896982109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13624274860476497195976145 10218206145357372896982109)
                    ·
                      refine ⟨3831827304509014836368291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10218206145357372896982109 3831827304509014836368291)
                      ·
                        rfl

theorem cell23_7462457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_7462457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7462457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7462457 prefixEnd_7462457 := by exact prefixLift 7462457
  have htrace : WordTrace (prefixWord ++ tailWord_7462457) baseStart_7462457 baseEnd_7462457 := by
    simpa [prefixWord, tailWord_7462457, baseEnd_7462457] using wordTrace_append hprefix tailTrace_7462457
  have hstable : (prefixWord ++ tailWord_7462457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7462457).length < 2 ^ (prefixWord ++ tailWord_7462457).sum := by decide
  have hdescent : baseEnd_7462457 < baseStart_7462457 := by decide
  rcases family_descends (prefixWord ++ tailWord_7462457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7462514 : List Nat := [3, 2, 1, 2, 3, 1, 2, 2, 2, 3, 2]
def baseStart_7462514 : Nat := 118140960795 + 7462514 * 2 ^ 59
def prefixEnd_7462514 : Nat := 4983230072969 + 3 ^ 40 * 7462514 * 2
def baseEnd_7462514 : Nat := 3831856572906321113355529

theorem tailTrace_7462514 : CollatzResearch.WordTrace tailWord_7462514 prefixEnd_7462514 3831856572906321113355529 := by
  unfold tailWord_7462514
  simp only [CollatzResearch.WordTrace]
  refine ⟨68045061521648437192126649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181453497391062499179004397 68045061521648437192126649)
  ·
    refine ⟨51033796141236327894094987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68045061521648437192126649 51033796141236327894094987)
    ·
      refine ⟨76550694211854491841142481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51033796141236327894094987 76550694211854491841142481)
      ·
        refine ⟨57413020658890868880856861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76550694211854491841142481 57413020658890868880856861)
        ·
          refine ⟨21529882747084075830321323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57413020658890868880856861 21529882747084075830321323)
          ·
            refine ⟨32294824120626113745481985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21529882747084075830321323 32294824120626113745481985)
            ·
              refine ⟨24221118090469585309111489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32294824120626113745481985 24221118090469585309111489)
              ·
                refine ⟨18165838567852188981833617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24221118090469585309111489 18165838567852188981833617)
                ·
                  refine ⟨13624378925889141736375213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18165838567852188981833617 13624378925889141736375213)
                  ·
                    refine ⟨5109142097208428151140705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13624378925889141736375213 5109142097208428151140705)
                    ·
                      refine ⟨3831856572906321113355529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5109142097208428151140705 3831856572906321113355529)
                      ·
                        rfl

theorem cell23_7462514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 2, 3, 2].length) (baseStart_7462514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7462514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7462514 prefixEnd_7462514 := by exact prefixLift 7462514
  have htrace : WordTrace (prefixWord ++ tailWord_7462514) baseStart_7462514 baseEnd_7462514 := by
    simpa [prefixWord, tailWord_7462514, baseEnd_7462514] using wordTrace_append hprefix tailTrace_7462514
  have hstable : (prefixWord ++ tailWord_7462514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7462514).length < 2 ^ (prefixWord ++ tailWord_7462514).sum := by decide
  have hdescent : baseEnd_7462514 < baseStart_7462514 := by decide
  rcases family_descends (prefixWord ++ tailWord_7462514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7462537 : List Nat := [1, 2, 1, 1, 4, 1, 4, 3, 2, 4]
def baseStart_7462537 : Nat := 118140960795 + 7462537 * 2 ^ 59
def prefixEnd_7462537 : Nat := 4983230072969 + 3 ^ 40 * 7462537 * 2
def baseEnd_7462537 : Nat := 1277289460987124841122641

theorem tailTrace_7462537 : CollatzResearch.WordTrace tailWord_7462537 prefixEnd_7462537 1277289460987124841122641 := by
  unfold tailWord_7462537
  simp only [CollatzResearch.WordTrace]
  refine ⟨272181084965510423696593865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181454056643673615797729243 272181084965510423696593865)
  ·
    refine ⟨204135813724132817772445399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272181084965510423696593865 204135813724132817772445399)
    ·
      refine ⟨306203720586199226658668099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204135813724132817772445399 306203720586199226658668099)
      ·
        refine ⟨459305580879298839988002149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306203720586199226658668099 459305580879298839988002149)
        ·
          refine ⟨86119796414868532497750403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 459305580879298839988002149 86119796414868532497750403)
          ·
            refine ⟨129179694622302798746625605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86119796414868532497750403 129179694622302798746625605)
            ·
              refine ⟨24221192741681774764992301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129179694622302798746625605 24221192741681774764992301)
              ·
                refine ⟨9082947278130665536872113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24221192741681774764992301 9082947278130665536872113)
                ·
                  refine ⟨6812210458597999152654085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9082947278130665536872113 6812210458597999152654085)
                  ·
                    refine ⟨1277289460987124841122641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6812210458597999152654085 1277289460987124841122641)
                    ·
                      rfl

theorem cell23_7462537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 3, 2, 4].length) (baseStart_7462537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7462537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7462537 prefixEnd_7462537 := by exact prefixLift 7462537
  have htrace : WordTrace (prefixWord ++ tailWord_7462537) baseStart_7462537 baseEnd_7462537 := by
    simpa [prefixWord, tailWord_7462537, baseEnd_7462537] using wordTrace_append hprefix tailTrace_7462537
  have hstable : (prefixWord ++ tailWord_7462537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7462537).length < 2 ^ (prefixWord ++ tailWord_7462537).sum := by decide
  have hdescent : baseEnd_7462537 < baseStart_7462537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7462537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7462548 : List Nat := [2, 4, 2, 2, 2, 2, 1, 1, 2, 3, 2]
def baseStart_7462548 : Nat := 118140960795 + 7462548 * 2 ^ 59
def prefixEnd_7462548 : Nat := 4983230072969 + 3 ^ 40 * 7462548 * 2
def baseEnd_7462548 : Nat := 3831874031248573980330373

theorem tailTrace_7462548 : CollatzResearch.WordTrace tailWord_7462548 prefixEnd_7462548 3831874031248573980330373 := by
  unfold tailWord_7462548
  simp only [CollatzResearch.WordTrace]
  refine ⟨136090743084235286287622149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181454324112313715050162865 136090743084235286287622149)
  ·
    refine ⟨25517014328294116178929153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136090743084235286287622149 25517014328294116178929153)
    ·
      refine ⟨19137760746220587134196865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25517014328294116178929153 19137760746220587134196865)
      ·
        refine ⟨14353320559665440350647649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19137760746220587134196865 14353320559665440350647649)
        ·
          refine ⟨10764990419749080262985737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14353320559665440350647649 10764990419749080262985737)
          ·
            refine ⟨8073742814811810197239303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10764990419749080262985737 8073742814811810197239303)
            ·
              refine ⟨12110614222217715295858955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8073742814811810197239303 12110614222217715295858955)
              ·
                refine ⟨18165921333326572943788433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12110614222217715295858955 18165921333326572943788433)
                ·
                  refine ⟨13624440999994929707841325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18165921333326572943788433 13624440999994929707841325)
                  ·
                    refine ⟨5109165374998098640440497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13624440999994929707841325 5109165374998098640440497)
                    ·
                      refine ⟨3831874031248573980330373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5109165374998098640440497 3831874031248573980330373)
                      ·
                        rfl

theorem cell23_7462548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_7462548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7462548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7462548 prefixEnd_7462548 := by exact prefixLift 7462548
  have htrace : WordTrace (prefixWord ++ tailWord_7462548) baseStart_7462548 baseEnd_7462548 := by
    simpa [prefixWord, tailWord_7462548, baseEnd_7462548] using wordTrace_append hprefix tailTrace_7462548
  have hstable : (prefixWord ++ tailWord_7462548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7462548).length < 2 ^ (prefixWord ++ tailWord_7462548).sum := by decide
  have hdescent : baseEnd_7462548 < baseStart_7462548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7462548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7462561 : List Nat := [1, 2, 3, 3, 2, 3, 2, 1, 1, 1, 4]
def baseStart_7462561 : Nat := 118140960795 + 7462561 * 2 ^ 59
def prefixEnd_7462561 : Nat := 4983230072969 + 3 ^ 40 * 7462561 * 2
def baseEnd_7462561 : Nat := 3831880706497082429467813

theorem tailTrace_7462561 : CollatzResearch.WordTrace tailWord_7462561 prefixEnd_7462561 3831880706497082429467813 := by
  unfold tailWord_7462561
  simp only [CollatzResearch.WordTrace]
  refine ⟨272181960317423475795467537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181454640211615650530311691 272181960317423475795467537)
  ·
    refine ⟨204136470238067606846600653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272181960317423475795467537 204136470238067606846600653)
    ·
      refine ⟨76551176339275352567475245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204136470238067606846600653 76551176339275352567475245)
      ·
        refine ⟨28706691127228257212803217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76551176339275352567475245 28706691127228257212803217)
        ·
          refine ⟨21530018345421192909602413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28706691127228257212803217 21530018345421192909602413)
          ·
            refine ⟨8073756879532947341100905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21530018345421192909602413 8073756879532947341100905)
            ·
              refine ⟨6055317659649710505825679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8073756879532947341100905 6055317659649710505825679)
              ·
                refine ⟨9082976489474565758738519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6055317659649710505825679 9082976489474565758738519)
                ·
                  refine ⟨13624464734211848638107779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9082976489474565758738519 13624464734211848638107779)
                  ·
                    refine ⟨20436697101317772957161669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13624464734211848638107779 20436697101317772957161669)
                    ·
                      refine ⟨3831880706497082429467813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20436697101317772957161669 3831880706497082429467813)
                      ·
                        rfl

theorem cell23_7462561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_7462561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7462561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7462561 prefixEnd_7462561 := by exact prefixLift 7462561
  have htrace : WordTrace (prefixWord ++ tailWord_7462561) baseStart_7462561 baseEnd_7462561 := by
    simpa [prefixWord, tailWord_7462561, baseEnd_7462561] using wordTrace_append hprefix tailTrace_7462561
  have hstable : (prefixWord ++ tailWord_7462561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7462561).length < 2 ^ (prefixWord ++ tailWord_7462561).sum := by decide
  have hdescent : baseEnd_7462561 < baseStart_7462561 := by decide
  rcases family_descends (prefixWord ++ tailWord_7462561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7462564 : List Nat := [2, 3, 1, 2, 2, 3, 1, 3, 1, 2, 3]
def baseStart_7462564 : Nat := 118140960795 + 7462564 * 2 ^ 59
def prefixEnd_7462564 : Nat := 4983230072969 + 3 ^ 40 * 7462564 * 2
def baseEnd_7462564 : Nat := 3831882246939045917730299

theorem tailTrace_7462564 : CollatzResearch.WordTrace tailWord_7462564 prefixEnd_7462564 3831882246939045917730299 := by
  unfold tailWord_7462564
  simp only [CollatzResearch.WordTrace]
  refine ⟨136091034868206303653913373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181454713157608404871884497 136091034868206303653913373)
  ·
    refine ⟨51034138075577363870217515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136091034868206303653913373 51034138075577363870217515)
    ·
      refine ⟨76551207113366045805326273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51034138075577363870217515 76551207113366045805326273)
      ·
        refine ⟨57413405335024534353994705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76551207113366045805326273 57413405335024534353994705)
        ·
          refine ⟨43060054001268400765496029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57413405335024534353994705 43060054001268400765496029)
          ·
            refine ⟨16147520250475650287061011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43060054001268400765496029 16147520250475650287061011)
            ·
              refine ⟨24221280375713475430591517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16147520250475650287061011 24221280375713475430591517)
              ·
                refine ⟨9082980140892553286471819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24221280375713475430591517 9082980140892553286471819)
                ·
                  refine ⟨13624470211338829929707729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9082980140892553286471819 13624470211338829929707729)
                  ·
                    refine ⟨10218352658504122447280797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13624470211338829929707729 10218352658504122447280797)
                    ·
                      refine ⟨3831882246939045917730299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10218352658504122447280797 3831882246939045917730299)
                      ·
                        rfl

theorem cell23_7462564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_7462564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7462564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7462564 prefixEnd_7462564 := by exact prefixLift 7462564
  have htrace : WordTrace (prefixWord ++ tailWord_7462564) baseStart_7462564 baseEnd_7462564 := by
    simpa [prefixWord, tailWord_7462564, baseEnd_7462564] using wordTrace_append hprefix tailTrace_7462564
  have hstable : (prefixWord ++ tailWord_7462564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7462564).length < 2 ^ (prefixWord ++ tailWord_7462564).sum := by decide
  have hdescent : baseEnd_7462564 < baseStart_7462564 := by decide
  rcases family_descends (prefixWord ++ tailWord_7462564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7462587 : List Nat := [1, 1, 1, 1, 1, 2, 3, 3, 5, 3, 2]
def baseStart_7462587 : Nat := 118140960795 + 7462587 * 2 ^ 59
def prefixEnd_7462587 : Nat := 4983230072969 + 3 ^ 40 * 7462587 * 2
def baseEnd_7462587 : Nat := 3831894056994099327742693

theorem tailTrace_7462587 : CollatzResearch.WordTrace tailWord_7462587 prefixEnd_7462587 3831894056994099327742693 := by
  unfold tailWord_7462587
  simp only [CollatzResearch.WordTrace]
  refine ⟨272182908615329282235914015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181455272410219521490609343 272182908615329282235914015)
  ·
    refine ⟨408274362922993923353871023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272182908615329282235914015 408274362922993923353871023)
    ·
      refine ⟨612411544384490885030806535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408274362922993923353871023 612411544384490885030806535)
      ·
        refine ⟨918617316576736327546209803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 612411544384490885030806535 918617316576736327546209803)
        ·
          refine ⟨1377925974865104491319314705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 918617316576736327546209803 1377925974865104491319314705)
          ·
            refine ⟨1033444481148828368489486029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1377925974865104491319314705 1033444481148828368489486029)
            ·
              refine ⟨387541680430810638183557261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1033444481148828368489486029 387541680430810638183557261)
              ·
                refine ⟨145328130161553989318833973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 387541680430810638183557261 145328130161553989318833973)
                ·
                  refine ⟨13624512202645686498640685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 145328130161553989318833973 13624512202645686498640685)
                  ·
                    refine ⟨5109192075992132436990257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13624512202645686498640685 5109192075992132436990257)
                    ·
                      refine ⟨3831894056994099327742693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5109192075992132436990257 3831894056994099327742693)
                      ·
                        rfl

theorem cell23_7462587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 5, 3, 2].length) (baseStart_7462587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7462587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7462587 prefixEnd_7462587 := by exact prefixLift 7462587
  have htrace : WordTrace (prefixWord ++ tailWord_7462587) baseStart_7462587 baseEnd_7462587 := by
    simpa [prefixWord, tailWord_7462587, baseEnd_7462587] using wordTrace_append hprefix tailTrace_7462587
  have hstable : (prefixWord ++ tailWord_7462587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7462587).length < 2 ^ (prefixWord ++ tailWord_7462587).sum := by decide
  have hdescent : baseEnd_7462587 < baseStart_7462587 := by decide
  rcases family_descends (prefixWord ++ tailWord_7462587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7462598 : List Nat := [6, 1, 2, 1, 1, 1, 1, 4, 1, 2, 3]
def baseStart_7462598 : Nat := 118140960795 + 7462598 * 2 ^ 59
def prefixEnd_7462598 : Nat := 4983230072969 + 3 ^ 40 * 7462598 * 2
def baseEnd_7462598 : Nat := 3831899705281298784705143

theorem tailTrace_7462598 : CollatzResearch.WordTrace tailWord_7462598 prefixEnd_7462598 3831899705281298784705143 := by
  unfold tailWord_7462598
  simp only [CollatzResearch.WordTrace]
  refine ⟨8505728431821544722330139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 181455539878859620743042965 8505728431821544722330139)
  ·
    refine ⟨12758592647732317083495209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8505728431821544722330139 12758592647732317083495209)
    ·
      refine ⟨9568944485799237812621407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12758592647732317083495209 9568944485799237812621407)
      ·
        refine ⟨14353416728698856718932111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9568944485799237812621407 14353416728698856718932111)
        ·
          refine ⟨21530125093048285078398167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14353416728698856718932111 21530125093048285078398167)
          ·
            refine ⟨32295187639572427617597251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21530125093048285078398167 32295187639572427617597251)
            ·
              refine ⟨48442781459358641426395877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32295187639572427617597251 48442781459358641426395877)
              ·
                refine ⟨9083021523629745267449227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48442781459358641426395877 9083021523629745267449227)
                ·
                  refine ⟨13624532285444617901173841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9083021523629745267449227 13624532285444617901173841)
                  ·
                    refine ⟨10218399214083463425880381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13624532285444617901173841 10218399214083463425880381)
                    ·
                      refine ⟨3831899705281298784705143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10218399214083463425880381 3831899705281298784705143)
                      ·
                        rfl

theorem cell23_7462598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_7462598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7462598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7462598 prefixEnd_7462598 := by exact prefixLift 7462598
  have htrace : WordTrace (prefixWord ++ tailWord_7462598) baseStart_7462598 baseEnd_7462598 := by
    simpa [prefixWord, tailWord_7462598, baseEnd_7462598] using wordTrace_append hprefix tailTrace_7462598
  have hstable : (prefixWord ++ tailWord_7462598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7462598).length < 2 ^ (prefixWord ++ tailWord_7462598).sum := by decide
  have hdescent : baseEnd_7462598 < baseStart_7462598 := by decide
  rcases family_descends (prefixWord ++ tailWord_7462598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7462640 : List Nat := [2, 1, 1, 1, 3, 1, 2, 5, 7]
def baseStart_7462640 : Nat := 118140960795 + 7462640 * 2 ^ 59
def prefixEnd_7462640 : Nat := 4983230072969 + 3 ^ 40 * 7462640 * 2
def baseEnd_7462640 : Nat := 425769030163198624486661

theorem tailTrace_7462640 : CollatzResearch.WordTrace tailWord_7462640 prefixEnd_7462640 425769030163198624486661 := by
  unfold tailWord_7462640
  simp only [CollatzResearch.WordTrace]
  refine ⟨136092420842068636143796687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181456561122758181525062249 136092420842068636143796687)
  ·
    refine ⟨204138631263102954215695031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136092420842068636143796687 204138631263102954215695031)
    ·
      refine ⟨306207946894654431323542547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204138631263102954215695031 306207946894654431323542547)
      ·
        refine ⟨459311920341981646985313821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306207946894654431323542547 459311920341981646985313821)
        ·
          refine ⟨172241970128243117619492683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 459311920341981646985313821 172241970128243117619492683)
          ·
            refine ⟨258362955192364676429239025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172241970128243117619492683 258362955192364676429239025)
            ·
              refine ⟨193772216394273507321929269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 258362955192364676429239025 193772216394273507321929269)
              ·
                refine ⟨18166145286963141311430869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 193772216394273507321929269 18166145286963141311430869)
                ·
                  refine ⟨425769030163198624486661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18166145286963141311430869 425769030163198624486661)
                  ·
                    rfl

theorem cell23_7462640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 7].length) (baseStart_7462640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7462640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7462640 prefixEnd_7462640 := by exact prefixLift 7462640
  have htrace : WordTrace (prefixWord ++ tailWord_7462640) baseStart_7462640 baseEnd_7462640 := by
    simpa [prefixWord, tailWord_7462640, baseEnd_7462640] using wordTrace_append hprefix tailTrace_7462640
  have hstable : (prefixWord ++ tailWord_7462640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7462640).length < 2 ^ (prefixWord ++ tailWord_7462640).sum := by decide
  have hdescent : baseEnd_7462640 < baseStart_7462640 := by decide
  rcases family_descends (prefixWord ++ tailWord_7462640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7462662 : List Nat := [6, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3]
def baseStart_7462662 : Nat := 118140960795 + 7462662 * 2 ^ 59
def prefixEnd_7462662 : Nat := 4983230072969 + 3 ^ 40 * 7462662 * 2
def baseEnd_7462662 : Nat := 3831932568043186534304849

theorem tailTrace_7462662 : CollatzResearch.WordTrace tailWord_7462662 prefixEnd_7462662 3831932568043186534304849 := by
  unfold tailWord_7462662
  simp only [CollatzResearch.WordTrace]
  refine ⟨8505801377814299063902945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 181457096060038380029929493 8505801377814299063902945)
  ·
    refine ⟨6379351033360724297927209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8505801377814299063902945 6379351033360724297927209)
    ·
      refine ⟨4784513275020543223445407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6379351033360724297927209 4784513275020543223445407)
      ·
        refine ⟨7176769912530814835168111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4784513275020543223445407 7176769912530814835168111)
        ·
          refine ⟨10765154868796222252752167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7176769912530814835168111 10765154868796222252752167)
          ·
            refine ⟨16147732303194333379128251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10765154868796222252752167 16147732303194333379128251)
            ·
              refine ⟨24221598454791500068692377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16147732303194333379128251 24221598454791500068692377)
              ·
                refine ⟨18166198841093625051519283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24221598454791500068692377 18166198841093625051519283)
                ·
                  refine ⟨27249298261640437577278925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18166198841093625051519283 27249298261640437577278925)
                  ·
                    refine ⟨10218486848115164091479597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27249298261640437577278925 10218486848115164091479597)
                    ·
                      refine ⟨3831932568043186534304849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10218486848115164091479597 3831932568043186534304849)
                      ·
                        rfl

theorem cell23_7462662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_7462662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7462662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7462662 prefixEnd_7462662 := by exact prefixLift 7462662
  have htrace : WordTrace (prefixWord ++ tailWord_7462662) baseStart_7462662 baseEnd_7462662 := by
    simpa [prefixWord, tailWord_7462662, baseEnd_7462662] using wordTrace_append hprefix tailTrace_7462662
  have hstable : (prefixWord ++ tailWord_7462662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7462662).length < 2 ^ (prefixWord ++ tailWord_7462662).sum := by decide
  have hdescent : baseEnd_7462662 < baseStart_7462662 := by decide
  rcases family_descends (prefixWord ++ tailWord_7462662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7462687 : List Nat := [1, 1, 2, 4, 2, 1, 1, 4, 2, 5]
def baseStart_7462687 : Nat := 118140960795 + 7462687 * 2 ^ 59
def prefixEnd_7462687 : Nat := 4983230072969 + 3 ^ 40 * 7462687 * 2
def baseEnd_7462687 : Nat := 1277315135019849645497411

theorem tailTrace_7462687 : CollatzResearch.WordTrace tailWord_7462687 prefixEnd_7462687 1277315135019849645497411 := by
  unfold tailWord_7462687
  simp only [CollatzResearch.WordTrace]
  refine ⟨272186555914966999314554315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181457703943311332876369543 272186555914966999314554315)
  ·
    refine ⟨408279833872450498971831473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272186555914966999314554315 408279833872450498971831473)
    ·
      refine ⟨306209875404337874228873605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408279833872450498971831473 306209875404337874228873605)
      ·
        refine ⟨57414351638313351417913801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 306209875404337874228873605 57414351638313351417913801)
        ·
          refine ⟨43060763728735013563435351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57414351638313351417913801 43060763728735013563435351)
          ·
            refine ⟨64591145593102520345153027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43060763728735013563435351 64591145593102520345153027)
            ·
              refine ⟨96886718389653780517729541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64591145593102520345153027 96886718389653780517729541)
              ·
                refine ⟨18166259698060083847074289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96886718389653780517729541 18166259698060083847074289)
                ·
                  refine ⟨13624694773545062885305717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18166259698060083847074289 13624694773545062885305717)
                  ·
                    refine ⟨1277315135019849645497411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13624694773545062885305717 1277315135019849645497411)
                    ·
                      rfl

theorem cell23_7462687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 2, 5].length) (baseStart_7462687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7462687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7462687 prefixEnd_7462687 := by exact prefixLift 7462687
  have htrace : WordTrace (prefixWord ++ tailWord_7462687) baseStart_7462687 baseEnd_7462687 := by
    simpa [prefixWord, tailWord_7462687, baseEnd_7462687] using wordTrace_append hprefix tailTrace_7462687
  have hstable : (prefixWord ++ tailWord_7462687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7462687).length < 2 ^ (prefixWord ++ tailWord_7462687).sum := by decide
  have hdescent : baseEnd_7462687 < baseStart_7462687 := by decide
  rcases family_descends (prefixWord ++ tailWord_7462687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7462737 : List Nat := [1, 2, 2, 1, 5, 1, 1, 1, 2, 1, 6]
def baseStart_7462737 : Nat := 118140960795 + 7462737 * 2 ^ 59
def prefixEnd_7462737 : Nat := 4983230072969 + 3 ^ 40 * 7462737 * 2
def baseEnd_7462737 : Nat := 3831971079092273740867003

theorem tailTrace_7462737 : CollatzResearch.WordTrace tailWord_7462737 prefixEnd_7462737 3831971079092273740867003 := by
  unfold tailWord_7462737
  simp only [CollatzResearch.WordTrace]
  refine ⟨272188379564785857853874465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181458919709857238569249643 272188379564785857853874465)
  ·
    refine ⟨204141284673589393390405849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272188379564785857853874465 204141284673589393390405849)
    ·
      refine ⟨153105963505192045042804387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204141284673589393390405849 153105963505192045042804387)
      ·
        refine ⟨229658945257788067564206581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153105963505192045042804387 229658945257788067564206581)
        ·
          refine ⟨21530526117917631334144367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 229658945257788067564206581 21530526117917631334144367)
          ·
            refine ⟨32295789176876447001216551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21530526117917631334144367 32295789176876447001216551)
            ·
              refine ⟨48443683765314670501824827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32295789176876447001216551 48443683765314670501824827)
              ·
                refine ⟨72665525647972005752737241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48443683765314670501824827 72665525647972005752737241)
                ·
                  refine ⟨54499144235979004314552931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72665525647972005752737241 54499144235979004314552931)
                  ·
                    refine ⟨81748716353968506471829397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54499144235979004314552931 81748716353968506471829397)
                    ·
                      refine ⟨3831971079092273740867003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81748716353968506471829397 3831971079092273740867003)
                      ·
                        rfl

theorem cell23_7462737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 1, 6].length) (baseStart_7462737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7462737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7462737 prefixEnd_7462737 := by exact prefixLift 7462737
  have htrace : WordTrace (prefixWord ++ tailWord_7462737) baseStart_7462737 baseEnd_7462737 := by
    simpa [prefixWord, tailWord_7462737, baseEnd_7462737] using wordTrace_append hprefix tailTrace_7462737
  have hstable : (prefixWord ++ tailWord_7462737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7462737).length < 2 ^ (prefixWord ++ tailWord_7462737).sum := by decide
  have hdescent : baseEnd_7462737 < baseStart_7462737 := by decide
  rcases family_descends (prefixWord ++ tailWord_7462737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7462751 : List Nat := [1, 1, 2, 3, 1, 4, 2, 4, 1, 4]
def baseStart_7462751 : Nat := 118140960795 + 7462751 * 2 ^ 59
def prefixEnd_7462751 : Nat := 4983230072969 + 3 ^ 40 * 7462751 * 2
def baseEnd_7462751 : Nat := 1277326089273812228697313

theorem tailTrace_7462751 : CollatzResearch.WordTrace tailWord_7462751 prefixEnd_7462751 1277326089273812228697313 := by
  unfold tailWord_7462751
  simp only [CollatzResearch.WordTrace]
  refine ⟨272188890186735138244884107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181459260124490092163256071 272188890186735138244884107)
  ·
    refine ⟨408283335280102707367326161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272188890186735138244884107 408283335280102707367326161)
    ·
      refine ⟨306212501460077030525494621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408283335280102707367326161 306212501460077030525494621)
      ·
        refine ⟨114829688047528886447060483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 306212501460077030525494621 114829688047528886447060483)
        ·
          refine ⟨172244532071293329670590725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114829688047528886447060483 172244532071293329670590725)
          ·
            refine ⟨32295849763367499313235761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172244532071293329670590725 32295849763367499313235761)
            ·
              refine ⟨24221887322525624484926821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32295849763367499313235761 24221887322525624484926821)
              ·
                refine ⟨4541603872973554590923779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24221887322525624484926821 4541603872973554590923779)
                ·
                  refine ⟨6812405809460331886385669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4541603872973554590923779 6812405809460331886385669)
                  ·
                    refine ⟨1277326089273812228697313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6812405809460331886385669 1277326089273812228697313)
                    ·
                      rfl

theorem cell23_7462751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 4, 1, 4].length) (baseStart_7462751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7462751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7462751 prefixEnd_7462751 := by exact prefixLift 7462751
  have htrace : WordTrace (prefixWord ++ tailWord_7462751) baseStart_7462751 baseEnd_7462751 := by
    simpa [prefixWord, tailWord_7462751, baseEnd_7462751] using wordTrace_append hprefix tailTrace_7462751
  have hstable : (prefixWord ++ tailWord_7462751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7462751).length < 2 ^ (prefixWord ++ tailWord_7462751).sum := by decide
  have hdescent : baseEnd_7462751 < baseStart_7462751 := by decide
  rcases family_descends (prefixWord ++ tailWord_7462751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7462784 : List Nat := [2, 1, 1, 2, 1, 2, 3, 3, 1, 5, 2]
def baseStart_7462784 : Nat := 118140960795 + 7462784 * 2 ^ 59
def prefixEnd_7462784 : Nat := 4983230072969 + 3 ^ 40 * 7462784 * 2
def baseEnd_7462784 : Nat := 3831995212683035056979287

theorem tailTrace_7462784 : CollatzResearch.WordTrace tailWord_7462784 prefixEnd_7462784 3831995212683035056979287 := by
  unfold tailWord_7462784
  simp only [CollatzResearch.WordTrace]
  refine ⟨136095046897807792440417703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181460062530410389920556937 136095046897807792440417703)
  ·
    refine ⟨204142570346711688660626555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136095046897807792440417703 204142570346711688660626555)
    ·
      refine ⟨306213855520067532990939833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204142570346711688660626555 306213855520067532990939833)
      ·
        refine ⟨229660391640050649743204875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306213855520067532990939833 229660391640050649743204875)
        ·
          refine ⟨344490587460075974614807313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229660391640050649743204875 344490587460075974614807313)
          ·
            refine ⟨258367940595056980961105485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 344490587460075974614807313 258367940595056980961105485)
            ·
              refine ⟨96887977723146367860414557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 258367940595056980961105485 96887977723146367860414557)
              ·
                refine ⟨36332991646179887947655459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96887977723146367860414557 36332991646179887947655459)
                ·
                  refine ⟨54499487469269831921483189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36332991646179887947655459 54499487469269831921483189)
                  ·
                    refine ⟨5109326950244046742639049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54499487469269831921483189 5109326950244046742639049)
                    ·
                      refine ⟨3831995212683035056979287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5109326950244046742639049 3831995212683035056979287)
                      ·
                        rfl

theorem cell23_7462784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 1, 5, 2].length) (baseStart_7462784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7462784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7462784 prefixEnd_7462784 := by exact prefixLift 7462784
  have htrace : WordTrace (prefixWord ++ tailWord_7462784) baseStart_7462784 baseEnd_7462784 := by
    simpa [prefixWord, tailWord_7462784, baseEnd_7462784] using wordTrace_append hprefix tailTrace_7462784
  have hstable : (prefixWord ++ tailWord_7462784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7462784).length < 2 ^ (prefixWord ++ tailWord_7462784).sum := by decide
  have hdescent : baseEnd_7462784 < baseStart_7462784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7462784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7462831 : List Nat := [1, 1, 2, 1, 2, 2, 4, 1, 5, 2, 2]
def baseStart_7462831 : Nat := 118140960795 + 7462831 * 2 ^ 59
def prefixEnd_7462831 : Nat := 4983230072969 + 3 ^ 40 * 7462831 * 2
def baseEnd_7462831 : Nat := 3832019346273796373091571

theorem tailTrace_7462831 : CollatzResearch.WordTrace tailWord_7462831 prefixEnd_7462831 3832019346273796373091571 := by
  unfold tailWord_7462831
  simp only [CollatzResearch.WordTrace]
  refine ⟨272191808026445311907796347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181461205350963541271864231 272191808026445311907796347)
  ·
    refine ⟨408287712039667967861694521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272191808026445311907796347 408287712039667967861694521)
    ·
      refine ⟨306215784029750975896270891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408287712039667967861694521 306215784029750975896270891)
      ·
        refine ⟨459323676044626463844406337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306215784029750975896270891 459323676044626463844406337)
        ·
          refine ⟨344492757033469847883304753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 459323676044626463844406337 344492757033469847883304753)
          ·
            refine ⟨258369567775102385912478565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 344492757033469847883304753 258369567775102385912478565)
            ·
              refine ⟨48444293957831697358589731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 258369567775102385912478565 48444293957831697358589731)
              ·
                refine ⟨72666440936747546037884597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48444293957831697358589731 72666440936747546037884597)
                ·
                  refine ⟨6812478837820082441051681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72666440936747546037884597 6812478837820082441051681)
                  ·
                    refine ⟨5109359128365061830788761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6812478837820082441051681 5109359128365061830788761)
                    ·
                      refine ⟨3832019346273796373091571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5109359128365061830788761 3832019346273796373091571)
                      ·
                        rfl

theorem cell23_7462831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 5, 2, 2].length) (baseStart_7462831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7462831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7462831 prefixEnd_7462831 := by exact prefixLift 7462831
  have htrace : WordTrace (prefixWord ++ tailWord_7462831) baseStart_7462831 baseEnd_7462831 := by
    simpa [prefixWord, tailWord_7462831, baseEnd_7462831] using wordTrace_append hprefix tailTrace_7462831
  have hstable : (prefixWord ++ tailWord_7462831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7462831).length < 2 ^ (prefixWord ++ tailWord_7462831).sum := by decide
  have hdescent : baseEnd_7462831 < baseStart_7462831 := by decide
  rcases family_descends (prefixWord ++ tailWord_7462831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7462882 : List Nat := [3, 3, 3, 1, 2, 1, 1, 2, 3, 2, 2]
def baseStart_7462882 : Nat := 118140960795 + 7462882 * 2 ^ 59
def prefixEnd_7462882 : Nat := 4983230072969 + 3 ^ 40 * 7462882 * 2
def baseEnd_7462882 : Nat := 3832045533787175673553837

theorem tailTrace_7462882 : CollatzResearch.WordTrace tailWord_7462882 prefixEnd_7462882 3832045533787175673553837 := by
  unfold tailWord_7462882
  simp only [CollatzResearch.WordTrace]
  refine ⟨68048417037315136904475725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181462445432840365078601933 68048417037315136904475725)
  ·
    refine ⟨25518156388993176339178397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68048417037315136904475725 25518156388993176339178397)
    ·
      refine ⟨9569308645872441127191899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25518156388993176339178397 9569308645872441127191899)
      ·
        refine ⟨14353962968808661690787849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9569308645872441127191899 14353962968808661690787849)
        ·
          refine ⟨10765472226606496268090887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14353962968808661690787849 10765472226606496268090887)
          ·
            refine ⟨16148208339909744402136331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10765472226606496268090887 16148208339909744402136331)
            ·
              refine ⟨24222312509864616603204497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16148208339909744402136331 24222312509864616603204497)
              ·
                refine ⟨18166734382398462452403373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24222312509864616603204497 18166734382398462452403373)
                ·
                  refine ⟨6812525393399423419651265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18166734382398462452403373 6812525393399423419651265)
                  ·
                    refine ⟨5109394045049567564738449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6812525393399423419651265 5109394045049567564738449)
                    ·
                      refine ⟨3832045533787175673553837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5109394045049567564738449 3832045533787175673553837)
                      ·
                        rfl

theorem cell23_7462882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_7462882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7462882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7462882 prefixEnd_7462882 := by exact prefixLift 7462882
  have htrace : WordTrace (prefixWord ++ tailWord_7462882) baseStart_7462882 baseEnd_7462882 := by
    simpa [prefixWord, tailWord_7462882, baseEnd_7462882] using wordTrace_append hprefix tailTrace_7462882
  have hstable : (prefixWord ++ tailWord_7462882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7462882).length < 2 ^ (prefixWord ++ tailWord_7462882).sum := by decide
  have hdescent : baseEnd_7462882 < baseStart_7462882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7462882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7462902 : List Nat := [5, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3]
def baseStart_7462902 : Nat := 118140960795 + 7462902 * 2 ^ 59
def prefixEnd_7462902 : Nat := 4983230072969 + 3 ^ 40 * 7462902 * 2
def baseEnd_7462902 : Nat := 3832055803400265595303745

theorem tailTrace_7462902 : CollatzResearch.WordTrace tailWord_7462902 prefixEnd_7462902 3832055803400265595303745 := by
  unfold tailWord_7462902
  simp only [CollatzResearch.WordTrace]
  refine ⟨17012149850574255689601935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 181462931739458727355753973 17012149850574255689601935)
  ·
    refine ⟨25518224775861383534402903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17012149850574255689601935 25518224775861383534402903)
    ·
      refine ⟨38277337163792075301604355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25518224775861383534402903 38277337163792075301604355)
      ·
        refine ⟨57416005745688112952406533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38277337163792075301604355 57416005745688112952406533)
        ·
          refine ⟨10765501077316521178576225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57416005745688112952406533 10765501077316521178576225)
          ·
            refine ⟨8074125807987390883932169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10765501077316521178576225 8074125807987390883932169)
            ·
              refine ⟨6055594355990543162949127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8074125807987390883932169 6055594355990543162949127)
              ·
                refine ⟨9083391533985814744423691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6055594355990543162949127 9083391533985814744423691)
                ·
                  refine ⟨13625087300978722116635537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9083391533985814744423691 13625087300978722116635537)
                  ·
                    refine ⟨10218815475734041587476653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13625087300978722116635537 10218815475734041587476653)
                    ·
                      refine ⟨3832055803400265595303745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10218815475734041587476653 3832055803400265595303745)
                      ·
                        rfl

theorem cell23_7462902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3].length) (baseStart_7462902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7462902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7462902 prefixEnd_7462902 := by exact prefixLift 7462902
  have htrace : WordTrace (prefixWord ++ tailWord_7462902) baseStart_7462902 baseEnd_7462902 := by
    simpa [prefixWord, tailWord_7462902, baseEnd_7462902] using wordTrace_append hprefix tailTrace_7462902
  have hstable : (prefixWord ++ tailWord_7462902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7462902).length < 2 ^ (prefixWord ++ tailWord_7462902).sum := by decide
  have hdescent : baseEnd_7462902 < baseStart_7462902 := by decide
  rcases family_descends (prefixWord ++ tailWord_7462902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7462908 : List Nat := [2, 2, 2, 1, 2, 2, 3, 3, 1, 3, 2]
def baseStart_7462908 : Nat := 118140960795 + 7462908 * 2 ^ 59
def prefixEnd_7462908 : Nat := 4983230072969 + 3 ^ 40 * 7462908 * 2
def baseEnd_7462908 : Nat := 3832058884284192571828717

theorem tailTrace_7462908 : CollatzResearch.WordTrace tailWord_7462908 prefixEnd_7462908 3832058884284192571828717 := by
  unfold tailWord_7462908
  simp only [CollatzResearch.WordTrace]
  refine ⟨136097308223583177029174689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181463077631444236038899585 136097308223583177029174689)
  ·
    refine ⟨102072981167687382771881017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136097308223583177029174689 102072981167687382771881017)
    ·
      refine ⟨76554735875765537078910763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102072981167687382771881017 76554735875765537078910763)
      ·
        refine ⟨114832103813648305618366145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76554735875765537078910763 114832103813648305618366145)
        ·
          refine ⟨86124077860236229213774609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114832103813648305618366145 86124077860236229213774609)
          ·
            refine ⟨64593058395177171910330957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86124077860236229213774609 64593058395177171910330957)
            ·
              refine ⟨24222396898191439466374109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64593058395177171910330957 24222396898191439466374109)
              ·
                refine ⟨9083398836821789799890291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24222396898191439466374109 9083398836821789799890291)
                ·
                  refine ⟨13625098255232684699835437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9083398836821789799890291 13625098255232684699835437)
                  ·
                    refine ⟨5109411845712256762438289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13625098255232684699835437 5109411845712256762438289)
                    ·
                      refine ⟨3832058884284192571828717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5109411845712256762438289 3832058884284192571828717)
                      ·
                        rfl

theorem cell23_7462908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 3, 1, 3, 2].length) (baseStart_7462908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7462908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7462908 prefixEnd_7462908 := by exact prefixLift 7462908
  have htrace : WordTrace (prefixWord ++ tailWord_7462908) baseStart_7462908 baseEnd_7462908 := by
    simpa [prefixWord, tailWord_7462908, baseEnd_7462908] using wordTrace_append hprefix tailTrace_7462908
  have hstable : (prefixWord ++ tailWord_7462908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7462908).length < 2 ^ (prefixWord ++ tailWord_7462908).sum := by decide
  have hdescent : baseEnd_7462908 < baseStart_7462908 := by decide
  rcases family_descends (prefixWord ++ tailWord_7462908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7462932 : List Nat := [2, 4, 3, 2, 1, 2, 1, 1, 1, 3, 3]
def baseStart_7462932 : Nat := 118140960795 + 7462932 * 2 ^ 59
def prefixEnd_7462932 : Nat := 4983230072969 + 3 ^ 40 * 7462932 * 2
def baseEnd_7462932 : Nat := 3832071207819900477928607

theorem tailTrace_7462932 : CollatzResearch.WordTrace tailWord_7462932 prefixEnd_7462932 3832071207819900477928607 := by
  unfold tailWord_7462932
  simp only [CollatzResearch.WordTrace]
  refine ⟨136097745899539703078611525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181463661199386270771482033 136097745899539703078611525)
  ·
    refine ⟨25518327356163694327239661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136097745899539703078611525 25518327356163694327239661)
    ·
      refine ⟨9569372758561385372714873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25518327356163694327239661 9569372758561385372714873)
      ·
        refine ⟨7177029568921039029536155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9569372758561385372714873 7177029568921039029536155)
        ·
          refine ⟨10765544353381558544304233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7177029568921039029536155 10765544353381558544304233)
          ·
            refine ⟨8074158265036168908228175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10765544353381558544304233 8074158265036168908228175)
            ·
              refine ⟨12111237397554253362342263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8074158265036168908228175 12111237397554253362342263)
              ·
                refine ⟨18166856096331380043513395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12111237397554253362342263 18166856096331380043513395)
                ·
                  refine ⟨27250284144497070065270093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18166856096331380043513395 27250284144497070065270093)
                  ·
                    refine ⟨10218856554186401274476285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27250284144497070065270093 10218856554186401274476285)
                    ·
                      refine ⟨3832071207819900477928607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10218856554186401274476285 3832071207819900477928607)
                      ·
                        rfl

theorem cell23_7462932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_7462932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7462932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7462932 prefixEnd_7462932 := by exact prefixLift 7462932
  have htrace : WordTrace (prefixWord ++ tailWord_7462932) baseStart_7462932 baseEnd_7462932 := by
    simpa [prefixWord, tailWord_7462932, baseEnd_7462932] using wordTrace_append hprefix tailTrace_7462932
  have hstable : (prefixWord ++ tailWord_7462932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7462932).length < 2 ^ (prefixWord ++ tailWord_7462932).sum := by decide
  have hdescent : baseEnd_7462932 < baseStart_7462932 := by decide
  rcases family_descends (prefixWord ++ tailWord_7462932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
